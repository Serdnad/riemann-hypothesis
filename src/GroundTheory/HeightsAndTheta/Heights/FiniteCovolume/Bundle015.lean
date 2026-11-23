module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.MajorantInvolutionDiagonalForm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open GroundTheory.Automorphic Matrix
open scoped ComplexOrder

noncomputable section

theorem KTransitive.proof (ι : Type*) [Fintype ι] [DecidableEq ι]
    (h₁ : IsotropicSplit.Statement ι) (h₂ : EigenReflectionMaps.Statement ι)
    (h₃ : PhaseOnMinus.Statement ι) (_h₄ : EigenspacesOrthogonal.Statement ι) :
    KTransitive.Statement ι := by
  intro H P hmaj z z' hz hz' hzH hz'H
  obtain ⟨ha, hb, hab⟩ := h₁ H P hmaj z hzH
  obtain ⟨ha', hb', hab'⟩ := h₁ H P hmaj z' hz'H
  have hsplit : ∀ w : ι → ℂ, plusPart H P w + minusPart H P w = w := by
    intro w; ext i; simp only [plusPart, minusPart, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul]; ring
  have hPpos := hmaj.1
  have hne : ∀ w : ι → ℂ, w ≠ 0 →
      star (plusPart H P w) ⬝ᵥ (P *ᵥ plusPart H P w) =
        star (minusPart H P w) ⬝ᵥ (P *ᵥ minusPart H P w) → plusPart H P w ≠ 0 := by
    intro w hw heq h0
    apply hw
    rw [h0] at heq
    simp only [star_zero, zero_dotProduct] at heq
    have hm : minusPart H P w = 0 := by
      by_contra hm
      exact (hPpos.dotProduct_mulVec_pos hm).ne heq
    rw [← hsplit w, h0, hm, add_zero]
  set a := plusPart H P z with ha_def
  set b := minusPart H P z with hb_def
  set a' := plusPart H P z' with ha'_def
  set b' := minusPart H P z' with hb'_def
  have ha0 : a ≠ 0 := hne z hz hab
  have ha'0 : a' ≠ 0 := hne z' hz' hab'
  have hp := hPpos.dotProduct_mulVec_pos ha0
  have hq := hPpos.dotProduct_mulVec_pos ha'0
  set p := star a ⬝ᵥ (P *ᵥ a) with hp_def
  set q := star a' ⬝ᵥ (P *ᵥ a') with hq_def
  obtain ⟨hpr, hpi⟩ := Complex.lt_def.mp hp
  obtain ⟨hqr, hqi⟩ := Complex.lt_def.mp hq
  simp only [Complex.zero_re, Complex.zero_im] at hpr hpi hqr hqi
  set t : ℝ := Real.sqrt (p.re / q.re) with ht_def
  have ht : 0 < t := Real.sqrt_pos.mpr (div_pos hpr hqr)
  have htt : t * t = p.re / q.re := Real.mul_self_sqrt (div_nonneg hpr.le hqr.le)
  have ht2 : (t : ℂ) * t * q = p := by
    have key : t * t * q.re = p.re := by rw [htt, div_mul_cancel₀ _ hqr.ne']
    apply Complex.ext
    · simp [Complex.mul_re, ← hqi, key]
    · simp [Complex.mul_im, ← hqi, ← hpi]
  have hscale : ∀ v : ι → ℂ, star ((t : ℂ) • v) ⬝ᵥ (P *ᵥ ((t : ℂ) • v)) =
      (t : ℂ) * t * (star v ⬝ᵥ (P *ᵥ v)) := by
    intro v
    rw [star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct]
    simp only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
    ring
  have hA1 : majInvolution H P *ᵥ ((t : ℂ) • a') = (1 : ℂ) • ((t : ℂ) • a') := by
    rw [mulVec_smul, ha', one_smul]
  have hAm : majInvolution H P *ᵥ ((t : ℂ) • b') = (-1 : ℂ) • ((t : ℂ) • b') := by
    rw [mulVec_smul, hb', neg_one_smul, smul_neg]
  obtain ⟨α, hα, Rp, hRpP, hRpH, hRpa, hRpfix⟩ := h₂ H P hmaj 1 (Or.inl rfl) a ((t : ℂ) • a')
    (by rw [ha, one_smul]) hA1 (by rw [hscale, ht2])
  obtain ⟨β, hβ, Rm, hRmP, hRmH, hRmb, hRmfix⟩ := h₂ H P hmaj (-1) (Or.inr rfl) b ((t : ℂ) • b')
    (by rw [hb, neg_one_smul]) hAm (by rw [hscale, ← hab', ht2, hab])
  have hβ0 : β ≠ 0 := by
    intro h; rw [h, norm_zero] at hβ; exact zero_ne_one hβ
  have hc : ‖α / β‖ = 1 := by rw [norm_div, hα, hβ, div_one]
  obtain ⟨hDP, hDH, hDplus, hDminus⟩ := h₃ H P hmaj (α / β) hc
  set D := phaseOnMinus H P (α / β) with hD_def
  set M := D * Rm * Rp with hM_def
  have hunit : ∀ X : Matrix ι ι ℂ, Dᴴ * X * D = X → Rmᴴ * X * Rm = X → Rpᴴ * X * Rp = X →
      Mᴴ * X * M = X := by
    intro X h1 h2 h3
    have e : Mᴴ * X * M = Rpᴴ * (Rmᴴ * (Dᴴ * X * D) * Rm) * Rp := by
      simp only [hM_def, conjTranspose_mul, Matrix.mul_assoc]
    rw [e, h1, h2, h3]
  have hMH : Mᴴ * H * M = H := hunit H hDH hRmH hRpH
  have hMP : Mᴴ * P * M = P := hunit P hDP hRmP hRpP
  have hct : ∀ X : Matrix ι ι ℂ, (X.map (starRingEnd ℂ))ᵀ = Xᴴ := fun X => by
    ext i j; simp [conjTranspose_apply]
  have hRma : Rm *ᵥ a = a := hRmfix a (by rw [ha, neg_neg, one_smul])
  have hMz : M *ᵥ ((t : ℂ) • z') = α • z := by
    have hz'2 : (t : ℂ) • z' = (t : ℂ) • a' + (t : ℂ) • b' := by rw [← smul_add, hsplit z']
    rw [hz'2, hM_def, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_add, hRpa, hRpfix _ hAm,
      mulVec_add, mulVec_smul, hRma, hRmb, mulVec_add, mulVec_smul, mulVec_smul, hDplus a ha,
      hDminus b hb, smul_smul, mul_div_cancel₀ _ hβ0, ← smul_add, hsplit z]
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hdet : IsUnit M.det := isUnit_det_of_unitary (starRingEnd ℂ) hmaj.2.2.1 (by rw [hct]; exact hMH)
  refine ⟨nonsingInvUnit M hdet, ?_, ?_, (t : ℂ)⁻¹ * α, ?_⟩
  · rw [mem_unitaryGroupMatrix]
    show (M.map (starRingEnd ℂ))ᵀ * H * M = H
    rw [hct]; exact hMH
  · rw [mem_unitaryGroupMatrix]
    show (M.map (starRingEnd ℂ))ᵀ * P * M = P
    rw [hct]; exact hMP
  · show M *ᵥ z' = ((t : ℂ)⁻¹ * α) • z
    rw [mulVec_smul] at hMz
    rw [mul_smul, ← hMz, smul_smul, inv_mul_cancel₀ htc, one_smul]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [DecidableEq ι] in
theorem star_mulVec_dotProduct_mulVec_mulVec (M H : Matrix ι ι ℂ) (y z : ι → ℂ) :
    star (M *ᵥ y) ⬝ᵥ (H *ᵥ (M *ᵥ z)) = star y ⬝ᵥ ((Mᴴ * H * M) *ᵥ z) := by
  rw [star_mulVec, mulVec_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mul_assoc]

theorem ArchInvariant.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    ArchInvariant.Statement h v := by
  intro g y z w
  have hmem := mem_archUnitary.mp (g⁻¹ : archUnitary h v).2 w
  set M : Matrix ι ι ℂ := (((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)
    with hM
  have hct : (M.map (starRingEnd ℂ))ᵀ = Mᴴ := by
    ext i j
    simp [conjTranspose_apply]
  rw [hct] at hmem
  show star (M *ᵥ y w) ⬝ᵥ (gramAt h v w *ᵥ (M *ᵥ z w)) = star (y w) ⬝ᵥ (gramAt h v w *ᵥ z w)
  rw [star_mulVec_dotProduct_mulVec_mulVec, hmem]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField Module

theorem CoeffLatticeBasis.proof (E : Type*) [Field E] [NumberField E] :
    CoeffLatticeBasis.Statement E := by
  intro A hO hfg
  have : AddGroup.FG A := (AddGroup.fg_iff_addSubgroup_fg A).mpr hfg
  obtain ⟨n, b⟩ : Σ n : ℕ, Basis (Fin n) ℤ A := Module.basisOfFiniteTypeTorsionFree'

  let f : A →ₗ[ℤ] E := A.subtype.toIntLinearMap
  let v : Fin n → E := fun i => (b i : E)
  have hv : v = f ∘ b := rfl
  have hliZ : LinearIndependent ℤ v :=
    b.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hliQ : LinearIndependent ℚ v := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hliZ

  have hA : ∀ a ∈ A, a ∈ Submodule.span ℚ (Set.range v) := by
    intro a ha
    have h1 : f ⟨a, ha⟩ ∈ Submodule.span ℤ (f '' Set.range b) :=
      Submodule.apply_mem_span_image_of_mem_span f (b.mem_span _)
    rw [← Set.range_comp, ← hv] at h1
    exact Submodule.span_le_restrictScalars ℤ ℚ _ h1
  have hsp : ⊤ ≤ Submodule.span ℚ (Set.range v) := by
    rw [← (integralBasis E).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [integralBasis_apply]
    exact hA _ (hO ⟨_, rfl⟩)
  have hn : finrank ℚ E = n := by
    rw [finrank_eq_card_basis (Basis.mk hliQ hsp), Fintype.card_fin]
  exact ⟨b.reindex (finCongr hn.symm)⟩

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem GramAtData.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    GramAtData.Statement h v := by
  intro w
  refine ⟨?_, ?_⟩
  · ext i j
    simp only [gramAt, conjTranspose_apply, map_apply, Automorphic.gram_apply]
    change starRingEnd ℂ (w.embedding (h.toSesq (v j) (v i))) = w.embedding (h.toSesq (v i) (v j))
    rw [← embedding_conj (F := F) w.embedding]
    congr 1
    exact h.isSymm.eq (v j) (v i)
  · simp only [gramAt]
    rw [show ((gram h.toSesq v).map w.embedding).det = w.embedding (gram h.toSesq v).det from
      (RingHom.map_det w.embedding _).symm]
    exact (isUnit_det_gram h v).map w.embedding

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

section Places

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem HermAtPlace.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    HermAtPlace.Statement h v := by
  intro w x y
  rw [sesq_eq_sum h.toSesq v x y]

  simp only [map_sum, map_mul, embedding_conj, dotProduct, mulVec, gramAt, vecAt, Pi.star_apply,
  Matrix.map_apply, Finset.mul_sum, RCLike.star_def]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Places

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Matrix

theorem IsotropicSplit.proof (ι : Type*) [Fintype ι] [DecidableEq ι]
    (h₁ : EigenspacesOrthogonal.Statement ι) : IsotropicSplit.Statement ι := by
  intro H P hM z hz
  obtain ⟨hP, hH, hdet, hPHP⟩ := hM
  set A := majInvolution H P with hAdef
  have hA2 : A * A = 1 := by
    rw [hAdef, majInvolution, show H⁻¹ * P * (H⁻¹ * P) = H⁻¹ * (P * H⁻¹ * P) by
      simp only [Matrix.mul_assoc], hPHP, nonsing_inv_mul H hdet]
  have hPA : P * A = H := by
    rw [hAdef, majInvolution, ← Matrix.mul_assoc, hPHP]
  have hAA (v : ι → ℂ) : A *ᵥ (A *ᵥ v) = v := by
    rw [mulVec_mulVec, hA2, one_mulVec]
  set a := plusPart H P z with hadef
  set b := minusPart H P z with hbdef
  have ha : A *ᵥ a = a := by
    rw [hadef, plusPart, ← hAdef, mulVec_smul, mulVec_add, hAA, add_comm]
  have hb : A *ᵥ b = -b := by
    rw [hbdef, minusPart, ← hAdef, mulVec_smul, mulVec_sub, hAA, ← smul_neg, neg_sub]
  have hzab : z = a + b := by
    rw [hadef, hbdef, plusPart, minusPart, ← smul_add]
    ext i
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hAzab : A *ᵥ z = a - b := by
    rw [hadef, hbdef, plusPart, minusPart, ← hAdef, ← smul_sub]
    ext i
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hab : star a ⬝ᵥ (P *ᵥ b) = 0 := h₁ H P ⟨hP, hH, hdet, hPHP⟩ a b ha hb
  have hba : star b ⬝ᵥ (P *ᵥ a) = 0 := by
    rw [star_dotProduct, star_mulVec, ← dotProduct_mulVec, hP.1.eq, hab, star_zero]
  refine ⟨ha, hb, ?_⟩
  have h0 : star (a + b) ⬝ᵥ (P *ᵥ (a - b)) = 0 := by
    rw [← hAzab, ← hzab, mulVec_mulVec, hPA, hz]
  rw [star_add, add_dotProduct, mulVec_sub, dotProduct_sub, dotProduct_sub, hab, hba] at h0
  linear_combination h0

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

noncomputable section

variable {E : Type*} [Field E]
variable (W : Type*) [AddCommGroup W] [Module E W]

theorem LineCoeffsFG.proof : LineCoeffsFG.Statement (E := E) W := by
  intro La x hLa hx
  let f : E →+ W := (smulAddHom E W).flip x
  have hf : Function.Injective f.toIntLinearMap := by
    intro a b hab
    have h : a • x = b • x := hab
    exact smul_left_injective E hx h
  have hS : La.toIntSubmodule.FG := by
    rw [Submodule.fg_iff_addSubgroup_fg]
    simpa using hLa
  have hle : (lineCoeffs (E := E) La x).toIntSubmodule.map f.toIntLinearMap ≤
      La.toIntSubmodule := by
    rintro _ ⟨a, ha, rfl⟩
    exact ha
  have hN : (lineCoeffs (E := E) La x).toIntSubmodule.FG :=
    Submodule.fg_of_fg_map_injective _ hf (hS.of_le hle)
  rw [Submodule.fg_iff_addSubgroup_fg] at hN
  simpa using hN

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField

variable (E : Type*) [Field E] [NumberField E]
variable (W : Type*) [AddCommGroup W] [Module E W]

theorem LineIndexCoeffs.proof : LineIndexCoeffs.Statement (E := E) W := by
  intro La x hx
  let f : E →+ W := (smulAddHom E W).flip x
  have hfa : ∀ a : E, f a = a • x := fun a => rfl
  have hf : Function.Injective f := by
    intro a b hab
    rw [hfa, hfa] at hab
    exact smul_left_injective E hx hab
  have h1 : (intSubgroup E).map f = ringMultiples E x := by
    rw [intSubgroup, ringMultiples, AddMonoidHom.range_comp]
  have hrange : f.range = (Submodule.span E {x}).toAddSubgroup := by
    ext y
    simp only [AddMonoidHom.mem_range, Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton,
      hfa]
  have h2 : (lineCoeffs La x).map f = La ⊓ (Submodule.span E {x}).toAddSubgroup := by
    rw [lineCoeffs, AddSubgroup.map_comap_eq, hrange, inf_comm]
  unfold lineIndex
  rw [← h1, ← h2, AddSubgroup.relIndex_map_map_of_injective _ _ hf]

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Module Matrix

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (d : ℕ) [Fact (finrank ℝ V = d)]

theorem VolumeFormIntComb.proof : VolumeFormIntComb.Statement V d := by
  intro o b T
  have hd : finrank ℝ V = d := Fact.out
  let e : Basis (Fin d) ℝ V := Module.finBasisOfFinrankEq ℝ V hd
  have key : ∀ v : Fin d → V, o.volumeForm v = o.volumeForm e * e.det v := by
    intro v
    conv_lhs => rw [AlternatingMap.eq_smul_basis_det e o.volumeForm]
    rfl
  have hmat : e.toMatrix (fun i => ∑ j, (T i j : ℝ) • b j) =
      e.toMatrix b * (T.map (Int.cast : ℤ → ℝ))ᵀ := by
    ext k i

    simp [Basis.toMatrix_apply, Matrix.mul_apply, map_sum, map_smul, Finset.sum_apply,
    mul_comm]
  rw [key, key b, Basis.det_apply, Basis.det_apply, hmat, det_mul, det_transpose,
    Int.cast_det T]
  ring

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField Module Matrix
open scoped ComplexOrder

section Steps

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem WeightPos.proof (h : GroundTheory.Automorphic.HermitianForm F E W) (v : Basis ι E W)
    (h₁ : VecAtNeZero.Statement v) : WeightPos.Statement h v := by
  intro M g x hx w
  set k : GL ι ℂ := ((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w with hk
  have hne : invApply g (vecAt v x) w ≠ 0 := by
    intro hz
    have hz' : (k : Matrix ι ι ℂ) *ᵥ vecAt v x w = 0 := hz
    have h2 : ((k⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) *ᵥ ((k : Matrix ι ι ℂ) *ᵥ vecAt v x w) = 0 := by
      rw [hz', mulVec_zero]
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec] at h2
    exact h₁ x hx w h2
  have hpos := (M.posDef w).dotProduct_mulVec_pos hne
  exact (Complex.pos_iff.mp hpos).1

end Steps

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField NumberField.InfinitePlace Module

theorem WeightedSpaceDim.proof (E : Type*) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] :
    WeightedSpaceDim.Statement E := by
  unfold WeightedSpaceDim.Statement
  rw [finrank_euclideanSpace, Fintype.card_prod, Fintype.card_fin,
    card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero,
    IsTotallyComplex.finrank]
  ring

end GroundTheory.Heights₂.Heights.FiniteCovolume
end
