module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle004
public import Development.AutomorphicArithmetic.CMTraceEmbeddings.Bundle001
public import Development.AutomorphicArithmetic.CMTraceEmbeddings.Bundle002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle223
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle007
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle003
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Heckecomm
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015

@[expose] public section

section

noncomputable section

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed.Ori

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private def dv (A : Arith E) (n : ℕ) (σ : E →+* ℂ) (i : Fin n) : ℂ :=
  if 0 < (σ (A.hd n i : E)).re then Complex.I else -Complex.I

private theorem hd_ne (hS : HdSign) (A : Arith E) (n : ℕ) (σ : E →+* ℂ) (i : Fin n) : (σ (A.hd n i : E)).re ≠ 0 := by
  obtain ⟨-, -, h1, h2⟩ := hS E A n σ i
  by_cases h : InfinitePlace.mk σ = InfinitePlace.mk A.τ₀ ∧ (i : ℕ) = 0
  · exact (h1 h).ne'
  · exact (h2 h).ne

private theorem dv_sq (A : Arith E) (n : ℕ) (σ : E →+* ℂ) (i : Fin n) : dv A n σ i * dv A n σ i = -1 := by
  unfold dv; split_ifs <;> simp

private theorem dv_conj (A : Arith E) (n : ℕ) (σ : E →+* ℂ) (i : Fin n) :
    (starRingEnd ℂ) (dv A n σ i) = -dv A n σ i := by
  unfold dv; split_ifs <;> simp

private theorem gram_diag (A : Arith E) (n : ℕ) (σ : E →+* ℂ) :
    gramAt (A.H n) σ = Matrix.diagonal fun i => σ (A.hd n i : E) := by
  ext i j
  simp only [gramAt, Arith.H, Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h
    simp
  · simp [h, Ne.symm h]

private theorem real_abs (h : ℂ) (hi : h.im = 0) (hr : h.re ≠ 0) :
    -Complex.I * (h * (if 0 < h.re then Complex.I else -Complex.I)) = ((|h.re| : ℝ) : ℂ) ∧
    Complex.I * (h * (starRingEnd ℂ) (if 0 < h.re then Complex.I else -Complex.I)) = ((|h.re| : ℝ) : ℂ) := by
  have hh : h = ((h.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hi])
  split_ifs with hp
  · rw [abs_of_pos hp]
    constructor
    · rw [hh]
      ring_nf
      simp
    · rw [hh]
      simp
      ring_nf
      simp
  · rw [abs_of_neg (lt_of_le_of_ne (not_lt.mp hp) hr)]
    constructor
    · rw [hh]
      ring_nf
      simp
    · rw [hh]
      simp
      ring_nf
      simp

open scoped ComplexOrder in
private theorem posDiag {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    (Matrix.diagonal fun i => ((a i : ℝ) : ℂ)).PosDef := by
  rw [Matrix.posDef_diagonal_iff]
  intro i
  exact Complex.zero_lt_real.mpr (ha i)

open scoped Classical ComplexOrder in
private theorem orient_core (hT : TraceType) (hS : HdSign) (A : Arith E) (n : ℕ)
    (rep : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Module.End ℚ (ℚ ⊗[ℤ] (Fin n → 𝓞 E))) (hrep : RepOK A n rep) :
    ∃ J : ℝ ⊗[ℚ] Matrix (Fin n) (Fin n) E, J * J = -1 ∧
      (starT (hermStar (A.H n) (A.det_ne n)) ℝ J).unop = -J ∧
      (∀ x, x ≠ 0 → 0 < ((A.EF n).baseChange ℚ).baseChange ℝ (actOn rep ℝ J x) x) ∧
      ∀ v : InfinitePlace E, ((if v.embedding (A.ω : E) = A.τ₀ (A.ω : E) then -Complex.I else Complex.I) •
        (gramAt (A.H n) v.embedding * evM v.embedding J)).PosDef := by
  obtain ⟨J, hJ⟩ := (cmField_real_tensor_matrix_bijective_cmType hT A n).2 (fun τ : Phi A => Matrix.diagonal (dv A n τ.1))
  have hJτ : ∀ τ : Phi A, evM τ.1 J = Matrix.diagonal (dv A n τ.1) := fun τ => congrFun hJ τ
  have hne : ∀ (σ : E →+* ℂ) (i : Fin n), σ (A.hd n i : E) ≠ 0 := fun σ i h0 =>
    hd_ne hS A n σ i (by rw [h0]; simp)
  obtain ⟨β, hβ1, hβ2⟩ := hrep
  refine ⟨J, ?_, ?_, ?_, ?_⟩
  · refine (cmField_real_tensor_matrix_bijective_cmType hT A n).1 (funext fun τ => ?_)
    dsimp only
    rw [map_mul, map_neg, map_one, hJτ, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [dv_sq]
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  · refine (cmField_real_tensor_matrix_bijective_cmType hT A n).1 (funext fun τ => ?_)
    dsimp only
    have key := evM_star (A.H n) (A.herm n) (A.det_ne n) τ.1 J
    rw [gram_diag, hJτ, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal] at key
    rw [map_neg, hJτ]
    ext i j
    have hk := congrFun (congrFun key i) j
    rw [Matrix.diagonal_mul] at hk
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq, Pi.star_apply, Matrix.neg_apply] at hk ⊢
      apply mul_left_cancel₀ (hne τ.1 i)
      rw [hk, Complex.star_def, dv_conj]
      ring
    · simp only [Matrix.diagonal_apply_ne _ hij, Matrix.neg_apply, neg_zero] at hk ⊢
      exact (mul_eq_zero.mp hk).resolve_left (hne τ.1 i)
  · intro x hx
    rw [cmField_hermitianForm_baseChange_real_eq_sum hT A n (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℚ] Fin n → E) hβ1]
    have hterm : ∀ k : Phi A × Fin n,
        Th (fun τ : Phi A => (τ : E →+* ℂ)) (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℚ] Fin n → E) (actOn rep ℝ J x) k =
          dv A n k.1.1 k.2 * Th (fun τ : Phi A => (τ : E →+* ℂ)) (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℚ] Fin n → E) x k := by
      rintro ⟨τ, i⟩
      rw [Th_act (fun τ : Phi A => (τ : E →+* ℂ)) (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℚ] Fin n → E) rep hβ2 J x τ i,
        hJτ, Matrix.mulVec_diagonal]
    have hz : ∃ k, Th (fun τ : Phi A => (τ : E →+* ℂ)) (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℚ] Fin n → E) x k ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply hx
      apply cmType_trace_embedding_injective_of_linearEquiv hT A n β
      rw [map_zero]
      funext k
      exact hc k
    obtain ⟨k₀, hk₀⟩ := hz
    have tp := fun (τ : Phi A) (i : Fin n) (z : ℂ) => term_pos (τ.1 A.δ) (τ.1 (A.hd n i : E)) z
      (hS E A n τ.1 i).2.1 (A.δ_sign τ.1 τ.2) (hS E A n τ.1 i).1 (hd_ne hS A n τ.1 i)
    apply Finset.sum_pos'
    · rintro ⟨τ, i⟩ -
      rw [hterm]
      unfold dv
      exact mul_nonneg two_pos.le (tp τ i _).1
    · refine ⟨k₀, Finset.mem_univ _, ?_⟩
      obtain ⟨τ, i⟩ := k₀
      rw [hterm]
      unfold dv
      exact mul_pos two_pos ((tp τ i _).2 hk₀)
  · intro v
    obtain ⟨τ, hτv, -⟩ := (hT E A).2.2.1 v
    subst hτv
    have hω := (hT E A).2.2.2
    rcases InfinitePlace.embedding_mk_eq (τ : E →+* ℂ) with he | he
    · rw [he, if_pos τ.2, gram_diag, hJτ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]
      have hf : (-Complex.I • fun i => τ.1 (A.hd n i : E) * dv A n τ.1 i) =
          fun i => (((|(τ.1 (A.hd n i : E)).re| : ℝ)) : ℂ) := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul]
        exact (real_abs _ (hS E A n τ.1 i).1 (hd_ne hS A n τ.1 i)).1
      rw [hf]
      exact posDiag _ fun i => abs_pos.mpr (hd_ne hS A n τ.1 i)
    · have hc : ¬ (ComplexEmbedding.conjugate (τ : E →+* ℂ)) (A.ω : E) = A.τ₀ (A.ω : E) := by
        intro h
        rw [ComplexEmbedding.conjugate_coe_eq, τ.2] at h
        exact hω (Complex.conj_eq_iff_im.mp h)
      rw [he, if_neg hc, gram_diag, evM_conj, hJτ, Matrix.diagonal_map (map_zero _),
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]
      have hf : (Complex.I • fun i => (ComplexEmbedding.conjugate (τ : E →+* ℂ)) (A.hd n i : E) *
          (starRingEnd ℂ) (dv A n τ.1 i)) = fun i => (((|(τ.1 (A.hd n i : E)).re| : ℝ)) : ℂ) := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, ComplexEmbedding.conjugate_coe_eq]
        rw [Complex.conj_eq_iff_im.mpr (hS E A n τ.1 i).1]
        exact (real_abs _ (hS E A n τ.1 i).1 (hd_ne hS A n τ.1 i)).2
      rw [hf]
      exact posDiag _ fun i => abs_pos.mpr (hd_ne hS A n τ.1 i)

end UpperTheory.Gal.W2.Seed.Ori

theorem UpperTheory.Gal.W2.Seed.pOrient :
    TraceType → HdSign → Orient := by
  intro hT hS E _ _ _ A n hn hs p _ P rep hrep
  exact UpperTheory.Gal.W2.Seed.Ori.orient_core hT hS A n rep hrep
end
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.W2.Seed.IntRev

private theorem mem_range_map {R : Type} [CommRing R] (S : Subring R) {m : ℕ} (x : GL (Fin m) R)
    (h1 : ∀ i j, x.1 i j ∈ S) (h2 : ∀ i j, (x⁻¹).1 i j ∈ S) : x ∈ (GeneralLinearGroup.map S.subtype).range := by
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, ?_, ?_⟩, rfl⟩
  · refine Matrix.map_injective S.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · refine Matrix.map_injective S.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

variable {E : Type} [Field E] [NumberField E] {p : ℕ} [Fact p.Prime]

private theorem norm_le (τ : E →+* PadicAlgCl p) (x : E)
    (h : ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → w.valuation E x ≤ 1) : ‖τ x‖ ≤ 1 := by
  have hp : p.Prime := Fact.out
  obtain ⟨N, -, hNc, hN⟩ := GlobalTheory.HilbertThetaSeries.DenP.exists_away hp x
  have hint : IsIntegral ℤ ((N : E) * x) := by
    refine (GlobalTheory.HilbertThetaSeries.DenP.isIntegral_iff_val _).2 fun w => ?_
    by_cases hw : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal
    · rw [map_mul, GlobalTheory.HilbertThetaSeries.DenP.val_coprime hNc hw, one_mul]; exact h w hw
    · exact hN w hw
  have h1 : ‖τ ((N : E) * x)‖ ≤ 1 := GlobalTheory.CongW.PlaceEmb.norm_int_le τ ⟨_, hint⟩
  have h3 : ‖(N : ℚ_[p])‖ = 1 := (Padic.norm_natCast_eq_one_iff).2 hNc.symm
  have h2 : ‖(N : PadicAlgCl p)‖ = 1 := by
    rw [← h3, ← PadicAlgCl.norm_extends p, map_natCast]
  rwa [map_mul, map_natCast, norm_mul, h2, one_mul] at h1

variable [IsCMField E] {n : ℕ}

private theorem entry_le (y : Gam0 E n) (hy : ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w (rat y) ∈ GlobalTheory.LFun.KGL w (n := n))
    (τ : E →+* PadicAlgCl p) (i j : Fin n) : ‖τ (y.1.1.val i j)‖ ≤ 1 := by
  refine norm_le τ _ fun w hw => ?_
  have h1 : (comp w (rat y)).val i j ∈ w.adicCompletionIntegers E := (GlobalTheory.AdelicU.mem_GLint_iff.1 (hy w hw)).1 i j
  have h2 : (comp w (rat y)).val i j = ((y.1.1.val i j : E) : w.adicCompletion E) := rfl
  rw [h2, HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h1
  exact h1

private theorem hyp_inv (y : Gam0 E n) (hy : ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w (rat y) ∈ GlobalTheory.LFun.KGL w (n := n)) :
    ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w (rat y⁻¹) ∈ GlobalTheory.LFun.KGL w (n := n) := fun w hw => by
  rw [map_inv, map_inv]; exact inv_mem (hy w hw)

private theorem mult_le (hn : 0 < n) (τ : E →+* PadicAlgCl p) (y : Gam0 E n)
    (hy : ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w (rat y) ∈ GlobalTheory.LFun.KGL w (n := n)) :
    algebraMap ℚ_[p] (PadicAlgCl p) (algebraMap ℚ ℚ_[p] (y.1.2 : ℚ)) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p := by
  have h : (y.1.1.val.map (GlobalTheory.SplitPts.conjE E).toRingHom)ᵀ * y.1.1.val =
      algebraMap ℚ E y.1.2 • (1 : Matrix (Fin n) (Fin n) E) := y.2.1
  have h0 := congrArg τ (congrFun (congrFun h ⟨0, hn⟩) ⟨0, hn⟩)

  rw [Matrix.mul_apply, map_sum, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h0
  have e : algebraMap ℚ_[p] (PadicAlgCl p) (algebraMap ℚ ℚ_[p] (y.1.2 : ℚ)) = τ (algebraMap ℚ E y.1.2) := by
    simp only [eq_ratCast, map_ratCast]
  rw [e, ← h0]
  refine sum_mem fun k _ => ?_
  rw [map_mul]
  exact mul_mem (ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff.2 (entry_le y hy (τ.comp (GlobalTheory.SplitPts.conjE E).toRingHom) k ⟨0, hn⟩))
    (ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff.2 (entry_le y hy τ k ⟨0, hn⟩))

omit [NumberField E] [IsCMField E] in
private theorem incl_mem (τ : E →+* PadicAlgCl p) (x : E) (hx : ‖τ x‖ ≤ 1) :
    GlobalTheory.LKRes.inclK p (FwOf τ) 1 (embOf τ x) ∈ GlobalTheory.LKRes.intKQ p (FwOf τ) 1 :=
  Subring.subset_closure (Or.inl ⟨⟨embOf τ x, ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff.2 hx⟩, rfl⟩)

end UpperTheory.Gal.W2.Seed.IntRev

open UpperTheory.Gal.W2.Seed.IntRev in
theorem UpperTheory.Gal.W2.Seed.pPIntRev :
    IntConj → PIntRev := by
  intro _ E _ _ _ A n p _ S y hy
  have hn : 0 < n := S.facts.pos
  have hy' := hyp_inv y hy
  refine Subgroup.mem_prod.2 ⟨mem_range_map _ _ (fun i j => ?_) (fun i j => ?_),
    (Subgroup.mem_pi _).2 fun k _ => mem_range_map _ _ (fun i j => ?_) (fun i j => ?_)⟩
  · obtain rfl : i = j := Subsingleton.elim _ _
    have h := mult_le hn (S.P.iotaP.comp S.P.s) y hy
    show Matrix.scalar (Fin 1) _ i i ∈ _
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
    exact h
  · obtain rfl : i = j := Subsingleton.elim _ _
    have h := mult_le hn (S.P.iotaP.comp S.P.s) y⁻¹ hy'
    show Matrix.scalar (Fin 1) _ i i ∈ _
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
    exact h
  · exact incl_mem (S.P.emb k) (y.1.1.val i j) (entry_le y hy (S.P.emb k) i j)
  · exact incl_mem (S.P.emb k) ((y⁻¹).1.1.val i j) (entry_le y⁻¹ hy' (S.P.emb k) i j)
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.W2.Seed

private theorem hAct_slice {X V : Type} [Group X] [AddCommGroup V] [Module ℂ V] (K : Subgroup X)
    (hK : IsCommensurated K) (f : X → ℂ) (hf : f ∈ Hecke ℂ K) (φ : X → V) (L : V →ₗ[ℂ] V) (a g : X) :
    hAct K f (fun x => L (φ (a * x))) g = L (hAct K f φ (a * g)) := by
  have hfin := Formalism.UG.P.finite_supp K hK f hf
  unfold hAct
  rw [map_finsum L (hfin.subset (fun x hx => by
    intro h0; apply hx; simp [h0]))]
  refine finsum_congr fun x => ?_
  rw [map_smul, mul_assoc]

private theorem op_eq {p : ℕ} [Fact p.Prime] {G : HTGroup p} {V : Type} [AddCommGroup V] [Module ℂ V]
    (K : Subgroup G.GAf) (f : G.GAf → ℂ) (F : G.GAf × Gr G 1 → V) (g : G.GAf) (g₂ : Gr G 1) :
    UpperTheory.Gal.Spc.op K f F (g, g₂) = hAct K f (fun x => F (x, g₂)) g := by
  unfold UpperTheory.Gal.Spc.op hAct
  refine finsum_congr fun h => ?_
  simp [Prod.mk_mul_mk]

private theorem op_eig {p : ℕ} [Fact p.Prime] {G : HTGroup p} {V Γ : Type} [AddCommGroup V] [Module ℂ V] [Group Γ]
    (ι : Γ →* G.GAf × Gr G 1) (K : Subgroup G.GAf) (hK : IsCommensurated K) (ξ' : Representation ℂ Γ V)
    (φ : G.GAf → V) (F : G.GAf × Gr G 1 → V)
    (hF : ∀ g₂ : Gr G 1, (∀ g, F (g, g₂) = 0) ∨ ∃ γ, ∀ g, F (g, g₂) = ξ' γ (φ ((ι γ).1⁻¹ * g)))
    (f : G.GAf → ℂ) (hf : f ∈ Hecke ℂ K) (c : ℂ) (h : hAct K f φ = c • φ) :
    UpperTheory.Gal.Spc.op K f F = c • F := by
  funext ⟨g, g₂⟩
  rw [op_eq]
  rcases hF g₂ with h0 | ⟨γ, hγ⟩
  · have e : (fun x => F (x, g₂)) = fun _ => 0 := funext h0
    rw [e]
    simp [hAct, h0]
  · have e : (fun x => F (x, g₂)) = fun x => ξ' γ (φ ((ι γ).1⁻¹ * x)) := funext hγ
    rw [e, hAct_slice K hK f hf, h]
    simp [hγ]

end UpperTheory.Gal.W2.Seed

theorem UpperTheory.Gal.W2.Seed.pHasEigOf :
    StdForm → PInt → PPart → ExtP → HasEigOf := by
  intro hStd hPI hPP hExt E _ _ _ A n p _ S T V _ _ ξ Φ hΦL hΦR hΦ0 K₀ hK₀ hK₀inv J ψ θ e hψ he heΦ hψΦ
  obtain ⟨B, x, hx, ee, hee, hemb⟩ := hStd E A n p S T
  let ξ' : Representation ℂ (S.G.Cˣ × ℚˣ) V := ξ
  let ξ₀ : Representation ℂ (GlobalTheory.LKCx.grp S.G B.β) V := ξ'.comp (GlobalTheory.LKCx.grp S.G B.β).subtype
  let φ : S.G.GAf → V := fun h => Φ (T.sec h)
  have hEq : ∀ γ : GlobalTheory.LKCx.grp S.G B.β, (B.embAt x 1 hx γ).2 ∈ UpperTheory.Gal.LocalSmoothExtension.Kp S.G → ∀ g,
      φ ((B.embAt x 1 hx γ).1 * g) = ξ₀ γ (φ g) := by
    intro γ hγ g
    have h1 : (B.embAt x 1 hx γ).1 = T.j (rat (ee γ)) := hemb γ
    have hy : inclG S.G 1 (locC S.G ((ee γ : Gam0 E n) : GL (Fin n) E × ℚˣ)) ∈ UpperTheory.Gal.LocalSmoothExtension.Kp S.G := by
      rw [hee]; exact hγ
    obtain ⟨hI, -⟩ := hPI E A n p S (ee γ) hy
    obtain ⟨k, hk, hk1, hk2, hk3⟩ := hPP E A n p S T (rat (ee γ))
    have hsec : T.sec (T.j (rat (ee γ))) = rat (ee γ) * k⁻¹ := eq_mul_inv_of_mul_eq hk.symm
    have hc : k⁻¹ * T.sec g = T.sec g * k⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq, mul_assoc, hk3 g, inv_mul_cancel_left]
    have hR : ∀ g', Φ (g' * k⁻¹) = Φ g' := hΦR k⁻¹
      (fun w hw => by rw [map_inv, hk1 w hw, inv_one])
      (fun w hw => by rw [map_inv]; exact inv_mem (by rw [hk2 w hw]; exact hI w hw))
    show Φ (T.sec ((B.embAt x 1 hx γ).1 * g)) = ξ₀ γ (Φ (T.sec g))
    rw [h1, map_mul, hsec, mul_assoc, hc, hΦL, hR, hee]
    rfl
  obtain ⟨F, hF1, hF2⟩ := hExt (GlobalTheory.LKCx.grp S.G B.β) S.G.GAf (Gr S.G 1) V (B.embAt x 1 hx) K₀
    (UpperTheory.Gal.LocalSmoothExtension.Kp S.G) ξ₀ φ hEq (fun k hk g => hK₀inv k hk g)
  have hne : F ≠ 0 := by
    obtain ⟨g₀, hg₀, hg₀p⟩ := hΦ0
    obtain ⟨k, hk, hk1, hk2, -⟩ := hPP E A n p S T g₀
    have h2 : Φ g₀ = φ (T.j g₀) := by
      calc Φ g₀ = Φ (T.sec (T.j g₀) * k) := congrArg Φ hk
        _ = φ (T.j g₀) := hΦR k hk1 (fun w hw => by rw [hk2 w hw]; exact hg₀p w hw) _
    intro h0
    apply hg₀
    rw [h2, ← hF1, h0]
    rfl
  refine ⟨B, x, 1, hx, (F : S.G.GAf × Gr S.G 1 → V), F.2, ?_, ?_, fun j => ?_⟩
  · intro h0
    exact hne (Subtype.ext h0)
  · have := op_eig (B.embAt x 1 hx) K₀ hK₀ ξ₀ φ (F : S.G.GAf × Gr S.G 1 → V) hF2 e he 1 (by simpa using heΦ)
    simpa using this
  · exact op_eig (B.embAt x 1 hx) K₀ hK₀ ξ₀ φ (F : S.G.GAf × Gr S.G 1 → V) hF2 (ψ j) (hψ j) (θ j) (hψΦ j)
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

theorem UpperTheory.Gal.W2.Seed.pSphComm :
    SphComm := by
  intro E _ _ n w t t'
  have hb : ∀ s : GL (Fin n) (w.adicCompletion E), IsBiInv (GlobalTheory.LFun.KGL w (n := n)) (dosetInd ℂ (GlobalTheory.LFun.KGL w (n := n)) s) := fun s => (Formalism.UG.Final.DosetIndMem _ _ ℂ s).1
  exact Formalism.UG.P.heckecomm_gelfand (GlobalTheory.LFun.KGL w (n := n)) Formalism.UG.P.heckecomm_tr Formalism.UG.P.heckecomm_tr_mul
    Formalism.UG.P.heckecomm_tr_tr (fun x hx => Formalism.UG.P.heckecomm_tr_mem _ x hx)
    (Formalism.UG.P.heckecomm_tr_dc Formalism.UG.P.cartan_decomposition_holds E w n) _ _ (hb t) (hb t')
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

theorem UpperTheory.Gal.W2.Seed.pMemDeck :
    MemSum → TfCen → MemDeck := by
  intro hSum hCen X M _ _ T K hT k hk hnorm
  have hconj : ∀ a ∈ T.K₀, ∀ u ∈ T.K₀, a * u * a⁻¹ ∈ T.K₀ := fun a ha u hu =>
    T.K₀.mul_mem (T.K₀.mul_mem ha hu) (T.K₀.inv_mem ha)
  have hmem := hSum X T.K₀ T.K₀ T.K₀ k le_rfl (by simp) hconj (fun a ha u hu => by
    have h1 := hnorm (a * u * a⁻¹) (hconj a ha u hu)
    simpa [mul_assoc, _root_.mul_inv_rev] using h1)
  refine ⟨hmem.1, map_one _, ?_⟩
  intro V _ _ Φ hΦ
  funext g
  have hc : T.Cen 1 := ⟨fun g => by simp, map_one _⟩
  rw [one_smul, hCen X M T 1 hc V Φ hΦ g, mul_one]
  have hinv0 : ∀ k' ∈ T.K₀, ∀ g, Φ (g * k') = Φ g := fun k' hk' g => by
    rw [hΦ k' (T.le hk') g, T.ker k' hk' _]
    simp
  rw [hmem.2.2 V Φ hinv0 g]
  have hall : ∀ a b : ↥T.K₀ ⧸ T.K₀.subgroupOf T.K₀, a = b := by
    intro a b
    induction a using QuotientGroup.induction_on
    induction b using QuotientGroup.induction_on
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact SetLike.coe_mem _
  letI : Unique (↥T.K₀ ⧸ T.K₀.subgroupOf T.K₀) :=
    ⟨⟨QuotientGroup.mk (1 : ↥T.K₀)⟩, fun a => hall a _⟩
  rw [finsum_unique]
  have hx : (↑(Quotient.out (default : ↥T.K₀ ⧸ T.K₀.subgroupOf T.K₀)) : X) ∈ T.K₀ :=
    SetLike.coe_mem _
  rw [_root_.mul_inv_rev, ← mul_assoc, hΦ k⁻¹ (hT.1 (K.inv_mem hk)) _,
    hT.2 k⁻¹ (K.inv_mem hk) _]
  simp only [Units.val_one, one_smul]
  exact hinv0 _ (T.K₀.inv_mem hx) g
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

theorem UpperTheory.Gal.W2.Seed.pAtApart :
    JEq → AtApart := by
  intro hJ
  unfold AtApart
  intro E _ _ _ A n p _ S T hc w hw hp
  have key : ∀ (u : Plc E) (hu : IsSplitAt u) (hpu : (p : 𝓞 E) ∉ u.asIdeal)
      (x : GL (Fin n) (u.adicCompletion E)),
      T.sec ((T.at hc u hu hpu).loc x) = UpperTheory.Gal.CertificateRingHomMap.loc hu x := by
    intro u hu hpu x
    apply (hJ E A n p S T.toAdT T.μ T.mu T.a T.j T.j_mx).1
    intro v
    by_cases hv : (p : 𝓞 E) ∈ v.asIdeal
    · rw [T.sec_p _ v hv, UpperTheory.Gal.CertificateRingHomMap.comp_loc_of_apart hu (apart_of_not_mem hpu hv)]
    · exact (T.j_eq _ _).1 (T.j_sec _) v hv
  refine ⟨key w hw hp, ?_⟩
  intro w' hw' hp' hap
  constructor
  · intro x
    show comp w (T.sec ((T.at hc w' hw' hp').loc x)) = 1
    rw [key w' hw' hp' x]
    exact UpperTheory.Gal.CertificateRingHomMap.comp_loc_of_apart hw' hap x
  · intro x
    show comp w' (T.sec ((T.at hc w hw hp).loc x)) = 1
    rw [key w hw hp x]
    exact UpperTheory.Gal.CertificateRingHomMap.comp_loc_of_apart hw (Ne.symm hap) x
end
