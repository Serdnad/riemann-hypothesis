module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzDeterminedBySchrodingerThetaValues
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
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1349
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1318
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
import Development.WeilBound.ThetaLifts.TowerModels.Bundle003

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.InertLagLevi

theorem det_sub_one_ann {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] (e : R)
    (M : Matrix ι ι R) (h : ∀ i j, e * (M i j - (1 : Matrix ι ι R) i j) = 0) : e * (M.det - 1) = 0 := by
  set I : Ideal R := (Submodule.span R {e}).annihilator
  have hI : ∀ a, a ∈ I ↔ a * e = 0 := fun a => by
    rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul]
  have h1 : (Ideal.Quotient.mk I).mapMatrix M = 1 := by
    ext i j
    rw [← map_one (Ideal.Quotient.mk I).mapMatrix, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
      Matrix.map_apply, Matrix.map_apply, Ideal.Quotient.eq, hI, mul_comm]
    exact h i j
  have h2 := congrArg Matrix.det h1
  rw [← RingHom.map_det, Matrix.det_one, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq, hI] at h2
  rw [mul_comm]; exact h2

end GlobalTheory.InertLagLevi

open GlobalTheory.InertLagLevi in
theorem GlobalTheory.InertLagLevi.levi_det : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), J.det ≠ 0 →
    ∀ (v : Pl (F := F)) (p : UG (cA σ) (dbl (incM F J))) (t : GL (Fin n) (AE F E)), At (evFin F v) ((p.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) - 1) →
    (p.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * diagCols (Fin n) = diagCols (Fin n) * t.val →
    At (evFin F v) (t.val.det - 1) ∧ At (evFin F v) (Algebra.norm (AF F) t.val.det - 1) ∧
      ∃ s : GL (Fin n) (AE F E), s.val = ((p⁻¹).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)).toBlocks₁₁ - ((p⁻¹).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)).toBlocks₂₁ ∧
        Algebra.norm (AF F) s.val.det = Algebra.norm (AF F) t.val.det := by
  intro F E _ _ _ _ _ σ hσ n J hJ v p t hsupp hpt
  set P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E) := p.1.1 with hP
  set Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E) := (p⁻¹).1.1 with hQ
  set D : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E) := diagCols (Fin n) with hD
  set T := t.val with hT
  set Ti := (t⁻¹).val with hTi
  have hTTi : T * Ti = 1 := by simp [T, Ti]
  have hQP : Q * P = 1 := by simp [Q, P]

  have htsupp : ∀ u : AF F, evFin F v u = 0 → u • (T - 1) = 0 := by
    intro u hu
    have h0 : u • (P - 1) = 0 := hsupp u hu
    have h1 : u • (P * D - D) = 0 := by
      rw [show P * D - D = (P - 1) * D by rw [Matrix.sub_mul, Matrix.one_mul], ← Matrix.smul_mul, h0, Matrix.zero_mul]
    rw [show P * D = D * T from hpt, show D * T - D = Matrix.fromRows (T - 1) (T - 1) by
      ext (i|i) j <;> simp [D, diagCols, Matrix.fromRows_mul]] at h1
    ext i j
    have := congrFun (congrFun h1 (Sum.inl i)) j
    simpa using this
  have hdet : ∀ u : AF F, evFin F v u = 0 → u • (T.det - 1) = 0 := by
    intro u hu
    have h := htsupp u hu
    rw [Algebra.smul_def]
    refine det_sub_one_ann _ T fun i j => ?_
    have := congrFun (congrFun h i) j
    rwa [Matrix.smul_apply, Matrix.sub_apply, Algebra.smul_def] at this
  refine ⟨hdet, ?_, ?_⟩
  · intro u hu
    have hz := hdet u hu
    let b := Module.Free.chooseBasis (AF F) (AE F E)
    rw [Algebra.norm_eq_matrix_det b, smul_eq_mul]
    refine det_sub_one_ann _ _ fun i j => ?_
    rw [← Matrix.sub_apply, ← map_one (Algebra.leftMulMatrix b), ← map_sub, Algebra.leftMulMatrix_eq_repr_mul,
      ← smul_eq_mul, ← Finsupp.smul_apply, ← map_smul, ← smul_mul_assoc, hz, zero_mul, map_zero, Finsupp.zero_apply]
  · have hpt' : P * D = D * T := hpt
    set K : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E) := Matrix.fromRows 1 (-1) with hKdef
    have hq : Qᵀ * dbl (incM F J) * Q.map (cA σ) = dbl (incM F J) := (p⁻¹).2
    have hQD : Q * D = D * Ti := by
      calc Q * D = Q * (D * T * Ti) := by rw [Matrix.mul_assoc D, hTTi, Matrix.mul_one]
        _ = Q * P * D * Ti := by
          rw [Matrix.mul_assoc Q P D, hpt']; simp only [Matrix.mul_assoc]
        _ = D * Ti := by rw [hQP, Matrix.one_mul]
    have hDc : D.map (cA σ) = D := by
      simp only [D, diagCols, Matrix.fromRows_map, Matrix.map_one _ (map_zero (cA σ)) (map_one (cA σ))]
    have hK : dbl (incM F J) * D = K * incM F J := by
      simp only [dbl, D, diagCols, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul]
      simp [K, Matrix.fromRows_mul]
    have h2 : Qᵀ * (K * incM F J) * Ti.map (cA σ) = K * incM F J := by
      rw [← hK]
      calc Qᵀ * (dbl (incM F J) * D) * Ti.map (cA σ)
          = Qᵀ * dbl (incM F J) * (D.map (cA σ) * Ti.map (cA σ)) := by rw [hDc]; simp only [Matrix.mul_assoc]
        _ = Qᵀ * dbl (incM F J) * (Q.map (cA σ) * D.map (cA σ)) := by
          have hm1 : (Q * D).map (cA σ) = Q.map (cA σ) * D.map (cA σ) := Matrix.map_mul (f := (cA σ).toRingHom)
          have hm2 : (D * Ti).map (cA σ) = D.map (cA σ) * Ti.map (cA σ) := Matrix.map_mul (f := (cA σ).toRingHom)
          rw [← hm1, ← hm2, hQD]
        _ = dbl (incM F J) * D := by rw [hDc, ← Matrix.mul_assoc, hq]
    set X := Q.toBlocks₁₁ - Q.toBlocks₂₁ with hX
    have hQK : Qᵀ * K = Matrix.fromRows Xᵀ (Q.toBlocks₁₂ - Q.toBlocks₂₂)ᵀ := by
      rw [hKdef, ← Matrix.transpose_transpose (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1)),
        ← Matrix.transpose_mul, Matrix.transpose_fromRows]
      conv_lhs => rw [← Matrix.fromBlocks_toBlocks Q]
      rw [Matrix.fromCols_mul_fromBlocks, Matrix.transpose_fromCols]
      simp [X, sub_eq_add_neg]
    rw [← Matrix.mul_assoc, hQK, hKdef, Matrix.fromRows_mul, Matrix.fromRows_mul, Matrix.fromRows_mul] at h2
    have h3 : Xᵀ * incM F J * Ti.map (cA σ) = incM F J := by
      have := (Matrix.fromRows_inj h2).1
      rw [this, Matrix.one_mul]
    have hdJ : (incM F J).det = inclR (AF F) J.det := (RingHom.map_det _ J).symm
    have hJu : IsUnit (incM F J).det := hdJ ▸ (Ne.isUnit hJ).map _
    have hdTi : (Ti.map (cA σ)).det = cA σ Ti.det := (AlgHom.map_det (cA σ) Ti).symm
    have hx : X.det * cA σ Ti.det = 1 := by
      have := congrArg Matrix.det h3
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdTi, mul_right_comm] at this
      exact (hJu.mul_left_inj).1 (this.trans (one_mul _).symm)
    have hTd : T.det * Ti.det = 1 := by rw [← Matrix.det_mul, hTTi, Matrix.det_one]
    have hXd : X.det = cA σ T.det := by
      calc X.det = X.det * (cA σ Ti.det * cA σ T.det) := by
            rw [← map_mul, mul_comm Ti.det, hTd, map_one, mul_one]
        _ = (X.det * cA σ Ti.det) * cA σ T.det := by ring
        _ = cA σ T.det := by rw [hx, one_mul]
    refine ⟨Matrix.nonsingInvUnit X (isUnit_iff_exists_inv.mpr ⟨_, hx⟩), rfl, ?_⟩
    show Algebra.norm (AF F) X.det = _
    have hcc : ∀ x, cA σ (cA σ x) = x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [cA, GlobalTheory.AdelicU.cm_conj_conj hσ]
      | add x y hx hy => simp [hx, hy]
    let cE : AE F E ≃ₐ[AF F] AE F E := AlgEquiv.ofAlgHom (cA σ) (cA σ) (AlgHom.ext hcc) (AlgHom.ext hcc)
    rw [hXd]
    exact Algebra.norm_eq_of_algEquiv cE T.det
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch

noncomputable section

namespace GlobalTheory.ArchTraceNondeg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem det_ne_zero_of_hasSig {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} {r s : ℕ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have h1 : A'ᵀ * M * A'.map star = (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm := by
    rw [← hA]
    ext i j
    simp [A', Matrix.mul_apply, Matrix.submatrix, Matrix.transpose_apply, Matrix.map_apply]
  have h2 : (A'ᵀ * M * A'.map star).det ≠ 0 := by
    rw [h1, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
    simp [Matrix.det_neg]
  intro hM
  apply h2
  simp [Matrix.det_mul, hM]

theorem det_J_ne_zero {σ : E →ₐ[F] E} (B : Base F E) {n : ℕ} {X : Spc F E n} {r s : ℕ} (hX : X.IsHerm σ B r s) :
    X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h := det_ne_zero_of_hasSig (hX.sig w)
  intro h0
  apply h
  have := RingHom.map_det (B.emb w).1 X.J
  rw [h0, map_zero] at this
  exact this.symm

theorem sigma_surjective (σ : E →ₐ[F] E) : Function.Surjective σ := by
  have hinj : Function.Injective ((σ : E →+* E).toRatAlgHom.toLinearMap) := (σ : E →+* E).injective
  exact LinearMap.injective_iff_surjective.1 hinj

def cAinv (σ : E →ₐ[F] E) : AE F E →ₐ[AF F] AE F E :=
  Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F))
    (AlgEquiv.ofBijective σ ⟨(σ : E →+* E).injective, sigma_surjective σ⟩).symm.toAlgHom

theorem cA_cAinv (σ : E →ₐ[F] E) (x : AE F E) : cA σ (cAinv σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    simp only [cAinv, cA, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.coe_toAlgHom, AlgHom.coe_coe]
    congr 1
    exact AlgEquiv.apply_symm_apply (AlgEquiv.ofBijective σ ⟨(σ : E →+* E).injective, sigma_surjective σ⟩) y
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem at_cAinv (σ : E →ₐ[F] E) {t : AE F E} (ht : At (evI F) t) : At (evI F) (cAinv σ t) := by
  intro u hu
  rw [← map_smul, ht u hu, map_zero]

theorem at_single {n : ℕ} (k : Fin n) {t : AE F E} (ht : At (evI F) t) :
    At (evI F) (Pi.single k t : Fin n → AE F E) := by
  intro u hu
  funext j
  by_cases hj : j = k
  · subst hj; simp [ht u hu]
  · simp [Pi.single_apply, hj]

theorem at_vecMul {n : ℕ} {b : Fin n → AE F E} (hb : At (evI F) b) (A : Matrix (Fin n) (Fin n) (AE F E)) (k : Fin n) :
    At (evI F) ((b ᵥ* A) k) := by
  intro u hu
  have h := hb u hu
  simp only [Matrix.vecMul, dotProduct, Finset.smul_sum, smul_mul_assoc]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← smul_mul_assoc]
  have : u • b i = 0 := by simpa using congrFun h i
  rw [this, zero_mul]

theorem eq_zero_of_trace_orth : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E)
    {n : ℕ} (X : Spc F E n) (r s : ℕ),
    (∀ β : AE F E, At (evI F) β → (∀ t : AE F E, At (evI F) t →
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (Algebra.trace (AF F) (AE F E) (β * t))) = 0) → β = 0) →
    X.IsHerm σ B r s → ∀ b : Fin n → AE F E, At (evI F) b →
    (∀ c : Fin n → AE F E, At (evI F) c → Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (evI F (Algebra.trace (AF F) (AE F E) (b ⬝ᵥ (incM F X.J *ᵥ fun k => cA σ (c k))))) = 0) → b = 0 := by
  intro F E _ _ _ _ _ σ B n X r s hβ hX b hb hc
  have hdet : IsUnit (incM F X.J).det := by
    have h : (incM F X.J).det = inclR (F := F) (AF F) X.J.det := by
      rw [RingHom.map_det]; rfl
    rw [h]
    exact (isUnit_iff_ne_zero.2 (det_J_ne_zero B hX)).map _
  have hv : b ᵥ* incM F X.J = 0 := by
    funext k
    apply hβ _ (at_vecMul hb _ k)
    intro t ht
    have h := hc (Pi.single k (cAinv σ t)) (at_single k (at_cAinv σ ht))
    rw [Matrix.dotProduct_mulVec] at h
    have hw : (fun j => cA σ ((Pi.single k (cAinv σ t) : Fin n → AE F E) j)) = Pi.single k t := by
      funext j
      by_cases hj : j = k
      · subst hj; simp [cA_cAinv]
      · simp [Pi.single_apply, hj]
    rw [hw, dotProduct_single] at h
    exact h
  calc b = b ᵥ* (incM F X.J * (incM F X.J)⁻¹) := by rw [Matrix.mul_nonsing_inv _ hdet, Matrix.vecMul_one]
    _ = (b ᵥ* incM F X.J) ᵥ* (incM F X.J)⁻¹ := (Matrix.vecMul_vecMul _ _ _).symm
    _ = 0 := by rw [hv, Matrix.zero_vecMul]

end GlobalTheory.ArchTraceNondeg
end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.UnipDom

noncomputable section

namespace GlobalTheory.CMTrace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sig_sig {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem sig_ne_id {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  by_contra hc
  push_neg at hc
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hr : w.IsReal := by
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    ext x
    simp only [ComplexEmbedding.conjugate_coe_eq]
    have := h.2.2.2 w.embedding x
    rw [hc x] at this
    exact this.symm
  exact (InfinitePlace.not_isReal_iff_isComplex.mpr (h.2.1.isComplex w)) hr

def sigE {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : Gal(E/F) :=
  AlgEquiv.ofAlgHom σ σ (AlgHom.ext fun x => sig_sig h x) (AlgHom.ext fun x => sig_sig h x)

theorem trace_eq {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (e : E) :
    algebraMap F E (Algebra.trace F E e) = e + σ e := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h.2.2.1
  have hne : (1 : Gal(E/F)) ≠ sigE h := by
    intro h1
    obtain ⟨x, hx⟩ := sig_ne_id h
    exact hx (congrArg (fun g : Gal(E/F) => g x) h1).symm
  have hle : Nat.card Gal(E/F) ≤ 2 := by
    calc Nat.card Gal(E/F) ≤ Nat.card (E →ₐ[F] E) :=
          Nat.card_le_card_of_injective (fun g => (g : E →ₐ[F] E)) (fun a b hab => AlgEquiv.coe_algHom_injective hab)
      _ ≤ Module.finrank F E := card_algHom_le_finrank F E E
      _ = 2 := h.2.2.1
  have hall : ∀ g : Gal(E/F), g = 1 ∨ g = sigE h := by
    classical
    have hc : (({1, sigE h} : Finset Gal(E/F))).card = 2 := Finset.card_pair hne
    have hu : ({1, sigE h} : Finset Gal(E/F)) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [hc]
      rw [← Nat.card_eq_fintype_card]
      have : 2 ≤ Nat.card Gal(E/F) := by
        rw [Nat.card_eq_fintype_card, ← hc]; exact Finset.card_le_univ _
      omega
    intro g
    have := Finset.mem_univ g
    rw [← hu] at this
    simpa using this
  have hgal : IsGalois F E := by
    apply IsGalois.of_card_aut_eq_finrank
    rw [h.2.2.1]
    apply le_antisymm hle
    classical
    rw [Nat.card_eq_fintype_card, ← Finset.card_pair hne]
    exact Finset.card_le_univ _
  rw [trace_eq_sum_automorphisms]
  classical
  rw [Fintype.sum_eq_add 1 (sigE h) hne (fun g hg => absurd (hall g) (by tauto))]
  rfl

end GlobalTheory.CMTrace

namespace GlobalTheory.CMTrace

theorem adele_trace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : AF F, Algebra.trace (AF F) (AE F E) (algebraMap (AF F) (AE F E) x) = 2 * x) ∧ ∀ c : AE F E, algebraMap (AF F) (AE F E) (Algebra.trace (AF F) (AE F E) c) = c + cA σ c := by
  intro F E _ _ _ _ _ σ h
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h.2.2.1
  haveI : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  refine ⟨fun x => ?_, fun c => ?_⟩
  · rw [Algebra.trace_algebraMap, Module.finrank_baseChange, h.2.2.1, nsmul_eq_mul, Nat.cast_ofNat]
  · have htm : ∀ (a : AF F) (e : E), Algebra.trace (AF F) (AE F E) (a ⊗ₜ[F] e) =
        a * algebraMap F (AF F) (Algebra.trace F E e) := by
      intro a e
      have h1 : a ⊗ₜ[F] e = a • ((1 : AF F) ⊗ₜ[F] e) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
        LinearMap.trace_baseChange, smul_eq_mul]
    induction c using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]; abel
    | tmul a e =>
      rw [htm, Algebra.TensorProduct.algebraMap_apply, cA, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        ← TensorProduct.tmul_add, ← trace_eq h, mul_comm, ← Algebra.smul_def, Algebra.algebraMap_self,
        RingHom.id_apply, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]

end GlobalTheory.CMTrace
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.integral_indicator_preimage_injective_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ],
    ∀ (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ j : (Fin N → Fv F v) →ₗ[Fv F v] (κ → Fv F v) × (κ → Fv F v), Function.Injective j →
    ∀ c : ℂ, c ≠ 0 → ∀ U : Set ((κ → Fv F v) × (κ → Fv F v)), IsOpen U → IsCompact U → 0 ∈ U →
    ∫ y, U.indicator (fun _ => c) (j y) ∂ν ≠ 0 := by
  intro F _ _ v κ _ N ν hν j hj c hc U hUo hUc h0
  letI : MeasurableSpace (Fin N → Fv F v) := borel _
  haveI : BorelSpace (Fin N → Fv F v) := ⟨rfl⟩
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective j (LinearMap.ker_eq_bot.mpr hj)
  have hjc : Continuous j := IsModuleTopology.continuous_of_linearMap j
  have hgc : Continuous g := IsModuleTopology.continuous_of_linearMap g
  set S : Set (Fin N → Fv F v) := j ⁻¹' U with hSdef
  have hSo : IsOpen S := hUo.preimage hjc
  have hSsub : S ⊆ g '' U := by
    intro y hy
    refine ⟨j y, hy, ?_⟩
    have := congrArg (fun f => f y) hg
    simpa using this
  have hfin : ν S < ⊤ := lt_of_le_of_lt (measure_mono hSsub) ((hUc.image hgc).measure_lt_top)
  have hpos : 0 < ν S := hSo.measure_pos ν ⟨0, by simp [hSdef, h0]⟩
  have heq : (fun y => U.indicator (fun _ => c) (j y)) = S.indicator (fun _ => c) := by
    funext y
    by_cases hy : j y ∈ U
    · have : y ∈ S := hy
      simp [Set.indicator_of_mem hy, Set.indicator_of_mem this]
    · have : y ∉ S := hy
      simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem this]
  rw [heq, integral_indicator_const c hSo.measurableSet]
  refine smul_ne_zero ?_ hc
  rw [Measure.real]
  exact ENNReal.toReal_ne_zero.mpr ⟨hpos.ne', hfin.ne⟩
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.SkewGram

theorem det_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), X.IsSkew σ B r s → X.J.det ≠ 0 := by
  intro F E _ _ _ _ _ σ B n X r s h hJ
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨hrs, A, hA⟩ := h.sig w
  have hM : (Complex.I • X.J.map (B.emb w).1).det = 0 := by
    rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hJ, map_zero, mul_zero]
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let P : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have key : Pᵀ * (Complex.I • X.J.map (B.emb w).1) * P.map star =
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)).submatrix e.symm e.symm := by
    rw [← hA]; rfl
  have hd := congrArg Matrix.det key
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_mul, Matrix.det_mul, hM] at hd
  rw [Matrix.det_neg, Matrix.det_one, Matrix.det_one, mul_one, one_mul, mul_zero, zero_mul] at hd
  exact (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hd.symm

end GlobalTheory.SkewGram
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory

theorem det_ne_zero_of_hasSig {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} {r s : ℕ} (h : HasSig M r s) : M.det ≠ 0 := by
  apply _root_.PositivityTheory.ThKG.Tow.det_ne_zero_of_hasSig <;> assumption

theorem isUnit_det_of_isHerm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n : ℕ) (X : Spc F E n) (r s : ℕ), X.IsHerm σ B r s → IsUnit X.J.det := by
  intro F E _ _ _ _ _ σ B n X r s hX
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h := det_ne_zero_of_hasSig (hX.sig w)
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
  exact isUnit_iff_ne_zero.mpr fun h0 => h (by rw [h0, map_zero])

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.adelicSchwartz_determined_by_schrodingerThetaValues : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (κ : Type) [Fintype κ],
    ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ' ∈ GlobalTheory.WeilM.schA D.host.F κ,
      (∀ w : (κ → AF D.host.F) × (κ → AF D.host.F), GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ w φ) =
        GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ w φ')) → φ = φ' := by
  first | exact @GlobalTheory.SchrodingerUniq.main | exact GlobalTheory.SchrodingerUniq.main | (intros; apply GlobalTheory.SchrodingerUniq.main <;> assumption)
end
