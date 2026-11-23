module

public import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem cm_invol (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem rId_zero : rId F 0 = 1 := by
  rw [rId, Real.exp_zero, sub_self, realAd, map_zero, map_zero, map_zero]
  exact add_zero (1 : AF F)

def formL (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (y : Fin n → E) : (Fin n → E) →ₗ[E] E where
  toFun x := form σ J x y
  map_add' a b := by simp [form, add_dotProduct]
  map_smul' c a := by simp [form, smul_dotProduct]

omit [NumberField F] [NumberField E] in
theorem formL_apply {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (y x : Fin n → E) : formL σ J y x = form σ J x y := rfl

theorem form_swap (h : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : EpsHerm σ J) :
    ∃ ε : E, ε * ε = 1 ∧ ∀ x y, form σ J y x = ε * σ (form σ J x y) := by
  have key : ∀ ε : E, (∀ i j, σ (J j i) = ε * J i j) → ε * ε = 1 → ∀ x y, form σ J y x = ε * σ (form σ J x y) := by
    intro ε h1 h2 x y

    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, cm_invol h, h1, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    linear_combination (-(y j * J j i * σ (x i))) * h2
  rcases hJ.1 with h1 | h1
  · exact ⟨1, by simp, key 1 (by simpa using h1) (by simp)⟩
  · exact ⟨-1, by simp, key (-1) (by simpa using h1) (by simp)⟩

theorem frameBasis_of : FrameBasis := by
  intro F E _ _ _ _ _ σ hσ n J hJ fr hfr
  classical
  obtain ⟨ε, hε, hsw⟩ := form_swap hσ hJ
  have hε0 : ε ≠ 0 := by rintro rfl; simp at hε
  have yx : ∀ i j, form σ J (fr.y i) (fr.x j) = if i = j then ε else 0 := by
    intro i j
    rw [hsw, hfr.xy]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  let K : Submodule E (Fin n → E) := ⨅ i, (LinearMap.ker (formL σ J (fr.x i)) ⊓ LinearMap.ker (formL σ J (fr.y i)))
  have hK : ∀ u, u ∈ K ↔ ∀ i, form σ J u (fr.x i) = 0 ∧ form σ J u (fr.y i) = 0 := by
    intro u
    simp [K, Submodule.mem_iInf, formL_apply]
  let bK := Module.finBasis E K
  let v : (Fin fr.r ⊕ Fin fr.r) ⊕ Fin (Module.finrank E K) → Fin n → E :=
    Sum.elim (Sum.elim fr.x fr.y) fun k => (bK k : Fin n → E)
  have hli : LinearIndependent E v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h1 : ∀ j, g (.inl (.inl j)) = 0 := by
      intro j
      have := congrArg (formL σ J (fr.y j)) hg

      simp only [map_sum, map_smul, map_zero] at this
      simpa [Fintype.sum_sum_type, v, formL_apply, hfr.xy, hfr.yy, ((hK _).1 (bK _).2 j).2] using this
    have h2 : ∀ j, g (.inl (.inr j)) = 0 := by
      intro j
      have := congrArg (formL σ J (fr.x j)) hg

      simp only [map_sum, map_smul, map_zero] at this
      simpa [Fintype.sum_sum_type, v, formL_apply, hfr.xx, yx, ((hK _).1 (bK _).2 j).1, hε0] using this
    have h3 : ∑ k, g (.inr k) • bK k = 0 := by
      apply Subtype.ext
      simpa [Fintype.sum_sum_type, v, h1, h2] using hg
    have h4 := Fintype.linearIndependent_iff.1 bK.linearIndependent _ h3
    rintro ((j | j) | j)
    exacts [h1 j, h2 j, h4 j]
  have hsp : ⊤ ≤ Submodule.span E (Set.range v) := by
    intro u _
    let a := ∑ i, form σ J u (fr.y i) • fr.x i + ∑ i, (ε * form σ J u (fr.x i)) • fr.y i
    have ha : a ∈ Submodule.span E (Set.range v) :=
      add_mem (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨.inl (.inl i), rfl⟩))
        (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨.inl (.inr i), rfl⟩))
    have hu : u - a ∈ K := by
      rw [hK]
      intro j
      constructor
      · rw [← formL_apply]

        simp only [a, map_sub, map_add (f := _), map_sum, map_smul, formL_apply, hfr.xx, yx, smul_eq_mul, mul_zero,
        Finset.sum_const_zero, mul_ite, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        linear_combination (-form σ J u (fr.x j)) * hε
      · rw [← formL_apply]

        simp only [a, map_sub, map_add (f := _), map_sum, map_smul]
        simp [formL_apply, hfr.xy, hfr.yy]
    have hb : u - a ∈ Submodule.span E (Set.range v) := by
      have : u - a = ∑ k, bK.repr ⟨_, hu⟩ k • (bK k : Fin n → E) := by
        have := congrArg Subtype.val (bK.sum_repr ⟨_, hu⟩)
        rw [Submodule.coe_sum] at this
        exact this.symm
      rw [this]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨.inr i, rfl⟩)
    simpa using add_mem hb ha
  let B := Module.Basis.mk hli hsp
  let e : ((Fin fr.r ⊕ Fin fr.r) ⊕ Fin (Module.finrank E K)) ≃ Fin n := B.indexEquiv (Pi.basisFun E (Fin n))
  let M : Matrix (Fin n) (Fin n) E := Matrix.of fun l k => v (e.symm k) l
  have hM : IsUnit M := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli.comp e.symm e.symm.injective
  let lam0 : (Fin fr.r ⊕ Fin fr.r) ⊕ Fin (Module.finrank E K) → (Fin fr.r → ℝ) →ₗ[ℝ] ℝ :=
    Sum.elim (Sum.elim (fun i => LinearMap.proj i) fun i => -LinearMap.proj i) fun _ => 0
  refine ⟨hM.unit, fun k => lam0 (e.symm k), ⟨fun i => e (.inl (.inl i)), fun i j h => by simpa using h⟩,
    ⟨fun i => e (.inl (.inr i)), fun i j h => by simpa using h⟩, fun i j h => by simpa using e.injective h,
    fun i t => ⟨congrArg (fun z => lam0 z t) (e.symm_apply_apply _), congrArg (fun z => lam0 z t) (e.symm_apply_apply _)⟩,
    fun k hk => ?_, fun i => congrArg v (e.symm_apply_apply _), fun t => ?_⟩
  · obtain ⟨k, rfl⟩ := e.surjective k
    rcases k with (j | j) | j
    · exact absurd rfl (hk j).1
    · exact absurd rfl (hk j).2
    · simp [lam0]
  · have key : ∀ k, mat (fr.a t) *ᵥ incV F (v k) = rId F (lam0 k t) • incV F (v k) := by
      rintro ((j | j) | j)
      · exact hfr.ax t j
      · exact hfr.ay t j
      · have := hfr.a0 t _ ((hK _).1 (bK j).2)
        simpa [lam0, rId_zero, v] using this
    ext l k
    have := congrFun (key (e.symm k)) l
    rw [Matrix.mul_diagonal, mul_comm, ← Algebra.smul_def]
    exact this

end PositivityTheory.ThKEst

end
end

section

noncomputable section

namespace PositivityTheory.ThKEst

open scoped Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace SignatureOfHermitianForm

theorem sig_sq {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : r + s = n) (A : Matrix (Fin n) (Fin r ⊕ Fin s) ℂ)
    (hA : Aᵀ * M * A.map star = Matrix.fromBlocks 1 0 0 (-1)) :
    M.det ≠ 0 ∧ Function.Surjective A.mulVec := by
  let e : Fin n ≃ Fin r ⊕ Fin s := (finCongr h.symm).trans finSumFinEquiv.symm
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e
  have h1 : A'ᵀ * M * A'.map star
      = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)).submatrix e e := by
    rw [← hA]
    ext i j
    simp [A', Matrix.mul_apply]
  have h2 : A'.det * M.det * (A'.map star).det ≠ 0 := by
    rw [← Matrix.det_transpose A', ← Matrix.det_mul, ← Matrix.det_mul, h1, Matrix.det_submatrix_equiv_self,
      Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]
    simp
  have h3 : A'.det ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul h2)
  refine ⟨right_ne_zero_of_mul (left_ne_zero_of_mul h2), fun x => ?_⟩
  have hu : IsUnit A' := (Matrix.isUnit_iff_isUnit_det A').2 (Ne.isUnit h3)
  obtain ⟨u, hu⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hu x
  refine ⟨u ∘ e.symm, ?_⟩
  rw [← hu]
  ext i
  simp only [A', Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id, Function.comp]
  rw [← e.sum_comp]
  simp

theorem block_form {r s : ℕ} (w : Fin r ⊕ Fin s → ℂ) :
    w ⬝ᵥ (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)) *ᵥ star w
      = ((∑ i, Complex.normSq (w (Sum.inl i)) - ∑ j, Complex.normSq (w (Sum.inr j)) : ℝ) : ℂ) := by
  rw [Matrix.fromBlocks_mulVec]
  simp [dotProduct, Fintype.sum_sum_type, Matrix.neg_mulVec, Complex.mul_conj, sub_eq_add_neg]

theorem sig_index {n r s k : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) (c : ℂ) (hc : c ≠ 0)
    (x y : Fin k → Fin n → ℂ) (hxx : ∀ i j, x i ⬝ᵥ M *ᵥ star (x j) = 0)
    (hxy : ∀ i j, x i ⬝ᵥ M *ᵥ star (y j) = if i = j then c else 0) : k ≤ min r s := by
  obtain ⟨h, A, hA⟩ := h
  choose u hu using fun i => (sig_sq h A hA).2 (x i)
  let L : (Fin k → ℂ) →ₗ[ℂ] (Fin r ⊕ Fin s → ℂ) := Fintype.linearCombination ℂ u
  have hL : ∀ v, A *ᵥ L v = ∑ i, v i • x i := by
    intro v
    simp only [L, Fintype.linearCombination_apply, Matrix.mulVec_sum, Matrix.mulVec_smul, hu]
  have hinj : ∀ v, L v = 0 → v = 0 := by
    intro v hv
    have h0 := hL v
    rw [hv, Matrix.mulVec_zero] at h0
    ext j
    have h1 := congrArg (fun z => z ⬝ᵥ M *ᵥ star (y j)) h0
    simp only [zero_dotProduct, sum_dotProduct, smul_dotProduct, hxy, smul_eq_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
    exact (mul_eq_zero.1 h1.symm).resolve_right hc
  have hiso : ∀ v, ∑ i, Complex.normSq (L v (Sum.inl i)) = ∑ j, Complex.normSq (L v (Sum.inr j)) := by
    intro v
    have h1 := block_form (L v)
    have h2 : (A *ᵥ L v) ⬝ᵥ M *ᵥ star (A *ᵥ L v) = 0 := by
      rw [hL]
      simp only [star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, sum_dotProduct, smul_dotProduct,
        dotProduct_sum, dotProduct_smul, hxx, smul_zero, Finset.sum_const_zero]
    have h3 : star (A *ᵥ L v) = A.map star *ᵥ star (L v) := by
      ext i
      simp [Matrix.mulVec, dotProduct]
    rw [h3, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      hA, h1] at h2
    exact sub_eq_zero.1 (Complex.ofReal_eq_zero.1 h2)
  have hz : ∀ {m : ℕ} (f : Fin m → ℂ), ∑ i, Complex.normSq (f i) = 0 → ∀ i, f i = 0 := by
    intro m f hf i
    exact Complex.normSq_eq_zero.1
      ((Finset.sum_eq_zero_iff_of_nonneg fun i _ => Complex.normSq_nonneg (f i)).1 hf i (Finset.mem_univ i))
  refine le_min ?_ ?_
  · have := LinearMap.finrank_le_finrank_of_injective (f := (LinearMap.funLeft ℂ ℂ Sum.inl) ∘ₗ L) (by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro v hv
      have h1 : ∀ i, L v (Sum.inl i) = 0 := fun i => congrFun hv i
      have h2 := hz (fun j => L v (Sum.inr j)) (by rw [← hiso]; simp [h1])
      apply hinj
      ext (i | j)
      · exact h1 i
      · exact h2 j)
    simpa using this
  · have := LinearMap.finrank_le_finrank_of_injective (f := (LinearMap.funLeft ℂ ℂ Sum.inr) ∘ₗ L) (by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro v hv
      have h1 : ∀ i, L v (Sum.inr i) = 0 := fun i => congrFun hv i
      have h2 := hz (fun j => L v (Sum.inl j)) (by rw [hiso]; simp [h1])
      apply hinj
      ext (i | j)
      · exact h2 i
      · exact h1 j)
    simpa using this

theorem form_map {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (τ : E →+* ℂ)
    (hτ : ∀ x, τ (σ x) = star (τ x)) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (c : ℂ) (x y : Fin n → E) :
    (fun i => τ (x i)) ⬝ᵥ (c • J.map τ) *ᵥ star (fun i => τ (y i)) = c * τ (x ⬝ᵥ J *ᵥ fun i => σ (y i)) := by
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  simp [dotProduct, Matrix.mulVec, hτ]

theorem of_sig {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (τ : E →+* ℂ) (hτ : ∀ x, τ (σ x) = star (τ x)) {n r s : ℕ} (J : Matrix (Fin n) (Fin n) E) (c : ℂ) (hc : c ≠ 0)
    (h : HasSig (c • J.map τ) r s) :
    J.det ≠ 0 ∧ r + s = n ∧ ∀ fr : Frame σ J, fr.IsGood → fr.r ≤ min r s := by
  refine ⟨?_, h.1, fun fr hfr => ?_⟩
  · obtain ⟨h, A, hA⟩ := h
    intro h0
    apply (sig_sq h A hA).1
    have : (J.map τ).det = τ J.det := (RingHom.map_det τ J).symm
    rw [Matrix.det_smul, this, h0, map_zero, mul_zero]
  · refine sig_index h c hc (fun i l => τ (fr.x i l)) (fun i l => τ (fr.y i l)) (fun i j => ?_) (fun i j => ?_)
    · have := hfr.xx i j
      unfold form at this
      rw [form_map σ τ hτ, this, map_zero, mul_zero]
    · have := hfr.xy i j
      unfold form at this
      rw [form_map σ τ hτ, this]
      split_ifs <;> simp

end SignatureOfHermitianForm

theorem epsOf_of : EpsOf := by
  intro F E _ _ _ _ _ σ B hB n X r s hX
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hτ := hB.cm.2.2.2 (B.emb w).1
  rcases hX with hX | hX
  · have := SignatureOfHermitianForm.of_sig σ _ hτ X.J 1 one_ne_zero (r := r) (s := s) (by rw [one_smul]; exact hX.sig w)
    exact ⟨⟨Or.inl hX.herm, this.1⟩, this.2⟩
  · have := SignatureOfHermitianForm.of_sig σ _ hτ X.J Complex.I Complex.I_ne_zero (hX.sig w)
    exact ⟨⟨Or.inr hX.skew, this.1⟩, this.2⟩

end PositivityTheory.ThKEst
end
end

section

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem ht_mul_le {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : ht (g * h) ≤ ht g * ht h :=
  heightGL_mul_le F g.1 h.1

theorem ht_inv {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : ht g⁻¹ = ht g := heightGL_inv F g.1

theorem one_le_ht {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : 1 ≤ ht g := one_le_heightGL F g.1

theorem exp_le_ht (hT : GrpTop) (hc : IsCMExt F E σ) {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (hJ : EpsHerm σ J)
    {fr : Frame σ J} (h2 : TorHt fr) {Ω : Set (UA σ J)} (hΩ : IsCompact Ω) :
    ∃ (A : ℝ) (k : ℕ), 0 ≤ A ∧ ∀ h : UA σ J, ∀ δ ∈ ratU σ J, ∀ t ∈ Cone fr.r, ∀ κ ∈ Ω, δ * h = fr.a t * κ →
      Real.exp (∑ i, t i) ≤ A * (ht h : ℝ) ^ k := by
  obtain ⟨C, k, hC⟩ := h2
  obtain ⟨B, hB⟩ := (hT F E σ hc d J hJ).2.2.2.2.2.2.2 Ω hΩ
  refine ⟨max C 0 * (B : ℝ) ^ k, k, by positivity, fun h δ hδ t ht' κ hκ e => ?_⟩
  have e2 : δ⁻¹ * fr.a t = h * κ⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, e, mul_inv_cancel_right]
  have h3 := (hC t ht').2 δ⁻¹ (inv_mem hδ)
  rw [e2] at h3
  have h4 : (ht (h * κ⁻¹) : ℝ) ≤ B * ht h := by
    have hb : ht κ⁻¹ ≤ B := by rw [ht_inv]; exact hB κ hκ
    have := (ht_mul_le h κ⁻¹).trans (mul_le_mul_right hb _)
    rw [mul_comm] at this
    exact_mod_cast this
  calc _ ≤ C * (ht (h * κ⁻¹) : ℝ) ^ k := h3
    _ ≤ max C 0 * ((B : ℝ) * ht h) ^ k := by gcongr; exact le_max_left _ _
    _ = _ := by rw [mul_pow, mul_assoc]

theorem latSum_redH (hT : GrpTop) (hS : SiegelAll) (hI : LatInv) (hK : LatCpt) (hA : LatArch) (hc : IsCMExt F E σ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) {n d : ℕ} {J : Matrix (Fin n) (Fin n) E} {J' : Matrix (Fin d) (Fin d) E}
    (hJ : EpsHerm σ J) (hJ' : EpsHerm σ J') (N : ℕ) :
    ∃ k : ℕ, ∀ C, IsCompact C → ∃ (C' : Set (Ten F E n d)) (K : ℝ), IsCompact C' ∧ 0 ≤ K ∧ ∀ (g : UA σ J) (h : UA σ J'),
      latSum τ C N Set.univ g h ≤ ENNReal.ofReal ((K * (ht h : ℝ) ^ k) ^ 2) * latSum τ C' N Set.univ g (1 : UA σ J') := by
  obtain ⟨fr, hg, -, ⟨Ω, hΩ, hcov⟩, -, hht⟩ := hS F E σ hc d J' hJ'
  obtain ⟨A, k, hA0, hAk⟩ := exp_le_ht hT hc hJ' hht hΩ
  refine ⟨k * N, fun C hC => ?_⟩
  obtain ⟨C₁, K₁, hC₁, h₁⟩ := hK F E σ hc τ n d J J' hJ hJ' {1} Ω isCompact_singleton hΩ C N hC
  obtain ⟨C₂, K₂, hC₂, h₂⟩ := hA F E σ hc τ n d J J' hJ hJ' fr hg C₁ N hC₁
  refine ⟨C₂, K₁ * K₂ * A ^ N + 1, hC₂, by positivity, fun g h => ?_⟩
  obtain ⟨δ, hδ, t, ht', κ, hκ, e⟩ := hcov h
  have e1 := hI F E σ hc τ n d J J' hJ hJ' C N Set.univ (by simp) 1 (one_mem _) δ hδ g h
  rw [← e1, e, one_mul]
  have e2 := h₁ Set.univ g (fr.a t) 1 rfl κ hκ
  rw [mul_one] at e2
  refine e2.trans ((mul_le_mul_right (h₂ Set.univ g t ht') _).trans ?_)
  rw [← mul_assoc, ← mul_assoc]
  refine mul_le_mul_left ?_ _
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : (1 : ℝ) ≤ (ht h : ℝ) ^ (k * N) := one_le_pow₀ (by exact_mod_cast one_le_ht h)
  have h3 : Real.exp (N * ∑ j, t j) ≤ A ^ N * (ht h : ℝ) ^ (k * N) := by
    rw [Real.exp_nat_mul, pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (Real.exp_pos _).le (hAk h δ hδ t ht' κ hκ e) _
  have h4 : (0 : ℝ) ≤ K₁ * K₂ * A ^ N := by positivity
  have h5 : (1 : ℝ) ≤ (K₁ * K₂ * A ^ N + 1) * (ht h : ℝ) ^ (k * N) := by nlinarith
  calc (K₁ : ℝ) * K₂ * Real.exp (N * ∑ j, t j) ≤ K₁ * K₂ * (A ^ N * (ht h : ℝ) ^ (k * N)) := by gcongr
    _ ≤ (K₁ * K₂ * A ^ N + 1) * (ht h : ℝ) ^ (k * N) := by nlinarith
    _ ≤ _ := by nlinarith

end PositivityTheory.ThKEst

end
end

section

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

def latInvEquiv {E : Type} [Field E] {n d : ℕ} (a : GL (Fin n) E) (b : GL (Fin d) E) :
    Matrix (Fin n) (Fin d) E ≃ Matrix (Fin n) (Fin d) E where
  toFun x := a.1 * x * b.1ᵀ
  invFun x := (a⁻¹).1 * x * (b⁻¹).1ᵀ
  left_inv x := by
    have h1 : (a⁻¹).1 * a.1 = 1 := a.inv_mul
    have h2 : b.1ᵀ * (b⁻¹).1ᵀ = 1 := by
      rw [← Matrix.transpose_mul, show (b⁻¹).1 * b.1 = 1 from b.inv_mul, Matrix.transpose_one]
    simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [Matrix.mul_assoc, h2, Matrix.mul_one]
  right_inv x := by
    have h1 : a.1 * (a⁻¹).1 = 1 := a.mul_inv
    have h2 : (b⁻¹).1ᵀ * b.1ᵀ = 1 := by
      rw [← Matrix.transpose_mul, show b.1 * (b⁻¹).1 = 1 from b.mul_inv, Matrix.transpose_one]
    simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [Matrix.mul_assoc, h2, Matrix.mul_one]

theorem latInvEquiv_rank {E : Type} [Field E] {n d : ℕ} (a : GL (Fin n) E) (b : GL (Fin d) E)
    (x : Matrix (Fin n) (Fin d) E) : (latInvEquiv a b x).rank = x.rank := by
  have ha : IsUnit a.1.det := (Matrix.isUnit_iff_isUnit_det _).1 a.isUnit
  have hb : IsUnit b.1ᵀ.det := by
    rw [Matrix.det_transpose]; exact (Matrix.isUnit_iff_isUnit_det _).1 b.isUnit
  change (a.1 * x * b.1ᵀ).rank = x.rank
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hb, Matrix.rank_mul_eq_right_of_isUnit_det _ _ ha]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem latInv_mat_inv_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (γ : UA σ J) (hγ : γ ∈ ratU σ J) :
    ∃ a : GL (Fin n) E, ∀ g : UA σ J, mat (γ * g)⁻¹ = mat g⁻¹ * incM F a.1 := by
  obtain ⟨a, ha⟩ := Subgroup.mem_subgroupOf.1 ((ratU σ J).inv_mem hγ)
  refine ⟨a, fun g => ?_⟩
  have h1 : mat γ⁻¹ = incM F a.1 := (congrArg Units.val ha).symm
  rw [mul_inv_rev, ← h1]
  rfl

theorem latInv_incM {n d : ℕ} (a : GL (Fin n) E) (b : GL (Fin d) E) (x : Matrix (Fin n) (Fin d) E) :
    incM F (latInvEquiv a b x) = incM F a.1 * incM F x * (incM F b.1)ᵀ := by
  change incM F (a.1 * x * b.1ᵀ) = _
  simp only [incM, Matrix.map_mul, Matrix.transpose_map]

theorem latInv_of : LatInv := by
  intro F E _ _ _ _ _ σ _ τ n d J J' _ _ C N S hS γ hγ δ hδ g h
  obtain ⟨a, ha⟩ := latInv_mat_inv_mul γ hγ
  obtain ⟨b, hb⟩ := latInv_mat_inv_mul δ hδ
  have hSS : ∀ x, x ∈ S ↔ latInvEquiv a b x ∈ S := by
    intro x
    rcases hS with rfl | rfl
    · simp
    · simp only [fullRank, Set.mem_setOf_eq, latInvEquiv_rank]
  unfold latSum
  rw [← Equiv.tsum_eq ((latInvEquiv a b).subtypeEquiv hSS)
    (fun x : S => ENNReal.ofReal (maj τ C N (mat g⁻¹ * incM F x.1 * (mat h⁻¹)ᵀ)))]
  refine tsum_congr fun x => ?_
  rw [Equiv.subtypeEquiv_apply, ha, hb, latInv_incM, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

end PositivityTheory.ThKEst

end
end
