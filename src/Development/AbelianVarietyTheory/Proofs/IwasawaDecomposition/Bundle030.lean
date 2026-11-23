module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle014
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle015
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle016
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.SetTheory.Cardinal.Continuum
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle003
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle017
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle018
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Countable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Localization.Module
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001

@[expose] public section

section

open Matrix

theorem _root_.GlobalTheory.T.exists_dotProduct_mulVec_eq_of_linearIndependent' : ∀ (r k : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (ε : Fin k → Fin r → ℚ), Mq.det ≠ 0 → LinearIndependent ℚ ε → ∀ t : Fin k → ℚ, ∃ x : Fin r → ℚ, ∀ i, x ⬝ᵥ Mq *ᵥ ε i = t i := by
  first | exact @GlobalTheory.exists_dotProduct_mulVec_eq_of_linearIndependent | exact GlobalTheory.exists_dotProduct_mulVec_eq_of_linearIndependent | (intros; apply GlobalTheory.exists_dotProduct_mulVec_eq_of_linearIndependent <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.mem_of_orthogonal_orthogonal_of_skew_det_ne_zero : ∀ (r : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (V : Submodule ℚ (Fin r → ℚ)), Mqᵀ = -Mq → Mq.det ≠ 0 → ∀ x : Fin r → ℚ, (∀ y : Fin r → ℚ, (∀ w ∈ V, y ⬝ᵥ Mq *ᵥ w = 0) → x ⬝ᵥ Mq *ᵥ y = 0) → x ∈ V := by
  first | exact @GlobalTheory.rat_alternating_orthogonal_orthogonal_le | exact GlobalTheory.rat_alternating_orthogonal_orthogonal_le | (intros; apply GlobalTheory.rat_alternating_orthogonal_orthogonal_le <;> assumption)
end

section

open IsDedekindDomain NumberField

namespace GlobalTheory.LatticeMinuscule

open Matrix

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {n : ℕ}

open IsDedekindDomain NumberField in
open Matrix in
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {n : ℕ} in
theorem _root_.GlobalTheory.LatticeMinuscule.lattice_elementary_divisors (R K : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (ϖ : R)
    (hϖ : Irreducible ϖ) (n k : ℕ) (hk : k ≤ n) (Λ : Submodule R (Fin n → K)) (hfg : Λ.FG)
    (hsp : Submodule.span K (Λ : Set (Fin n → K)) = ⊤) (a a' : Matrix (Fin n) (Fin n) K)
    (haa : a * a' = 1) (h1 : ∀ y ∈ Λ, a.mulVec y ∈ Λ)
    (h2 : ∀ y ∈ Λ, ∃ z ∈ Λ, algebraMap R K ϖ • y = a.mulVec z) (u : Rˣ)
    (hdet : a.det = algebraMap R K ϖ ^ k * algebraMap R K (u : R)) :
    ∃ B : Matrix (Fin n) (Fin n) K,
      (∀ y, y ∈ Λ ↔ ∃ z : Fin n → R, y = B.mulVec (fun i => algebraMap R K (z i))) ∧
      (∀ y, (∃ x ∈ Λ, y = a'.mulVec x) ↔ ∃ z : Fin n → R, y = B.mulVec (fun i =>
        algebraMap R K ϖ ^ (if i.1 < n - k then (0 : ℤ) else -1) * algebraMap R K (z i))) := by
  classical
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hϖ0 : algebraMap R K ϖ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hϖ.ne_zero
  haveI : Module.Finite R Λ := Module.Finite.iff_fg.mpr hfg
  haveI : Module.Free R Λ := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis R Λ
  have hli : LinearIndependent K (fun i => (b i : Fin n → K)) :=
    (LinearIndependent.iff_fractionRing R K).mp
      (b.linearIndependent.map' Λ.subtype (Submodule.ker_subtype Λ))
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex R Λ) = n := by
    have hspan : ⊤ ≤ Submodule.span K (Set.range fun i => (b i : Fin n → K)) := by
      rw [← hsp, Submodule.span_le]
      intro x hx
      rw [← show ((⟨x, hx⟩ : Λ) : Fin n → K) = x from rfl, ← b.sum_repr ⟨x, hx⟩,
        Submodule.coe_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [Submodule.coe_smul, ← algebraMap_smul K]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have h := Module.finrank_eq_card_basis (Module.Basis.mk hli hspan)
    rw [Module.finrank_fin_fun] at h
    exact h.symm
  let b' := b.reindex (Fintype.equivFinOfCardEq hcard)
  let B0 : Matrix (Fin n) (Fin n) K := Matrix.of fun i j => (b' j : Fin n → K) i
  have key : ∀ z : Fin n → R, B0 *ᵥ (fun i => algebraMap R K (z i)) =
      ((b'.equivFun.symm z : Λ) : Fin n → K) := by
    intro z; ext i
    simp [B0, Matrix.mulVec, dotProduct, Module.Basis.equivFun_symm_apply, Submodule.coe_sum,
      Finset.sum_apply, Algebra.smul_def, mul_comm]
  have memL : ∀ y, y ∈ Λ ↔ ∃ z : Fin n → R, y = B0 *ᵥ (fun i => algebraMap R K (z i)) := by
    intro y; constructor
    · intro hy; refine ⟨b'.equivFun ⟨y, hy⟩, ?_⟩; rw [key, LinearEquiv.symm_apply_apply]
    · rintro ⟨z, rfl⟩; rw [key]; exact Subtype.prop _
  have keyinj : ∀ z w : Fin n → R, B0 *ᵥ (fun i => algebraMap R K (z i)) =
      B0 *ᵥ (fun i => algebraMap R K (w i)) → z = w := by
    intro z w h; rw [key, key] at h; exact b'.equivFun.symm.injective (Subtype.coe_injective h)
  have hmap : ∀ (N : Matrix (Fin n) (Fin n) R) (z : Fin n → R),
      N.map (algebraMap R K) *ᵥ (fun i => algebraMap R K (z i)) =
        fun i => algebraMap R K ((N *ᵥ z) i) := by
    intro N z; funext i; exact (RingHom.map_mulVec (algebraMap R K) N z i).symm
  have h1' : ∀ j, ∃ z : Fin n → R,
      a *ᵥ (b' j : Fin n → K) = B0 *ᵥ (fun i => algebraMap R K (z i)) :=
    fun j => (memL _).1 (h1 _ (b' j).2)
  choose zM hzM using h1'
  let M : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => zM j i
  have haB : a * B0 = B0 * M.map (algebraMap R K) := by
    ext i j
    have := congrFun (hzM j) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, B0, M] using this
  have h2' : ∀ j, ∃ z : Fin n → R, algebraMap R K ϖ • (b' j : Fin n → K) =
      a *ᵥ (B0 *ᵥ (fun i => algebraMap R K (z i))) := by
    intro j
    obtain ⟨x, hx, hxe⟩ := h2 _ (b' j).2
    obtain ⟨z, rfl⟩ := (memL x).1 hx
    exact ⟨z, hxe⟩
  choose zM' hzM' using h2'
  let M' : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => zM' j i
  have hMM : M * M' = ϖ • (1 : Matrix (Fin n) (Fin n) R) := by
    ext i j
    have h := hzM' j
    rw [Matrix.mulVec_mulVec, haB, ← Matrix.mulVec_mulVec, hmap] at h
    have hl : algebraMap R K ϖ • (b' j : Fin n → K) =
        B0 *ᵥ (fun i => algebraMap R K ((ϖ • Pi.single j (1 : R) : Fin n → R) i)) := by
      rw [key, map_smul, Module.Basis.equivFun_symm_apply]
      simp [Pi.single_apply, algebraMap_smul]
    have h3 := congrFun (keyinj _ _ (hl.symm.trans h)) i
    rw [show (M * M') i j = (M *ᵥ zM' j) i from rfl, ← h3]
    simp [Matrix.one_apply, Pi.single_apply]
  have hsurj : Function.Surjective B0.mulVec := by
    intro y
    have hy : y ∈ Submodule.span K (Λ : Set (Fin n → K)) := hsp ▸ Submodule.mem_top
    have hle : Submodule.span K (Λ : Set (Fin n → K)) ≤ LinearMap.range (Matrix.mulVecLin B0) := by
      rw [Submodule.span_le]
      intro x hx
      obtain ⟨z, rfl⟩ := (memL x).1 hx
      exact ⟨_, rfl⟩
    obtain ⟨w, hw⟩ := hle hy
    exact ⟨w, hw⟩
  have hB0 : B0.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det B0).mp (Matrix.mulVec_surjective_iff_isUnit.mp hsurj)).ne_zero
  have hdetM : Associated M.det (ϖ ^ k) := by
    have h := congrArg Matrix.det haB
    have hdm : (M.map (algebraMap R K)).det = algebraMap R K M.det := (RingHom.map_det _ _).symm
    rw [Matrix.det_mul, Matrix.det_mul, mul_comm, hdet, hdm, ← map_pow, ← map_mul] at h
    have h' := hinj (mul_left_cancel₀ hB0 h)
    exact ⟨u⁻¹, by rw [← h', mul_assoc, Units.mul_inv, mul_one]⟩
  obtain ⟨P, Q, hP, hQ, hMQ⟩ :=
    _root_.GlobalTheory.SmithBetween.smith_between R ϖ hϖ n k hk M M' hMM hdetM
  have haa' : a' * a = 1 := mul_eq_one_comm.mp haa
  have hE : ∀ z : Fin n → R, a *ᵥ ((B0 * Q.map (algebraMap R K)) *ᵥ (fun i =>
      algebraMap R K ϖ ^ (if i.1 < n - k then (0 : ℤ) else -1) * algebraMap R K (z i))) =
        B0 *ᵥ (fun i => algebraMap R K ((P *ᵥ z) i)) := by
    intro z
    have hdw : ((Matrix.diagonal fun i : Fin n => if i.1 < n - k then (1 : R) else ϖ).map
        (algebraMap R K)) *ᵥ (fun i =>
          algebraMap R K ϖ ^ (if i.1 < n - k then (0 : ℤ) else -1) * algebraMap R K (z i)) =
        fun i => algebraMap R K (z i) := by
      rw [Matrix.diagonal_map (map_zero _)]
      funext i
      rw [Matrix.mulVec_diagonal]
      by_cases hi : i.1 < n - k <;> simp [hi, hϖ0]
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, haB, Matrix.mul_assoc, ← Matrix.map_mul, hMQ,
      Matrix.map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hdw, hmap]
  refine ⟨B0 * Q.map (algebraMap R K), fun y => ?_, fun y => ?_⟩
  · rw [memL]
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨Q⁻¹ *ᵥ z, ?_⟩
      rw [← Matrix.mulVec_mulVec, hmap, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv Q hQ,
        Matrix.one_mulVec]
    · rintro ⟨z, rfl⟩
      exact ⟨Q *ᵥ z, by rw [← Matrix.mulVec_mulVec, hmap]⟩
  · constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨z, rfl⟩ := (memL x).1 hx
      refine ⟨P⁻¹ *ᵥ z, ?_⟩
      have h := hE (P⁻¹ *ᵥ z)
      have hz : P *ᵥ (P⁻¹ *ᵥ z) = z := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv P hP, Matrix.one_mulVec]
      rw [hz] at h
      rw [← h, Matrix.mulVec_mulVec, haa', Matrix.one_mulVec]
    · rintro ⟨z, rfl⟩
      refine ⟨_, (memL _).2 ⟨P *ᵥ z, rfl⟩, ?_⟩
      rw [← hE z, Matrix.mulVec_mulVec, haa', Matrix.one_mulVec]

end GlobalTheory.LatticeMinuscule
end

section


theorem _root_.GlobalTheory.T.posSemidef_real_of_int_quadForm_nonneg : ∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℤ), B.IsSymm → (∀ v : Fin g → ℤ, 0 ≤ dotProduct v (B.mulVec v)) → (B.map (Int.cast : ℤ → ℝ)).PosSemidef := by
  first | exact @GlobalTheory.intSymm_posSemidef_real | exact GlobalTheory.intSymm_posSemidef_real | (intros; apply GlobalTheory.intSymm_posSemidef_real <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_injective_baseChange_inf_restrictScalars_range_eq : ∀ {O V : Type} [CommRing O] [IsDomain O] [AddCommGroup V] [Module (FractionRing O) V] [Module O V]
    [IsScalarTower O (FractionRing O) V] (N : Submodule O V),
    Submodule.span (FractionRing O) (N : Set V) = ⊤ → ∀ (W : Submodule (FractionRing O) V),
    ∃ e : FractionRing O ⊗[O] ↥(N ⊓ W.restrictScalars O) →ₗ[FractionRing O] V,
      Function.Injective e ∧ LinearMap.range e = W ∧
      ∀ (c : FractionRing O) (x : ↥(N ⊓ W.restrictScalars O)), e (c ⊗ₜ[O] x) = c • (x : V) := by
  first | exact @GlobalTheory.baseChange_inf_lattice_eq_subspace | exact GlobalTheory.baseChange_inf_lattice_eq_subspace | (intros; apply GlobalTheory.baseChange_inf_lattice_eq_subspace <;> assumption)
end

section

open ReciprocityTheory.ChartRestriction.G.FD NumberField

namespace GlobalTheory

theorem exists_common_denominator (E : Type) [Field E] [NumberField E] (n : ℕ) (f : Fin n → E) :
    ∃ d : ℕ, 0 < d ∧ ∀ j, IsIntegral ℤ ((d : E) * f j) := by
  classical
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ (L := E) (Finset.univ.image f)
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, fun j => ?_⟩
  have hj := h (f j) (Finset.mem_image_of_mem f (Finset.mem_univ j))
  rw [zsmul_eq_mul] at hj
  rcases Int.natAbs_eq y with e | e
  · have : ((y.natAbs : ℕ) : E) = (y : E) := by
      conv_rhs => rw [e]
      simp
    rw [this]; exact hj
  · have : ((y.natAbs : ℕ) : E) = -(y : E) := by
      conv_rhs => rw [e]
      simp
    rw [this, neg_mul]; exact hj.neg

end GlobalTheory
end

section

open NumberField IsDedekindDomain Matrix
open scoped BigOperators

theorem _root_.GlobalTheory.T.comap_single_span_algebraMap_numberField : ∀ (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M] (ι : Type) [Fintype ι] [DecidableEq ι] (S : Set (ι → E)) (τ : ι), (Submodule.span (𝓞 M) ((fun (v : ι → E) (i : ι) => algebraMap E M (v i)) '' S)).comap (LinearMap.single (𝓞 M) (fun _ : ι => M) τ) = Submodule.span (𝓞 M) (algebraMap E M '' ((Submodule.span (𝓞 E) S).comap (LinearMap.single (𝓞 E) (fun _ : ι => E) τ) : Set E)) := by
  first | exact @GlobalTheory.comap_single_span_algebraMap | exact GlobalTheory.comap_single_span_algebraMap | (intros; apply GlobalTheory.comap_single_span_algebraMap <;> assumption)
end

section

namespace GlobalTheory

open Cardinal

theorem cardinalMk_padic_eq_continuum (l : ℕ) [Fact l.Prime] : #ℚ_[l] = 𝔠 := by
  apply le_antisymm
  · have hd := Padic.denseRange_ratCast l
    have h : ∀ x : ℚ_[l], ∃ u : ℕ → ℚ,
        Filter.Tendsto (fun n => (u n : ℚ_[l])) Filter.atTop (nhds x) := by
      intro x
      obtain ⟨v, hv, hx⟩ := mem_closure_iff_seq_limit.1 (hd x)
      choose u hu using hv
      exact ⟨u, by simpa only [hu] using hx⟩
    choose u hu using h
    have hi : Function.Injective u := fun x y hxy =>
      tendsto_nhds_unique (hu x) (hxy ▸ hu y)
    refine (Cardinal.mk_le_of_injective hi).trans ?_
    simp
  · exact continuum_le_cardinal_of_nontriviallyNormedField ℚ_[l]

theorem cardinalMk_padicAlgCl_eq_continuum (l : ℕ) [Fact l.Prime] : #(PadicAlgCl l) = 𝔠 := by
  apply le_antisymm
  · exact (Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[l] (PadicAlgCl l)).trans
      (max_le (cardinalMk_padic_eq_continuum l).le Cardinal.aleph0_le_continuum)
  · rw [← cardinalMk_padic_eq_continuum l]
    exact Cardinal.mk_le_of_injective (algebraMap ℚ_[l] (PadicAlgCl l)).injective

theorem nonempty_padicAlgCl_ringEquiv_complex (l : ℕ) [Fact l.Prime] :
    Nonempty (PadicAlgCl l ≃+* ℂ) :=
  IsAlgClosed.ringEquiv_of_equiv_of_charZero
    (by rw [cardinalMk_padicAlgCl_eq_continuum]; exact Cardinal.aleph0_lt_continuum)
    (Cardinal.eq.mp (by rw [cardinalMk_padicAlgCl_eq_continuum, Cardinal.mk_complex]))

theorem exists_padicAlgCl_ringEquiv_complex_comp_eq_of_countable (l : ℕ) [Fact l.Prime]
    (K : Type) [Field K] [Countable K] (a : K →+* PadicAlgCl l) (b : K →+* ℂ) :
    ∃ e : PadicAlgCl l ≃+* ℂ, ∀ x, e (a x) = b x := by
  obtain ⟨e₀⟩ := nonempty_padicAlgCl_ringEquiv_complex l
  obtain ⟨σ, hσ⟩ := GaloisDescent.exists_complex_ringEquiv_comp_eq (e₀.toRingHom.comp a) b
  exact ⟨e₀.trans σ, fun x => hσ x⟩

theorem exists_padicAlgCl_ringEquiv_complex_comp_eq (l : ℕ) [Fact l.Prime]
    (K : Type) [Field K] [NumberField K] (a : K →+* PadicAlgCl l) (b : K →+* ℂ) :
    ∃ e : PadicAlgCl l ≃+* ℂ, (e : PadicAlgCl l →+* ℂ).comp a = b := by
  haveI : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  obtain ⟨e, he⟩ := exists_padicAlgCl_ringEquiv_complex_comp_eq_of_countable l K a b
  exact ⟨e, RingHom.ext he⟩

end GlobalTheory
end

section

open NumberField IsDedekindDomain Matrix
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_matrix_basis_lattice_up_to_denominator_notMem : ∀ (K : Type) [Field K] [NumberField K] (n : Type) [Fintype n] [DecidableEq n] (L : Submodule (𝓞 K) (n → K)) (𝔭 : HeightOneSpectrum (𝓞 K)), L.FG → Submodule.span K (L : Set (n → K)) = ⊤ → ∃ g : Matrix n n K, IsUnit g.det ∧ ∃ t : 𝓞 K, t ∉ 𝔭.asIdeal ∧ (∀ x ∈ L, ∀ i, (t : K) * (g⁻¹ *ᵥ x) i ∈ (algebraMap (𝓞 K) K).range) ∧ ∀ j, (t : K) • (fun i => g i j) ∈ L := by
  first | exact @GlobalTheory.LatticeLocBasis.exists_matrix_up_to_notMem | exact GlobalTheory.LatticeLocBasis.exists_matrix_up_to_notMem | (intros; apply GlobalTheory.LatticeLocBasis.exists_matrix_up_to_notMem <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix
open scoped BigOperators

theorem _root_.GlobalTheory.T.selfDual_lattice_standard_at_rational_prime : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* K) (n : Type) [Fintype n] [DecidableEq n] (p : ℕ) (𝔭 : HeightOneSpectrum (𝓞 K)) (α β : 𝓞 K) (L : Submodule (𝓞 K) (n → K)) (t : 𝓞 K), (∀ x, σ (σ x) = x) → (∀ x : 𝓞 K, ∃ m : ℤ, (x : K) * σ x = m) → p.Prime → (p : 𝓞 K) ∈ 𝔭.asIdeal → α ∈ 𝔭.asIdeal → β ∉ 𝔭.asIdeal → (β : K) = σ α → (∀ x, x ∈ L ↔ ∀ y ∈ L, ∑ i, x i * σ (y i) ∈ (algebraMap (𝓞 K) K).range) → t ∉ 𝔭.asIdeal → (∀ x ∈ L, ∀ i, (t : K) * x i ∈ (algebraMap (𝓞 K) K).range) → (∀ j, (Pi.single j (t : K) : n → K) ∈ L) → ∃ s : ℕ, Nat.Coprime s p ∧ (∀ x ∈ L, ∀ i, (s : K) * x i ∈ (algebraMap (𝓞 K) K).range) ∧ ∀ v : n → K, (∀ i, v i ∈ (algebraMap (𝓞 K) K).range) → (s : K) • v ∈ L := by
  first | exact @GlobalTheory.selfDual_standard_at_rational_prime | exact GlobalTheory.selfDual_standard_at_rational_prime | (intros; apply GlobalTheory.selfDual_standard_at_rational_prime <;> assumption)
end

section

open NumberField Matrix

theorem _root_.GlobalTheory.T.unitary_family_eq_cayley_of_skew_family : ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ), (∀ σ, X σ * (X (ComplexEmbedding.conjugate σ))ᵀ = 1) → (∀ σ, (1 + X σ).det ≠ 0) → ∃ Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ, (∀ σ, Y (ComplexEmbedding.conjugate σ) = -(Y σ)ᵀ) ∧ (∀ σ, (1 - Y σ).det ≠ 0) ∧ ∀ σ, (1 + Y σ) * (1 - Y σ)⁻¹ = X σ := by
  first | exact @GlobalTheory.unitary_isCayley_of_det_ne_zero | exact GlobalTheory.unitary_isCayley_of_det_ne_zero | (intros; apply GlobalTheory.unitary_isCayley_of_det_ne_zero <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.nonempty_adicCompletion_quotient_ringEquiv : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (J q : Ideal A), Nonempty ((AdicCompletion J A ⧸ q.map (algebraMap A (AdicCompletion J A))) ≃+* AdicCompletion (J.map (Ideal.Quotient.mk q)) (A ⧸ q)) := by
  first | exact @GlobalTheory.adicCompletion_quotient_ringEquiv | exact GlobalTheory.adicCompletion_quotient_ringEquiv | (intros; apply GlobalTheory.adicCompletion_quotient_ringEquiv <;> assumption)
end
