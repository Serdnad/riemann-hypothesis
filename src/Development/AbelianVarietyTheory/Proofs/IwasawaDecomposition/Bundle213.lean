module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle199
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier

namespace StepLoc

variable {ι : Type} {m k : ι → ℕ} {K : Type} [Field K] {O : Subring K} {τ : ι}

abbrev blk (k : ι → ℕ) (τ : ι) (P : Mat m K) : Matrix (Rest m k τ) (Rest m k τ) K :=
  (P τ).submatrix Subtype.val Subtype.val

theorem mul_apply_rest {P : Mat m K} (hP : Par k O P) (g : Mat m K) (a : Fin (m τ)) (j : Rest m k τ) :
    (g * P) τ a j.1 = Matrix.vecMul (fun l : Rest m k τ => g τ a l.1) (blk k τ P) j := by
  rw [Pi.mul_apply, Matrix.mul_apply, ← Fintype.sum_subtype_add_sum_subtype (fun l : Fin (m τ) => k τ ≤ (l : ℕ))]
  have : ∑ l : {l : Fin (m τ) // ¬ k τ ≤ (l : ℕ)}, g τ a l.1 * P τ l.1 j.1 = 0 :=
    Finset.sum_eq_zero fun l _ => by
      have h1 := l.2
      have h2 := j.2
      rw [(hP τ).2.2.2 l.1 j.1 (by omega) (by show (l.1 : ℕ) < j.1; omega), mul_zero]
  rw [this, add_zero]
  rfl

theorem blk_mul_inv {P : Mat m K} (hP : Par k O P) : blk k τ P * blk k τ P⁻¹ = 1 := by
  ext a j
  have := mul_apply_rest hP.inv P a.1 j
  rw [Mat.mul_inv hP.det_ne] at this
  refine this.symm.trans ?_
  show (1 : Matrix _ _ K) a.1 j.1 = _
  simp only [Matrix.one_apply, Subtype.ext_iff]

theorem line_iff {Q : Mat m K} (hQ : Par k O Q) (hk : k τ < m τ) {s : Rest m k τ → K} {b : K}
    (hs : ∀ j : Rest m k τ, s j = b * Q τ ⟨k τ, hk⟩ j.1) (hb : b ≠ 0) (g : Mat m K) :
    (∃ a : K, ∀ j : Rest m k τ, (g * Q) τ ⟨k τ, hk⟩ j.1 = a * s j) ↔
      ∀ j : Fin (m τ), k τ < j → g τ ⟨k τ, hk⟩ j = 0 := by
  have e : ∀ (x : K) (j : Rest m k τ), Matrix.vecMul (Pi.single (⟨⟨k τ, hk⟩, le_rfl⟩ : Rest m k τ) x) (blk k τ Q) j
      = x * Q τ ⟨k τ, hk⟩ j.1 := fun x j => by
    rw [Matrix.single_vecMul]
    simp
  constructor
  · rintro ⟨a, ha⟩ j hj
    have h1 : Matrix.vecMul (fun l : Rest m k τ => g τ ⟨k τ, hk⟩ l.1) (blk k τ Q) =
        Matrix.vecMul (Pi.single (⟨⟨k τ, hk⟩, le_rfl⟩ : Rest m k τ) (a * b)) (blk k τ Q) := by
      funext l
      rw [← mul_apply_rest hQ, ha, e, hs, mul_assoc]
    have h2 := congrArg (Matrix.vecMul · (blk k τ Q⁻¹)) h1
    simp only [Matrix.vecMul_vecMul, blk_mul_inv hQ, Matrix.vecMul_one] at h2
    have h3 := congrFun h2 ⟨j, hj.le⟩
    rwa [Pi.single_eq_of_ne (fun h => hj.ne' (congrArg (fun x : Rest m k τ => (x.1 : ℕ)) h))] at h3
  · intro h
    refine ⟨g τ ⟨k τ, hk⟩ ⟨k τ, hk⟩ / b, fun j => ?_⟩
    have h1 : (fun l : Rest m k τ => g τ ⟨k τ, hk⟩ l.1) =
        Pi.single (⟨⟨k τ, hk⟩, le_rfl⟩ : Rest m k τ) (g τ ⟨k τ, hk⟩ ⟨k τ, hk⟩) := by
      funext l
      by_cases hl : l = ⟨⟨k τ, hk⟩, le_rfl⟩
      · rw [hl, Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne hl]
        exact h _ (lt_of_le_of_ne l.2 fun h' => hl (Subtype.ext (Fin.ext h'.symm)))
    rw [mul_apply_rest hQ, h1, e, hs, ← mul_assoc, div_mul_cancel₀ _ hb]

theorem par_succ_iff {k' : ι → ℕ} (hk : k τ < m τ) (h1 : k' τ = k τ + 1) (h2 : ∀ τ', τ' ≠ τ → k' τ' = k τ')
    (g : Mat m K) :
    Par k' O g ↔ Par k O g ∧ ∀ j : Fin (m τ), k τ < j → g τ ⟨k τ, hk⟩ j = 0 := by
  constructor
  · intro h
    refine ⟨h.mono (fun t => ?_) le_rfl, fun j hj => (h τ).2.2.2 _ j (by rw [h1]; exact Nat.lt_succ_self _) hj⟩
    by_cases ht : t = τ
    · rw [ht, h1]; exact Nat.le_succ _
    · exact (h2 t ht).ge
  · rintro ⟨h, h'⟩ t
    refine ⟨(h t).1, (h t).2.1, (h t).2.2.1, fun i j hi hij => ?_⟩
    by_cases ht : t = τ
    · subst ht
      rw [h1] at hi
      rcases (Nat.lt_succ_iff.1 hi).lt_or_eq with hi | hi
      · exact (h t).2.2.2 i j hi hij
      · obtain rfl : i = ⟨k t, hk⟩ := Fin.ext hi
        exact h' j hij
    · exact (h t).2.2.2 i j (h2 t ht ▸ hi) hij

theorem exists_completion (hk : k τ < m τ) (c : Rest m k τ → K) (i : Rest m k τ) (hi : c i = 1) :
    ∃ N : Mat m K, (∀ j : Rest m k τ, N τ ⟨k τ, hk⟩ j.1 = c j) ∧
      ∀ O : Subring K, (∀ j, c j ∈ O) → Par k O N := by
  classical
  let v : Fin (m τ) → K := fun j => if h : k τ ≤ (j : ℕ) then c ⟨j, h⟩ else 0
  have hv : ∀ j : Rest m k τ, v j.1 = c j := fun j => dif_pos j.2
  let T : Matrix (Fin (m τ)) (Fin (m τ)) K :=
    ((1 : Matrix _ _ K).updateRow i.1 v).submatrix (Equiv.swap ⟨k τ, hk⟩ i.1) id
  have hd : T.det * T.det = 1 := by
    have e : ((1 : Matrix _ _ K).updateRow i.1 v).det = 1 := by
      rw [← Matrix.cramer_transpose_apply, Matrix.transpose_one, Matrix.cramer_one]
      exact (hv i).trans hi
    rw [Matrix.det_permute, e, mul_one, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  refine ⟨Function.update (1 : Mat m K) τ T, fun j => ?_, fun O hO t => ?_⟩
  · rw [Function.update_self]
    show ((1 : Matrix _ _ K).updateRow i.1 v) (Equiv.swap ⟨k τ, hk⟩ i.1 ⟨k τ, hk⟩) j.1 = _
    rw [Equiv.swap_apply_left, Matrix.updateRow_self, hv]
  by_cases ht : t = τ
  · subst ht
    rw [Function.update_self]
    have hm : ∀ a b, T a b ∈ O := fun a b => by
      show ((1 : Matrix _ _ K).updateRow i.1 v) _ b ∈ O
      rw [Matrix.updateRow_apply]
      split_ifs
      · show dite _ _ _ ∈ O
        split_ifs
        exacts [hO _, O.zero_mem]
      · rw [Matrix.one_apply]; split_ifs; exacts [O.one_mem, O.zero_mem]
    refine ⟨hm, left_ne_zero_of_mul_eq_one hd, ?_, fun a b ha hab => ?_⟩
    · rw [← eq_inv_of_mul_eq_one_left hd]; exact det_mem hm
    · have h1 : a ≠ ⟨k t, hk⟩ := fun h => ha.ne (congrArg Fin.val h)
      have h2 : a ≠ i.1 := fun h => (h ▸ ha).not_ge i.2
      show ((1 : Matrix _ _ K).updateRow i.1 v) (Equiv.swap ⟨k t, hk⟩ i.1 a) b = 0
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Matrix.updateRow_ne h2, Matrix.one_apply_ne hab.ne]
  · rw [Function.update_of_ne ht]
    exact Par.one t

end StepLoc


open StepLoc in
theorem exists_fr_stepSet (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']
    (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (ι : Type) [Finite ι]
    (m k k' : ι → ℕ) (S : Fr M m k) (τ : ι) (hk : k τ < m τ) (A₀ : Mat m Ω) (EE : M.Lat (Rest m k τ))
    (s : Rest m k τ → Ω') (h1 : k' τ = k τ + 1) (h2 : ∀ τ', τ' ≠ τ → k' τ' = k τ')
    (hA₀ : A₀ ∈ S.S (genericPoint M.Z))
    (hE : ∀ z, ∀ A ∈ S.S z, (dualBlock k τ A₀ A).det ≠ 0 ∧
      EE.E z = Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A)))
    (hP : ProjPoints M EE M' φ f s) :
    ∃ S' : Fr M' m k', ∀ z', S'.S z' = stepSet S τ hk A₀ M' φ f s z' := by
  refine ⟨⟨stepSet S τ hk A₀ M' φ f s, fun z' => ?_⟩, fun _ => rfl⟩
  obtain ⟨U, A, hz, hA, hU⟩ := S.loc (f z')
  have hAU : ∀ w ∈ U, A ∈ S.S w := fun w hw => (hU w hw A).2 (by rw [Mat.mul_inv hA]; exact Par.one)
  obtain ⟨hd, hE'⟩ := hE _ A (hAU _ hz)
  obtain ⟨i, hi⟩ := hP.cover z' _ hd hE'
  set c := ((dualBlock k τ A₀ A).map φ).mulVec s with hc
  let ψ : Ω →+* Ω' := φ
  obtain ⟨N, hN, hNO⟩ := exists_completion hk (fun j => c j / c i) i (div_self hi.1)
  have hAφ : ∀ t, (A.map ψ t).det ≠ 0 := fun t => by rw [Mat.det_map]; exact (map_ne_zero ψ).2 (hA t)
  have hN0 : Par k ⊤ N := hNO ⊤ fun _ => trivial
  have hP0 : Par k ⊤ ((A * A₀⁻¹).map ψ) :=
    ((Fr.mem_iff hA₀).1 (Fr.mem_genericPoint (hAU _ hz))).map ψ fun _ _ => trivial
  have hs : s = Matrix.vecMul c (blk k τ ((A * A₀⁻¹).map ψ)) := by
    have hP1 := (Fr.mem_iff hA₀).1 (Fr.mem_genericPoint (hAU _ hz))
    have e1 : (blk k τ (A * A₀⁻¹))⁻¹ * blk k τ (A * A₀⁻¹) = 1 :=
      Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_right_inverse (blk_mul_inv hP1))
    have e2 : c = Matrix.vecMul s ((blk k τ (A * A₀⁻¹))⁻¹.map ψ) := by
      rw [hc, ← Matrix.mulVec_transpose]
      rfl
    have e3 : blk k τ ((A * A₀⁻¹).map ψ) = (blk k τ (A * A₀⁻¹)).map ψ := rfl
    rw [e2, e3, Matrix.vecMul_vecMul, ← Matrix.map_mul, e1, Matrix.map_one _ ψ.map_zero ψ.map_one,
      Matrix.vecMul_one]
  have hQ : ∀ j : Rest m k τ, s j = c i * (N * (A * A₀⁻¹).map ψ) τ ⟨k τ, hk⟩ j.1 := fun j => by
    have e : (fun l : Rest m k τ => N τ ⟨k τ, hk⟩ l.1) = (c i)⁻¹ • c := by
      funext l
      rw [hN, Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
    rw [mul_apply_rest hP0, e, Matrix.smul_vecMul, ← hs, Pi.smul_apply, smul_eq_mul, mul_inv_cancel_left₀ hi.1]
  have hA₁ : ∀ t, ((N * A.map ψ) t).det ≠ 0 := fun t => by
    rw [Pi.mul_apply, Matrix.det_mul]; exact mul_ne_zero (hN0.det_ne t) (hAφ t)
  refine ⟨f ⁻¹ᵁ U ⊓ ⟨_, M'.isOpen_setOf_div c i⟩, N * A.map ψ, ⟨hz, hi⟩, hA₁, fun w hw A' => ?_⟩
  have hNw : Par k (M'.O w).toSubring N := hNO _ hw.2.2
  have hAw : A ∈ S.S (f w) := hAU _ hw.1
  rw [par_succ_iff hk h1 h2, ← line_iff (hN0.mul hP0) hk hQ hi.1]
  have e1 : A' * (N * A.map ψ)⁻¹ * (N * (A * A₀⁻¹).map ψ) = A' * (A₀.map ψ)⁻¹ := by
    rw [Mat.map_mul, Mat.map_inv, ← mul_assoc N, mul_assoc A', ← mul_assoc _ (N * A.map ψ), Mat.inv_mul hA₁,
      one_mul]
  rw [e1]
  refine and_congr_left' ⟨fun h => ?_, fun h B hB => ?_⟩
  · have := (h A hAw).mul hNw.inv
    rwa [Mat.mul_inv_rev, ← mul_assoc]
  · have h3 : Par k (M'.O w).toSubring ((A * B⁻¹).map ψ) :=
      ((Fr.mem_iff hB).1 hAw).map ψ fun _ hx => hP.hom.map_mem_O hx
    have := h.mul (hNw.mul h3)
    rw [Mat.map_mul, Mat.map_inv, ← mul_assoc N, mul_assoc A', ← mul_assoc _ (N * A.map ψ), Mat.inv_mul hA₁,
      one_mul] at this
    exact this

end GlobalTheory.FlagBundle
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier
open scoped TensorProduct

variable {F Ω Ω' : Type} [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']

theorem exists_openImmersion_ringOn (M : RatModel F Ω) {U : M.Z.Opens} (hU : IsAffineOpen U)
    (hne : (U : Set M.Z).Nonempty) : ∃ ι : Sp (M.ringOn U) ⟶ M.Z, IsOpenImmersion ι ∧ Set.range ι = U ∧
      ι ≫ M.s = spMap (algebraMap F (M.ringOn U)) := by
  let e : Γ(M.Z, U) ≅ CommRingCat.of (M.ringOn U) := (M.sectionsEquiv U hne).toCommRingCatIso
  have hx := GlobalTheory.Points.le_preimage_specMap_fromSpec hU e.hom
  have hv : ∀ f, valR (Spec.map e.hom ≫ hU.fromSpec) U f = M.sectionsEquiv U hne f := fun f => by
    rw [GlobalTheory.Points.valR_eq _ U hx, GlobalTheory.Points.valMap_specMap_fromSpec]
    rfl
  refine ⟨Spec.map e.hom ≫ hU.fromSpec, inferInstance, ?_, ?_⟩
  · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, (Spec.map e.hom).surjective.range_eq,
      Set.image_univ, hU.range_fromSpec]
  · rw [← Spec.map_preimage ((Spec.map e.hom ≫ hU.fromSpec) ≫ M.s)]
    refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun b => ?_))
    rw [← GlobalTheory.Points.valR_constFn M.s _ U hx, hv]
    exact Subtype.ext ((RatModel.coe_sectionsEquiv U hne _).trans (M.valF_constFn hne b))

theorem exists_openImmersion_tensor (M : RatModel F Ω) {U : M.Z.Opens} (hU : IsAffineOpen U)
    (hne : (U : Set M.Z).Nonempty) {K : Type} [Field K] [Algebra F K] {Z : Scheme.{0}} {p : Z ⟶ M.Z} {q : Z ⟶ Sp K}
    (h : IsPullback p q M.s (spMap (algebraMap F K))) :
    ∃ j : Sp (M.ringOn U ⊗[F] K) ⟶ Z, IsOpenImmersion j ∧ Set.range j = p ⁻¹' U := by
  obtain ⟨ι, hι, hr, hs⟩ := exists_openImmersion_ringOn M hU hne
  have h1 := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct F (M.ringOn U) K)
  rw [show Spec.map (CommRingCat.ofHom (algebraMap F (M.ringOn U))) = ι ≫ M.s from hs.symm] at h1
  let j := h.lift (_ ≫ ι) _ ((Category.assoc _ _ _).trans h1.w)
  have h2 : IsPullback j _ p ι :=
    (IsPullback.of_bot (h₁₁ := _) (by simpa [j] using h1) (h.lift_fst _ _ _).symm h).flip
  refine ⟨j, MorphismProperty.of_isPullback h2.flip hι, ?_⟩
  refine Eq.trans ?_ (congrArg (p ⁻¹' ·) hr)
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨_, by rw [← Scheme.Hom.comp_apply, ← h2.w, Scheme.Hom.comp_apply]⟩
  · rintro ⟨w, hw⟩
    obtain ⟨v, hv, -⟩ := Scheme.exists_preimage_of_isPullback h2 z w hw.symm
    exact ⟨v, hv⟩

theorem nonempty_algEquiv_adjoin (φ : Ω →ₐ[F] Ω') (A : Subalgebra F Ω) {σ : Type} (t : σ → Ω')
    (ht : ∀ P : MvPolynomial σ Ω, MvPolynomial.eval₂ (φ : Ω →+* Ω') t P = 0 → P = 0) :
    Nonempty (MvPolynomial σ A ≃ₐ[F] Algebra.adjoin F (φ '' (A : Set Ω) ∪ Set.range t)) := by
  let ψ : MvPolynomial σ A →ₐ[F] Ω' := MvPolynomial.aevalTower (φ.comp A.val) t
  have hinj : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro P hP
    refine MvPolynomial.map_injective (A.val : A →+* Ω) Subtype.val_injective ?_
    rw [map_zero]
    refine ht _ ?_
    rw [MvPolynomial.eval₂_map]
    exact hP
  have hr : ψ.range = Algebra.adjoin F (φ '' (A : Set Ω) ∪ Set.range t) := by
    refine le_antisymm ?_ (Algebra.adjoin_le ?_)
    · rintro _ ⟨P, rfl⟩
      show ψ P ∈ _
      induction P using MvPolynomial.induction_on with
      | C a => exact Algebra.subset_adjoin (Or.inl ⟨a, a.2, by simp [ψ]⟩)
      | add P Q hP hQ => rw [map_add]; exact add_mem hP hQ
      | mul_X P i hP =>
        rw [map_mul]
        exact mul_mem hP (Algebra.subset_adjoin (Or.inr ⟨i, by simp [ψ]⟩))
    · rintro _ (⟨a, ha, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨MvPolynomial.C ⟨a, ha⟩, by simp [ψ]⟩
      · exact ⟨MvPolynomial.X i, by simp [ψ]⟩
  exact ⟨(AlgEquiv.ofInjective ψ hinj).trans (Subalgebra.equivOfEq _ _ hr)⟩

theorem isDomain_mvPolynomial_tensor (A K σ : Type) [CommRing A] [Algebra F A] [CommRing K] [Algebra F K]
    [IsDomain (A ⊗[F] K)] : IsDomain (MvPolynomial σ A ⊗[F] K) := by
  let e1 : MvPolynomial σ A ⊗[F] K ≃ₐ[F] (A ⊗[F] MvPolynomial σ F) ⊗[F] K :=
    Algebra.TensorProduct.congr ((MvPolynomial.algebraTensorAlgEquiv F A).symm.restrictScalars F) AlgEquiv.refl
  let e2 : (A ⊗[F] MvPolynomial σ F) ⊗[F] K ≃ₐ[F] (A ⊗[F] K) ⊗[F] MvPolynomial σ F :=
    (Algebra.TensorProduct.assoc F F F A (MvPolynomial σ F) K).trans
      ((Algebra.TensorProduct.congr AlgEquiv.refl (Algebra.TensorProduct.comm F _ _)).trans
        (Algebra.TensorProduct.assoc F F F A K (MvPolynomial σ F)).symm)
  let e3 := MvPolynomial.algebraTensorAlgEquiv (σ := σ) F (A ⊗[F] K)
  exact (((e1.trans e2).toRingEquiv).trans e3.toRingEquiv).toMulEquiv.isDomain _

theorem AffCover.geometricallyIntegral : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']
    (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (r : ℕ), AffCover M M' φ f r →
    GeometricallyIntegral M.s → GeometricallyIntegral M'.s := by
  intro F Ω Ω' _ _ _ _ _ M M' φ f r h hM
  refine ⟨geometrically_iff_of_commRing.2 fun K _ _ Z p q hZ => ?_⟩
  have hI : IsIntegral (pullback M.s (spMap (algebraMap F K))) :=
    pullback_of_geometrically hM.geometrically_isIntegral K _
  have key : ∀ z' : M'.Z, ∃ (U : M'.Z.Opens) (Y : Scheme.{0}) (j : Y ⟶ Z), z' ∈ U ∧ IsIntegral Y ∧
      IsOpenImmersion j ∧ Set.range j = p ⁻¹' U := by
    intro z'
    obtain ⟨U, W, t, hU, hW, hz, hUW, ht, hR⟩ := h.2 z'
    have hWne : (W : Set M.Z).Nonempty := ⟨_, hUW z' hz⟩
    obtain ⟨i, hi, -⟩ := exists_openImmersion_tensor M hW hWne (IsPullback.of_hasPullback M.s (spMap (algebraMap F K)))
    have : Nontrivial (M.ringOn W ⊗[F] K) := inferInstance
    have : IsIntegral (Sp (M.ringOn W ⊗[F] K)) := isIntegral_of_isOpenImmersion i
    have : IsDomain (M.ringOn W ⊗[F] K) := (affine_isIntegral_iff (CommRingCat.of _)).1 this
    have := isDomain_mvPolynomial_tensor (F := F) (M.ringOn W) K (Fin r)
    obtain ⟨e⟩ := nonempty_algEquiv_adjoin φ (M.ringOn W) t ht
    rw [← hR] at e
    have : IsDomain (M'.ringOn U ⊗[F] K) :=
      (Algebra.TensorProduct.congr e.symm (AlgEquiv.refl (A₁ := K) (R := F))).toMulEquiv.isDomain _
    obtain ⟨j, hj, hr⟩ := exists_openImmersion_tensor M' hU ⟨_, hz⟩ hZ
    exact ⟨U, _, j, hz, inferInstance, hj, hr⟩
  have hred : IsReduced Z := by
    have : ∀ z : Z, _root_.IsReduced (Z.presheaf.stalk z) := fun z => by
      obtain ⟨U, Y, j, hz, hY, hj, hr⟩ := key (p z)
      obtain ⟨y, rfl⟩ : z ∈ Set.range j := hr ▸ hz
      exact isReduced_of_injective (j.stalkMap y).hom (asIso (j.stalkMap y)).commRingCatIsoToRingEquiv.injective
    exact isReduced_of_isReduced_stalk Z
  have hopen : UniversallyOpen p := MorphismProperty.of_isPullback hZ.flip inferInstance
  have hirr : IrreducibleSpace Z := by
    obtain ⟨U, Y, j, hz, hY, hj, hr⟩ := key (genericPoint M'.Z)
    have h1 : IsIrreducible (Set.range j) := by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ Y).image _ j.continuous.continuousOn
    have h2 : Dense (Set.range j) := by
      rw [hr]
      exact (U.isOpen.dense ⟨_, hz⟩).preimage p.isOpenMap
    have h3 := h1.closure
    rw [h2.closure_eq] at h3
    exact (irreducibleSpace_def Z).2 h3
  exact isIntegral_of_irreducibleSpace_of_isReduced Z

end GlobalTheory.FlagBundle
end
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

variable {ι : Type} {m : ι → ℕ}

theorem mat_chain {K₁ K₂ K₃ : Type} [Field K₁] [Field K₂] [Field K₃] (ψ : K₁ →+* K₂) (ψ' : K₂ →+* K₃)
    (A'' : Mat m K₃) (A' : Mat m K₂) (A : Mat m K₁) (hA' : ∀ τ, (A' τ).det ≠ 0) :
    A'' * (A'.map ψ')⁻¹ * (A' * (A.map ψ)⁻¹).map ψ' = A'' * (A.map (ψ'.comp ψ))⁻¹ := by
  rw [Mat.map_mul, Mat.map_inv, mul_assoc, ← mul_assoc (A'.map ψ')⁻¹,
    Mat.inv_mul (fun τ => by rw [Mat.det_map]; exact (map_ne_zero ψ').2 (hA' τ)), one_mul]
  congr 2

def valAt {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) {K : Type} [Field K]
    (q : Sp K ⟶ M.Z) : (M.O (q (IsLocalRing.closedPoint K))).toSubring →+* K :=
  RatModel.valHom q _ (RatModel.range_eq_singleton q (IsLocalRing.closedPoint K))

theorem valAt_apply {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) {K : Type} [Field K]
    (q : Sp K ⟶ M.Z) (x : (M.O (q (IsLocalRing.closedPoint K))).toSubring) : M.val q x = valAt M q x := rfl

end GlobalTheory.FlagBundle

namespace GlobalTheory.FlagBundle

variable {ι : Type} {m : ι → ℕ} {F : Type} [Field F] {Ω Ω' Ω'' : Type} [Field Ω] [Algebra F Ω] [Field Ω']
  [Algebra F Ω'] [Field Ω''] [Algebra F Ω'']

theorem val_chain {M' : RatModel F Ω'} {M'' : RatModel F Ω''} {φ : Ω →ₐ[F] Ω'}
    {φ' : Ω' →ₐ[F] Ω''} {f' : M''.Z ⟶ M'.Z} (hf' : M'.IsHom M'' φ' f') {K : Type} [Field K] (q : Sp K ⟶ M''.Z)
    {k k' : ι → ℕ} {A'' : Mat m Ω''} {A' : Mat m Ω'} {A : Mat m Ω} (hA' : ∀ τ, (A' τ).det ≠ 0)
    (h2 : Par k' (M''.O (q (IsLocalRing.closedPoint K))).toSubring (A'' * (A'.map φ')⁻¹))
    (h1 : Par k (M'.O (f' (q (IsLocalRing.closedPoint K)))).toSubring (A' * (A.map φ)⁻¹)) :
    (A'' * (A.map (φ'.comp φ))⁻¹).map (M''.val q) =
      (A'' * (A'.map φ')⁻¹).map (M''.val q) * (A' * (A.map φ)⁻¹).map (M'.val (q ≫ f')) := by
  have h1' : Par k (M''.O (q (IsLocalRing.closedPoint K))).toSubring ((A' * (A.map φ)⁻¹).map φ') :=
    h1.map (φ' : Ω' →+* Ω'') fun x hx => hf'.map_mem_O hx
  have e := mat_chain (φ : Ω →+* Ω') (φ' : Ω' →+* Ω'') A'' A' A hA'
  have e2 : (A'' * (A.map (φ'.comp φ))⁻¹) = A'' * (A'.map φ')⁻¹ * (A' * (A.map φ)⁻¹).map φ' := e.symm
  rw [e2, Par.map_mul_of h2 h1' (M''.val q) (valAt M'' q) (valAt_apply M'' q)]
  congr 1
  funext τ
  ext i j
  show M''.val q (φ' ((A' * (A.map φ)⁻¹) τ i j)) = M'.val (q ≫ f') ((A' * (A.map φ)⁻¹) τ i j)
  exact (hf'.val_comp q (IsLocalRing.closedPoint K) ((h1 τ).1 i j)).symm

theorem Refines.comp {M : RatModel F Ω} {M' : RatModel F Ω'} {M'' : RatModel F Ω''} {φ : Ω →ₐ[F] Ω'}
    {f : M'.Z ⟶ M.Z} {φ' : Ω' →ₐ[F] Ω''} {f' : M''.Z ⟶ M'.Z} {k k' k'' : ι → ℕ} {S : Fr M m k}
    {S' : Fr M' m k'} {S'' : Fr M'' m k''} (h1 : Refines S S' φ f) (h2 : Refines S' S'' φ' f') :
    Refines S S'' (φ'.comp φ) (f' ≫ f) := {
  le := le_trans h1.le h2.le
  hom := h1.hom.comp h2.hom
  sub z'' A'' hA'' A hA := by
    obtain ⟨A', hA'⟩ := S'.nonempty (f' z'')
    have e : A'' * (A.map (φ'.comp φ))⁻¹ = A'' * (A'.map φ')⁻¹ * (A' * (A.map φ)⁻¹).map φ' :=
      (mat_chain (φ : Ω →+* Ω') (φ' : Ω' →+* Ω'') A'' A' A (Fr.det_ne hA')).symm
    rw [e]
    exact ((h2.sub z'' A'' hA'' A' hA').mono h1.le le_rfl).mul
      ((h1.sub (f' z'') A' hA' A hA).map (φ' : Ω' →+* Ω'') fun x hx => h2.hom.map_mem_O hx)
  rad z'' g hg := h2.rad z'' (φ g) (h1.rad (f' z'') g hg)
  lifts K _ x A hA h hh := by
    obtain ⟨p', ⟨hp'x, A', hA', hP'⟩, hu1⟩ := h1.lifts K x A hA h hh
    obtain ⟨p'', ⟨hp'', A'', hA'', hP''⟩, hu2⟩ :=
      h2.lifts K p' A' hA' (h * ((A' * (A.map φ)⁻¹).map (M'.val p'))⁻¹) hP'
    have hAx : A ∈ S.S (f (p' (IsLocalRing.closedPoint K))) := by
      have h0 := hA; rw [← hp'x] at h0; exact h0
    have fac : ∀ q : Sp K ⟶ M''.Z, q ≫ f' = p' → ∀ B'' ∈ S''.S (q (IsLocalRing.closedPoint K)),
        (B'' * (A.map (φ'.comp φ))⁻¹).map (M''.val q) =
          (B'' * (A'.map φ')⁻¹).map (M''.val q) * (A' * (A.map φ)⁻¹).map (M'.val p') := by
      intro q hq B'' hB''
      have hq' : p' (IsLocalRing.closedPoint K) = f' (q (IsLocalRing.closedPoint K)) := by
        rw [← hq]; rfl
      have hA'q : A' ∈ S'.S (f' (q (IsLocalRing.closedPoint K))) := by rw [← hq']; exact hA'
      have hAq : A ∈ S.S (f (f' (q (IsLocalRing.closedPoint K)))) := by rw [← hq']; exact hAx
      rw [val_chain h2.hom q (Fr.det_ne hA') (h2.sub _ B'' hB'' A' hA'q) (h1.sub _ A' hA'q A hAq), hq]
    refine ⟨p'', ⟨by rw [← Category.assoc, hp'', hp'x], A'', hA'', ?_⟩, ?_⟩
    · rw [fac p'' hp'' A'' hA'', Mat.mul_inv_rev, ← mul_assoc]
      exact hP''
    · rintro q ⟨hqx, B'', hB'', hPq⟩
      have hq1 : q ≫ f' = p' := by
        refine hu1 (q ≫ f') ⟨by rw [Category.assoc, hqx], ?_⟩
        obtain ⟨A₁, hA₁⟩ := S'.nonempty ((q ≫ f') (IsLocalRing.closedPoint K))
        refine ⟨A₁, hA₁, ?_⟩
        have hA₁' : A₁ ∈ S'.S (f' (q (IsLocalRing.closedPoint K))) := hA₁
        have hAq : A ∈ S.S (f (f' (q (IsLocalRing.closedPoint K)))) := by
          have h0 := hA; rw [← hqx] at h0; exact h0
        have h2s := h2.sub _ B'' hB'' A₁ hA₁'
        rw [val_chain h2.hom q (Fr.det_ne hA₁') h2s (h1.sub _ A₁ hA₁' A hAq)] at hPq
        have hG : Par k' ⊤ ((B'' * (A₁.map φ')⁻¹).map (M''.val q)) :=
          h2s.map_of _ (valAt M'' q) (valAt_apply M'' q)
        have e : h * ((A₁ * (A.map φ)⁻¹).map (M'.val (q ≫ f')))⁻¹ =
            h * ((B'' * (A₁.map φ')⁻¹).map (M''.val q) * (A₁ * (A.map φ)⁻¹).map (M'.val (q ≫ f')))⁻¹ *
              (B'' * (A₁.map φ')⁻¹).map (M''.val q) := by
          rw [Mat.mul_inv_rev, mul_assoc, mul_assoc, Mat.inv_mul hG.det_ne, mul_one]
        rw [e]
        exact (hPq.mono h2.le le_rfl).mul hG
      refine hu2 q ⟨hq1, B'', hB'', ?_⟩
      rw [fac q hq1 B'' hB'', Mat.mul_inv_rev, ← mul_assoc] at hPq
      exact hPq }

end GlobalTheory.FlagBundle

theorem GlobalTheory.FlagBundle.refines_comp : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (Ω'' : Type) [Field Ω''] [Algebra F Ω''] (M'' : RatModel F Ω'') (φ' : Ω' →ₐ[F] Ω'') (f' : M''.Z ⟶ M'.Z) (ι : Type) (m k k' k'' : ι → ℕ) (S : Fr M m k) (S' : Fr M' m k') (S'' : Fr M'' m k''), Refines S S' φ f → Refines S' S'' φ' f' → Refines S S'' (φ'.comp φ) (f' ≫ f) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 => h1.comp h2
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical

theorem _root_.GlobalTheory.T.heckeChar_finiteOrder_of_trivial_at_infinity : ∀ (L : Type) [Field L] [NumberField L] (χ : _root_.Formalism.L2.Host.HChar L), (∀ k, χ.inf k = 1) → ∃ n : ℕ, 0 < n ∧ χ.OrderDvd n := by
  first | exact @GlobalTheory.Mem.FinOrder.finite_order_of_inf_eq_one | exact GlobalTheory.Mem.FinOrder.finite_order_of_inf_eq_one | (intros; apply GlobalTheory.Mem.FinOrder.finite_order_of_inf_eq_one <;> assumption)
end
