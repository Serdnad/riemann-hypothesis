module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

@[expose] public section

section

noncomputable section

namespace GlobalTheory.MonoConj

def dualRep {Γ k : Type} [Group Γ] [CommRing k] {a : ℕ} (r : Γ →* GL (Fin a) k) : Γ →* GL (Fin a) k where
  toFun g := ⟨((r g⁻¹ : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).transpose,
    ((r g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).transpose, by
      rw [← Matrix.transpose_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
        Matrix.transpose_one], by
      rw [← Matrix.transpose_mul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
        Matrix.transpose_one]⟩
  map_one' := by
    apply Units.ext
    simp
  map_mul' g h := by
    apply Units.ext
    simp [mul_inv_rev, Matrix.transpose_mul]

theorem coe_dualRep {Γ k : Type} [Group Γ] [CommRing k] {a : ℕ} (r : Γ →* GL (Fin a) k) (g : Γ) :
    ((dualRep r g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) =
      ((r g⁻¹ : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).transpose := rfl

end GlobalTheory.MonoConj

end
end

section

noncomputable section

namespace GlobalTheory.PMon

variable {F G ι : Type} [Field F] [Group G] [Fintype ι] [DecidableEq ι]

def repOf (ρ₀ : G →* GL ι F) : Representation F G (ι → F) where
  toFun g := Matrix.toLin' (ρ₀ g : Matrix ι ι F)
  map_one' := by simp; rfl
  map_mul' g h := by simp [Matrix.toLin'_mul]; rfl

@[simp] theorem repOf_apply (ρ₀ : G →* GL ι F) (g : G) (v : ι → F) :
    repOf ρ₀ g v = (ρ₀ g : Matrix ι ι F).mulVec v := rfl

theorem toMatrix_repOf (ρ₀ : G →* GL ι F) (g : G) :
    LinearMap.toMatrix (Pi.basisFun F ι) (Pi.basisFun F ι) (repOf ρ₀ g) = (ρ₀ g : Matrix ι ι F) := by
  rw [LinearMap.toMatrix_eq_toMatrix']
  exact LinearMap.toMatrix'_toLin' _

end GlobalTheory.PMon

end
end

section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem gl_factor_fromBlocks_mod_uniformizer : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ (g : GL (Fin r) (IsLocalRing.ResidueField O)) (L : Matrix (Fin r) (Fin r) O), L.map (IsLocalRing.residue O) = (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)) → ∀ (B : Matrix (Fin r) (Fin t) O) (q : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O), (∀ i j, IsLocalRing.residue O (q i j) = IsLocalRing.residue O (Matrix.fromBlocks L B 0 (1 : Matrix (Fin t) (Fin t) O) i j)) → ∃ h : GL (Fin r ⊕ Fin t) O, (∀ i j, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inl i) (Sum.inl j) - (1 : Matrix (Fin r) (Fin r) O) i j ∈ Ideal.span {ϖ}) ∧ (∀ i j, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inr i) (Sum.inl j) ∈ Ideal.span {ϖ}) ∧ (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) * Matrix.fromBlocks L 0 0 (1 : Matrix (Fin t) (Fin t) O) = q := by
  intro O _ _ _ r t ϖ hϖ g L hL B q hq
  classical
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hmem : ∀ x : O, IsLocalRing.residue O x = 0 → x ∈ Ideal.span {ϖ} := fun x hx =>
    hmax ▸ (IsLocalRing.residue_eq_zero_iff x).mp hx
  have hg : IsUnit (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
  have hLdet : IsLocalRing.residue O L.det = (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hL]
  have hLu : IsUnit L.det :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).mp (by rw [hLdet]; exact hg.ne_zero)
  set D : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O := Matrix.fromBlocks L 0 0 1 with hDdef
  have hDu : IsUnit D.det := by
    rw [hDdef, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]; exact hLu
  have hqmap : q.map (IsLocalRing.residue O) =
      (Matrix.fromBlocks L B 0 (1 : Matrix (Fin t) (Fin t) O)).map (IsLocalRing.residue O) := by
    ext i j; exact hq i j
  have hqu : IsUnit q.det := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hqmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one, hLdet]
    exact hg.ne_zero
  have hHu : IsUnit (q * D⁻¹).det := by
    rw [Matrix.det_mul]; exact hqu.mul (Matrix.isUnit_nonsing_inv_det D hDu)
  have hHD : q * D⁻¹ * D = q := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hDu, Matrix.mul_one]
  have hMD : (q * D⁻¹).map (IsLocalRing.residue O) * D.map (IsLocalRing.residue O) =
      q.map (IsLocalRing.residue O) := by
    rw [← Matrix.map_mul, hHD]
  rw [hqmap, ← Matrix.fromBlocks_toBlocks ((q * D⁻¹).map (IsLocalRing.residue O)), hDdef,
    Matrix.fromBlocks_map, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at hMD
  obtain ⟨h11, -, h21, -⟩ := hMD
  simp only [Matrix.map_zero _ (map_zero _), Matrix.mul_zero, add_zero, hL] at h11 h21
  have e11 : ((q * D⁻¹).map (IsLocalRing.residue O)).toBlocks₁₁ = 1 := by
    have := congrArg (· * ((g⁻¹ : GL (Fin r) (IsLocalRing.ResidueField O)) : Matrix (Fin r) (Fin r) _)) h11
    simpa [Matrix.mul_assoc] using this
  have e21 : ((q * D⁻¹).map (IsLocalRing.residue O)).toBlocks₂₁ = 0 := by
    have hgg : (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)) *
        ((g⁻¹ : GL (Fin r) (IsLocalRing.ResidueField O)) : Matrix (Fin r) (Fin r) _) = 1 := Units.mul_inv g
    rw [hDdef, ← Matrix.mul_one (Matrix.toBlocks₂₁ _), ← hgg, ← Matrix.mul_assoc, h21, Matrix.zero_mul]
  refine ⟨Matrix.nonsingInvUnit (q * D⁻¹) hHu, ?_, ?_, hHD⟩
  · intro i j
    apply hmem
    have := congrFun (congrFun e11 i) j
    simp only [Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.map_apply] at this
    show IsLocalRing.residue O ((q * D⁻¹) (Sum.inl i) (Sum.inl j) - (1 : Matrix (Fin r) (Fin r) O) i j) = 0
    rw [map_sub, this]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  · intro i j
    show (q * D⁻¹) (Sum.inr i) (Sum.inl j) ∈ Ideal.span {ϖ}
    apply hmem
    have := congrFun (congrFun e21 i) j
    simpa [Matrix.toBlocks₂₁] using this

end GlobalTheory
end

section

open scoped BigOperators

namespace GlobalTheory


open Matrix in
theorem det_ne_zero_of_intertwines_of_span_eq_top {k : Type} [Field k] {G : Type} {r : ℕ}
    (M N : G → Matrix (Fin r) (Fin r) k) (hM : Submodule.span k (Set.range M) = ⊤)
    (B : Matrix (Fin r) (Fin r) k) (i j : Fin r) (hB : B i j ≠ 0)
    (h : ∀ g, N g * B = B * M g) : B.det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hall : ∀ X : Matrix (Fin r) (Fin r) k, ∃ Y, Y * B = B * X := by
    intro X
    have hle : Submodule.span k (Set.range M) ≤
        (LinearMap.range (LinearMap.mulRight k B)).comap (LinearMap.mulLeft k B) := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mem_range]
      exact ⟨N g, by simp [h g]⟩
    have hX := hle (hM ▸ Submodule.mem_top : X ∈ Submodule.span k (Set.range M))
    rw [Submodule.mem_comap, LinearMap.mem_range] at hX
    obtain ⟨Y, hY⟩ := hX
    exact ⟨Y, by simpa using hY⟩
  obtain ⟨c, hc⟩ : ∃ c, v c ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hv0 (funext hne)
  let X : Matrix (Fin r) (Fin r) k :=
    Matrix.of fun a b => if a = j then (if b = c then (v c)⁻¹ else 0) else 0
  have hXv : X *ᵥ v = Pi.single j 1 := by
    ext a
    by_cases ha : a = j
    · subst ha
      simp [X, Matrix.mulVec, dotProduct, hc]
    · simp [X, Matrix.mulVec, dotProduct, ha]
  obtain ⟨Y, hY⟩ := hall X
  have key : B *ᵥ (X *ᵥ v) = 0 := by
    rw [Matrix.mulVec_mulVec, ← hY, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  have hi := congrFun key i
  rw [hXv] at hi
  simp [Matrix.mulVec, dotProduct, Pi.single_apply] at hi
  exact hB hi

theorem exists_gl_intertwiner_of_residual_span_eq_top :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (G : Type) [Group G] (r : ℕ) (ρ ρ' : G →* Matrix.GeneralLinearGroup (Fin r) O), Submodule.span (IsLocalRing.ResidueField O) (Set.range fun g => (ρ g : Matrix (Fin r) (Fin r) O).map (IsLocalRing.residue O)) = ⊤ → (∃ A : Matrix (Fin r) (Fin r) O, A.det ≠ 0 ∧ ∀ g, (ρ' g : Matrix (Fin r) (Fin r) O) * A = A * ρ g) → ∃ U : Matrix.GeneralLinearGroup (Fin r) O, ∀ g, ρ' g * U = U * ρ g := by
  classical
  intro O _ _ _ G _ r ρ ρ' hspan ⟨A, hdet, hA⟩
  by_cases hr : r = 0
  · subst hr
    exact ⟨1, fun g => Units.ext (Matrix.ext fun a _ => a.elim0)⟩
  have : Nonempty (Fin r) := ⟨⟨0, Nat.pos_of_ne_zero hr⟩⟩
  obtain ⟨p, -, hp⟩ := Finset.exists_min_image Finset.univ
    (fun q : Fin r × Fin r => IsDiscreteValuationRing.addVal O (A q.1 q.2)) Finset.univ_nonempty
  have hdvd : ∀ x y, A p.1 p.2 ∣ A x y := fun x y =>
    IsDiscreteValuationRing.addVal_le_iff_dvd.mp (hp (x, y) (Finset.mem_univ _))
  have hd : A p.1 p.2 ≠ 0 := by
    intro h0
    apply hdet
    have hA0 : A = 0 := by
      ext x y
      have hxy := hdvd x y
      rw [h0, zero_dvd_iff] at hxy
      simpa using hxy
    rw [hA0, Matrix.det_zero]
  choose C hC using hdvd
  generalize hdd : A p.1 p.2 = d at hC hd
  have hC1 : C p.1 p.2 = 1 :=
    mul_left_cancel₀ hd (((hC p.1 p.2).symm.trans hdd).trans (mul_one d).symm)
  have hAeq : A = d • Matrix.of C := by
    ext x y
    rw [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ← hC]
  have hint : ∀ g, (ρ' g : Matrix (Fin r) (Fin r) O) * Matrix.of C =
      Matrix.of C * (ρ g : Matrix (Fin r) (Fin r) O) := by
    intro g
    have h1 := hA g
    rw [hAeq, Matrix.mul_smul, Matrix.smul_mul] at h1
    ext x y
    have hxy := congrFun (congrFun h1 x) y
    rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul] at hxy
    exact mul_left_cancel₀ hd hxy
  have hB : (Matrix.of C).map (IsLocalRing.residue O) p.1 p.2 ≠ 0 := by
    rw [Matrix.map_apply, Matrix.of_apply, hC1, map_one]
    exact one_ne_zero
  have hdet' := det_ne_zero_of_intertwines_of_span_eq_top
    (fun g => (ρ g : Matrix (Fin r) (Fin r) O).map (IsLocalRing.residue O))
    (fun g => (ρ' g : Matrix (Fin r) (Fin r) O).map (IsLocalRing.residue O)) hspan
    ((Matrix.of C).map (IsLocalRing.residue O)) p.1 p.2 hB
    (fun g => by rw [← Matrix.map_mul, ← Matrix.map_mul, hint g])
  have hunit : IsUnit (Matrix.of C).det := by
    by_contra hu
    apply hdet'
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hu)
  refine ⟨((Matrix.isUnit_iff_isUnit_det _).mpr hunit).unit, fun g => ?_⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, IsUnit.unit_spec, hint g]

end GlobalTheory
end

section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators Matrix

namespace GlobalTheory

theorem exists_det_add_mul_one_sub_mul_ne_zero {k : Type*} [Field k] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) k) :
    ∃ T : Matrix (Fin n) (Fin n) k, (A + T * (1 - B * A)).det ≠ 0 := by
  classical
  set LA := Matrix.toLin' A with hLA
  set K := LinearMap.ker LA
  obtain ⟨U, hU⟩ := Submodule.exists_isCompl (LinearMap.range LA)
  obtain ⟨K', hK'⟩ := Submodule.exists_isCompl K
  have h1 : Module.finrank k (LinearMap.range LA) + Module.finrank k K = Module.finrank k (Fin n → k) :=
    LinearMap.finrank_range_add_finrank_ker LA
  have h2 := Submodule.finrank_add_eq_of_isCompl hU
  have hdim : Module.finrank k K = Module.finrank k U := by omega
  let e : K ≃ₗ[k] U := LinearEquiv.ofFinrankEq K U hdim
  let f : (Fin n → k) →ₗ[k] (Fin n → k) :=
    U.subtype ∘ₗ (e : K →ₗ[k] U) ∘ₗ Submodule.linearProjOfIsCompl K K' hK'
  refine ⟨LinearMap.toMatrix' f, ?_⟩
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv0
  have hfw : ∀ w, LinearMap.toMatrix' f *ᵥ w = f w := by
    intro w
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  have hfU : ∀ w, f w ∈ U := fun w => (e _).2
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hfw] at hv
  have hAv : A *ᵥ v = 0 := by
    have hr : A *ᵥ v ∈ LinearMap.range LA := ⟨v, by rw [hLA, Matrix.toLin'_apply]⟩
    have hu : A *ᵥ v ∈ U := by
      rw [eq_neg_of_add_eq_zero_left hv]
      exact U.neg_mem (hfU _)
    exact (Submodule.disjoint_def.mp hU.disjoint) _ hr hu
  rw [hAv, zero_add, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hAv,
    Matrix.mulVec_zero, sub_zero] at hv
  have hvK : v ∈ K := by
    show LA v = 0
    rw [hLA, Matrix.toLin'_apply, hAv]
  have hp : Submodule.linearProjOfIsCompl K K' hK' v = ⟨v, hvK⟩ :=
    Submodule.linearProjOfIsCompl_apply_left hK' ⟨v, hvK⟩
  have he : e ⟨v, hvK⟩ = 0 := by
    apply Subtype.ext
    have : f v = 0 := hv
    change U.subtype ((e : K →ₗ[k] U) ⟨v, hvK⟩) = 0
    simpa only [f, LinearMap.comp_apply, hp] using this
  have he' : e ⟨v, hvK⟩ = e 0 := by
    exact he.trans (map_zero (e : K →ₗ[k] U)).symm
  have : (⟨v, hvK⟩ : K) = 0 := e.injective he'
  simpa using congrArg Subtype.val this

theorem exists_GL_of_span_range_eq : ∀ (O M : Type) [CommRing O] [IsLocalRing O] [AddCommGroup M]
    [Module O M] (n : ℕ) (x y : Fin n → M),
    Submodule.span O (Set.range x) = Submodule.span O (Set.range y) →
    ∃ h : GL (Fin n) O, ∀ i, y i = ∑ j, (h : Matrix (Fin n) (Fin n) O) i j • x j := by
  intro O M _ _ _ _ n x y hspan
  classical
  have hA : ∀ i, ∃ c : Fin n → O, ∑ j, c j • x j = y i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun O).mp (hspan ▸ Submodule.subset_span ⟨i, rfl⟩)
  have hB : ∀ i, ∃ c : Fin n → O, ∑ j, c j • y j = x i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun O).mp (hspan.symm ▸ Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin n) (Fin n) O, ∀ i, ∑ j, A i j • x j = y i :=
    ⟨fun i => (hA i).choose, fun i => (hA i).choose_spec⟩
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin n) (Fin n) O, ∀ i, ∑ j, B i j • y j = x i :=
    ⟨fun i => (hB i).choose, fun i => (hB i).choose_spec⟩
  have hmul : ∀ (P Q : Matrix (Fin n) (Fin n) O) (z : Fin n → M) i,
      ∑ j, (P * Q) i j • z j = ∑ l, P i l • ∑ j, Q l j • z j := by
    intro P Q z i
    simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
    exact Finset.sum_comm
  have hC : ∀ l, ∑ j, ((1 : Matrix (Fin n) (Fin n) O) - B * A) l j • x j = 0 := by
    intro l
    simp only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib, hmul, hA, hB]
    simp [Matrix.one_apply]
  let r := IsLocalRing.residue O
  obtain ⟨Tb, hTb⟩ := exists_det_add_mul_one_sub_mul_ne_zero (r.mapMatrix A) (r.mapMatrix B)
  obtain ⟨s, hs⟩ : ∃ s : IsLocalRing.ResidueField O → O, ∀ a, r (s a) = a :=
    ⟨Function.surjInv IsLocalRing.residue_surjective, Function.surjInv_eq _⟩
  let T : Matrix (Fin n) (Fin n) O := Tb.map s
  have hT : r.mapMatrix T = Tb := by ext i j; simp [T, hs]
  let H : Matrix (Fin n) (Fin n) O := A + T * (1 - B * A)
  have hdet : IsUnit H.det := by
    have hne : r H.det ≠ 0 := by
      rw [RingHom.map_det]
      simp only [H, map_add (f := _), map_mul, map_sub, map_one, hT]
      exact hTb
    by_contra hnu
    exact hne ((IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hnu))
  have hHu : IsUnit H := (Matrix.isUnit_iff_isUnit_det H).mpr hdet
  refine ⟨hHu.unit, fun i => ?_⟩
  rw [IsUnit.unit_spec]
  simp only [H, Matrix.add_apply, add_smul, Finset.sum_add_distrib, hA, hmul, hC, smul_zero,
    Finset.sum_const_zero, add_zero]

end GlobalTheory
end

section

open Polynomial

namespace GlobalTheory

theorem antidiag_twisted_norm : ∀ (E : Type) [Field E] (c : E ≃+* E), (∀ x, c (c x) = x) → ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) E), Φ = Matrix.of (fun i j : Fin a => if j = i.rev then (-1 : E) ^ (i : ℕ) else 0) → Φ.transpose = (-1 : E) ^ (a - 1) • Φ ∧ IsUnit Φ.det ∧ ∀ δ : Matrix (Fin a) (Fin a) E, IsUnit δ.det → δ * (Φ * ((δ.map c).transpose)⁻¹ * Φ⁻¹) = (-1 : E) ^ (a - 1) • ((δ * Φ) * (((δ * Φ).map c).transpose)⁻¹) ∧ Φ * (((Φ * ((δ.map c).transpose)⁻¹ * Φ⁻¹).map c).transpose)⁻¹ * Φ⁻¹ = δ := by
  intro E _ c hc a Φ hΦ
  have hpm : ∀ n : ℕ, (-1 : E) ^ n * (-1 : E) ^ n = 1 := by
    intro n; rw [← mul_pow]; simp
  have hss : (-1 : E) ^ (a - 1) * (-1 : E) ^ (a - 1) = 1 := hpm _
  have hsign : ∀ i : Fin a, (-1 : E) ^ (i.rev : ℕ) = (-1 : E) ^ (a - 1) * (-1 : E) ^ (i : ℕ) := by
    intro i
    have hi := i.isLt
    rw [Fin.val_rev, ← pow_add]
    have : a - 1 + (i:ℕ) = (a - ((i:ℕ) + 1)) + 2 * (i:ℕ) := by omega
    rw [this, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
  have hT : Φ.transpose = (-1 : E) ^ (a - 1) • Φ := by
    subst hΦ
    ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    by_cases h : j = i.rev
    · subst h
      simp only [Fin.rev_rev, if_true]
      exact hsign i
    · have h' : ¬ i = j.rev := by
        intro h2; apply h; rw [h2, Fin.rev_rev]
      simp [h, h']
  have hsq : Φ * Φ = (-1 : E) ^ (a - 1) • (1 : Matrix (Fin a) (Fin a) E) := by
    subst hΦ
    ext i k
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i.rev]
    · by_cases h : k = i
      · subst h
        simp only [Fin.rev_rev, if_true, hsign]
        rw [mul_one, mul_left_comm, hpm, mul_one]
      · have : ¬ k = i.rev.rev := by rwa [Fin.rev_rev]
        simp [this, h, Ne.symm h]
    · intro j _ hj; simp [hj]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hright : Φ * Φ.transpose = 1 := by
    rw [hT, Matrix.mul_smul, hsq, smul_smul, hss, one_smul]
  have hleft : Φ.transpose * Φ = 1 := by
    rw [hT, Matrix.smul_mul, hsq, smul_smul, hss, one_smul]
  have hinv : Φ⁻¹ = Φ.transpose := Matrix.inv_eq_left_inv hleft
  have hTinv : (Φ.transpose)⁻¹ = Φ := Matrix.inv_eq_left_inv hright
  have hdet : IsUnit Φ.det := Matrix.isUnit_det_of_left_inverse hleft
  have hΦc : Φ.map c = Φ := by
    subst hΦ
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp
  have hmapmul : ∀ A B : Matrix (Fin a) (Fin a) E, (A * B).map c = A.map c * B.map c :=
    fun A B => Matrix.map_mul (f := (c : E →+* E))
  have hmapinv : ∀ A : Matrix (Fin a) (Fin a) E, IsUnit A.det → (A⁻¹).map c = (A.map c)⁻¹ := by
    intro A hA
    refine (Matrix.inv_eq_left_inv ?_).symm
    rw [← hmapmul, Matrix.nonsing_inv_mul _ hA, Matrix.map_one _ c.map_zero c.map_one]
  have hcc : ∀ A : Matrix (Fin a) (Fin a) E, (A.map c).map c = A := by
    intro A; ext i j; simp [hc]
  refine ⟨hT, hdet, fun δ hδ => ⟨?_, ?_⟩⟩
  · rw [hmapmul, hΦc, Matrix.transpose_mul, Matrix.mul_inv_rev, hTinv, hinv, hT]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  · have hYd : IsUnit ((δ.map c).transpose).det := by
      rw [Matrix.det_transpose]
      have h1 := RingHom.map_det (c : E →+* E) δ
      rw [RingHom.mapMatrix_apply] at h1
      have h2 : (δ.map c).det = c δ.det := h1.symm
      rw [h2]; exact hδ.map c
    have hΦTc : (Φ.transpose).map c = Φ.transpose := by rw [Matrix.transpose_map, hΦc]
    rw [hinv, hmapmul, hmapmul, hΦc, hΦTc, hmapinv _ hYd,
      Matrix.transpose_map, hcc, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_nonsing_inv, Matrix.transpose_transpose,
      Matrix.mul_inv_rev, Matrix.mul_inv_rev, hTinv, Matrix.nonsing_inv_nonsing_inv _ hδ, hinv]
    have e : Φ * (Φ * δ * Φ.transpose) * Φ.transpose = (Φ * Φ) * δ * (Φ.transpose * Φ.transpose) := by
      simp only [Matrix.mul_assoc]
    rw [e, ← Matrix.transpose_mul, hsq, Matrix.transpose_smul, Matrix.transpose_one,
      Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, hss, one_smul]

end GlobalTheory
end
