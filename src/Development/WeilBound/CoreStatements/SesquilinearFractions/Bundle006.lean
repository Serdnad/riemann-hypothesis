module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle011
public import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.PiTensorProduct
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf

private theorem pt_zero_lemma {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] {x : Sp R ⟶ S}
    {U : Type} [AddCommGroup U] [Module R U] (M : LieModel G x U) : M.pt 0 = 1 := by
  have h := M.add 0 0
  rw [add_zero] at h
  exact mul_eq_left.mp h.symm

private theorem LieModel_pt_sum_eq_prod {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] {x : Sp R ⟶ S}
    {U : Type} [AddCommGroup U] [Module R U] (M : LieModel G x U) :
    ∀ (n : ℕ) (v : Fin n → U), M.pt (∑ k, v k) = (List.ofFn fun k => M.pt (v k)).prod := by
  intro n
  induction n with
  | zero => intro v; simp [pt_zero_lemma M]
  | succ n ih =>
    intro v
    rw [Fin.sum_univ_succ, M.add, ih, List.ofFn_succ, List.prod_cons]

private theorem isComb_pt_iff_eq_pt_sum {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] {x : Sp R ⟶ S}
    {U : Type} [AddCommGroup U] [Module R U] (M : LieModel G x U) (n : ℕ) (c : Fin n → R) (u : Fin n → U)
    (w : epsAt x ⟶ G) :
    GlobalTheory.CompanionTheory.Ar.Fl.IsComb c (fun k => M.pt (u k)) w ↔ w = M.pt (∑ k, c k • u k) := by
  unfold GlobalTheory.CompanionTheory.Ar.Fl.IsComb
  rw [LieModel_pt_sum_eq_prod M]
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hv' : v = fun i => M.pt (c i • u i) := by
      funext i
      apply Over.OverMorphism.ext
      rw [hv i, M.smul]
    rw [hv']
  · intro h
    refine ⟨fun i => M.pt (c i • u i), fun i => ?_, h⟩
    rw [M.smul]

private theorem isEigVec_pt_iff_mem_eigSp {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] {x : Sp R ⟶ S}
    {U : Type} [AddCommGroup U] [Module R U] (M : LieModel G x U) {O : Type} [CommRing O] (act : OAct O G)
    (ρ : O →+* Module.End R U) (τ : O →+* R) (hM : M.IsActOf act.act ρ) (u : U) :
    GlobalTheory.CompanionTheory.Ar.Fl.IsEigVec act x τ (M.pt u) ↔ u ∈ eigSp ρ τ := by
  unfold GlobalTheory.CompanionTheory.Ar.Fl.IsEigVec eigSp
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]
  constructor
  · rintro ⟨-, h⟩ a
    apply M.inj
    apply Over.OverMorphism.ext
    rw [hM a u, M.smul, h a]
  · intro h
    refine ⟨M.tan u, fun a => ?_⟩
    rw [← hM a u, h a, M.smul]

theorem lie_model_eigenvectors_action : ∀ (S : Scheme.{0}) (R : Type) [CommRing R] (G : Over S) [GrpObj G] (x : Sp R ⟶ S) (U : Type) [AddCommGroup U] [Module R U] (M : LieModel G x U), (∀ (n : ℕ) (c : Fin n → R) (u : Fin n → U) w, IsComb c (fun k => M.pt (u k)) w ↔ w = M.pt (∑ k, c k • u k)) ∧ ∀ (O : Type) [CommRing O] (act : OAct O G) (ρ : O →+* Module.End R U) (τ : O →+* R), M.IsActOf act.act ρ → (∀ u, IsEigVec act x τ (M.pt u) ↔ u ∈ eigSp ρ τ) ∧ ∀ (n : ℕ) (u : Fin n → U), IsEigFrame act x τ (fun k => M.pt (u k)) ↔ LinearIndependent R u ∧ Submodule.span R (Set.range u) = eigSp ρ τ := by
  intro S R _ G _ x U _ _ M
  refine ⟨fun n c u w => isComb_pt_iff_eq_pt_sum M n c u w, fun O _ act ρ τ hM => ⟨fun u => isEigVec_pt_iff_mem_eigSp M act ρ τ hM u, fun n u => ?_⟩⟩
  unfold GlobalTheory.CompanionTheory.Ar.Fl.IsEigFrame
  constructor
  · rintro ⟨hu, huniq⟩
    have hu' : ∀ i, u i ∈ eigSp ρ τ := fun i => (isEigVec_pt_iff_mem_eigSp M act ρ τ hM (u i)).mp (hu i)
    have hex : ∀ e ∈ eigSp ρ τ, ∃! c : Fin n → R, e = ∑ k, c k • u k := by
      intro e he
      obtain ⟨c, hc, huq⟩ := huniq (M.pt e) ((isEigVec_pt_iff_mem_eigSp M act ρ τ hM e).mpr he)
      exact ⟨c, M.inj ((isComb_pt_iff_eq_pt_sum M n c u _).mp hc),
        fun c' hc' => huq c' ((isComb_pt_iff_eq_pt_sum M n c' u _).mpr (congrArg M.pt hc'))⟩
    refine ⟨?_, ?_⟩
    · rw [Fintype.linearIndependent_iff]
      intro g hg i
      obtain ⟨c, -, huq⟩ := hex 0 (Submodule.zero_mem _)
      have hg0 : g = 0 := (huq g hg.symm).trans (huq 0 (by simp)).symm
      rw [hg0]
      rfl
    · apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact hu' i
      · intro e he
        obtain ⟨c, hc, -⟩ := hex e he
        rw [hc]
        exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rintro ⟨hli, hsp⟩
    have hu' : ∀ i, u i ∈ eigSp ρ τ := fun i => hsp ▸ Submodule.subset_span ⟨i, rfl⟩
    refine ⟨fun i => (isEigVec_pt_iff_mem_eigSp M act ρ τ hM (u i)).mpr (hu' i), fun w hw => ?_⟩
    have ht : IsTanAt G x w := by
      obtain ⟨h, -⟩ := hw
      exact h
    obtain ⟨e, rfl⟩ := M.onto w ht
    have he : e ∈ eigSp ρ τ := (isEigVec_pt_iff_mem_eigSp M act ρ τ hM e).mp hw
    rw [← hsp] at he
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp he
    refine ⟨c, (isComb_pt_iff_eq_pt_sum M n c u _).mpr (congrArg M.pt hc.symm), fun c' hc' => ?_⟩
    have h1 : e = ∑ k, c' k • u k := M.inj ((isComb_pt_iff_eq_pt_sum M n c' u _).mp hc')
    have h2 : ∑ k, (c' k - c k) • u k = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← h1, hc, sub_self]
    funext k
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h2 k)

end PositivityTheory.Xgf
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf.HermitianFormSum

variable {S : Scheme.{0}}

theorem one_left (G : Over S) [GrpObj G] (Y : Over S) : (1 : Y ⟶ G).left = Y.hom ≫ (η[G] : 𝟙_ (Over S) ⟶ G).left := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

theorem hermForm_sum {g n m : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a : Fin n → ℂ) (b : Fin m → ℂ)
    (W : Fin n → Fin g → ℂ) (W' : Fin m → Fin g → ℂ) :
    hermForm Hm (∑ i, a i • W i : Fin g → ℂ) (∑ j, b j • W' j : Fin g → ℂ) = ∑ i, ∑ j, a i * star (b j) * hermForm Hm (W i) (W' j) := by
  simp only [hermForm, dotProduct, mulVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.star_apply, star_sum,
    star_mul', Finset.mul_sum, Finset.sum_mul]
  have e1 : ∀ x x1, (∑ x_2 : Fin m, ∑ i : Fin n, a i * W i x * (Hm x x1 * (star (b x_2) * star (W' x_2 x1)))) =
      ∑ i : Fin n, ∑ x_2 : Fin m, a i * W i x * (Hm x x1 * (star (b x_2) * star (W' x_2 x1))) := fun x x1 => Finset.sum_comm
  simp only [e1]
  have e2 : ∀ x, (∑ x1 : Fin g, ∑ i : Fin n, ∑ x_2 : Fin m, a i * W i x * (Hm x x1 * (star (b x_2) * star (W' x_2 x1)))) =
      ∑ i : Fin n, ∑ x1 : Fin g, ∑ x_2 : Fin m, a i * W i x * (Hm x x1 * (star (b x_2) * star (W' x_2 x1))) := fun x => Finset.sum_comm
  simp only [e2]
  rw [Finset.sum_comm (f := fun (x : Fin g) (i : Fin n) => ∑ x1 : Fin g, ∑ x_2 : Fin m, a i * W i x * (Hm x x1 * (star (b x_2) * star (W' x_2 x1))))]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e3 : ∀ x, (∑ x1 : Fin g, ∑ x_2 : Fin m, a i * W i x * (Hm x x1 * (star (b x_2) * star (W' x_2 x1)))) =
      ∑ x_2 : Fin m, ∑ x1 : Fin g, a i * W i x * (Hm x x1 * (star (b x_2) * star (W' x_2 x1))) := fun x => Finset.sum_comm
  simp only [e3]
  rw [Finset.sum_comm (f := fun (x : Fin g) (x_2 : Fin m) => ∑ x1 : Fin g, a i * W i x * (Hm x x1 * (star (b x_2) * star (W' x_2 x1))))]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

end PositivityTheory.Xgf.HermitianFormSum

namespace PositivityTheory.Xgf

open PositivityTheory.Xgf.HermitianFormSum in
theorem hodge_gram_linear_combination : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (x : Sp ℂ ⟶ S) (n n' : ℕ) (v : Fin n → (epsAt x ⟶ G)) (v' : Fin n' → (epsAt x ⟶ G)) (Γ : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin n') (Fin n) ℂ), (∀ k, IsTanAt G x (v k)) → IsHodgeGram G L x v Γ → (∀ k, IsComb (A k) v (v' k)) → IsHodgeGram G L x v' (A * Γ * Aᴴ) := by
  intro S G _ L x n n' v v' Γ A hT hG hC
  obtain ⟨Q, ψ, v₁, u, Hm, χ, W, hPB, hLB, hAH, hv, hΓ⟩ := hG
  have hη : (η[Q.A] : 𝟙_ (Over (Sp ℂ)) ⟶ Q.A).left ≫ ψ = x ≫ (η[G] : 𝟙_ (Over S) ⟶ G).left := by
    have hw : ((1 : 𝟙_ (Over (Sp ℂ)) ⟶ Q.A).left ≫ ψ) ≫ G.hom = (Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ x)).hom := by
      rw [Category.assoc, hPB.1.w, ← Category.assoc, Over.w]
      rfl
    let a₀ : Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ x) ⟶ G := Over.homMk ((1 : 𝟙_ (Over (Sp ℂ)) ⟶ Q.A).left ≫ ψ) hw
    have hm := hPB.2 (𝟙_ (Over (Sp ℂ))) 1 1 a₀ a₀ rfl rfl
    rw [_root_.mul_one] at hm
    have h1 : a₀ * a₀ = a₀ * 1 := by
      rw [_root_.mul_one]
      exact Over.OverMorphism.ext hm
    have h2 := congrArg (fun h => h.left) (mul_left_cancel h1)
    simp only [a₀, Over.homMk_left, one_left] at h2
    simpa using h2
  have hunit : ∀ T : Over (Sp ℂ), (1 : T ⟶ Q.A).left ≫ ψ = (1 : Over.mk (T.hom ≫ x) ⟶ G).left := by
    intro T
    rw [one_left, one_left, Category.assoc, hη]
    simp
  have hprod : ∀ (k : ℕ) (uu : Fin k → (epsR ℂ ⟶ Q.A)) (dd : Fin k → (epsAt x ⟶ G)),
      (∀ i, (dd i).left = (uu i).left ≫ ψ) → (List.ofFn dd).prod.left = (List.ofFn uu).prod.left ≫ ψ := by
    intro k
    induction k with
    | zero => intro uu dd _; simpa using (hunit (epsR ℂ)).symm
    | succ k ih =>
      intro uu dd h
      rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons]
      exact hPB.2 (epsR ℂ) _ _ _ _ (h 0) (ih _ _ fun i => h i.succ)
  have hsp : ∀ (c : ℂ), spMap (epsScaleR c) ≫ (epsR ℂ).hom = (epsR ℂ).hom := by
    intro c
    simp only [epsR, Over.mk_hom, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext z
    · simp [epsScaleR]
    · simp [epsScaleR]
  have htan : ∀ i, IsTangent (v₁ i) := by
    intro i
    apply hPB.1.hom_ext
    · rw [Category.assoc, (hv i).1, hT i, one_left, hη]
      rfl
    · rw [Category.assoc, Over.w, Over.w]
      simp only [epsR, Over.mk_hom, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      have e : ((TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ := by
        ext z; simp
      erw [e, CommRingCat.ofHom_id, Spec.map_id]
      rfl
  choose u' hu' hv' using hC
  let uu : ∀ k, Fin n → (epsR ℂ ⟶ Q.A) := fun k i =>
    Over.homMk (spMap (epsScaleR (A k i)) ≫ (v₁ i).left) (by rw [Category.assoc, Over.w]; exact hsp _)
  refine ⟨Q, ψ, fun k => (List.ofFn (uu k)).prod, u, Hm, χ, fun k => ∑ i, A k i • W i, hPB, hLB, hAH,
    fun k => ⟨?_, ?_⟩, fun k l => ?_⟩
  · rw [hv' k]
    exact (hprod n (uu k) (u' k) fun i => by
      rw [hu' k i]
      show _ = (spMap (epsScaleR (A k i)) ≫ (v₁ i).left) ≫ ψ
      rw [Category.assoc, (hv i).1]
      rfl).symm
  · exact GlobalTheory.isDiff_sum_smul_of_isLieComb Q.A Q.isAb Q.L Q.g n u v₁ W (A k) _ htan (fun i => (hv i).2)
      ⟨uu k, fun i => rfl, rfl⟩
  · rw [hermForm_sum]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hΓ, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [RCLike.star_def]
    ring

end PositivityTheory.Xgf
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem eq_zero_of_trace_pairing_zero {z : E} (h : ∀ c : 𝓞 E, Algebra.trace ℚ E ((c : E) * z) = 0) : z = 0 := by
  rw [HT.LatBasic.expand_dual z]
  refine Finset.sum_eq_zero fun k _ => ?_
  have hk := h (RingOfIntegers.basis E k)
  rw [integralBasis_apply, mul_comm, ← RingOfIntegers.coe_eq_algebraMap, hk, zero_smul]

theorem eq_of_trace_pairing_eq {z w : E} (h : ∀ c : 𝓞 E, Algebra.trace ℚ E ((c : E) * z) = Algebra.trace ℚ E ((c : E) * w)) :
    z = w := by
  rw [← sub_eq_zero]
  exact eq_zero_of_trace_pairing_zero fun c => by rw [mul_sub, map_sub, h c, sub_self]

theorem trace_mul_sesq_eq_form (D : Datum H) (a : 𝓞 E) (x y : D.La) :
    Algebra.trace ℚ E ((a : E) * sesq D x y) = (D.EF (a • x) y : ℚ) := by
  classical
  have e : ∀ k, Algebra.trace ℚ E ((a : E) * ((D.EF (RingOfIntegers.basis E k • x) y : E) * HT.dualInt E k)) =
      (D.EF (RingOfIntegers.basis E k • x) y : ℚ) * ((RingOfIntegers.basis E).repr a k : ℚ) := by
    intro k
    rw [show (a : E) * ((D.EF (RingOfIntegers.basis E k • x) y : E) * HT.dualInt E k) =
        (D.EF (RingOfIntegers.basis E k • x) y : ℤ) • (HT.dualInt E k * (a : E)) by rw [zsmul_eq_mul]; ring,
      map_zsmul, zsmul_eq_mul, HT.LatBasic.repr_eq_trace]

  simp only [sesq, Finset.mul_sum, map_sum, e]
  have ha : a • x = ∑ k, ((RingOfIntegers.basis E).repr a k : ℤ) • (RingOfIntegers.basis E k • x) := by
    conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr a]
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun k _ => smul_assoc _ _ _

  rw [ha, map_sum, LinearMap.sum_apply]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, LinearMap.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem Datum_EF_antisymm (D : Datum H) (x y : D.La) : D.EF y x = -D.EF x y := by
  have h := D.alt (x + y)
  simp only [map_add (f := _), LinearMap.add_apply, D.alt x, D.alt y, zero_add, add_zero] at h
  linarith

theorem Host_bar_bar (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.coe_injective
  show ((H.bar (H.bar a) : 𝓞 E) : E) = (a : E)
  rw [H.bar_eq, H.bar_eq]
  exact IsCMField.complexConj_apply_apply E (a : E)

theorem trace_complexConj (z : E) :
    Algebra.trace ℚ E (IsCMField.complexConj E z) = Algebra.trace ℚ E z := by
  let σ : E ≃ₐ[ℚ] E := (IsCMField.complexConj E).restrictScalars ℚ
  have hσ : ∀ w, σ w = IsCMField.complexConj E w := fun _ => rfl
  rw [← hσ, Algebra.trace_apply, Algebra.trace_apply]
  have : Algebra.lmul ℚ E (σ z) = σ.toLinearEquiv.conj (Algebra.lmul ℚ E z) := by
    ext w
    show σ z * w = σ (z * σ.symm w)
    rw [map_mul, AlgEquiv.apply_symm_apply]
  rw [this, LinearMap.trace_conj']

theorem sesq_sesquilinear_properties (D : Datum H) :
    (∀ (a : 𝓞 E) x y, Algebra.trace ℚ E ((a : E) * sesq D x y) = (D.EF (a • x) y : ℚ)) ∧
      (∀ x x' y, sesq D (x + x') y = sesq D x y + sesq D x' y) ∧
      (∀ x y y', sesq D x (y + y') = sesq D x y + sesq D x y') ∧
      (∀ (a : 𝓞 E) x y, sesq D (a • x) y = a * sesq D x y) ∧
      (∀ (a : 𝓞 E) x y, sesq D x (a • y) = IsCMField.complexConj E (a : E) * sesq D x y) ∧
      (∀ x y, sesq D y x = -IsCMField.complexConj E (sesq D x y)) ∧
      ∀ δ ∈ differentIdeal ℤ (𝓞 E), ∀ x y, ∃ b : 𝓞 E, (δ : E) * sesq D x y = b := by
  refine ⟨trace_mul_sesq_eq_form D, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x x' y
    simp only [sesq, smul_add, map_add (f := _), LinearMap.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]
  · intro x y y'
    simp only [sesq, map_add (f := _), Int.cast_add, add_mul, Finset.sum_add_distrib]
  · intro a x y
    apply eq_of_trace_pairing_eq
    intro c
    rw [trace_mul_sesq_eq_form, ← _root_.mul_assoc, ← map_mul, trace_mul_sesq_eq_form, smul_smul]
  · intro a x y
    apply eq_of_trace_pairing_eq
    intro c
    have h1 : D.EF (c • x) (a • y) = D.EF ((H.bar a * c) • x) y := by
      conv_lhs => rw [← Host_bar_bar (H := H) a]
      rw [← D.adj, smul_smul]
    rw [trace_mul_sesq_eq_form, h1, ← _root_.mul_assoc, mul_comm (c : E), ← H.bar_eq, ← map_mul, trace_mul_sesq_eq_form]
  · intro x y
    apply eq_of_trace_pairing_eq
    intro c
    have h1 : D.EF (c • y) x = -D.EF ((H.bar c) • x) y := by
      rw [Datum_EF_antisymm, D.adj, Host_bar_bar]
    rw [trace_mul_sesq_eq_form, h1, mul_neg, map_neg, Int.cast_neg, neg_inj]
    have h2 : (c : E) * IsCMField.complexConj E (sesq D x y) =
        IsCMField.complexConj E (((H.bar c : 𝓞 E) : E) * sesq D x y) := by
      rw [map_mul, H.bar_eq, IsCMField.complexConj_apply_apply]
    rw [h2, trace_complexConj, trace_mul_sesq_eq_form]
  · intro δ hδ x y
    have hdual : sesq D x y ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
      rw [FractionalIdeal.mem_dual (@one_ne_zero (FractionalIdeal (nonZeroDivisors (𝓞 E)) E) _ _ _)]
      intro c hc
      obtain ⟨c, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hc
      refine ⟨D.EF (c • x) y, ?_⟩
      rw [Algebra.traceForm_apply, mul_comm, ← RingOfIntegers.coe_eq_algebraMap, trace_mul_sesq_eq_form]
      simp
    have hmul : (δ : E) * sesq D x y ∈ ((differentIdeal ℤ (𝓞 E) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) *
        FractionalIdeal.dual ℤ ℚ 1) :=
      FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal _).2 ⟨δ, hδ, rfl⟩) hdual
    rw [coeIdeal_differentIdeal ℤ ℚ, inv_mul_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ (@one_ne_zero (FractionalIdeal (nonZeroDivisors (𝓞 E)) E) _ _ _))] at hmul
    obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).1 hmul
    exact ⟨b, hb.symm⟩

end GlobalTheory.CompanionTheory.Ar.Fl

namespace PositivityTheory.Xgf

theorem sesq_sesquilinear_skew_hermitian : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), (∀ (a : 𝓞 E) x y, Algebra.trace ℚ E ((a : E) * sesq D x y) = (D.EF (a • x) y : ℚ)) ∧ (∀ x x' y, sesq D (x + x') y = sesq D x y + sesq D x' y) ∧ (∀ x y y', sesq D x (y + y') = sesq D x y + sesq D x y') ∧ (∀ (a : 𝓞 E) x y, sesq D (a • x) y = a * sesq D x y) ∧ (∀ (a : 𝓞 E) x y, sesq D x (a • y) = IsCMField.complexConj E (a : E) * sesq D x y) ∧ (∀ x y, sesq D y x = -IsCMField.complexConj E (sesq D x y)) ∧ ∀ δ ∈ differentIdeal ℤ (𝓞 E), ∀ x y, ∃ b : 𝓞 E, (δ : E) * sesq D x y = b :=
  fun _ _ _ _ _ D => GlobalTheory.CompanionTheory.Ar.Fl.sesq_sesquilinear_properties D

end PositivityTheory.Xgf
end
