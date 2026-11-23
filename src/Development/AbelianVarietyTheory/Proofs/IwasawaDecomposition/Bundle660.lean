module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle066
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle626
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle035
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle046
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishesToPullChartIffOfFlat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle633
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle648
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle628
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt

@[expose] public section

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.Hor.PerBasis

theorem mult_conj_add_mult {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (D : Datum H) (τ : E →+* ℂ) : D.mult (conjEmb τ) + D.mult τ = D.p + D.q := by
  first
  | exact @_root_.GlobalTheory.ConjugateMultiplicity.target
  | exact _root_.GlobalTheory.ConjugateMultiplicity.target
  | (apply _root_.GlobalTheory.ConjugateMultiplicity.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.ConjugateMultiplicity.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ConjugateMultiplicity.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ConjugateMultiplicity.target ..)

theorem exists_indep {E : Type} [Field E] [NumberField E] (M : Type) [AddCommGroup M] [Module (𝓞 E) M]
    [Module.Finite (𝓞 E) M] (J : Type) [Fintype J] (hJ : Fintype.card J = Module.finrank (𝓞 E) M) :
    ∃ x : J → M, LinearIndependent (𝓞 E) x ∧
      ∀ v, ∃ n : ℕ, n ≠ 0 ∧ n • v ∈ Submodule.span (𝓞 E) (Set.range x) := by
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 E) (M := M) (n := Fintype.card J) hJ.le
  let e := Fintype.equivFin J
  refine ⟨f ∘ e, hf.comp _ e.injective, fun v => ?_⟩
  rw [e.surjective.range_comp]
  have hc : ∃ c : 𝓞 E, c ≠ 0 ∧ c • v ∈ Submodule.span (𝓞 E) (Set.range f) := by
    by_contra hcon
    push Not at hcon
    have hli : LinearIndependent (𝓞 E) (Fin.cons v f : Fin (Fintype.card J + 1) → M) := by
      refine LinearIndependent.finCons' v f hf fun c y hy h => ?_
      by_contra hc
      refine hcon c hc ?_
      rw [eq_neg_of_add_eq_zero_left h]
      exact neg_mem hy
    have := hli.fintype_card_le_finrank
    simp at this
    omega
  obtain ⟨c, hc0, hc⟩ := hc
  refine ⟨Ideal.absNorm (Ideal.span {c}), ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hc0
  · obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {c}))
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E), ← hd, mul_smul]
    exact Submodule.smul_mem _ _ hc

theorem exists_trace_rep {E : Type} [Field E] [NumberField E] (φ : 𝓞 E →ₗ[ℤ] ℤ) :
    ∃ h : E, ∀ a : 𝓞 E, ((φ a : ℤ) : ℚ) = Algebra.trace ℚ E ((a : E) * h) := by
  let ψ : E →ₗ[ℚ] ℚ := (integralBasis E).constr ℚ fun i => (φ (RingOfIntegers.basis E i) : ℚ)
  have hψ : ∀ a : 𝓞 E, ((φ a : ℤ) : ℚ) = ψ (a : E) := by
    intro a
    have : (Int.castAddHom ℚ).toIntLinearMap ∘ₗ φ =
        (ψ.restrictScalars ℤ) ∘ₗ ((algebraMap (𝓞 E) E).toAddMonoidHom.toIntLinearMap) := by
      refine (RingOfIntegers.basis E).ext fun i => ?_
      change ((φ (RingOfIntegers.basis E i) : ℤ) : ℚ) = ψ (algebraMap (𝓞 E) E (RingOfIntegers.basis E i))
      rw [← integralBasis_apply, Module.Basis.constr_basis]
    exact LinearMap.congr_fun this a
  refine ⟨((Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)).symm ψ, fun a => ?_⟩
  rw [hψ, mul_comm, ← Algebra.traceForm_apply]
  exact (LinearMap.BilinForm.apply_toDual_symm_apply _ _).symm

theorem exists_isPerBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw Di : Datum H) (τ : E →+* ℂ), Di.p = Dw.p ∧ Di.q = Dw.q →
    ∃ (x : Idx Dw τ → Di.La) (hm : Matrix (Idx Dw τ) (Idx Dw τ) E), IsPerBasis Di x hm := by
  intro E _ _ _ H Dw Di τ ⟨hp, hq⟩
  have := Di.fin
  obtain ⟨x, hx, hsp⟩ := exists_indep (E := E) Di.La (Idx Dw τ) (by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, mult_conj_add_mult, Di.rank, hp, hq])
  have hrep : ∀ k k', ∃ h : E, ∀ a : 𝓞 E,
      ((Di.EF (a • x k) (x k') : ℤ) : ℚ) = Algebra.trace ℚ E ((a : E) * h) := fun k k' =>
    exists_trace_rep (AddMonoidHom.toIntLinearMap
      { toFun := fun a : 𝓞 E => Di.EF (a • x k) (x k')
        map_zero' := by simp
        map_add' := fun a b => by simp [add_smul] })
  choose hm hhm using hrep
  refine ⟨x, Matrix.of hm, hx, hsp, fun a k k' => hhm k k' a, fun hdet => ?_⟩
  obtain ⟨c₀, hc₀, hker⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 E)) c₀
  choose c hc using hd
  set v := ∑ k, c k • x k with hv
  have h1 : ∀ (a : 𝓞 E) k', Di.EF (a • v) (x k') = 0 := by
    intro a k'
    have hk := congrFun hker k'
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply] at hk
    have : ((Di.EF (a • v) (x k') : ℤ) : ℚ) = 0 := by

      rw [hv, Finset.smul_sum, map_sum, LinearMap.sum_apply]
      push_cast
      simp_rw [← mul_smul, hhm]

      rw [← map_sum]
      have : ∑ k, ((a * c k : 𝓞 E) : E) * hm k k' = (a : E) * ((d : 𝓞 E) : E) * ∑ k, c₀ k * hm k k' := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        have h2 : ((c k : 𝓞 E) : E) = ((d : 𝓞 E) : E) * c₀ k := by
          exact (hc k).trans (Algebra.smul_def _ _)
        have h3 : ((a * c k : 𝓞 E) : E) = (a : E) * ((c k : 𝓞 E) : E) := map_mul (algebraMap (𝓞 E) E) _ _
        rw [h3, h2]; ring
      rw [this, hk]; simp
    exact_mod_cast this
  have h2 : ∀ w ∈ Submodule.span (𝓞 E) (Set.range x), ∀ a : 𝓞 E, Di.EF v (a • w) = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨k, rfl⟩ := hw
      intro a
      have := h1 (H.bar.symm a) k
      rwa [Di.adj, RingEquiv.apply_symm_apply] at this
    | zero => simp
    | add y z _ _ hy hz => intro a; rw [smul_add, map_add (f := _), hy, hz, add_zero]
    | smul b y _ hy => intro a; rw [← mul_smul, hy]
  have h3 : v = 0 := by
    apply Di.unimod.1
    rw [map_zero]
    ext w
    obtain ⟨n, hn, hw⟩ := hsp w
    have := h2 _ hw 1
    rw [one_smul, map_nsmul] at this
    simpa [hn] using this
  apply hc₀
  funext k
  have h4 := Fintype.linearIndependent_iff.1 hx c h3 k
  have h5 := hc k
  rw [h4, map_zero, Algebra.smul_def] at h5
  refine (mul_eq_zero.1 h5.symm).resolve_left ?_
  exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 (nonZeroDivisors.coe_ne_zero d)

end GlobalTheory.ShFam.Hor.PerBasis
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.Hor.Chg

open GlobalTheory.ShFam.OpenReg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ} {g : ℕ} {e : Fin g ≃ Letter Dw} {Fu : Fam Xo c σ e} {i : Fin Fu.n}
  {P : (Fu.Di i).La →+ (Fin g → ℂ)} {y : Sp ℂ ⟶ Xo.XF c}


variable (Z P y) in
def Lifts (w : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ Z.t.G.left) : Prop :=
  ∃ v₀ : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left,
    v₀ ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y ∧ v₀ ≫ Z.m.φ = v ∧
    IsDerivAt0 (fun w => (Fu.ex i P w).left) w (v₀ ≫ Z.m0.toSABMap.φ)

variable (hP : IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P)
  (hy : y ≫ pullback.fst _ _ = Fu.u i P) {x : Sp ℂ ⟶ Z.X} (hx : y ≫ Z.jQ ≫ pullback.fst _ _ = x)

include hP hy hx

theorem exists_dir {v : Sp (DualNumber ℂ) ⟶ Z.t.G.left} (hv : IsTanAtG Z.t x v) : ∃ w, Lifts Z P y w v := by
  obtain ⟨v₀, h1, rfl⟩ := exists_lift Z.m (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) v
    (by rw [hv.1, ← hx, Category.assoc])
  obtain ⟨w, hw, -⟩ := (isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ Fu i P hP).2.2 _
    ((tan_iff Z.m0.toSABMap hy h1).2 ((tan_iff Z.m hx h1).1 hv))
  exact ⟨w, v₀, h1, rfl, hw⟩

theorem eq_sum_of_comb {n : ℕ} {v : Fin n → (Sp (DualNumber ℂ) ⟶ Z.t.G.left)} {W : Fin n → Fin g → ℂ}
    (hW : ∀ k, Lifts Z P y (W k) (v k)) {v' : Sp (DualNumber ℂ) ⟶ Z.t.G.left} {w : Fin g → ℂ} (hw : Lifts Z P y w v')
    {a : Fin n → ℂ} (h : IsCombAtG Z.t x v a v') : w = ∑ k, a k • W k := by
  choose u h1 h2 h3 using hW
  obtain ⟨u', h1', rfl, h3'⟩ := hw
  obtain rfl : v = fun k => u k ≫ Z.m.φ := funext fun k => (h2 k).symm
  have h4 := (comb_iff Z.m0.toSABMap hy h1 a h1').2 ((comb_iff Z.m hx h1 a h1').1 h)
  have h5 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ Fu i P hP n _ W h3 a _).1 h4
  have ht := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ Fu i P hP
  exact (ht.2.2 _ (ht.1 _ _ h3')).unique h3' h5

theorem span_eq_top (f : EigFrame Z σ x) {W : Letter Dw → Fin g → ℂ} (hW : ∀ z, Lifts Z P y (W z) (f.v z.1 z.2)) :
    ⊤ ≤ Submodule.span ℂ (Set.range W) := by
  rw [← (Pi.basisFun ℂ (Fin g)).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  have ht := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ Fu i P hP
  obtain ⟨v, hv, -⟩ := ht.2.1 (Pi.basisFun ℂ (Fin g) j)
  have he := (isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e Fu i P hP _ v (e j).1 hv).2 (fun k hk => by
    obtain rfl : k = j := by
      by_contra hne
      exact hk (by simp [hne])
    rfl)
  have htan := ht.1 _ _ hv
  obtain ⟨v₀, h1, rfl⟩ := exists_lift Z.m0.toSABMap (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) v
    (by rw [htan.1, ← hy, Category.assoc])
  obtain ⟨a, ha, -⟩ := f.basis (e j).1 (v₀ ≫ Z.m.φ) ((tan_iff Z.m hx h1).2 ((tan_iff Z.m0.toSABMap hy h1).1 htan))
    fun a => (eig_iff Z.m h1 a _).2 ((eig_iff Z.m0.toSABMap h1 a _).1 (he a))
  rw [eq_sum_of_comb hP hy hx (W := fun k => W ⟨(e j).1, k⟩) (fun k => hW ⟨_, k⟩) ⟨v₀, h1, rfl, hv⟩ ha]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem linearIndependent (f : EigFrame Z σ x) {W : Letter Dw → Fin g → ℂ}
    (hW : ∀ z, Lifts Z P y (W z) (f.v z.1 z.2)) : LinearIndependent ℂ W :=
  linearIndependent_of_top_le_span_of_card_eq_finrank (span_eq_top hP hy hx f hW)
    (by rw [← Fintype.card_congr e]; simp)

end GlobalTheory.ShFam.Hor.Chg

namespace GlobalTheory.ShFam.Hor

theorem per_chg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (a a' : CxFr Z σ) (i : Fin Fu.n) (Q : (Fu.Di i).La →+ (Letter Dw → ℂ)), Per Fu a i Q → a.1 = a'.1 → ∃ Q', Per Fu a' i Q' ∧ ∀ ρ M, Chg a a' ρ M → ∀ v k, Q v ⟨ρ, k⟩ = ∑ j, Q' v ⟨ρ, j⟩ * M j k := by
  rintro E _ _ _ H Dw l Xo c O _ β Z σ g e Fu ⟨x, f⟩ ⟨x', f'⟩ i Q ⟨P, W, y, hP, hy, hyx, hW, hQ⟩ hxx
  obtain rfl : x = x' := hxx
  have hx : y ≫ Z.jQ ≫ pullback.fst _ _ = x.1 ≫ genι Z := by rw [← Category.assoc, hyx]
  choose W' hW' using fun z : Letter Dw => Chg.exists_dir hP hy hx (f'.tan z.1 z.2)
  let b := Module.Basis.mk (Chg.linearIndependent hP hy hx f' hW') (Chg.span_eq_top hP hy hx f' hW')
  let Q' : (Fu.Di i).La →+ (Letter Dw → ℂ) := b.equivFun.toLinearMap.toAddMonoidHom.comp P
  have hQ' : ∀ v, P v = ∑ z, Q' v z • W' z := fun v => by
    have := b.sum_equivFun (P v)
    simp only [b, Module.Basis.coe_mk] at this
    exact this.symm
  refine ⟨Q', ⟨P, W', y, hP, hy, hyx, hW', hQ'⟩, fun ρ M hM v k => ?_⟩
  choose N hN using fun (τ : E →+* ℂ) j => (f.basis τ _ (f'.tan τ j) (f'.eig τ j)).exists
  have hNM : ∀ j, N ρ j = M j := fun j => (f.basis ρ _ (f'.tan ρ j) (f'.eig ρ j)).unique (hN ρ j) (hM.2 j)
  have hc : ∀ τ j, W' ⟨τ, j⟩ = ∑ k, N τ j k • W ⟨τ, k⟩ := fun τ j =>
    Chg.eq_sum_of_comb hP hy hx (W := fun k => W ⟨τ, k⟩) (fun k => hW ⟨τ, k⟩) (hW' ⟨τ, j⟩) (hN τ j)
  have h1 : ∑ z, Q v z • W z = ∑ z : Letter Dw, (∑ j, Q' v ⟨z.1, j⟩ * N z.1 j z.2) • W z := by
    rw [← hQ, hQ', Fintype.sum_sigma, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [hc, Finset.smul_sum, Finset.sum_smul, smul_smul]
    exact Finset.sum_comm
  have h2 := Fintype.linearIndependent_iffₛ.1 (Chg.linearIndependent hP hy hx f hW) _ _ h1 ⟨ρ, k⟩
  simp only [hNM] at h2
  exact h2

end GlobalTheory.ShFam.Hor
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.Hor

open GlobalTheory.ShFam.OpenReg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ} {g : ℕ} {e : Fin g ≃ Letter Dw} {Fu : Fam Xo c σ e} {a : CxFr Z σ} {i : Fin Fu.n}
  {P : (Fu.Di i).La →+ (Fin g → ℂ)} {W : Letter Dw → Fin g → ℂ} {y : Sp ℂ ⟶ Xo.XF c}

section Directions

variable (hP : IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P)
  (hu : y ≫ pullback.fst _ _ = Fu.u i P) (hy : y ≫ Z.jQ = a.1.1)
  (hW : ∀ z : Letter Dw, ∃ v₀ : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left,
      v₀ ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y ∧ v₀ ≫ Z.m.φ = a.2.v z.1 z.2 ∧
      IsDerivAt0 (fun w => (Fu.ex i P w).left) (W z) (v₀ ≫ Z.m0.toSABMap.φ))


include hP hu hy hW in
theorem dirs_exists_comb (τ : E →+* ℂ) (w : Fin g → ℂ) (hw : ∀ j, w j ≠ 0 → (e j).1 = τ) :
    ∃ cf : Fin (Dw.mult τ) → ℂ, w = ∑ k, cf k • W ⟨τ, k⟩ := by
  choose v₀ h1 h2 h3 using hW
  have hx : y ≫ Z.jQ ≫ pullback.fst _ _ = a.1.1 ≫ genι Z := by rw [← Category.assoc, hy]
  obtain ⟨t1, t2, t3⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ Fu i P hP
  obtain ⟨v, hv, -⟩ := t2 w
  have ht := t1 w v hv
  have he := (GlobalTheory.isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e Fu i P hP w v τ hv).2 hw
  obtain ⟨v', k1, rfl⟩ := exists_lift Z.m0.toSABMap (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) v
    (by rw [ht.1, ← hu, Category.assoc])
  obtain ⟨cf, hcf, -⟩ := a.2.basis τ (v' ≫ Z.m.φ) ((tan_iff Z.m hx k1).2 ((tan_iff Z.m0.toSABMap hu k1).1 ht))
    fun b => (eig_iff Z.m k1 b _).2 ((eig_iff Z.m0.toSABMap k1 b _).1 (he b))
  have e1 : a.2.v τ = fun k => v₀ ⟨τ, k⟩ ≫ Z.m.φ := funext fun k => (h2 ⟨τ, k⟩).symm
  rw [e1] at hcf
  have hc := (comb_iff Z.m0.toSABMap hu (fun k => h1 ⟨τ, k⟩) cf k1).2 ((comb_iff Z.m hx (fun k => h1 ⟨τ, k⟩) cf k1).1 hcf)
  exact ⟨cf, (t3 _ ht).unique hv ((GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ Fu i P hP _ _
    (fun k => W ⟨τ, k⟩) (fun k => h3 ⟨τ, k⟩) cf _).1 hc)⟩


include hP hu hy hW in
theorem dirs_span : ⊤ ≤ Submodule.span ℂ (Set.range W) := by
  rw [← (Pi.basisFun ℂ (Fin g)).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  obtain ⟨cf, h⟩ := dirs_exists_comb hP hu hy hW (e j).1 (Pi.basisFun ℂ (Fin g) j) fun k hk => by
    by_contra hne
    exact hk (by rw [Pi.basisFun_apply]; exact Pi.single_eq_of_ne (fun h => hne (by rw [h])) _)
  rw [h]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)


include hP hu hy hW in
theorem dirs_basis : ∃ b : Module.Basis (Letter Dw) ℂ (Fin g → ℂ), ⇑b = W :=
  ⟨basisOfTopLeSpanOfCardEqFinrank W (dirs_span hP hu hy hW) (by
    rw [Module.finrank_fin_fun, ← Fintype.card_congr e, Fintype.card_fin]), coe_basisOfTopLeSpanOfCardEqFinrank _ _ _⟩

end Directions

theorem Inner.exists_lift {x : CxPts (genStr Z) σ} (h : Inner x) : ∃ y : Sp ℂ ⟶ Xo.XF c, y ≫ Z.jQ = x.1 := by
  have := Z.jQ_open
  have hr : Set.range x.1 ⊆ Set.range Z.jQ := by
    rintro _ ⟨p, rfl⟩
    obtain rfl : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    exact not_not.1 h
  exact ⟨IsOpenImmersion.lift Z.jQ _ hr, IsOpenImmersion.lift_fac _ _ _⟩

theorem exists_dirs (hP : IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P)
    (hu : y ≫ pullback.fst _ _ = Fu.u i P) (hy : y ≫ Z.jQ = a.1.1) :
    ∃ W : Letter Dw → Fin g → ℂ, ∀ z : Letter Dw, ∃ v₀ : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left,
      v₀ ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y ∧ v₀ ≫ Z.m.φ = a.2.v z.1 z.2 ∧
      IsDerivAt0 (fun w => (Fu.ex i P w).left) (W z) (v₀ ≫ Z.m0.toSABMap.φ) := by
  have hx : y ≫ Z.jQ ≫ pullback.fst _ _ = a.1.1 ≫ genι Z := by rw [← Category.assoc, hy]
  choose v₀ h1 h2 using fun z : Letter Dw => exists_lift Z.m (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) (a.2.v z.1 z.2)
    (by rw [(a.2.tan z.1 z.2).1, ← hx, Category.assoc])
  choose W hW using fun z : Letter Dw => ((GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ Fu i P hP).2.2 _
    ((tan_iff Z.m0.toSABMap hu (h1 z)).2 ((tan_iff Z.m hx (h1 z)).1 (h2 z ▸ a.2.tan z.1 z.2)))).exists
  exact ⟨W, fun z => ⟨v₀ z, h1 z, h2 z, hW z⟩⟩

theorem exists_per_of_isPeriod (hP : IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P)
    (hu : y ≫ pullback.fst _ _ = Fu.u i P) (hy : y ≫ Z.jQ = a.1.1) : ∃ Q, Per Fu a i Q := by
  obtain ⟨W, hW⟩ := exists_dirs hP hu hy
  obtain ⟨b, rfl⟩ := dirs_basis hP hu hy hW
  exact ⟨b.equivFun.toLinearMap.toAddMonoidHom.comp P, P, b, y, hP, hu, hy, hW, fun v => (b.sum_equivFun (P v)).symm⟩

theorem exists_per : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (a : CxFr Z σ), Inner a.1 → ∃ i Q, Per Fu a i Q := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ g e Fu a ha
  obtain ⟨y, hy⟩ := ha.exists_lift
  have hs : y ≫ pullback.snd _ _ = spMap σ := by
    rw [← Z.jQ_over, ← Category.assoc, hy]
    exact a.1.2
  obtain ⟨i, P, hP, hu⟩ := Fu.onto (y ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, OpenReg.spMap_comp])
  exact ⟨i, exists_per_of_isPeriod hP hu.symm hy⟩

end GlobalTheory.ShFam.Hor
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GermAff

theorem mem_map_of_germ : ∀ {T Y' : Scheme.{0}} [IsAffine T] (χ : T ⟶ Y') (I : Y'.IdealSheafData) (W : Y'.affineOpens)
    (hle : ⊤ ≤ χ ⁻¹ᵁ (W : Y'.Opens)) (s : Γ(T, ⊤)),
    (∀ t : T, (T.presheaf.germ ⊤ t trivial).hom s ∈ FinalTheorems.stalkId (I.comap χ) t) →
      s ∈ (I.ideal W).map (χ.appLE W ⊤ hle).hom := by
  intro T Y' _ χ I W hle s hs
  set K := (I.ideal W).map (χ.appLE W ⊤ hle).hom with hK
  have hc : I.comap χ = Scheme.IdealSheafData.ofIdealTop K := by
    refine (GlobalTheory.Vanishing.eq_comap_of_stalk fun z => ?_).symm
    have hz : χ z ∈ W.1 := hle trivial
    rw [GlobalTheory.LocM.stalkId_ofIdealTop, ds_stalkId_eq_map I W _ hz, Ideal.map_map, Ideal.map_map,
      ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE, Category.assoc]
    congr 3
    exact T.presheaf.germ_res (homOfLE hle) z (by trivial)
  have hs' : ∀ t : T, (T.presheaf.germ ⊤ t trivial).hom s ∈ K.map (T.presheaf.germ ⊤ t trivial).hom := by
    intro t
    rw [← GlobalTheory.LocM.stalkId_ofIdealTop, ← hc]
    exact hs t
  by_contra hns
  have hne : K.colon {s} ≠ ⊤ := by
    intro htop
    have h1 : (1 : Γ(T, ⊤)) ∈ K.colon {s} := htop ▸ Submodule.mem_top
    rw [Submodule.mem_colon_singleton, one_smul] at h1
    exact hns h1
  obtain ⟨P, hP, hCP⟩ := Ideal.exists_le_maximal _ hne
  let y : PrimeSpectrum Γ(T, ⊤) := ⟨P, hP.isPrime⟩
  have hA := isAffineOpen_top T
  let t : T := hA.fromSpec y
  have ht : t ∈ (⊤ : T.Opens) := trivial
  letI : Algebra Γ(T, ⊤) (T.presheaf.stalk t) := T.presheaf.algebra_section_stalk ⟨t, ht⟩
  haveI : IsLocalization y.asIdeal.primeCompl (T.presheaf.stalk t) := hA.isLocalization_stalk' y ht
  have hg : (T.presheaf.germ ⊤ t trivial).hom = algebraMap Γ(T, ⊤) (T.presheaf.stalk t) := rfl
  have h := hs' t
  rw [hg, IsLocalization.mem_map_algebraMap_iff y.asIdeal.primeCompl] at h
  obtain ⟨⟨⟨k, hk⟩, ⟨m, hm⟩⟩, he⟩ := h
  simp only at he
  rw [← map_mul, IsLocalization.eq_iff_exists y.asIdeal.primeCompl] at he
  obtain ⟨⟨c, hcm⟩, hc'⟩ := he
  simp only at hc'
  have hmem : c * m ∈ K.colon {s} := by
    rw [Submodule.mem_colon_singleton, smul_eq_mul]
    have : c * m * s = c * k := by rw [← hc']; ring
    rw [this]
    exact K.mul_mem_left c hk
  have hnot : c * m ∉ P := fun h' => (hP.isPrime.mem_or_mem h').elim hcm hm
  exact hnot (hCP hmem)

end GlobalTheory.GermAff
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

theorem _root_.GlobalTheory.T.exists_isProjOver_finite_fibreProduct : ∀ (O : Type) [CommRing O] (ι : Type) [Finite ι] (X : Scheme.{0}) (s : X ⟶ Sp O) (Y : ι → Scheme.{0}) (f : ∀ i, Y i ⟶ Sp O), IsProjOver s → (∀ i, IsProjOver (f i)) → ∃ (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ i, P ⟶ Y i), IsProjOver (p0 ≫ s) ∧ (∀ i, p i ≫ f i = p0 ≫ s) ∧ ∀ (Z : Scheme.{0}) (a : Z ⟶ X) (b : ∀ i, Z ⟶ Y i), (∀ i, b i ≫ f i = a ≫ s) → ∃! h : Z ⟶ P, h ≫ p0 = a ∧ ∀ i, h ≫ p i = b i := by
  first | exact @GlobalTheory.ProjFinProd.exists_isProjOver_finite_prod | exact GlobalTheory.ProjFinProd.exists_isProjOver_finite_prod | (intros; apply GlobalTheory.ProjFinProd.exists_isProjOver_finite_prod <;> assumption)
end
