module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Bundle001
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle003
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle017
import Formalism.LocalToGlobal.ProjectiveLattices.LieRel
public import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle013
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle013
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.RegularCharts.SCharts

@[expose] public section

section



noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg.IntLie

theorem int_comb {V L : Type} [CommRing V] [IsDomain V] [Field L] [Algebra V L] [IsFractionRing V L] {n r : ℕ}
    (ix : Fin r ↪ Fin n) (u : Matrix (Fin n) (Fin r) V) (hu : InCell ix u) (x : Fin n → V) (cf : Fin r → L)
    (h : (fun j => algebraMap V L (x j)) = ∑ i, cf i • fun j => algebraMap V L (u j i)) :
    ∃ a : Fin r → V, x = ∑ i, a i • fun j => u j i := by
  have h1 := ((GlobalTheory.cell_columns_saturated_and_triangular V L n r ix u hu).1 r x).1 (by
    rw [h]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, i.2, rfl⟩))
  obtain ⟨a, -, ha⟩ := (GlobalTheory.mem_span_first_columns_iff u r x).1 h1
  refine ⟨a, ?_⟩
  rw [ha]
  ext j
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, _root_.mul_comm]

theorem dualMapR_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (g.comp f)) =
      spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR g) ≫ spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) := by
  have : ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (g.comp f) =
      (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR g).comp (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) := by
    refine RingHom.ext fun x => ?_
    ext <;> simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR]
  rw [this, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

end GlobalTheory.Reg.IntLie

namespace GlobalTheory.Reg

open IntLie
open ReciprocityTheory.ChartRestriction.G.Chart (tvec tmap tvec_inj tvec_eig_iff isTan_tvec tcoord tcoord_spec univChartLoc tanBC_alg
  pushR pushR_left pushR_inj pushR_map tvec_tmap fB scaleD IsUnivChart dualMapA chart_of_basis dualMapR)
open Formalism.L2.Pj.LieRel
open scoped CategoryTheory.Obj



theorem tie_vectors_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (T : CDVR) (io : c.F →+* T.Fr) (f₀ : Γ(Y.X, M.U) →+* T.V) (ix : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) ↪ Fin M.n) (u₀ : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) T.V), (∀ τ, InCell (ix τ) (u₀ τ)) → letI := io.toAlgebra; ∀ (z : FrPt Xo c T.Fr) (Λ : M.Lift ((algebraMap T.V T.Fr).comp f₀) z.x), Λ.LieTie (fun τ => (u₀ τ).map (algebraMap T.V T.Fr)) z.u → ∀ (G : SAB H (Sp T.V)) (m : SABMap G Y.t (spMap f₀ ≫ M.hU.fromSpec)) (m2 : SABMap Λ.t' G (spMap (algebraMap T.V T.Fr))), m2.φ ≫ m.φ = Λ.m2.φ → ∃ ub : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G.G), (∀ τ i, IsTan (ub τ i)) ∧ (∀ τ i, IsEigV c io G τ (ub τ i)) ∧ (∀ τ (w : epsOver T.V T.V ⟶ G.G), IsTan w → IsEigV c io G τ w → ∃! a : Fin (Dw.mult τ) → T.V, IsComb (ub τ) a w) ∧ ∀ τ i, ∃ u' : Sp (DualNumber T.Fr) ⟶ Λ.t'.G.left, u' ≫ Λ.m1.φ = z.u τ i ∧ u' ≫ m2.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (ub τ i).left := by
  intro E _ _ _ H Dw l Xo c O _ β Y M T io f₀ ix u₀ hcell
  let _ := io.toAlgebra
  intro z Λ tie G m m2 hφ
  have := G.semi.smooth
  have : ∀ a, IsMonHom (G.act.act a) := G.act.hom
  obtain ⟨v, hv0, hvb, -⟩ := M.lie T.V f₀ G m
  obtain ⟨xc, hxc, hxv⟩ := chart_of_basis hvb
  obtain ⟨x', hx', hcomp⟩ := tanBC_alg (R := T.V) (R' := T.Fr) G.G M.n xc hxc
  have hpt : ∀ cc : Fin M.n → T.V, pushR G.G (tvec (x := x') (algebraMap T.V T.Fr ∘ cc)) =
      ReciprocityTheory.ChartRestriction.G.Chart.spMap (dualMapA T.V T.Fr) ≫ tvec (x := xc) cc := fun cc =>
    Over.OverMorphism.ext (by rw [pushR_left, hcomp cc]; rfl)
  have hM0 : ∀ (a : 𝓞 E) (cc : Fin M.n → T.V),
      tmap hx' ((Over.pullback (fB T.V T.Fr)).map (G.act.act a)) (algebraMap T.V T.Fr ∘ cc) =
        algebraMap T.V T.Fr ∘ tmap hxc (G.act.act a) cc := by
    intro a cc
    apply tvec_inj hx'
    apply pushR_inj G.G
    rw [tvec_tmap hx', pushR_map, hpt, hpt, tvec_tmap hxc, Category.assoc]
  have hM : ∀ (a : 𝓞 E) (cc : Fin M.n → T.V),
      tmap hx' ((Over.pullback (fB T.V T.Fr)).map (G.act.act a)) (fun j => algebraMap T.V T.Fr (cc j)) =
        fun j => algebraMap T.V T.Fr (tmap hxc (G.act.act a) cc j) := hM0
  have h1 := Λ.m1.cart
  have h2 : IsGrpPullback Λ.t'.G G.G (fB T.V T.Fr) m2.φ := m2.cart
  let vA := fun e : Fin M.n → T.Fr => Classical.choose (relA_exists_v z.x h1 h2 (tvec (x := x') e))
  have hvA := fun e : Fin M.n → T.Fr => Classical.choose_spec (relA_exists_v z.x h1 h2 (tvec (x := x') e))
  have tanA : ∀ e, IsTanAt z.x (vA e).left := fun e =>
    ⟨Over.w (vA e), (relA_tan z.x h1 h2 (hvA e)).2 (isTan_tvec hx' e)⟩
  have eigA : ∀ (τ : E →+* ℂ) e, IsEigAt c τ (vA e).left ↔
      ∀ a, tmap hx' ((Over.pullback (fB T.V T.Fr)).map (G.act.act a)) e = io (embK c τ a) • e := by
    intro τ e
    unfold IsEigAt
    refine forall_congr' fun a => ?_
    rw [← tvec_eig_iff hx']
    exact relA_eig z.x h1 h2 (hvA e) (Λ.t'.act.act a) (Xo.univ.t.act.act a) (G.act.act a) (Λ.m1.act a) (m2.act a) _
  have combA : ∀ {m : ℕ} (d : Fin m → Fin M.n → T.Fr) (cf : Fin m → T.Fr) (e : Fin M.n → T.Fr),
      IsCombAt z.x (fun i => (vA (d i)).left) cf (vA e).left ↔ e = ∑ i, cf i • d i := by
    intro m d cf e
    have hr : ∀ i, RelA z.x Λ.m1.φ m2.φ (sclA z.x (cf i) ≫ vA (d i))
        (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (cf i)) ≫ tvec (x := x') (d i)) :=
      fun i => relA_scl z.x (hvA (d i)) (cf i)
    have hp := relA_prod z.x h1 h2 _ _ hr
    rw [prod_tvec hx'] at hp
    constructor
    · rintro ⟨u, hu, hw⟩
      have hu' : u = fun i => sclA z.x (cf i) ≫ vA (d i) := funext fun i => Over.OverMorphism.ext (hu i)
      subst hu'
      exact tvec_inj hx' ((relA_uniq z.x h1 h2 (hvA e) hp).1 (Over.OverMorphism.ext hw.symm))
    · rintro rfl
      exact ⟨fun i => sclA z.x (cf i) ≫ vA (d i), fun i => rfl,
        congrArg (fun q => q.left) ((relA_uniq z.x h1 h2 hp (hvA _)).2 rfl)⟩
  choose χ hχ using fun τ a => int_val c T io τ a
  have combV : ∀ cc : Fin M.n → T.V, IsLieComb cc v (tvec (x := xc) cc) := by
    intro cc
    refine ⟨fun i => ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (cc i)) ≫ tvec (x := xc) (Pi.single i 1), fun i => ?_, ?_⟩
    · rw [hxv i]; rfl
    · refine Eq.trans ?_ (prod_tvec hxc cc fun i => Pi.single i 1).symm
      congr 1
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
  have gen : ∀ τ i, ∃ u' : epsR T.Fr ⟶ Λ.t'.G, u'.left ≫ Λ.m1.φ = z.u τ i ∧
      u'.left ≫ m2.φ = spMap (dualMapR (algebraMap T.V T.Fr)) ≫ (tvec (x := xc) fun j => u₀ τ j i).left := by
    intro τ i
    obtain ⟨v', u', hv', hc, hu'⟩ := tie τ i
    refine ⟨u', hu', ?_⟩
    refine (GlobalTheory.lieComb_baseChange T.V T.Fr (algebraMap T.V T.Fr) G.G Λ.t'.G m2.φ m2.cart M.n v _ _ v' u'
      (fun j => ?_) (combV fun j => u₀ τ j i)).2 hc
    apply m.cart.1.hom_ext
    · refine (Category.assoc _ _ _).trans (((congrArg ((v' j).left ≫ ·) hφ).trans (hv' j)).trans ?_)
      rw [dualMapR_comp]
      exact (Category.assoc _ _ _).trans
        ((congrArg (spMap (dualMapR (algebraMap T.V T.Fr)) ≫ ·) (hv0 j).symm).trans (Category.assoc _ _ _).symm)
    · rw [Category.assoc, m2.cart.1.w, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (GlobalTheory.LieCombBaseChange.dualMap_over _).symm
  have hz : ∀ τ, z.u τ = fun i => (vA fun j => algebraMap T.V T.Fr (u₀ τ j i)).left := by
    intro τ
    funext i
    obtain ⟨u', hu1, hu2⟩ := gen τ i
    obtain ⟨w, hw, hwl⟩ := hvA (fun j => algebraMap T.V T.Fr (u₀ τ j i))
    have hw' : w.left ≫ m2.φ = (tvec (x := x') (fun j => algebraMap T.V T.Fr (u₀ τ j i))).left ≫
          pullback.fst G.G.hom (fB T.V T.Fr) := hw
    have e : u'.left = w.left := by
      apply m2.cart.1.hom_ext
      · exact hu2.trans (hw'.trans (hcomp fun j => u₀ τ j i)).symm
      · exact (Over.w u').trans ((Over.w w).trans (Category.comp_id _)).symm
    rw [hwl, ← hu1, e]
  have inj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V T.Fr
  have eigV : ∀ τ (cc : Fin M.n → T.V), IsEigAt c τ (vA fun j => algebraMap T.V T.Fr (cc j)).left ↔
      ∀ a, tmap hxc (G.act.act a) cc = χ τ a • cc := by
    intro τ cc
    rw [eigA]
    refine forall_congr' fun a => ?_
    rw [hM, ← hχ, funext_iff, funext_iff]
    refine forall_congr' fun j => ?_
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, ← map_mul]
    exact inj.eq_iff
  have mapc : ∀ τ (r : Fin (Dw.mult τ) → T.V) (cc : Fin M.n → T.V), (cc = ∑ i, r i • fun j => u₀ τ j i) →
      (fun j => algebraMap T.V T.Fr (cc j)) =
        ∑ i, algebraMap T.V T.Fr (r i) • fun j => algebraMap T.V T.Fr (u₀ τ j i) := by
    rintro τ r cc rfl
    ext j

    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
  refine ⟨fun τ i => cvV (tvec (x := xc) fun j => u₀ τ j i), fun τ i => isTan_cvV (isTan_tvec hxc _),
    fun τ i a s hs => ?_, fun τ w hw he => ?_, fun τ i => ?_⟩
  · have hs' : s = χ τ a := inj (hs.trans (hχ τ a).symm)
    subst hs'
    refine (eigV_iff hxc (G.act.act a) _ _).2 ((eigV τ _).1 ?_ a)
    have := z.eig τ i
    rw [hz τ] at this
    exact this
  · obtain ⟨cc, rfl⟩ := tan_eq_cvV hxc hw
    have hcc : ∀ a, tmap hxc (G.act.act a) cc = χ τ a • cc := fun a =>
      (eigV_iff hxc (G.act.act a) cc _).1 (he a (χ τ a) (hχ τ a))
    obtain ⟨cf, hcf, hu⟩ := z.basis τ _ (tanA _) ((eigV τ cc).2 hcc)
    rw [hz τ] at hcf hu
    obtain ⟨r, hr⟩ := int_comb (ix τ) (u₀ τ) (hcell τ) cc cf ((combA _ cf _).1 hcf)
    refine ⟨r, (comb_iff hxc (fun i j => u₀ τ j i) r cc).2 hr, fun r' h' => ?_⟩
    have h'' := (comb_iff hxc (fun i j => u₀ τ j i) r' cc).1 h'
    have e1 := hu _ ((combA _ _ _).2 (mapc τ r cc hr))
    have e2 := hu _ ((combA _ _ _).2 (mapc τ r' cc h''))
    funext i
    exact inj (congrFun (e2.trans e1.symm) i)
  · obtain ⟨u', hu1, hu2⟩ := gen τ i
    refine ⟨u'.left, hu1, ?_⟩
    rw [cvV_left]
    exact hu2

end GlobalTheory.Reg
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

noncomputable section

namespace GlobalTheory

namespace IntegralCusp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
private theorem norm_eval_le_of_isHomogeneous' {N d : ℕ} {p : MvPolynomial (Fin N) ℂ}
    (hp : p.IsHomogeneous d) (w : Fin N → ℂ) :
    ‖MvPolynomial.eval w p‖ ≤ (∑ s ∈ p.support, ‖p.coeff s‖) * ‖w‖ ^ d := by
  rw [MvPolynomial.eval_eq', Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s hs => ?_)
  rw [norm_mul, norm_prod]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hdeg : ∑ j, s j = d := by
    have := hp (MvPolynomial.mem_support_iff.mp hs)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
  calc ∏ j, ‖w j ^ s j‖ ≤ ∏ j, ‖w‖ ^ s j := by
        refine Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j _ => ?_)
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm w j) _
    _ = ‖w‖ ^ d := by rw [Finset.prod_pow_eq_pow_sum, hdeg]


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.IntegralCusp.exists_root_bound (N k m : ℕ) (cf : ℕ → MvPolynomial (Fin N) ℂ)
    (hc : ∀ i < m, (cf i).IsHomogeneous ((m - i) * k)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : Fin N → ℂ) (g : ℂ),
      g * g ^ m + ∑ i ∈ Finset.range m, (g * MvPolynomial.eval w (cf i)) * g ^ i = 0 →
        ‖g‖ ≤ C * ‖w‖ ^ k := by
  classical
  set A : ℕ → ℝ := fun i => ∑ s ∈ (cf i).support, ‖(cf i).coeff s‖ with hA
  have hA0 : ∀ i, 0 ≤ A i := fun i => Finset.sum_nonneg fun _ _ => norm_nonneg _
  set B : ℝ := 1 + ∑ i ∈ Finset.range m, A i with hBdef
  have hB1 : 1 ≤ B := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hA0 i)
  have hB0 : 0 < B := by linarith
  refine ⟨B, hB0.le, fun w g hg => ?_⟩
  by_cases hg0 : g = 0
  · rw [hg0, norm_zero]; positivity
  have hroot : g ^ m = -∑ i ∈ Finset.range m, MvPolynomial.eval w (cf i) * g ^ i := by
    have h1 : g * (g ^ m + ∑ i ∈ Finset.range m, MvPolynomial.eval w (cf i) * g ^ i) = 0 := by
      have hs : ∑ i ∈ Finset.range m, (g * MvPolynomial.eval w (cf i)) * g ^ i =
          g * ∑ i ∈ Finset.range m, MvPolynomial.eval w (cf i) * g ^ i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _
      rw [mul_add, ← hs]
      exact hg
    exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp h1).resolve_left hg0)
  set x := ‖g‖ with hx
  set t := ‖w‖ ^ k with ht
  have hx0 : 0 < x := norm_pos_iff.mpr hg0
  have ht0 : 0 ≤ t := by positivity
  by_contra hlt
  push_neg at hlt
  have htx : t ≤ x / B := by rw [le_div_iff₀ hB0]; linarith
  have hterm : ∀ i ∈ Finset.range m,
      ‖MvPolynomial.eval w (cf i) * g ^ i‖ ≤ A i * (x ^ m / B) := by
    intro i hi
    have him : i < m := Finset.mem_range.mp hi
    rw [norm_mul, norm_pow]
    have hci := norm_eval_le_of_isHomogeneous' (hc i him) w
    have hpow : ‖w‖ ^ ((m - i) * k) = t ^ (m - i) := by rw [ht, ← pow_mul, mul_comm]
    have hkey : t ^ (m - i) * x ^ i ≤ x ^ m / B := by
      have h1 : t ^ (m - i) ≤ (x / B) ^ (m - i) := pow_le_pow_left₀ ht0 htx _
      have h2 : B ≤ B ^ (m - i) := le_self_pow₀ hB1 (by omega)
      calc t ^ (m - i) * x ^ i ≤ (x / B) ^ (m - i) * x ^ i := by gcongr
        _ = x ^ m / B ^ (m - i) := by
          rw [div_pow, div_mul_eq_mul_div, ← pow_add, Nat.sub_add_cancel him.le]
        _ ≤ x ^ m / B := div_le_div_of_nonneg_left (by positivity) hB0 h2
    calc ‖MvPolynomial.eval w (cf i)‖ * x ^ i ≤ A i * t ^ (m - i) * x ^ i := by
          gcongr
          rw [← hpow]
          exact hci
      _ = A i * (t ^ (m - i) * x ^ i) := by ring
      _ ≤ A i * (x ^ m / B) := mul_le_mul_of_nonneg_left hkey (hA0 i)
  have hbound : x ^ m ≤ (∑ i ∈ Finset.range m, A i) * (x ^ m / B) := by
    calc x ^ m = ‖g ^ m‖ := by rw [norm_pow]
      _ = ‖∑ i ∈ Finset.range m, MvPolynomial.eval w (cf i) * g ^ i‖ := by rw [hroot, norm_neg]
      _ ≤ ∑ i ∈ Finset.range m, ‖MvPolynomial.eval w (cf i) * g ^ i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range m, A i * (x ^ m / B) := Finset.sum_le_sum hterm
      _ = (∑ i ∈ Finset.range m, A i) * (x ^ m / B) := by rw [Finset.sum_mul]
  have hS : ∑ i ∈ Finset.range m, A i = B - 1 := by rw [hBdef]; ring
  have hxm : 0 < x ^ m / B := by positivity
  have hBx : B * (x ^ m / B) = x ^ m := by field_simp
  rw [hS, sub_mul, _root_.one_mul, hBx] at hbound
  linarith

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.IntegralCusp.nfac_nsmul {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la la' : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r)
    (k : ℕ) (h : ∀ τ i, la' τ i = k * la τ i) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) :
    X.nfac la' x = X.nfac la x ^ k := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.nfac
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [h, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  push_cast
  ring

variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
variable {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} in
theorem _root_.GlobalTheory.IntegralCusp.laU_nsmul {σ : c.F →+* ℂ} {r : ℕ} (U : _root_.Formalism.L2.PjFree.Unf Xo c σ r)
    (a : (E →+* ℂ) × ℕ → ℕ) (n k : ℕ) (hn : Even n) (j : U.Comp) (τ : (U.X j).Ψ) (i : Fin r) :
    _root_.Formalism.L2.PjFree.laU U (k • a) (k * n) j τ i = k * _root_.Formalism.L2.PjFree.laU U a n j τ i := by
  unfold _root_.Formalism.L2.PjFree.laU
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Nat.mul_div_assoc k hn.two_dvd]
  split_ifs <;> push_cast <;> ring

def evHom {σ : c.F →+* ℂ} (y : FrPt Xo c (CAt σ))
    (hy : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y) :
    Rul Xo c →+* ℂ where
  toFun f := Formalism.L2.PjFree.toC (evR Xo c f y)
  map_one' := evalAt_one _ _ y hy
  map_mul' f g := evalAt_mul _ _ f g y
  map_zero' := evalAt_zero _ _ y
  map_add' f g := evalAt_add _ _ f g y

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
variable {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} in
theorem _root_.GlobalTheory.IntegralCusp.evHom_aeval {σ : c.F →+* ℂ} (y : _root_.Formalism.L2.Pj.FrPt Xo c (_root_.Formalism.L2.Pj.CAt σ))
    (hy : _root_.Formalism.L2.Pj.FromTest (K := c.F) (fun S _ _ => _root_.Formalism.L2.Pj.FrPt Xo c S) (fun φ y z => _root_.Formalism.L2.Pj.FrMap φ y z) y) {N : ℕ}
    (w : Fin N → _root_.Formalism.L2.Pj.Rul Xo c) (p : MvPolynomial (Fin N) c.F) :
    _root_.GlobalTheory.IntegralCusp.evHom y hy (MvPolynomial.aeval w p) =
      MvPolynomial.eval (fun i => _root_.GlobalTheory.IntegralCusp.evHom y hy (w i))
        (MvPolynomial.map σ p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.aeval_C, MvPolynomial.map_C, MvPolynomial.eval_C,
      Algebra.algebraMap_eq_smul_one]
    show _root_.Formalism.L2.PjFree.toC (_root_.Formalism.L2.Pj.evalAt _ _ (a • (1 : _root_.Formalism.L2.Pj.Rul Xo c)) y) = σ a
    rw [_root_.Formalism.L2.Pj.evalAt_smul, _root_.Formalism.L2.Pj.evalAt_one _ _ y hy, _root_.mul_one]
    rfl
  | add p q hp hq =>
    rw [map_add (MvPolynomial.aeval w), (evHom y hy).map_add,
      map_add (MvPolynomial.map σ), map_add (MvPolynomial.eval _), hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, MvPolynomial.map_X, MvPolynomial.aeval_X, MvPolynomial.eval_X]

end IntegralCusp

end GlobalTheory
end
end
