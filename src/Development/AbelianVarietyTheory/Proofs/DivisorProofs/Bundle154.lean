module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle118
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle003
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Normed
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

section

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Cw2a

theorem coefM_apply_eq_coeff {n L : ℕ} (k : ℕ) (s : PolyM n L) :
    coefM n L k s = (optionEquivLeft ℂ (Fin L ⊕ EntIdx n) s).coeff k := by
  simp only [coefM, LinearMap.comp_apply, LinearMap.restrictScalars_apply, AlgEquiv.toLinearMap_apply,
    Polynomial.lcoeff_apply]

theorem dMu_eq_extDerivation {n L : ℕ} (ε : Fin n → Bool) (x : Mode ε) :
    dMu L ε x = mkDerivation ℂ (fun w : Option (Fin L ⊕ EntIdx n) => match w with
      | none => (0 : MvPolynomial (Option (Fin L ⊕ EntIdx n)) ℂ)
      | some v => rename some (dL L ε x (X v))) := by
  unfold dMu
  refine congrArg _ (funext fun w => ?_)
  cases w with
  | none => rfl
  | some v => simp only [inM]

theorem coefM_dMu : T_coefM_dMu := by
  intro n L ε x k s
  have h := GlobalTheory.coeff_optionEquivLeft_extDerivation (dL L ε x) k s
  rw [coefM_apply_eq_coeff, coefM_apply_eq_coeff, ← h]
  have e : dMu L ε x = mkDerivation ℂ (fun w : Option (Fin L ⊕ EntIdx n) => match w with
      | none => (0 : MvPolynomial (Option (Fin L ⊕ EntIdx n)) ℂ)
      | some v => rename some (dL L ε x (X v))) := dMu_eq_extDerivation ε x
  refine congrArg (fun D : Derivation ℂ (PolyM n L) (PolyM n L) => (optionEquivLeft ℂ (Fin L ⊕ EntIdx n) (D s)).coeff k) (e.trans ?_)
  refine congrArg _ (funext fun w => ?_)
  cases w <;> rfl

end GlobalTheory.PsCo.Cw2a
end

section

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Cw2a

theorem t_exL_dual : T_exL_dual := by
  intro n L m a
  exact GlobalTheory.coeff_allOnes_prod_one_add_mul (σ := EntIdx n) m a

end GlobalTheory.PsCo.Cw2a
end

section

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Cw2a

theorem t_coefM_pderiv : T_coefM_pderiv := by
  intro n L k s
  simp only [coefM, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
    Polynomial.lcoeff_apply, AlgEquiv.toLinearMap_apply]
  exact GlobalTheory.optionEquivLeft_pderiv_none_coeff k s

end GlobalTheory.PsCo.Cw2a
end

section

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Cw2a

theorem t_dual_prod : T_dual_prod := by
  intro A _ _ D L la m J hD hsq
  exact GlobalTheory.dualProd_logDeriv_modSq (K := ℂ) D la m J hD hsq

end GlobalTheory.PsCo.Cw2a
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators

namespace GlobalTheory.QFam


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
theorem _root_.GlobalTheory.QFam.hasQ_coeff_iff_hasQExpansion (N : ℕ) (f : ℍ → ℂ) (φ : PowerSeries ℂ) :
    _root_.GlobalTheory.QFam.HasQ N f (fun n => PowerSeries.coeff n φ) ↔
      _root_.GlobalTheory.HasQExpansion (N : ℝ) f φ := by
  rw [_root_.GlobalTheory.QFam.hasQ_iff]
  unfold _root_.GlobalTheory.HasQExpansion
  simp only [Function.Periodic.qParam, Complex.ofReal_natCast]

end GlobalTheory.QFam
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam

theorem HasQ.coeff_unique {N : ℕ} {f : ℍ → ℂ} {a b : ℕ → ℂ} (hN : 0 < N) (ha : HasQ N f a)
    (hb : HasQ N f b) : a = b := by
  have toSeries : ∀ c : ℕ → ℂ, HasQ N f c → GlobalTheory.HasQExpansion (N : ℝ) f (PowerSeries.mk c) := by
    intro c hc τ
    have hs := (hasQ_iff N f c).1 hc τ
    simpa [PowerSeries.coeff_mk, Function.Periodic.qParam] using hs
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hab := GlobalTheory.HasQExpansion.unique hN' (toSeries a ha) (toSeries b hb)
  funext n
  simpa using congrArg (PowerSeries.coeff n) hab

theorem HasQ.fun_unique {N : ℕ} {f g : ℍ → ℂ} {a : ℕ → ℂ} (hf : HasQ N f a) (hg : HasQ N g a) :
    f = g := by
  funext τ
  exact (hf τ).unique (hg τ)

theorem hasQ_unique_both :
    (∀ (N : ℕ) (f : ℍ → ℂ) (a b : ℕ → ℂ), 0 < N → HasQ N f a → HasQ N f b → a = b) ∧
    (∀ (N : ℕ) (f g : ℍ → ℂ) (a : ℕ → ℂ), HasQ N f a → HasQ N g a → f = g) :=
  ⟨fun _ _ _ _ hN ha hb => HasQ.coeff_unique hN ha hb, fun _ _ _ _ hf hg => HasQ.fun_unique hf hg⟩

end GlobalTheory.QFam
end

section

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.SmChart

open MvPolynomial

noncomputable def subst {O : Type} [CommRing O] (ϖ : O) (n : ℕ) (i : Fin (n + 1)) : MvPolynomial (Fin n) O :=
  Fin.cases (C ϖ) (fun j => X j) i

theorem prod_lt_one {O : Type} [CommRing O] (n : ℕ) :
    (∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => (i : ℕ) < 1), (X i : MvPolynomial (Fin (n + 1)) O)) = X 0 := by
  have : Finset.univ.filter (fun i : Fin (n + 1) => (i : ℕ) < 1) = {0} := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h; exact Fin.ext (by simpa using h)
    · rintro rfl; simp
  rw [this, Finset.prod_singleton]

noncomputable abbrev gen {O : Type} [CommRing O] (ϖ : O) (n : ℕ) : Ideal (MvPolynomial (Fin (n + 1)) O) :=
  Ideal.span {X 0 - C ϖ}

theorem subst_vanish {O : Type} [CommRing O] (ϖ : O) (n : ℕ) :
    ∀ a ∈ gen ϖ n, (aeval (subst ϖ n)).toRingHom a = 0 := by
  intro a ha
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  simp [subst, algebraMap_eq]

noncomputable def quotMap {O : Type} [CommRing O] (ϖ : O) (n : ℕ) :
    (MvPolynomial (Fin (n + 1)) O ⧸ gen ϖ n) →+* MvPolynomial (Fin n) O :=
  Ideal.Quotient.lift _ (aeval (subst ϖ n)).toRingHom (subst_vanish ϖ n)

noncomputable def quotInv {O : Type} [CommRing O] (ϖ : O) (n : ℕ) :
    MvPolynomial (Fin n) O →+* (MvPolynomial (Fin (n + 1)) O ⧸ gen ϖ n) :=
  (Ideal.Quotient.mk _).comp (rename Fin.succ).toRingHom

theorem quotMap_mk {O : Type} [CommRing O] (ϖ : O) (n : ℕ) (a : MvPolynomial (Fin (n + 1)) O) :
    quotMap ϖ n (Ideal.Quotient.mk _ a) = aeval (subst ϖ n) a := rfl

theorem quotMap_quotInv {O : Type} [CommRing O] (ϖ : O) (n : ℕ) :
    (quotMap ϖ n).comp (quotInv ϖ n) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [quotInv, quotMap_mk]
  · intro i
    simp [quotInv, quotMap_mk, subst]

theorem quotInv_quotMap {O : Type} [CommRing O] (ϖ : O) (n : ℕ) :
    (quotInv ϖ n).comp (quotMap ϖ n) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [quotInv, quotMap_mk]
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [RingHom.comp_apply, quotMap_mk, aeval_X, subst, Fin.cases_zero, RingHom.id_apply]
      simp only [quotInv, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, rename_C]
      rw [Ideal.Quotient.eq]
      rw [← neg_sub]; exact neg_mem (Ideal.subset_span rfl)
    · simp [quotInv, quotMap_mk, subst]

theorem quotMap_bijective {O : Type} [CommRing O] (ϖ : O) (n : ℕ) : Function.Bijective (quotMap ϖ n) :=
  ⟨Function.LeftInverse.injective (g := quotInv ϖ n) (fun a => congr($(quotInv_quotMap ϖ n) a)),
    Function.RightInverse.surjective (g := quotInv ϖ n) (fun a => congr($(quotMap_quotInv ϖ n) a))⟩

theorem quotMap_algebraMap {O : Type} [CommRing O] (ϖ : O) (n : ℕ) :
    (quotMap ϖ n).comp (algebraMap O _) = C := by
  refine RingHom.ext fun c => ?_
  change quotMap ϖ n (Ideal.Quotient.mk _ (C c)) = C c
  rw [quotMap_mk, aeval_C, algebraMap_eq]

end GlobalTheory.SmChart


open GlobalTheory.SmChart in
theorem GlobalTheory.SSG.chartAt_of_smooth : ∀ (O : Type) [CommRing O] (ϖ : O) (X : Scheme.{0})
    (p : X ⟶ Spec (CommRingCat.of O)) (V : X.Opens) (x : X), x ∈ V → Smooth (V.ι ≫ p) →
    GlobalTheory.SSG.ChartAt ϖ p x := by
  intro O _ ϖ X p V x hx hsm
  set f := V.ι ≫ p with hf
  let x' : V.toScheme := ⟨x, hx⟩
  obtain ⟨W, hW, hxW, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp V.toScheme.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top x')
  have hW : IsAffineOpen W := hW
  have e : W ≤ f ⁻¹ᵁ ⊤ := fun _ _ => trivial
  have hφ : (f.appLE ⊤ W e).hom.Smooth := f.smooth_appLE (isAffineOpen_top _) hW e
  rw [RingHom.smooth_iff_locally_isStandardSmooth,
    RingHom.locally_iff_isLocalization RingHom.isStandardSmooth_respectsIso] at hφ
  obtain ⟨s, hs, hfs⟩ := hφ
  have hs' := iSup_basicOpen_of_span_eq_top W (s : Set Γ(V.toScheme, W)) hs
  have hmem : x' ∈ (⨆ i ∈ (s : Set Γ(V.toScheme, W)), V.toScheme.basicOpen i) := hs'.symm ▸ hxW
  obtain ⟨r, hr, hxr⟩ : ∃ r ∈ s, x' ∈ V.toScheme.basicOpen r := by simpa using hmem
  have hW' : IsAffineOpen (V.toScheme.basicOpen r) := hW.basicOpen r
  have e' : V.toScheme.basicOpen r ≤ f ⁻¹ᵁ ⊤ := fun _ _ => trivial
  haveI : IsLocalization.Away r Γ(V.toScheme, V.toScheme.basicOpen r) := hW.isLocalization_basicOpen r
  have hst : (f.appLE ⊤ _ e').hom.IsStandardSmooth := by
    rw [← f.appLE_map e (homOfLE (V.toScheme.basicOpen_le r)).op]
    exact hfs r hr _
  obtain ⟨n, g, hgC, hg⟩ := RingHom.IsStandardSmooth.exists_etale_mvPolynomial hst
  let c : O →+* Γ(Spec (CommRingCat.of O), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom
  have hc : Function.Bijective c := (Scheme.ΓSpecIso (CommRingCat.of O)).symm.commRingCatIsoToRingEquiv.bijective
  let k := V.ι.appIso (V.toScheme.basicOpen r)
  have hk : Function.Bijective k.inv.hom := k.symm.commRingCatIsoToRingEquiv.bijective
  have hU : IsAffineOpen (V.ι ''ᵁ V.toScheme.basicOpen r) := hW'.image_of_isOpenImmersion V.ι
  have hxU : x ∈ V.ι ''ᵁ V.toScheme.basicOpen r := ⟨x', hxr, rfl⟩
  have hcomp : p.appLE ⊤ (V.ι ''ᵁ V.toScheme.basicOpen r) le_top ≫ k.hom = f.appLE ⊤ _ e' := by
    have h1 := Scheme.Hom.appLE_comp_appLE V.ι p ⊤ (V.ι ''ᵁ V.toScheme.basicOpen r) (V.toScheme.basicOpen r)
      le_top (V.ι.preimage_image_eq _).ge
    have h2 : k.hom = V.ι.appLE _ _ (V.ι.preimage_image_eq _).ge := by
      rw [Scheme.Hom.appIso_hom, Scheme.Hom.appLE]; rfl
    rw [h2]; exact h1
  refine ⟨_, hU, hxU, n + 1, 1, le_rfl, by omega, ?_⟩
  rw [prod_lt_one]
  refine ⟨k.inv.hom.comp (g.comp ((MvPolynomial.map c).comp (quotMap ϖ n))), ?_, ?_⟩
  · exact RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.stableUnderComposition _ _
        (RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective (quotMap_bijective ϖ n))
          (RingHom.Etale.of_bijective ⟨MvPolynomial.map_injective _ hc.1, MvPolynomial.map_surjective _ hc.2⟩))
        hg) (RingHom.Etale.of_bijective hk)
  · refine RingHom.ext fun a => ?_
    change k.inv.hom (g (MvPolynomial.map c (quotMap ϖ n (algebraMap O _ a)))) =
      (p.appLE ⊤ (V.ι ''ᵁ V.toScheme.basicOpen r) le_top).hom (c a)
    rw [show quotMap ϖ n (algebraMap O _ a) = MvPolynomial.C a from congr($(quotMap_algebraMap ϖ n) a),
      MvPolynomial.map_C, show g (MvPolynomial.C (c a)) = (f.appLE ⊤ _ e').hom (c a) from congr($hgC (c a)),
      ← hcomp]
    simp
end

section

open MvPolynomial
open scoped ContDiff
open GlobalTheory.PsCo.Pc1

noncomputable section

namespace GlobalTheory.PsCo.Pc1.B

theorem sb_derivcut (H : ℝ → ℝ) (hH : IsCutFn H) : IsCutFn (deriv H) := by
  obtain ⟨hc, R, hR⟩ := hH
  refine ⟨(contDiff_infty_iff_deriv.1 hc).2, R + 1, fun x hx => ?_⟩
  have h : H =ᶠ[nhds x] fun _ => (0 : ℝ) := by
    filter_upwards [Ioi_mem_nhds (show R < x by linarith)] with y hy
    exact hR y (le_of_lt hy)
  rw [h.deriv_eq]
  simp

theorem sb_evrp {n : ℕ} (ε : Fin n → Bool) (g : Mat n) : ev g (rP ε) = ((rM ε g : ℝ) : ℂ) := by

  simp only [rP, rM, map_sum, map_mul, ev, eval_X, Sum.elim_inl, Sum.elim_inr]
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem sb_degmono {n : ℕ} (ε : Fin n → Bool) (Z : Mat n) (s : _) (a : ℂ) :
    (dZ ε Z (monomial s a)).totalDegree ≤ (monomial s a).totalDegree := by
  refine induction_on_monomial (motive := fun p => (dZ ε Z p).totalDegree ≤ p.totalDegree) ?_ ?_ s a
  · intro a
    have : dZ ε Z (C a) = 0 := by
      rw [← MvPolynomial.algebraMap_eq]; exact (dZ ε Z).map_algebraMap a
    rw [this]; simp
  · intro p v ih
    by_cases hp : p = 0
    · simp [hp]
    rw [Derivation.leibniz, totalDegree_mul_of_isDomain hp (X_ne_zero v), totalDegree_X, smul_eq_mul, smul_eq_mul]
    refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · refine (totalDegree_mul _ _).trans (add_le_add le_rfl ?_)
      simp only [dZ, mkDerivation_X]
      cases v with
      | inl x =>
        simp only [Sum.elim_inl]
        refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun c _ => ?_)
        refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
        · exact (totalDegree_mul _ _).trans (by simp)
        · exact (totalDegree_mul _ _).trans (by simp)
      | inr x =>
        simp only [Sum.elim_inr]
        refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun c _ => ?_)
        refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
        · exact (totalDegree_mul _ _).trans (by simp)
        · exact (totalDegree_mul _ _).trans (by simp)
    · refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_X]
      omega

theorem sb_degdz {n : ℕ} (ε : Fin n → Bool) (Z : Mat n) (P : Poly n) :
    (dZ ε Z P).totalDegree ≤ P.totalDegree := by
  conv_lhs => rw [P.as_sum]

  rw [map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun m hm => ?_)
  refine (sb_degmono ε Z m _).trans ?_
  exact (totalDegree_monomial_le _ _).trans (le_totalDegree hm)

theorem sb_degrp {n : ℕ} (ε : Fin n → Bool) : (rP ε : Poly n).totalDegree ≤ 2 := by
  unfold rP
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun c _ => ?_)
  refine (totalDegree_mul _ _).trans ?_
  simp

theorem sb_evderiv {σ : Type} (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) (γ : ℝ → σ → ℂ) (s : ℝ)
    (hγ : ∀ v, HasDerivAt (fun u => γ u v) (MvPolynomial.eval (γ s) (D (MvPolynomial.X v))) s) (P : MvPolynomial σ ℂ) :
    HasDerivAt (fun u => MvPolynomial.eval (γ u) P) (MvPolynomial.eval (γ s) (D P)) s := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have : D (C a) = 0 := by
      rw [← MvPolynomial.algebraMap_eq]; exact D.map_algebraMap a
    simp only [this, eval_C, map_zero]
    exact hasDerivAt_const _ _
  | add p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  | mul_X p v hp =>
    have h := hp.fun_mul (hγ v)
    simp only [map_mul, eval_X]
    refine h.congr_deriv ?_
    rw [Derivation.leibniz, map_add (f := _), smul_eq_mul, smul_eq_mul, map_mul, map_mul, eval_X]
    ring

theorem sb_curve {n : ℕ} (Z g : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (a b : Fin n) :
    HasDerivAt (fun u : ℝ => (NormedSpace.exp (-((u : ℂ) • Z)) * g * NormedSpace.exp ((u : ℂ) • Z)) a b)
      (((NormedSpace.exp (-((s : ℂ) • Z)) * g * NormedSpace.exp ((s : ℂ) • Z)) * Z -
        Z * (NormedSpace.exp (-((s : ℂ) • Z)) * g * NormedSpace.exp ((s : ℂ) • Z))) a b) s := by
  let : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  let : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have h1 : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • (-Z))) (NormedSpace.exp (s • (-Z)) * (-Z)) s :=
    hasDerivAt_exp_smul_const _ _
  have h2 : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • Z)) (NormedSpace.exp (s • Z) * Z) s :=
    hasDerivAt_exp_smul_const _ _
  have h3 := (h1.mul_const g).mul h2
  have hc : Commute Z (NormedSpace.exp (s • Z)) := ((Commute.refl Z).smul_right s).exp_right
  have hc' : Commute (-Z) (NormedSpace.exp (s • (-Z))) := ((Commute.refl (-Z)).smul_right s).exp_right
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ := (Matrix.entryLinearMap ℝ ℂ a b).toContinuousLinearMap
  have h4 := L.hasFDerivAt.comp_hasDerivAt s h3
  simp only [Function.comp_def] at h4
  have e : ∀ u : ℝ, (u : ℂ) • Z = u • Z := fun u => by simp
  simp only [e, smul_neg] at *
  refine HasDerivAt.congr_deriv (f := fun u : ℝ => (NormedSpace.exp (-(u • Z)) * g * NormedSpace.exp (u • Z)) a b) h4 ?_
  show (NormedSpace.exp (-(s • Z)) * -Z * g * NormedSpace.exp (s • Z) +
        NormedSpace.exp (-(s • Z)) * g * (NormedSpace.exp (s • Z) * Z)) a b = _
  have hm : NormedSpace.exp (-(s • Z)) * -Z * g * NormedSpace.exp (s • Z) +
        NormedSpace.exp (-(s • Z)) * g * (NormedSpace.exp (s • Z) * Z) =
      NormedSpace.exp (-(s • Z)) * g * NormedSpace.exp (s • Z) * Z -
        Z * (NormedSpace.exp (-(s • Z)) * g * NormedSpace.exp (s • Z)) := by
    rw [← hc'.eq]; noncomm_ring
  rw [hm]

theorem sb_evcurve {n : ℕ} (ε : Fin n → Bool) (Z g : Mat n) (s : ℝ) (P : Poly n) (hZ : LieU ε Z) :
    HasDerivAt (fun u : ℝ => ev (NormedSpace.exp (-((u : ℂ) • Z)) * g * NormedSpace.exp ((u : ℂ) • Z)) P) (ev (NormedSpace.exp (-((s : ℂ) • Z)) * g * NormedSpace.exp ((s : ℂ) • Z)) (dZ ε Z P)) s := by
  refine sb_evderiv (dZ ε Z)
    (fun u : ℝ => Sum.elim (fun x : Fin n × Fin n => (NormedSpace.exp (-((u : ℂ) • Z)) * g * NormedSpace.exp ((u : ℂ) • Z)) x.1 x.2) (fun x => star ((NormedSpace.exp (-((u : ℂ) • Z)) * g * NormedSpace.exp ((u : ℂ) • Z)) x.1 x.2))) s ?_ P
  have hZ' : ∀ a b, barM ε Z a b = (starRingEnd ℂ) (Z a b) := fun a b => (hZ a b).symm
  rintro (x | x)
  · refine (sb_curve Z g s x.1 x.2).congr_deriv ?_
    simp [dZ, mkDerivation_X, Matrix.mul_apply, Matrix.sub_apply, Finset.sum_sub_distrib]
  · refine (sb_curve Z g s x.1 x.2).star.congr_deriv ?_
    simp [dZ, mkDerivation_X, Matrix.mul_apply, Matrix.sub_apply, Finset.sum_sub_distrib, hZ', star_sum, star_mul']

theorem cutoffPolynomial_conjugation_deriv_mem_shapeSpan : StBasDeriv := by
  intro n ε Z H P hZ hH
  refine ⟨?_, fun g s => ?_⟩
  · have h1 : bas ε (deriv H) (dZ ε Z (rP ε) * P) ∈ ShapeM ε (P.totalDegree + 2) := by
      refine Submodule.subset_span ⟨deriv H, _, sb_derivcut H hH, ?_, rfl⟩
      have := (sb_degdz ε Z (rP ε)).trans (sb_degrp ε)
      exact (totalDegree_mul _ _).trans (by omega)
    have h2 : bas ε H (dZ ε Z P) ∈ ShapeM ε (P.totalDegree + 2) := by
      refine Submodule.subset_span ⟨H, _, hH, ?_, rfl⟩
      exact (sb_degdz ε Z P).trans (by omega)
    have e : adBas ε Z H P = bas ε (deriv H) (dZ ε Z (rP ε) * P) + bas ε H (dZ ε Z P) := rfl
    rw [e]
    exact Submodule.add_mem _ h1 h2
  · have hE := sb_evcurve ε Z g s (rP ε) hZ
    simp only [sb_evrp] at hE
    obtain ⟨c, hc⟩ : ∃ c, c = ev (NormedSpace.exp (-((s : ℂ) • Z)) * g * NormedSpace.exp ((s : ℂ) • Z)) (dZ ε Z (rP ε)) := ⟨_, rfl⟩
    rw [← hc] at hE
    have hre : HasDerivAt (fun u : ℝ => rM ε (NormedSpace.exp (-((u : ℂ) • Z)) * g * NormedSpace.exp ((u : ℂ) • Z))) c.re s := by
      have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hE
      simpa [Function.comp_def] using this
    have him : c.im = 0 := by
      have h1 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hE
      simp [Function.comp_def] at h1
      exact h1.unique (hasDerivAt_const _ _)
    have hcre : ((c.re : ℝ) : ℂ) = c := Complex.ext (by simp) (by simp [him])
    have hHd : HasDerivAt H (deriv H (rM ε (NormedSpace.exp (-((s : ℂ) • Z)) * g * NormedSpace.exp ((s : ℂ) • Z)))) (rM ε (NormedSpace.exp (-((s : ℂ) • Z)) * g * NormedSpace.exp ((s : ℂ) • Z))) :=
      ((hH.1.differentiable (by simp)) _).hasDerivAt
    have hcomp := (hHd.comp s hre).ofReal_comp
    have hP := sb_evcurve ε Z g s P hZ
    have htot := hcomp.fun_mul hP
    refine htot.congr_deriv ?_
    simp only [adBas, bas, map_mul, ← hc, Function.comp_apply]
    rw [← hcre]
    simp only [Complex.ofReal_re, Complex.ofReal_mul]
    ring

end GlobalTheory.PsCo.Pc1.B
end
end
