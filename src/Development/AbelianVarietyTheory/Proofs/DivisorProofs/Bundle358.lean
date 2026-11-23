module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle257
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle260
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle262
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle263
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
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
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PtClosed

theorem _root_.GlobalTheory.T.affinePointProperty_of_le_ker_app : ∀ (S : Scheme.{0}) (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop),
  (∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S) (t : Finset R'), Ideal.span (t : Set R') = ⊤ →
     (∀ r ∈ t, P (Localization.Away r) (spMap (algebraMap R' (Localization.Away r)) ≫ x)) → P R' x) →
  (∀ (V : S.Opens) (hV : IsAffineOpen V), Represents (ptQ P V hV) (killIdeal (ptQ P V hV))) →
  ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S),
    (∀ (V : S.Opens) (hV : IsAffineOpen V), killIdeal (ptQ P V hV) ≤ RingHom.ker (x.app V).hom) → P R' x := by
  first | (exact @GlobalTheory.PtClosed.of_le_ker_app) | (exact GlobalTheory.PtClosed.of_le_ker_app) | (intros; apply GlobalTheory.PtClosed.of_le_ker_app  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PtClosed

theorem _root_.GlobalTheory.T.idealKilledByRingMapsWithProperty_le_ker_app : ∀ (S : Scheme.{0}) (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop),
  (∀ (R' : Type) [CommRing R'] (R'' : Type) [CommRing R''] (g : R' →+* R'') (x : Sp R' ⟶ S),
    P R' x → P R'' (spMap g ≫ x)) →
  ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S), P R' x →
    ∀ (V : S.Opens) (hV : IsAffineOpen V), killIdeal (ptQ P V hV) ≤ RingHom.ker (x.app V).hom := by
  first | exact @GlobalTheory.PtClosed.killIdeal_le_ker_app | exact GlobalTheory.PtClosed.killIdeal_le_ker_app | (intros; apply GlobalTheory.PtClosed.killIdeal_le_ker_app; all_goals assumption)
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PtClosed

theorem _root_.GlobalTheory.T.idealRepresents_of_away_cover : ∀ (A : Type) [CommRing A] (Q : ∀ (R' : Type) [CommRing R'], (A →+* R') → Prop),
  (∀ (R' : Type) [CommRing R'] (R'' : Type) [CommRing R''] (g : R' →+* R'') (f : A →+* R'),
    Q R' f → Q R'' (g.comp f)) →
  (∀ (R' : Type) [CommRing R'] (f : A →+* R') (t : Finset R'), Ideal.span (t : Set R') = ⊤ →
    (∀ r ∈ t, Q (Localization.Away r) ((algebraMap R' (Localization.Away r)).comp f)) → Q R' f) →
  ∀ (s : Finset A), Ideal.span (s : Set A) = ⊤ →
  (∀ a ∈ s, ∃ J : Ideal (Localization.Away a),
    Represents (fun (R' : Type) [CommRing R'] (h : Localization.Away a →+* R') ↦
      Q R' (h.comp (algebraMap A (Localization.Away a)))) J) →
  ∃ J : Ideal A, Represents Q J := by
  first | exact @GlobalTheory.PtClosed.represents_of_away_cover | exact GlobalTheory.PtClosed.represents_of_away_cover | (intros; apply GlobalTheory.PtClosed.represents_of_away_cover; all_goals assumption)
end

section

open scoped IntermediateField Polynomial RatFunc

open GlobalTheory.Nef Polynomial

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

theorem ord_mul_of_ne {k F : Type} [Field k] [Field F] [Algebra k F] (v : Place k F) {x y : F} (hx : x ≠ 0)
    (hy : y ≠ 0) : ord v (x * y) = ord v x + ord v y := by
  simp only [ord, map_mul]
  rw [WithZero.log_mul ((Valuation.ne_zero_iff _).2 hx) ((Valuation.ne_zero_iff _).2 hy)]
  ring

theorem ord_zpow_of_ne {k F : Type} [Field k] [Field F] [Algebra k F] (v : Place k F) {x : F} (hx : x ≠ 0)
    (m : ℤ) : ord v (x ^ m) = m * ord v x := by
  have h0 : v.1 x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  simp only [ord, map_zpow₀]
  rw [← WithZero.exp_log h0, ← WithZero.exp_zsmul, WithZero.log_exp, WithZero.log_exp, smul_eq_mul]
  ring

theorem admissible_degree_twistFamilyAtPlaceByScalar (k F : Type) [Field k] [Field F] [Algebra k F] [IsAlgClosed k] (n : ℕ)
    (h : Place k F → Matrix (Fin n) (Fin n) F) (hh : admitted h) (v₀ : Place k F) (π : F) (hπ : π ≠ 0)
    (h1 : ord v₀ π = 1) (e : ℤ) :
    admitted (twistAt v₀ (π ^ (-e)) h) ∧ deg (twistAt v₀ (π ^ (-e)) h) = deg h - n * e := by
  classical
  have hc : π ^ (-e) ≠ 0 := zpow_ne_zero _ hπ
  have hdet : ∀ v, (twistAt v₀ (π ^ (-e)) h v).det =
      (if v = v₀ then (π ^ (-e)) ^ n else 1) * (h v).det := by
    intro v
    by_cases hv : v = v₀
    · subst hv
      rw [twistAt_self, Matrix.det_smul, Fintype.card_fin, if_pos rfl]
    · rw [twistAt_of_ne _ _ _ _ hv, if_neg hv, one_mul]
  have hord : ∀ v, ord v (twistAt v₀ (π ^ (-e)) h v).det =
      ord v (h v).det - if v = v₀ then (n : ℤ) * e else 0 := by
    intro v
    rw [hdet, ord_mul_of_ne _ (by split_ifs; exacts [pow_ne_zero _ hc, one_ne_zero]) (hh.1 v)]
    split_ifs with hv
    · subst hv
      rw [← zpow_natCast, ← zpow_mul, ord_zpow_of_ne _ hπ, h1]
      ring
    · simp [ord]
  refine ⟨⟨fun v => ?_, (hh.2.union (Set.finite_singleton v₀)).subset fun v hv => ?_⟩, ?_⟩
  · rw [hdet]
    exact mul_ne_zero (by split_ifs; exacts [pow_ne_zero _ hc, one_ne_zero]) (hh.1 v)
  · by_cases hv' : v = v₀
    · exact Or.inr hv'
    · exact Or.inl (show ¬ Unimod v (h v) from fun hu => hv (by rw [twistAt_of_ne _ _ _ _ hv']; exact hu))
  · have hfin : (Function.support fun v => ord v (h v).det).Finite := by
      refine hh.2.subset fun v hv => ?_
      intro hu
      exact hv (by simp [ord, hu.2])
    have hfin' : (Function.support fun v : Place k F => if v = v₀ then (n : ℤ) * e else 0).Finite :=
      (Set.finite_singleton v₀).subset fun v hv => by
        by_contra h'
        exact hv (if_neg h')
    rw [deg, deg, finsum_congr hord, finsum_sub_distrib hfin hfin', finsum_eq_single _ v₀ fun v hv => if_neg hv, if_pos rfl]

end GlobalTheory.Nef
end
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef Polynomial

set_option autoImplicit false

namespace GlobalTheory.Nef

theorem symMat_upperTriangular {R : Type} [CommRing R] (m : ℕ) (A : Matrix (Fin 2) (Fin 2) R) :
    (symMat m A).BlockTriangular id := by
  intro a i hia
  simp only [symMat, Matrix.of_apply]
  refine Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt ?_ hia)
  rw [← C_pow]
  refine (natDegree_mul_C_le _ _).trans ?_
  have h1 : (C (A 0 1) + C (A 1 1) * X).natDegree ≤ 1 := by compute_degree
  simpa using natDegree_pow_le_of_le (i : ℕ) h1

theorem symMat_diag {R : Type} [CommRing R] (m : ℕ) (A : Matrix (Fin 2) (Fin 2) R) (i : Fin (m + 1)) :
    symMat m A i i = A 1 1 ^ (i : ℕ) * A 0 0 ^ (m - i) := by
  simp only [symMat, Matrix.of_apply]
  rw [← C_pow, coeff_mul_C]
  congr 1
  have h1 : (C (A 0 1) + C (A 1 1) * X).natDegree ≤ 1 := by compute_degree
  have := coeff_pow_of_natDegree_le (m := (i : ℕ)) h1
  rw [mul_one] at this
  rw [this]
  simp

theorem det_symMat_of_upper {R : Type} [CommRing R] (m : ℕ) (A : Matrix (Fin 2) (Fin 2) R) (h : A 1 0 = 0) :
    (symMat m A).det = A.det ^ (m * (m + 1) / 2) := by
  rw [Matrix.det_of_upperTriangular (symMat_upperTriangular m A)]
  simp only [symMat_diag]
  rw [Matrix.det_fin_two, h, mul_zero, sub_zero]
  rw [Fin.prod_univ_eq_prod_range (fun i => A 1 1 ^ i * A 0 0 ^ (m - i)) (m + 1), Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, mul_pow, mul_comm]
  have hs : ∑ i ∈ Finset.range (m + 1), i = m * (m + 1) / 2 := by
    rw [Finset.sum_range_id]; simp [mul_comm]
  have hr : ∑ i ∈ Finset.range (m + 1), (m - i) = m * (m + 1) / 2 := by
    rw [← hs]
    exact Finset.sum_range_reflect (fun i => i) (m + 1)
  rw [hs, hr]

theorem ord_pow' {k F : Type} [Field k] [Field F] [Algebra k F] (v : Place k F) (x : F) (N : ℕ) :
    ord v (x ^ N) = (N : ℤ) * ord v x := by
  simp only [ord, map_pow, WithZero.log_pow, nsmul_eq_mul, mul_neg]

theorem unimod_symMat {k F : Type} [Field k] [Field F] [Algebra k F] (v : Place k F) (m : ℕ)
    (A : Matrix (Fin 2) (Fin 2) F) (hA : A 1 0 = 0) (hu : Unimod v A) : Unimod v (symMat m A) := by
  refine ⟨fun a i => ?_, ?_⟩
  · let A' : Matrix (Fin 2) (Fin 2) v.O := fun i j => ⟨A i j, (Valuation.mem_valuationSubring_iff _ _).2 (hu.1 i j)⟩
    have e : A'.map v.O.subtype = A := by ext i j; rfl
    rw [← e, ← symMat_map]
    exact (Valuation.mem_valuationSubring_iff _ _).1 (symMat m A' a i).2
  · rw [det_symMat_of_upper m A hA, map_pow, hu.2, one_pow]

theorem admissible_degree_symmetricPowerFamily : ∀ (k F : Type) [Field k] [IsAlgClosed k] [Field F] [Algebra k F] (m : ℕ)
    (g : Place k F → Matrix (Fin 2) (Fin 2) F), admitted g → (∀ v, g v 1 0 = 0) →
      admitted (fun v => symMat m (g v)) ∧ deg (fun v => symMat m (g v)) = ((m * (m + 1) / 2 : ℕ) : ℤ) * deg g := by
  intro k F _ _ _ _ m g hg h0
  refine ⟨⟨fun v => ?_, hg.2.subset fun v hv hu => hv (unimod_symMat v m (g v) (h0 v) hu)⟩, ?_⟩
  · rw [det_symMat_of_upper m (g v) (h0 v)]
    exact pow_ne_zero _ (hg.1 v)
  · simp only [deg, det_symMat_of_upper m _ (h0 _), ord_pow']
    rw [mul_finsum]

end GlobalTheory.Nef
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CechDR.FormExtJ

attribute [local instance] opModJ isCentralScalarJ isScalarTowerJ

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (j : ℕ)

abbrev inrJ {T : C} (x : Om R (F.obj T) j) : (omjExt F j).obj T := TrivSqZeroExt.inr x

theorem inrJ_add {T : C} (x y : Om R (F.obj T) j) : inrJ F j (x + y) = inrJ F j x + inrJ F j y :=
  TrivSqZeroExt.inr_add _ x y

theorem inrJ_sub {T : C} (x y : Om R (F.obj T) j) : inrJ F j (x - y) = inrJ F j x - inrJ F j y :=
  TrivSqZeroExt.inr_sub _ x y

theorem snd_subJ {T : C} (a b : (omjExt F j).obj T) :
    TrivSqZeroExt.snd (a - b) = TrivSqZeroExt.snd a - TrivSqZeroExt.snd b :=
  TrivSqZeroExt.snd_sub a b

theorem oneCocycle_coboundary_of_restrict_coboundary {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type}
    [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (j : ℕ)
    (hinj : Function.Injective (CoefMap.restrict (FormExtJ.omjExt F j) G).pull1)
    (κ : W1 F j) (hκ : ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''),
      κ T T'' (φ ≫ ψ) = pOm F j ψ (κ T T' φ) + κ T' T'' ψ)
    (θ' : ∀ t, Om R (F.obj (G.obj t)) j)
    (hθ' : ∀ ⦃t t' : C'⦄ (a : t ⟶ t'), κ _ _ (G.map a) = θ' t' - pOm F j (G.map a) (θ' t)) :
    ∃ θ : W0 F j, ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), κ T T' φ = θ T' - pOm F j φ (θ T) := by
  let E := omjExt F j
  let f : Z1 E := ⟨fun T T' φ ↦ inrJ F j (κ T T' φ), fun T T' T'' φ ψ ↦ by
    change inrJ F j (κ T T'' (φ ≫ ψ)) = mp E ψ (inrJ F j (κ T T' φ)) + inrJ F j (κ T' T'' ψ)
    rw [mp_omjExt_inr, hκ φ ψ, inrJ_add]⟩
  have hpull : (CoefMap.restrict E G).pull1 (H1.mk E f) = (CoefMap.restrict E G).pull1 0 := by
    rw [map_zero, CoefMap.pullCohomologyOne_class, H1.mk_eq_zero]
    refine ⟨fun t ↦ inrJ F j (θ' t), ?_⟩
    funext t t' a
    change inrJ F j (θ' t') - mp E (G.map a) (inrJ F j (θ' t)) = inrJ F j (κ _ _ (G.map a))
    rw [mp_omjExt_inr, hθ' a, inrJ_sub]
  obtain ⟨g, hg⟩ := H1.mk_eq_zero.1 (hinj hpull)
  refine ⟨fun T ↦ (g T).snd, fun T T' φ ↦ ?_⟩
  have e := congrArg TrivSqZeroExt.snd (congrFun (congrFun (congrFun hg T) T') φ)
  rw [amitsur_d0_apply, snd_subJ, snd_mp_omjExt] at e
  exact e.symm

end GlobalTheory.CechDR.FormExtJ
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

namespace GlobalTheory

theorem compat_forms_extend : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), ∀ (j : ℕ), (∀ (T : C) (x : (FormExtJ.omjExt F j).obj T), (∀ t (u : T ⟶ G.obj t), mp (FormExtJ.omjExt F j) u x = 0) → x = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → (FormExtJ.omjExt F j).obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp (FormExtJ.omjExt F j) (G.map a) (s t u)) → ∃ x : (FormExtJ.omjExt F j).obj T, ∀ t u, mp (FormExtJ.omjExt F j) u x = s t u) → (∀ η' : ∀ t, Om R (F.obj (G.obj t)) j, (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), η' t' = pOm F j (G.map a) (η' t)) → ∃ η : W0 F j, (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), η T' = pOm F j φ (η T)) ∧ ∀ t, η (G.obj t) = η' t) := by
  intro R _ C _ C' _ F G j hsep hglue η' hη'
  obtain ⟨g, hg, hgG⟩ := compat_family_extend (FormExtJ.omjExt F j) G hsep hglue
    (fun t ↦ (TrivSqZeroExt.inr (η' t) : (FormExtJ.omjExt F j).obj (G.obj t)))
    (fun t t' a ↦ by rw [FormExtJ.mp_omjExt_inr, ← hη' a])
  refine ⟨fun T ↦ (g T).snd, fun T T' φ ↦ ?_, fun t ↦ ?_⟩
  · show (g T').snd = pOm F j φ (g T).snd
    rw [hg φ, FormExtJ.snd_mp_omjExt]
  · show (g (G.obj t)).snd = η' t
    rw [hgG t]
    rfl

end GlobalTheory
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.SepCech

theorem ringCocone_isColimit (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] :
    Nonempty (IsColimit (ringCocone K Ω)) := by
  haveI : ReflectsColimitsOfShape (FinSub K Ω) (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine ⟨isColimitOfReflects (forget CommRingCat.{0}) ?_⟩
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro x
    change Ω at x
    have hx : _root_.IsIntegral K x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    haveI := IntermediateField.adjoin.finiteDimensional hx
    exact ⟨⟨IntermediateField.adjoin K {x}, inferInstance⟩,
      ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩, rfl⟩
  · intro i j xi xj h
    refine ⟨⟨i.1 ⊔ j.1, by haveI := i.2; haveI := j.2; infer_instance⟩,
      homOfLE (le_sup_left (a := i.1)), homOfLE (le_sup_right (b := j.1)), ?_⟩
    apply Subtype.ext
    exact h

end GlobalTheory.SepCech
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.SepCech

theorem isLimit_leftFunc_arrCone (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    (hc : IsColimit (ringCocone K Ω)) :
    Nonempty (IsLimit (Arrow.leftFunc.mapCone (arrCone K Ω))) :=
  ⟨isLimitOfPreserves (Scheme.Spec ⋙ yoneda) hc.op⟩

end GlobalTheory.SepCech
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.CoindRetract

variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)

def adj : restr φ ⊣ coind φ :=
  Adjunction.restrictFullyFaithful
    ((ModuleCat.restrictCoextendScalarsAdj.{1, 1, 1} (liftHom φ)).whiskerRight (Scheme.{0}ᵒᵖ))
    (fullyFaithfulSheafToPresheaf _ _) (fullyFaithfulSheafToPresheaf _ _) (Iso.refl _) (Iso.refl _)

instance restr_faithful : (restr φ).Faithful :=
  show (sheafCompose (Scheme.etaleTopology.{0}) (ModuleCat.restrictScalars.{1} (liftHom φ))).Faithful from inferInstance

instance coind_preservesMono : (coind φ).PreservesMonomorphisms := by
  haveI : (coind φ).IsRightAdjoint := (adj φ).isRightAdjoint
  infer_instance

theorem coind_retract (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (I : Shv S) [Injective I] :
    ∃ (J : Shv R) (_ : Injective J) (i : I ⟶ (coind φ).obj J) (r : (coind φ).obj J ⟶ I), i ≫ r = 𝟙 I := by
  let J := Injective.under ((restr φ).obj I)
  let i : I ⟶ (coind φ).obj J := (adj φ).unit.app I ≫ (coind φ).map (Injective.ι ((restr φ).obj I))
  haveI : Mono i := mono_comp _ _
  exact ⟨J, inferInstance, i, Injective.factorThru (𝟙 I) i, Injective.comp_factorThru _ _⟩

end GlobalTheory.EtC.CoindRetract
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.EtC

variable {R : Type} [CommRing R]

instance (M : (ModuleCat.{1} (ULift.{1} R))ᵒᵖ) :
    ((linearCoyoneda (ULift.{1} R) (ModuleCat.{1} (ULift.{1} R))).obj M).IsRightAdjoint :=
  (ihom.adjunction M.unop).isRightAdjoint

def homSh (J : Shv R) : (ModuleCat.{1} (ULift.{1} R))ᵒᵖ ⥤ Shv R where
  obj M := (sheafCompose _ ((linearCoyoneda (ULift.{1} R) (ModuleCat.{1} (ULift.{1} R))).obj M)).obj J
  map f := (sheafCompose_map _ ((linearCoyoneda (ULift.{1} R) (ModuleCat.{1} (ULift.{1} R))).map f)).app J
  map_id M := by ext; simp
  map_comp f g := by ext; simp

instance (J : Shv R) : (homSh J).Additive where
  map_add {M N f g} := by
    ext U x
    exact Preadditive.add_comp _ _ _ f.unop g.unop x

variable {S : Type} [CommRing S]

def scalarsMod (φ : R →+* S) : ModuleCat.{1} (ULift.{1} R) :=
  (ModuleCat.restrictScalars.{1} (liftHom φ)).obj (ModuleCat.of (ULift.{1} S) (ULift.{1} S))

abbrev scalarsRes (φ : R →+* S) : ProjectiveResolution (scalarsMod φ) := projectiveResolution (scalarsMod φ)

def coindCx (φ : R →+* S) (J : Shv R) : CochainComplex (Shv R) ℕ :=
  CochainComplex.of (fun n => (homSh J).obj (op ((scalarsRes φ).complex.X n)))
    (fun n => (homSh J).map ((scalarsRes φ).complex.d (n + 1) n).op) (fun n => by
      rw [← Functor.map_comp, ← op_comp, HomologicalComplex.d_comp_d, op_zero, Functor.map_zero])

theorem coindCx_d (φ : R →+* S) (J : Shv R) (n : ℕ) :
    (coindCx φ J).d n (n + 1) = (homSh J).map ((scalarsRes φ).complex.d (n + 1) n).op :=
  by simp [coindCx]

abbrev homOfLin {A B : ModuleCat.{1} (ULift.{1} R)} (f : A →ₗ[ULift.{1} R] B) : A ⟶ B := ModuleCat.ofHom f

def coindToHom (φ : R →+* S) (J : Shv R) : (restr φ).obj ((coind φ).obj J) ⟶ (homSh J).obj (op (scalarsMod φ)) :=
  ⟨{ app := fun U => homOfLin
      { toFun := fun (g : (ModuleCat.coextendScalars.{1, 1, 1} (liftHom φ)).obj (J.obj.obj U)) =>
          homOfLin (ModuleCat.CoextendScalars.equiv (liftHom φ) _ g)
        map_add' := fun _ _ => rfl
        map_smul' := fun r g => by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          exact (congrArg (ModuleCat.CoextendScalars.equiv (liftHom φ) _ g) (mul_comm (show ULift.{1} S from x) (liftHom φ r))).trans
            ((ModuleCat.CoextendScalars.equiv (liftHom φ) _ g).map_smul r x) }
     naturality := fun _ _ _ => rfl }⟩

theorem etaleCoinductionAugmentation_comp_d_eq_zero (φ : R →+* S) (J : Shv R) :
    coindToHom φ J ≫ (homSh J).map ((scalarsRes φ).π.f 0 ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 (scalarsMod φ)).hom).op ≫
      (homSh J).map ((scalarsRes φ).complex.d (0 + 1) 0).op = 0 := by
  rw [← Functor.map_comp, ← op_comp, ProjectiveResolution.complex_d_comp_π_f_zero_assoc,
    zero_comp, op_zero, Functor.map_zero, comp_zero]

def coindAug (φ : R →+* S) (J : Shv R) :
    (CochainComplex.single₀ (Shv R)).obj ((restr φ).obj ((coind φ).obj J)) ⟶ coindCx φ J :=
  HomologicalComplex.mkHomFromSingle (coindToHom φ J ≫ (homSh J).map
    ((scalarsRes φ).π.f 0 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 (scalarsMod φ)).hom).op) (by
    rintro k rfl
    rw [coindCx_d]
    exact (Category.assoc _ _ _).trans (etaleCoinductionAugmentation_comp_d_eq_zero φ J))

theorem coindAug_f_zero (φ : R →+* S) (J : Shv R) :
    (coindAug φ J).f 0 = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 _).hom ≫ coindToHom φ J ≫
      (homSh J).map ((scalarsRes φ).π.f 0 ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 (scalarsMod φ)).hom).op :=
  HomologicalComplex.mkHomFromSingle_f _ _

end GlobalTheory.EtC
end
end
