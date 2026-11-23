module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle031
public import Development.EtaleCohomology.KummerTheory.CupAWCutEv
import Development.EtaleCohomology.KummerTheory.Bundle015
public import Development.EtaleCohomology.TateTwists.Bundle013
public import Mathlib.Order.CompletePartialOrder
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Cl.DiscNrmPf

def up {P : PSh} {U : Scheme.{0}} {p q : ℕ} (x : Sx (disc.obj P) p U) : Sx (disc.obj P) q U := x

theorem face_disc {P : PSh} {U : Scheme.{0}} {p : ℕ} (x : Sx (disc.obj P) (p + 1) U) (i : Fin (p + 2)) :
    ((disc.obj P).δ i).app (op U) x = up x := rfl

open LateralTheory.KummerTheory.AW in
theorem normal (R : Type) [CommRing R] (I : Cx R) (P : PSh) (n : ℤ) (α : Cocycle ((chains R).obj (disc.obj P)) I n) :
    ∃ β : Cochain ((chains R).obj (disc.obj P)) I (n - 1), ∀ p s h U y,
      ev (R := R) (α.1 - δ (n - 1) n β) (p + 1) s h U y = 0 := by
  have hα : δ n (n + 1) α.1 = 0 := (Cocycle.mem_iff n (n + 1) rfl α.1).1 α.2
  have hEval {k : ℤ} (γ : Cochain ((chains R).obj (disc.obj P)) I k) (p : ℕ) (s : ℤ)
      (h : -(p : ℤ) + k = s) (U : Scheme.{0}) (x : Sx (disc.obj P) p U) :
      ev (R := R) γ p s h U x = Sec.map ((chainsXIso R (disc.obj P) p).inv ≫ γ.v _ _ h) (freeGen R P U x) := rfl
  have hD {k l : ℤ} (hkl : k + 1 = l) (γ : Cochain ((chains R).obj (disc.obj P)) I k)
      (U : Scheme.{0}) (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + k = s)
      (ht : -((p + 1 : ℕ) : ℤ) + l = t) (x : Sx (disc.obj P) (p + 1) U) :
      ev (R := R) (δ k l γ) (p + 1) t ht U x = Sec.map (I.d s t) (ev (R := R) γ (p + 1) s hs U x) +
        l.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
          ev (R := R) γ p t (by omega) U (((disc.obj P).δ i).app (op U) x) := by
    rw [hEval, δ_v k l hkl γ _ _ ht s (-(p : ℤ)) (by omega) (by omega), Preadditive.comp_add,
      Linear.comp_units_smul, reassoc_of% (LateralTheory.KummerTheory.chains_d R (disc.obj P) p),
      Preadditive.sum_comp, sec_map_add]
    congr 1
    rw [Units.smul_def, Units.smul_def, sec_map_zsmul, sec_map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Preadditive.zsmul_comp, sec_map_zsmul, hEval]
    congr 1
    exact congrArg (Sec.map ((chainsXIso R (disc.obj P) p).inv ≫ γ.v (-(p : ℤ)) t (by omega)))
      (map_freeGen ((disc.obj P).δ i) U x)
  let a (p : ℕ) (s : ℤ) (h : -(p : ℤ) + (n - 1) = s) (U : Scheme.{0}) (x : Sx (disc.obj P) p U) : Sec (I.X s) U :=
    if Odd p then n.negOnePow • ev (R := R) α.1 (p + 1) s (by push_cast; omega) U (up x) else 0
  have hex (p : ℕ) (s : ℤ) (h : -(p : ℤ) + (n - 1) = s) :
      ∃ φ : (free R).obj P ⟶ I.X s, ∀ U x, Sec.map φ (freeGen R P U x) = a p s h U x :=
    LateralTheory.EtaleFoundations.EvMkPf.free_hom_exists R P (I.X s) (a p s h) (by
      intro V U g x
      dsimp only [a]
      split_ifs
      · rw [Units.smul_def, Units.smul_def]
        refine (map_zsmul ((I.X s).obj.map g.op).hom _ _).trans ?_
        congr 1
        change Sec.res g (ev (R := R) α.1 (p + 1) s _ U (up x)) =
          ev (R := R) α.1 (p + 1) s _ V (up (P.map g.op x))
        rw [hEval, hEval, sec_map_res, freeGen_res]
        rfl
      · exact map_zero _)
  choose φ hφ using hex
  let f (p : ℕ) (s : ℤ) (h : -(p : ℤ) + (n - 1) = s) : ((chains R).obj (disc.obj P)).X (-(p : ℤ)) ⟶ I.X s :=
    (chainsXIso R (disc.obj P) p).hom ≫ φ p s h
  let β : Cochain ((chains R).obj (disc.obj P)) I (n - 1) := Cochain.mk (fun i j hij =>
    if hi : 0 ≤ -i then
      (((chains R).obj (disc.obj P)).XIsoOfEq (show i = -(((-i).toNat : ℕ) : ℤ) by omega)).hom ≫
        f (-i).toNat j (by omega)
    else 0)
  have hβ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + (n - 1) = s) (U : Scheme.{0}) (x : Sx (disc.obj P) p U) :
      ev (R := R) β p s h U x = a p s h U x := by
    have hComponent (q : ℕ) (hq : q = p) (e : -(p : ℤ) = -(q : ℤ)) (h' : -(q : ℤ) + (n - 1) = s) :
        (((chains R).obj (disc.obj P)).XIsoOfEq e).hom ≫ f q s h' = f p s h := by
      subst q
      simp
    have hv : β.v (-(p : ℤ)) s h = f p s h := by
      simp only [β, Cochain.mk_v]
      rw [dite_eq_left (by omega)]
      exact hComponent _ (by omega) _ _
    rw [hEval, hv]
    simp only [f, Iso.inv_hom_id_assoc]
    exact hφ p s h U x
  refine ⟨β, ?_⟩
  intro p s h U y
  have hSub : ev (R := R) (α.1 - δ (n - 1) n β) (p + 1) s h U y =
      ev (R := R) α.1 (p + 1) s h U y - ev (R := R) (δ (n - 1) n β) (p + 1) s h U y := by
    rw [hEval, hEval, hEval, Cochain.sub_v, Preadditive.comp_sub]
    exact map_sub (AddMonoidHom.mk' (fun m => Sec.map m (freeGen R P U y)) (fun _ _ => sec_map_add _ _ _)) _ _
  rw [hSub, sub_eq_zero, hD (by omega) β U p (s - 1) s (by push_cast at h ⊢; omega) h y]
  simp only [face_disc, hβ, a]
  rcases Nat.even_or_odd p with hp | hp
  · have hp1 : Odd (p + 1) := hp.add_one
    have hp0 : ¬ Odd p := Nat.not_odd_iff_even.mpr hp
    simp only [hp1, hp0, ite_true, ite_false, smul_zero, Finset.sum_const_zero, add_zero]
    have hc := hD rfl α.1 U (p + 1) (s - 1) s (by push_cast at h ⊢; omega)
      (by push_cast at h ⊢; omega) (up y)
    rw [hα] at hc
    have hZero : ev (R := R) (0 : Cochain ((chains R).obj (disc.obj P)) I (n + 1))
        (p + 1 + 1) s (by push_cast at h ⊢; omega) U (up y) = 0 := by simp [ev]
    rw [hZero] at hc
    simp only [face_disc] at hc
    rw [← Finset.sum_smul, LateralTheory.KummerTheory.altsum] at hc
    have he : ¬ Even (p + 1 + 2) := by
      rw [Nat.not_even_iff_odd]; exact hp1.add_even even_two
    simp only [he, ite_false, one_smul] at hc
    rw [Int.negOnePow_succ, Units.neg_smul] at hc
    have key := add_neg_eq_zero.1 hc.symm
    rw [Units.smul_def]
    refine Eq.trans ?_ (map_zsmul ((I.d (s - 1) s).hom.app (op U)).hom _ _).symm
    rw [show (ModuleCat.Hom.hom ((I.d (s - 1) s).hom.app (op U))) (ev α.1 (p + 1 + 1) (s - 1) (by push_cast at h ⊢; omega) U (up y))
        = n.negOnePow • ev α.1 (p + 1) s (by push_cast at h ⊢; omega) U (up (up y)) from key]
    rw [← Units.smul_def, smul_smul, Int.units_mul_self, one_smul]
    rfl
  · have hp1 : ¬ Odd (p + 1) := Nat.not_odd_iff_even.mpr hp.add_one
    simp only [hp1, hp, ite_true, ite_false, map_zero, zero_add]
    rw [← Finset.sum_smul, LateralTheory.KummerTheory.altsum]
    have he : ¬ Even (p + 2) := by
      rw [Nat.not_even_iff_odd]; exact hp.add_even even_two
    simp only [he, ite_false, one_smul, smul_smul, Int.units_mul_self]
    rfl

end LateralTheory.CohomologicalPurity.Cl.DiscNrmPf

namespace LateralTheory.CohomologicalPurity.Cl

open DiscNrmPf LateralTheory.KummerTheory.AW in
theorem etale_discrete_presheaf_cocycle_normalization_holds : LeafDiscNrm := by
  intro R _ K n P z
  obtain ⟨β, hβ⟩ := normal R K P n z
  refine ⟨(chainsXIso R (disc.obj P) 0).inv ≫ (z.1 - δ (n - 1) n β).v (-((0 : ℕ) : ℤ)) n (by omega), β, ?_⟩
  rw [← sub_eq_iff_eq_add]
  have hExt (a b : Cochain ((chains R).obj (disc.obj P)) K n)
      (hab : ∀ p s h U x, ev (R := R) a p s h U x = ev (R := R) b p s h U x) : a = b := by
    ext i j hij : 1
    by_cases hi : 0 < i
    · exact (isZero_pos (R := R) (disc.obj P) i hi).eq_of_src _ _
    · obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨(-i).toNat, by omega⟩
      rw [← cancel_epi (chainsXIso R (disc.obj P) p).inv]
      exact free_ext _ _ (fun U x => hab p j hij U x)
  apply hExt
  intro p s h U x
  rcases p with _ | p
  · obtain rfl : s = n := by omega
    simp only [ev, Cochain.single_v, Iso.inv_hom_id_assoc]
  · rw [hβ]
    simp only [ev]
    rw [Cochain.single_v_eq_zero _ _ _ _ _ (by push_cast; omega), comp_zero]
    rfl

theorem LeafDisc_of' : LeafDisc := LeafDisc_of etale_discrete_presheaf_cocycle_normalization_holds

end LateralTheory.CohomologicalPurity.Cl
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem altSum (m : ℕ) : ∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ) = if Even m then 0 else 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (-1 : ℤ) ^ i) (m + 2)]
  induction m with
  | zero => simp [Finset.sum_range_succ]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd m with h | h
    · have h' : ¬ Even (m + 1) := by simpa [Nat.even_add_one] using h
      simp [h, h', pow_succ, h.neg_one_pow]
    · have h' : Even (m + 1) := by simpa [Nat.even_add_one, Nat.not_even_iff_odd] using h
      have hn : ¬ Even m := Nat.not_even_iff_odd.2 h
      simp [hn, h', pow_succ, h.neg_one_pow]

theorem dL {R : Type} [CommRing R] (Y : PSh) (m : ℕ) (T : Scheme.{0}ᵒᵖ) (z : ((((chainsP R).obj (disc.obj Y)).X (m + 1)).obj T)) :
    ((((chainsP R).obj (disc.obj Y)).d (m + 1) m).app T).hom z = (∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ)) • z := by
  change (((freeP R).obj Y).obj T) at z
  have e : ∀ i : Fin (m + 2), SimplicialObject.δ (disc.obj Y) i = 𝟙 _ := fun _ => rfl
  simp [chainsP, e]
  erw [LinearMap.sum_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp
  simpa only [Int.cast_pow, Int.cast_neg, Int.cast_one] using
    (Module.End.intCast_apply (R := ULift.{1} R) ((-1 : ℤ) ^ (i : ℕ)) z)

section
variable {R : Type} [CommRing R]

theorem bdyL (Y : PSh) (n : ℕ) (T : Scheme.{0}ᵒᵖ) (x : ((((chainsP R).obj (disc.obj Y)).X (n + 1)).obj T))
    (hx : Cyc ((chainsP R).obj (disc.obj Y)) (n + 1) T x) : Bdy ((chainsP R).obj (disc.obj Y)) (n + 1) T x := by
  by_cases h : Even (n + 1)
  · have h0 := hx n
    rw [dL, altSum, if_neg (by simpa [Nat.even_add_one] using h)] at h0
    simp only [one_smul] at h0
    exact ⟨0, by rw [map_zero]; exact h0.symm⟩
  · refine ⟨x, ?_⟩
    have e := dL (R := R) Y (n + 1) T x
    rw [altSum, if_neg h] at e
    exact e.trans (one_smul ℤ _)

def imSv {K L : PCx R} (φ : K ⟶ L) (n : ℕ) {T : Scheme.{0}} (y : (L.X n).obj (op T)) : Sieve T where
  arrows U f := ∃ x', ((φ.f n).app (op U)).hom x' = ((L.X n).map f.op).hom y
  downward_closed := by
    rintro U V f ⟨x', hx⟩ g
    refine ⟨((K.X n).map g.op).hom x', ?_⟩
    have h1 := congrArg (fun h => h.hom x') ((φ.f n).naturality g.op)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
    rw [h1, hx, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem imSv_add {K L : PCx R} (φ : K ⟶ L) (n : ℕ) {T : Scheme.{0}} (y z : (L.X n).obj (op T)) :
    imSv φ n y ⊓ imSv φ n z ≤ imSv φ n (y + z) := by
  rintro U f ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), ha, hb]⟩

theorem imSv_smul {K L : PCx R} (φ : K ⟶ L) (n : ℕ) {T : Scheme.{0}} (y : (L.X n).obj (op T)) (r : ULift.{1} R) :
    imSv φ n y ≤ imSv φ n (r • y) := by
  rintro U f ⟨a, ha⟩
  exact ⟨r • a, by rw [map_smul, map_smul, ha]⟩

theorem imSv_zero {K L : PCx R} (φ : K ⟶ L) (n : ℕ) {T : Scheme.{0}} :
    imSv φ n (0 : (L.X n).obj (op T)) = ⊤ := by
  ext U f
  simp only [Sieve.top_apply, iff_true]
  exact ⟨0, by rw [map_zero, map_zero]⟩

end

section
variable {J : Type} [Preorder J] (D : J ⥤ Scheme.{0}) (X : Scheme.{0}) (c : ∀ j, D.obj j ⟶ X)
  (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) (R : Type) [CommRing R]

theorem gen_mem (hcov : ∀ x : X, ∃ j, x ∈ Set.range (c j)) [∀ j, IsOpenImmersion (c j)]
    {T : Scheme.{0}} (g : T ⟶ X) :
    imSv ((chainsP R).map (aug _ hc)) 0
      (ModuleCat.freeMk (ULift.up g) : (((chainsP R).obj (disc.obj (yoneda.obj X))).X 0).obj (op T)) ∈
      Scheme.etaleTopology T := by
  let j : T → J := fun t => (hcov (g t)).choose
  let V : T → T.Opens := fun t => g ⁻¹ᵁ (c (j t)).opensRange
  have hV : ∀ t, t ∈ V t := fun t => (hcov (g t)).choose_spec
  let 𝒰 : T.Cover (Scheme.precoverage @Etale) := Scheme.Cover.mkOfCovers T (fun t => (V t).toScheme)
    (fun t => (V t).ι) (fun t => ⟨t, ⟨t, hV t⟩, by simp⟩)
  refine GrothendieckTopology.superset_covering _ ?_ 𝒰.mem_grothendieckTopology
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro _ _ ⟨t⟩
  have hr : Set.range ((V t).ι ≫ g) ⊆ Set.range (c (j t)) := by
    rintro _ ⟨y, rfl⟩
    have := (V t).range_ι ▸ Set.mem_range_self (f := (V t).ι) y
    simpa [V] using this
  let a := IsOpenImmersion.lift (c (j t)) ((V t).ι ≫ g) hr
  let σ : Fin (0 + 1) ⥤ J := (Functor.const _).obj (j t)
  refine ⟨ModuleCat.freeMk (ULift.up ((inj (D ⋙ yoneda) (op (SimplexCategory.mk 0)) σ).app (op (V t).toScheme) a)), ?_⟩
  erw [ModuleCat.free_map_apply, ModuleCat.free_map_apply]
  refine congrArg ModuleCat.freeMk (ULift.ext ?_)
  show (a ≫ D.map (𝟙 (j t))) ≫ c (j t) = (V t).ι ≫ g
  rw [D.map_id, Category.comp_id]
  exact IsOpenImmersion.lift_fac _ _ _
end

theorem all_mem {J : Type} [Preorder J] (D : J ⥤ Scheme.{0}) (X : Scheme.{0}) (c : ∀ j, D.obj j ⟶ X)
    (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) (R : Type) [CommRing R]
    (hcov : ∀ x : X, ∃ j, x ∈ Set.range (c j)) [∀ j, IsOpenImmersion (c j)] {T : Scheme.{0}}
    (x : (((chainsP R).obj (disc.obj (yoneda.obj X))).X 0).obj (op T)) :
    imSv ((chainsP R).map (aug _ hc)) 0 x ∈ Scheme.etaleTopology T := by
  let M := (((chainsP R).obj (disc.obj (yoneda.obj X))).X 0).obj (op T)
  let b : Module.Basis (ULift.{1} (T ⟶ X)) (ULift.{1} R) M := Finsupp.basisSingleOne
  have hx : x ∈ Submodule.span (ULift.{1} R) (Set.range b) := b.mem_span x
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨g⟩, rfl⟩ := hy
    exact gen_mem D X c hc R hcov g
  | zero => rw [imSv_zero]; exact GrothendieckTopology.top_mem _ _
  | add y z _ _ hy hz =>
    exact GrothendieckTopology.superset_covering _ (imSv_add _ _ y z)
      (GrothendieckTopology.intersection_covering _ hy hz)
  | smul r y _ hy => exact GrothendieckTopology.superset_covering _ (imSv_smul _ _ y r) hy

theorem LeafAugSurj_of : LeafAugSurj := by
  intro J _ D X c ho hcov hc R _ n T x hx
  rcases n with _ | n
  · refine ⟨imSv ((chainsP R).map (aug _ hc)) 0 x, ?_, ?_⟩
    · have := ho
      exact all_mem D X c hc R hcov x
    · rintro U f ⟨x', hx'⟩
      refine ⟨x', fun m => ?_, 0, ?_⟩
      · rw [HomologicalComplex.shape _ 0 m (by simp)]
        rfl
      · rw [map_zero, hx', sub_self]
  · refine ⟨⊤, GrothendieckTopology.top_mem _ _, fun U f _ => ⟨0, fun m => by simp, ?_⟩⟩
    obtain ⟨y, hy⟩ := bdyL _ n T x hx
    refine ⟨-((((chainsP R).obj (disc.obj (yoneda.obj X))).X (n + 1 + 1)).map f.op).hom y, ?_⟩
    have h := congrArg (fun h => h.hom y) ((((chainsP R).obj (disc.obj (yoneda.obj X))).d (n + 1 + 1) (n + 1)).naturality f.op)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [map_neg, map_zero, zero_sub, h, hy]

end LateralTheory.CohomologicalPurity.TubeCut
end
end
