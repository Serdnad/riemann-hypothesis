module

public import Development.EtaleCohomology.EtaleSheaves.Bundle017
public import Development.EtaleCohomology.EtaleSheaves.Bundle018
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.TypeStar

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LeafTermsPf

variable {R : Type} [CommRing R]

theorem HKpull_comp {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ) (x : HK R M F n) :
    HK.pull R (f ≫ g) F n x = HK.pull R f F n (HK.pull R g F n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem HKpull_id (K : Cx R) (F : Shv R) (n : ℤ) (x : HK R K F n) : HK.pull R (𝟙 K) F n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

theorem finite_of_retract {K L : Cx R} (s : K ⟶ L) (t : L ⟶ K) (h : s ≫ t = 𝟙 K) (F : Shv R) (n : ℤ)
    (hL : Finite (HK R L F n)) : Finite (HK R K F n) :=
  Finite.of_surjective (HK.pull R s F n) (fun x =>
    ⟨HK.pull R t F n x, by rw [← HKpull_comp, h, HKpull_id]⟩)

theorem finite_of_iso {A B : Shv R} (e : A ≅ B) (F : Shv R) (n : ℤ)
    (hB : Finite (HK R ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj B) F n)) :
    Finite (HK R ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj A) F n) :=
  finite_of_retract _ _ (((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).mapIso e).hom_inv_id) F n hB

theorem d_const_zero (P : PSh) : ((chains R).obj (disc.obj P)).d (-1) 0 = 0 := by
  have h := HomologicalComplex.extend_d_eq ((chainsN R).obj (disc.obj P)) ComplexShape.embeddingDownNat
    (i := 1) (j := 0) (i' := -1) (j' := 0) rfl rfl
  change (((chainsN R).obj (disc.obj P)).extend ComplexShape.embeddingDownNat).d (-1) 0 = 0
  rw [h]
  have : ((chainsN R).obj (disc.obj P)).d 1 0 = 0 := by
    simp [chainsN, Fin.sum_univ_two, SimplicialObject.δ, disc]
    all_goals first
      | (erw [neg_one_smul, one_smul, add_neg_cancel])
      | (simp only [one_smul, neg_smul]; exact add_neg_cancel _)
      | abel
    all_goals rfl
  rw [this]; simp

def proj0 (P : PSh) : (chains R).obj (disc.obj P) ⟶
    (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj (((chains R).obj (disc.obj P)).X 0) :=
  HomologicalComplex.mkHomToSingle (𝟙 _) (fun i hi => by
    have : i = -1 := by simp at hi; omega
    subst this; rw [d_const_zero]; simp)

theorem etale_chain_complex_degree_zero_incl_proj_eq_id (P : PSh) : LateralTheory.E.LeafSSCut.incl0 ((chains R).obj (disc.obj P)) ≫ proj0 P = 𝟙 _ := by
  apply HomologicalComplex.to_single_hom_ext
  simp [LateralTheory.E.LeafSSCut.incl0, proj0]

theorem finite_single_of_H (Z : Scheme.{0}) (F : Shv R) (m : ℤ) (h : Finite (H R (sch.obj Z) F m)) :
    Finite (HK R ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj ((free R).obj (yoneda.obj Z))) F m) :=
  finite_of_iso (chainsXIso R (disc.obj (yoneda.obj Z)) 0).symm F m
    (finite_of_retract _ _ (etale_chain_complex_degree_zero_incl_proj_eq_id (R := R) (yoneda.obj Z)) F m h)

section Geo
variable {Y X : Scheme.{0}} (f : Y ⟶ X)

abbrev W (n : ℕ) : Scheme.{0} := widePullback X (fun _ : Fin n => Y) (fun _ => f)

def toPb (n : ℕ) : W f (n + 1) ⟶ pullback (WidePullback.base (fun _ : Fin n => f)) f :=
  pullback.lift (WidePullback.lift (WidePullback.base _) (fun j => WidePullback.π _ j.succ) (by simp))
    (WidePullback.π _ 0) (by simp [WidePullback.lift_π, WidePullback.lift_π_assoc, WidePullback.lift_base, WidePullback.lift_base_assoc])

def ofPb (n : ℕ) : pullback (WidePullback.base (fun _ : Fin n => f)) f ⟶ W f (n + 1) :=
  WidePullback.lift (pullback.snd _ _ ≫ f)
    (Fin.cases (pullback.snd _ _) (fun j => pullback.fst _ _ ≫ WidePullback.π _ j))
    (by intro j; refine Fin.cases ?_ (fun j => ?_) j <;> simp [pullback.condition, WidePullback.lift_π, WidePullback.lift_π_assoc, WidePullback.lift_base, WidePullback.lift_base_assoc])

theorem toPb_ofPb (n : ℕ) : toPb f n ≫ ofPb f n = 𝟙 _ := by
  apply WidePullback.hom_ext
  · intro j
    simp only [Category.assoc, Category.id_comp]
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [ofPb, WidePullback.lift_π]; simp only [Fin.cases_zero]; rw [toPb, pullback.lift_snd]
    · rw [ofPb, WidePullback.lift_π]; simp only [Fin.cases_succ]
      rw [toPb, pullback.lift_fst_assoc, WidePullback.lift_π]
  · simp only [Category.assoc, Category.id_comp]
    rw [ofPb, WidePullback.lift_base, toPb, pullback.lift_snd_assoc, WidePullback.π_arrow]

theorem ofPb_toPb (n : ℕ) : ofPb f n ≫ toPb f n = 𝟙 _ := by
  apply pullback.hom_ext
  · apply WidePullback.hom_ext
    · intro j
      simp only [Category.assoc, Category.id_comp]
      rw [toPb, pullback.lift_fst_assoc, WidePullback.lift_π, ofPb, WidePullback.lift_π]
      simp only [Fin.cases_succ]
    · simp only [Category.assoc, Category.id_comp]
      rw [toPb, pullback.lift_fst_assoc, WidePullback.lift_base, ofPb, WidePullback.lift_base, pullback.condition]
  · simp only [Category.assoc, Category.id_comp]
    rw [toPb, pullback.lift_snd, ofPb, WidePullback.lift_π]
    simp only [Fin.cases_zero]

theorem base_zero_iso : IsIso (WidePullback.base (fun _ : Fin 0 => f)) :=
  ⟨⟨WidePullback.lift (𝟙 X) (fun j => j.elim0) (fun j => j.elim0), by
    refine ⟨WidePullback.hom_ext _ _ _ (fun j => j.elim0) (by simp [WidePullback.lift_π, WidePullback.lift_π_assoc, WidePullback.lift_base, WidePullback.lift_base_assoc]), by simp [WidePullback.lift_π, WidePullback.lift_π_assoc, WidePullback.lift_base, WidePullback.lift_base_assoc]⟩⟩⟩

theorem base_proper [IsProper f] : ∀ n : ℕ, IsProper (WidePullback.base (fun _ : Fin n => f))
  | 0 => by
    have := base_zero_iso f
    first | infer_instance | exact MorphismProperty.of_isIso (P := @IsProper) _
  | n + 1 => by
    have := base_proper n
    have hi : IsIso (toPb f n) := ⟨⟨ofPb f n, toPb_ofPb f n, ofPb_toPb f n⟩⟩
    have : WidePullback.base (fun _ : Fin (n + 1) => f) = toPb f n ≫ pullback.fst _ _ ≫ WidePullback.base _ := by
      rw [toPb, pullback.lift_fst_assoc, WidePullback.lift_base]
    rw [this]
    infer_instance

def eIso (n : ℕ) : yoneda.obj (W f n) ≅ widePullback (yoneda.obj X) (fun _ : Fin n => yoneda.obj Y) (fun _ => yoneda.map f) :=
  preservesLimitIso yoneda _ ≪≫ HasLimit.isoOfNatIso (WidePullbackShape.diagramIsoWideCospan _)

end Geo

theorem LeafTerms_of : LateralTheory.E.LeafSSCut.LeafTerms := by
  intro _ R _ F Y X f _ r m hZ
  refine finite_of_iso ((chainsXIso R (cech f) r) ≪≫ (free R).mapIso (eIso f (r + 1)).symm) F m ?_
  exact finite_single_of_H _ F m (hZ _ _ (base_proper f (r + 1)))

end LateralTheory.E.LeafTermsPf
end
end

section

noncomputable section
open LateralTheory.E.t_E1Cut LateralTheory.E.LCSplitPf LateralTheory.E.TorEtPf

namespace LateralTheory.E.ProjGPf

variable {S : Type} [CommRing S]

theorem isUnit_f_fg (f g : S) : IsUnit (algebraMap S (Localization.Away (f * g)) f) :=
  isUnit_of_dvd_unit (map_dvd _ (dvd_mul_right f g)) (IsLocalization.Away.algebraMap_isUnit (f * g))

theorem rL_alg (f g : S) (a : S) :
    rL f g (algebraMap S _ a) = algebraMap S (Localization.Away (f * g)) a :=
  IsLocalization.Away.awayToAwayRight_eq f g a

theorem rR_alg (f g : S) (a : S) :
    rR f g (algebraMap S _ a) = algebraMap S (Localization.Away (f * g)) a :=
  IsLocalization.Away.awayToAwayLeft_eq g f a

theorem rL_surj {ι : Type} [Finite ι] (f g : S) (w : ι → Localization.Away (f * g)) :
    ∃ (n : ℕ) (x : ι → Localization.Away f), ∀ k, rL f g (x k) = algebraMap S _ (g ^ n) * w k := by
  obtain ⟨⟨b, hb'⟩, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (Submonoid.powers (f * g)) w
  obtain ⟨n, rfl⟩ := Submonoid.mem_powers_iff _ _ |>.mp hb'
  choose a ha using hb
  refine ⟨n, fun k => IsLocalization.mk' (Localization.Away f) (a k) (⟨f ^ n, n, rfl⟩ : Submonoid.powers f), fun k => ?_⟩
  have hu : IsUnit (algebraMap S (Localization.Away (f * g)) (f ^ n)) := by
    rw [map_pow]; exact (isUnit_f_fg f g).pow n
  apply hu.mul_left_cancel
  have hs := IsLocalization.mk'_spec' (Localization.Away f) (a k) (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)
  change algebraMap S _ (f ^ n) * _ = _ at hs
  rw [← rL_alg, ← map_mul, hs, rL_alg, ha k, Algebra.smul_def]
  change algebraMap S _ ((f * g) ^ n) * w k = _
  rw [mul_pow, map_mul, mul_assoc, rL_alg]

theorem rL_ker (f g : S) (x : Localization.Away f) (hx : rL f g x = 0) :
    ∃ n : ℕ, algebraMap S _ (g ^ n) * x = 0 := by
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers f) x
  have h0 : algebraMap S (Localization.Away (f * g)) a = 0 := by
    rw [← rL_alg, ← hs, map_mul, hx, zero_mul]
  obtain ⟨⟨m, n, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (f * g)) _ a).mp h0
  refine ⟨n, ?_⟩
  have hu : IsUnit (algebraMap S (Localization.Away f) (f ^ n * s)) :=
    IsLocalization.map_units (Localization.Away f)
      (⟨f ^ n * s, Submonoid.mul_mem _ (Submonoid.pow_mem _ (Submonoid.mem_powers f) n) s.2⟩ : Submonoid.powers f)
  apply (hu.mul_left_eq_zero).mp
  have e1 : algebraMap S (Localization.Away f) (g ^ n) * x * algebraMap S _ (f ^ n * s)
      = algebraMap S _ (g ^ n * f ^ n) * (x * algebraMap S _ (s : S)) := by
    simp only [map_mul]; ring
  rw [e1, hs, ← map_mul, show g ^ n * f ^ n * a = (f * g) ^ n * a by ring, hm, map_zero]

theorem rL_ker_fam {ι : Type} [Fintype ι] (f g : S) (x : ι → Localization.Away f)
    (hx : ∀ k, rL f g (x k) = 0) : ∃ n : ℕ, ∀ k, algebraMap S _ (g ^ n) * x k = 0 := by
  choose n hn using fun k => rL_ker f g (x k) (hx k)
  refine ⟨Finset.univ.sup n, fun k => ?_⟩
  rw [← Nat.sub_add_cancel (Finset.le_sup (Finset.mem_univ k) : n k ≤ _), pow_add, map_mul, mul_assoc, hn k,
    mul_zero]

theorem twist_apply {q : ℕ} [NeZero q] {A : Type} [CommRing A] {ε : ZMod q → A}
    (hε : CompleteOrthogonalIdempotents ε) (z : ZMod q → A) (k : ZMod q) :
    twist hε z k = ∑ c, ε c * z (k + c) := rfl

theorem ProjG_of : ProjG := by
  intro q _ S _ f g hfg ε hε
  let _ := (torMap f g hε).toAlgebra
  let _ := (pr2 f g hε).toAlgebra
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    have e : algebraMap (Tor f g hε) (ZMod q → Localization.Away g) (algebraMap S (Tor f g hε) g ^ n)
        = fun _ => algebraMap S (Localization.Away g) g ^ n := by
      rw [map_pow]; rfl
    rw [e]
    exact Pi.isUnit_iff.mpr fun _ => (IsLocalization.Away.algebraMap_isUnit g).pow n
  · intro y
    obtain ⟨n, x, hx⟩ := rL_surj f g (twist hε (fun k => rR f g (y k)))
    have hmem : ((x, fun k => algebraMap S _ (g ^ n) * y k) : Amb f g q) ∈ Tor f g hε := by
      show h1 f g _ = h2 f g hε _
      funext k
      change rL f g (x k) = ∑ c, ε c * rR f g (algebraMap S _ (g ^ n) * y (k + c))
      rw [hx k, twist_apply]
      simp only [map_mul, rR_alg]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
    refine ⟨(⟨_, hmem⟩, ⟨algebraMap S _ g ^ n, n, rfl⟩), ?_⟩
    show y * pr2 f g hε (torMap f g hε g ^ n) = pr2 f g hε ⟨_, hmem⟩
    rw [map_pow]
    funext k
    change y k * (algebraMap S (Localization.Away g) g) ^ n = algebraMap S _ (g ^ n) * y k
    rw [map_pow, mul_comm]
  · intro t1 t2 h
    have h0 : (t1 - t2).1.2 = 0 := by
      have : pr2 f g hε (t1 - t2) = 0 := by
        rw [map_sub]; exact sub_eq_zero.mpr h
      exact this
    have hx : ∀ k, rL f g ((t1 - t2).1.1 k) = 0 := by
      intro k
      have hm : h1 f g (t1 - t2).1 = h2 f g hε (t1 - t2).1 := (t1 - t2).2
      have hk := congrFun hm k
      change rL f g ((t1 - t2).1.1 k) = ∑ c, ε c * rR f g ((t1 - t2).1.2 (k + c)) at hk
      rw [hk, h0]; simp
    obtain ⟨n, hn⟩ := rL_ker_fam f g (fun k => (t1 - t2).1.1 k) hx
    refine ⟨⟨algebraMap S _ g ^ n, n, rfl⟩, ?_⟩
    rw [← sub_eq_zero, ← mul_sub]
    show torMap f g hε g ^ n * (t1 - t2) = 0
    apply Subtype.ext
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · change (algebraMap S (Localization.Away f) g) ^ n * (t1 - t2).1.1 k = 0
      rw [← map_pow]; exact hn k
    · change (algebraMap S (Localization.Away g) g) ^ n * (t1 - t2).1.2 k = 0
      rw [h0]; simp

end LateralTheory.E.ProjGPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.DiagonalComparison

theorem hkpull_comp {R : Type} [CommRing R] {K L M : Cx R} (a : K ⟶ L) (b : L ⟶ M) (F : Shv R) (n : ℤ)
    (x : HK R M F n) : HK.pull R (a ≫ b) F n x = HK.pull R a F n (HK.pull R b F n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [HK.pull, HK.pre, cpre, zcomp, Cochain.ofHom_comp]

def diag {Y X : Scheme.{0}} (f : Y ⟶ X) : sch.obj Y ⟶ cech f where
  app n := WidePullback.lift (yoneda.map f) (fun _ => 𝟙 _) (fun _ => Category.id_comp _)
  naturality := by
    intro a b g
    apply WidePullback.hom_ext
    · intro j
      dsimp [sch, cech]
      simp only [Category.id_comp, Category.assoc]
      erw [WidePullback.lift_π, WidePullback.lift_π, WidePullback.lift_π]
    · dsimp [sch, cech]
      simp only [Category.id_comp, Category.assoc]
      erw [WidePullback.lift_base, WidePullback.lift_base, WidePullback.lift_base]

theorem diag_aug {Y X : Scheme.{0}} (f : Y ⟶ X) : diag f ≫ cechAug f = sch.map f := by
  apply NatTrans.ext; funext n
  erw [NatTrans.comp_app]
  simp only [cechAug, Arrow.augmentedCechNerve_hom_app]
  erw [WidePullback.lift_base]
  rfl

theorem lift_iso {C : Type*} [Category C] {B A : C} (h : A ⟶ B)
    [HasWidePullback B (fun _ : Fin 1 => A) (fun _ => h)] :
    IsIso (WidePullback.lift h (fun _ : Fin 1 => 𝟙 A) (fun _ => Category.id_comp _) :
      A ⟶ widePullback B (fun _ : Fin 1 => A) (fun _ => h)) := by
  refine ⟨⟨WidePullback.π _ 0, ?_, ?_⟩⟩
  · rw [WidePullback.lift_π]
  apply WidePullback.hom_ext
  · intro j
    obtain rfl := Fin.fin_one_eq_zero j
    rw [Category.assoc, WidePullback.lift_π, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, WidePullback.lift_base, Category.id_comp, WidePullback.π_arrow]

instance isIso_cech_nerve_diagonal_app_degree_zero {Y X : Scheme.{0}} (f : Y ⟶ X) : IsIso ((diag f).app (op (SimplexCategory.mk 0))) :=
  lift_iso (C := PSh) (yoneda.map f)

instance isIso_etale_chains_map_cech_diagonal_degree_zero {R : Type} [CommRing R] {Y X : Scheme.{0}} (f : Y ⟶ X) :
    IsIso (((chains R).map (diag f)).f 0) := by
  change IsIso ((HomologicalComplex.extendMap ((chainsN R).map (diag f)) ComplexShape.embeddingDownNat).f 0)
  rw [HomologicalComplex.extendMap_f _ _ (i := 0) (by simp)]
  have : IsIso (((chainsN R).map (diag f)).f 0) := by
    change IsIso ((free R).map ((diag f).app (op (SimplexCategory.mk 0))))
    infer_instance
  infer_instance

theorem etale_chains_degree_zero_inclusion_factors_through_cech_diagonal {R : Type} [CommRing R] {Y X : Scheme.{0}} (f : Y ⟶ X) :
    (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map (inv (((chains R).map (diag f)).f 0)) ≫
      LateralTheory.E.LeafSSCut.incl0 ((chains R).obj (sch.obj Y)) ≫ (chains R).map (diag f) =
    LateralTheory.E.LeafSSCut.incl0 ((chains R).obj (cech f)) := by
  apply HomologicalComplex.from_single_hom_ext
  simp [LateralTheory.E.LeafSSCut.incl0, HomologicalComplex.mkHomFromSingle_f, HomologicalComplex.single_map_f_self]

theorem LeafCompare_of : LateralTheory.E.LeafSSCut.LeafCompare := by
  intro _ R _ F Y X f n hE _
  have key : ∀ x, pull R (sch.map f) F n x = 0 →
      HK.pull R (LateralTheory.E.LeafSSCut.incl0 ((chains R).obj (cech f))) F n (pull R (cechAug f) F n x) = 0 := by
    intro x hx
    rw [← etale_chains_degree_zero_inclusion_factors_through_cech_diagonal f, hkpull_comp, hkpull_comp]
    have h0 : HK.pull R ((chains R).map (diag f)) F n (pull R (cechAug f) F n x) = 0 := by
      rw [← hx, ← diag_aug f, pull_comp]; rfl
    rw [h0, map_zero, map_zero]
  let φ : (pull R (sch.map f) F n).ker →
      (HK.pull R (LateralTheory.E.LeafSSCut.incl0 ((chains R).obj (cech f))) F n).ker :=
    fun x => ⟨pull R (cechAug f) F n x.1, AddMonoidHom.mem_ker.2 (key x.1 (AddMonoidHom.mem_ker.1 x.2))⟩
  have hφ : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext
    exact (hE n).1 (congrArg Subtype.val hxy)
  exact Finite.of_injective φ hφ

end LateralTheory.E.DiagonalComparison
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.GlobalPf

namespace LateralTheory.E.LocEtPf

lemma et_res {X : Scheme.{0}} {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U) :
    Et (X.presheaf.map (homOfLE h).op) := by
  have := (𝟙 X : X ⟶ X).etale_appLE hU hV h
  show (X.presheaf.map (homOfLE h).op).hom.Etale
  convert this using 2
  rfl

theorem LocEt_of : LocEt := by
  intro T X p _ x
  obtain ⟨_, _, V0, hV0, hx0, -, -⟩ := Smooth.exists_isStandardSmooth p x
  have hf : (p.appLE ⊤ V0 (by simp)).hom.Smooth := p.smooth_appLE (isAffineOpen_top _) hV0 _
  have hloc := (RingHom.Smooth.locally_isStandardSmooth hf).span_eq_top
  have hcov := AlgebraicGeometry.iSup_basicOpen_of_span_eq_top V0 _ hloc
  have hx1 : x ∈ (⨆ i ∈ {g : Γ(X, V0) | ((algebraMap Γ(X, V0) (Localization.Away g)).comp
      (p.appLE ⊤ V0 (by simp)).hom).IsStandardSmooth}, X.basicOpen i) := by rw [hcov]; exact hx0
  simp only [TopologicalSpace.Opens.mem_iSup] at hx1
  obtain ⟨t, ht, hxt⟩ := hx1
  have hB := hV0.basicOpen t
  let := hV0.isLocalization_basicOpen t
  let e : Localization.Away t ≃ₐ[Γ(X, V0)] Γ(X, X.basicOpen t) :=
    IsLocalization.algEquiv (Submonoid.powers t) _ _
  have hs : (gam p (X.basicOpen t)).hom.IsStandardSmooth := by
    have h1 := (RingHom.isStandardSmooth_respectsIso.1 _ e.toRingEquiv ht)
    have h2 := RingHom.isStandardSmooth_respectsIso.2 _ (Scheme.ΓSpecIso T).commRingCatIsoToRingEquiv.symm h1
    have hgam : gam p (X.basicOpen t) = (Scheme.ΓSpecIso T).inv ≫ p.appLE ⊤ V0 (by simp) ≫
        X.presheaf.map (homOfLE (X.basicOpen_le t)).op := by
      simp only [gam]
      congr 1
      exact (Scheme.Hom.appLE_map ..).symm
    have halg : algebraMap Γ(X, V0) Γ(X, X.basicOpen t) = (X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom := rfl
    rw [hgam]
    convert h2 using 1
    ext a
    simp only [RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_comp, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes, halg]
    rfl
  obtain ⟨n, g, hgC, hg⟩ := hs.exists_etale_mvPolynomial
  refine ⟨X.basicOpen t, n, hxt, fun V hV hVU => ?_⟩
  refine ⟨CommRingCat.ofHom g ≫ X.presheaf.map (homOfLE hVU).op, ?_, ?_⟩
  · exact RingHom.Etale.stableUnderComposition _ _ hg (et_res hB hV hVU)
  · ext1
    rw [← Category.assoc]
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
    rw [hgC]
    simp only [gam, Scheme.Hom.appLE, ← CommRingCat.hom_comp, Category.assoc, ← Functor.map_comp]
    rfl

end LateralTheory.E.LocEtPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.GlobalPf

namespace LateralTheory.E.AffinePf

theorem eqv_of_sq (R : Type) [CommRing R] (F : Shv R) {E₁ E₂ E₁' E₂' : Spc} (f : E₁ ⟶ E₂) (f' : E₁' ⟶ E₂')
    (a : E₁ ≅ E₁') (b : E₂ ≅ E₂') (h : f ≫ b.hom = a.hom ≫ f') (hf : Eqv R f' F) : Eqv R f F := fun n => by
  have hiso : ∀ {X Y : Spc} (e : X ≅ Y), Function.Bijective (pull R e.hom F n) := fun e => by
    refine ⟨Function.LeftInverse.injective (g := pull R e.inv F n) fun x => ?_,
      Function.RightInverse.surjective (g := pull R e.inv F n) fun x => ?_⟩
    · rw [← pull_comp, e.inv_hom_id, pull_id]
    · rw [← pull_comp, e.hom_inv_id, pull_id]
  have hf2 : f = a.hom ≫ f' ≫ b.inv := by rw [← Category.assoc, ← h]; simp
  have : ⇑(pull R f F n) = pull R a.hom F n ∘ pull R f' F n ∘ pull R b.inv F n := by
    funext x; rw [hf2]; simp only [Function.comp_apply]; rw [pull_comp, pull_comp]
  rw [this]
  exact (hiso a).comp ((hf n).comp (hiso b.symm))

theorem ι_comp_eq {T : CommRingCat.{0}} {X : Scheme.{0}} (p : X ⟶ Spec T) (V : X.Opens) (hV : IsAffineOpen V) :
    V.ι ≫ p = hV.isoSpec.hom ≫ Spec.map (gam p V) := by
  have h1 : Spec.map (gam p V) = hV.fromSpec ≫ p := by
    have := IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top (Spec T)) hV (by simp)
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at this
    rw [gam, Spec.map_comp]
    exact this
  rw [h1, ← Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec]

theorem Affine_of : Affine := by
  intro q i T K k X p V hV hb
  have hpo := IsPushout.of_hasPushout k (gam p V)
  have hre := hb _ _ _ hpo
  have hS := isPullback_SpecMap_of_isPushout _ _ _ _ hpo.flip
  have h1 := (isPullback_morphismRestrict (pullback.fst p (Spec.map k)) V).paste_vert
    (IsPullback.of_hasPullback p (Spec.map k))
  have h2 : IsPullback hV.isoSpec.hom (V.ι ≫ p) (Spec.map (gam p V)) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [ι_comp_eq p V hV, Category.comp_id]⟩
  have h3 := h1.paste_horiz h2
  rw [Category.comp_id] at h3
  refine eqv_of_sq _ _ _ (sch.map (Spec.map (pushout.inr k (gam p V))))
    (sch.mapIso (h3.isoIsPullback _ _ hS)) (sch.mapIso hV.isoSpec) ?_ hre
  simp only [Functor.mapIso_hom, ← Functor.map_comp, IsPullback.isoIsPullback_hom_fst]

end LateralTheory.E.AffinePf

end
end
