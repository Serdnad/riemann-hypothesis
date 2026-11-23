module

public import Development.EtaleCohomology.KummerTheory.Bundle003
public import Development.EtaleCohomology.KummerTheory.Bundle010
public import Development.EtaleCohomology.KummerTheory.Bundle005
public import Development.EtaleCohomology.KummerTheory.Bundle006
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory

def NrmMk : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
  (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U),
  (∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U),
    Sec.res g (a p s h U x) = a p s h V ((E.obj (op (SimplexCategory.mk p))).map g.op x)) →
  ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev α p s h U x = a p s h U x

def NrmDelta : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n m : ℤ} (_hm : n + 1 = m)
  (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}) (p : ℕ) (s t : ℤ)
  (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U),
  ev (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) +
    m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev α p t (by omega) U ((E.δ i).app (op U) x)

def up {X U : Scheme.{0}} {p q : ℕ} (x : Sx (sch.obj X) p U) : Sx (sch.obj X) q U := x

theorem face_sch {X U : Scheme.{0}} {p : ℕ} (x : Sx (sch.obj X) (p + 1) U) (i : Fin (p + 2)) :
    ((sch.obj X).δ i).app (op U) x = up x := rfl

theorem altsum (k : ℕ) : ∑ i : Fin k, (-1 : ℤ) ^ (i : ℕ) = if Even k then 0 else 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (-1 : ℤ) ^ i) k]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd k with hk | hk
    · have : ¬ Even (k + 1) := by rw [Nat.even_add_one]; exact not_not.mpr hk
      simp [hk, this, hk.neg_one_pow]
    · have : Even (k + 1) := hk.add_one
      have h2 : ¬ Even k := Nat.not_even_iff_odd.mpr hk
      simp [h2, this, hk.neg_one_pow]

theorem ev_zero' (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} p s h U x :
    ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := by simp [ev]

theorem ev_sub' (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n) p s h U x :
    ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x := by
  rw [sub_eq_add_neg, ev_add, ev_neg, ← sub_eq_add_neg]

end LateralTheory.KummerTheory

namespace LateralTheory.KummerTheory

theorem DictNormal_of (hM : NrmMk) (hD : NrmDelta) : DictNormal := by
  intro R _ I X n α
  have hα : δ n (n + 1) α.1 = 0 := (Cocycle.mem_iff n (n + 1) rfl α.1).1 α.2
  obtain ⟨β, hβ⟩ := hM R (E := sch.obj X) (I := I) (n := n - 1)
    (fun p s h U x => if Odd p then n.negOnePow • ev α.1 (p + 1) s (by push_cast; omega) U (up x) else 0)
    (by
      intro p s h V U g x
      dsimp only
      split_ifs
      · rw [Units.smul_def, Units.smul_def]
        refine (map_zsmul ((I.X s).obj.map g.op).hom _ _).trans ?_
        exact congrArg (fun v => (n.negOnePow : ℤ) • v) (ev_res R α.1 (p + 1) s _ V U g (up x))
      · exact map_zero _)
  let γ : Cocycle ((chains R).obj (sch.obj X)) I n :=
    ⟨δ (n - 1) n β, (Cocycle.mem_iff n (n + 1) rfl _).2 (δ_δ _ _ _ _)⟩
  refine ⟨α - γ, ?_, ?_⟩
  · rw [CohomologyClass.mk_sub, sub_eq_self, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff γ (n - 1) (by omega)]
    exact ⟨β, rfl⟩
  · intro p s h U y
    show ev (α.1 - δ (n - 1) n β) (p + 1) s h U y = 0
    rw [ev_sub', sub_eq_zero]
    rw [hD R (by omega) β U p (s - 1) s (by push_cast at h ⊢; omega) h y]
    simp only [face_sch, hβ]
    rcases Nat.even_or_odd p with hp | hp
    ·
      have hp1 : Odd (p + 1) := hp.add_one
      have hp0 : ¬ Odd p := Nat.not_odd_iff_even.mpr hp
      simp only [hp1, hp0, if_true, if_false, smul_zero, Finset.sum_const_zero, add_zero]
      have hc := hD R (n := n) (m := n + 1) rfl α.1 U (p + 1) (s - 1) s (by push_cast at h ⊢; omega)
        (by push_cast at h ⊢; omega) (up y)
      rw [hα, ev_zero'] at hc
      simp only [face_sch] at hc
      rw [← Finset.sum_smul, altsum] at hc
      have he : ¬ Even (p + 1 + 2) := by
        rw [Nat.not_even_iff_odd]; exact hp1.add_even even_two
      simp only [he, if_false, one_smul] at hc
      rw [Int.negOnePow_succ, Units.neg_smul] at hc
      have key := add_neg_eq_zero.1 hc.symm
      rw [Units.smul_def]
      refine Eq.trans ?_ (map_zsmul ((I.d (s - 1) s).hom.app (op U)).hom _ _).symm
      rw [show (ModuleCat.Hom.hom ((I.d (s - 1) s).hom.app (op U))) (ev α.1 (p + 1 + 1) (s - 1) (by push_cast at h ⊢; omega) U (up y))
          = n.negOnePow • ev α.1 (p + 1) s (by push_cast at h ⊢; omega) U (up (up y)) from key]
      rw [← Units.smul_def, smul_smul, Int.units_mul_self, one_smul]
      rfl
    · have hp1 : ¬ Odd (p + 1) := Nat.not_odd_iff_even.mpr hp.add_one
      simp only [hp1, hp, if_true, if_false, map_zero, zero_add]
      rw [← Finset.sum_smul, altsum]
      have he : ¬ Even (p + 2) := by
        rw [Nat.not_even_iff_odd]; exact hp.add_even even_two
      simp only [he, if_false, one_smul, smul_smul, Int.units_mul_self]
      rfl

end LateralTheory.KummerTheory

namespace LateralTheory.KummerTheory

theorem chains_d (R : Type) [CommRing R] (E : Spc) (p : ℕ) :
    (chainsXIso R E (p + 1)).inv ≫ ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) =
      (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i)) ≫ (chainsXIso R E p).inv := by
  simp only [chainsXIso, chains, Functor.comp_obj]
  erw [HomologicalComplex.extend_d_eq _ _ (i := p + 1) (j := p) rfl rfl]
  erw [Iso.inv_hom_id_assoc]
  congr 1
  simp only [chainsN, Functor.comp_obj]
  erw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
  rfl

def evAt {R : Type} [CommRing R] {F G : Shv R} (U : Scheme.{0}) (y : Sec F U) : (F ⟶ G) →+ Sec G U where
  toFun φ := (φ.hom.app (op U)).hom y
  map_zero' := by simp
  map_add' := by simp

theorem evAt_apply {R : Type} [CommRing R] {F G : Shv R} (U : Scheme.{0}) (y : Sec F U) (φ : F ⟶ G) :
    evAt U y φ = (φ.hom.app (op U)).hom y := rfl

theorem nrmDelta : NrmDelta := by
  intro R _ E I n m hm α U p s t hs ht x
  unfold ev
  rw [δ_v n m hm α (-((p + 1 : ℕ) : ℤ)) t ht s (-(p : ℤ)) (by omega) (by push_cast; omega)]
  rw [Preadditive.comp_add, Units.smul_def, Preadditive.comp_zsmul, ← Category.assoc _ (((chains R).obj E).d _ _),
    chains_d]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, Category.assoc]
  simp [Units.smul_def, Finset.smul_sum]
  refine (map_sum (evAt (G := I.X t) U (freeGen R (E.obj (op (SimplexCategory.mk (p + 1)))) U x)) _ _).trans ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, map_zsmul]
  congr 2
  have := free_gen_map R (E.δ i) U x
  rw [evAt_apply]
  simp
  exact congrArg (fun z => (ModuleCat.Hom.hom ((α.v (-(p : ℤ)) t (by push_cast at ht ⊢; omega)).hom.app (op U)))
    ((ModuleCat.Hom.hom ((chainsXIso R E p).inv.hom.app (op U))) z)) this

end LateralTheory.KummerTheory

namespace LateralTheory.KummerTheory

theorem DictNormal_of' (hM : NrmMk) : DictNormal := DictNormal_of hM nrmDelta
end LateralTheory.KummerTheory
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Polynomial

namespace LateralTheory.KummerTheory

theorem twGen_res {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (f : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res f (twGen i ζ) = twGen i (Prim.map f.appTop.hom ζ) := by
  have h := (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality f.op
  have h2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h)
    (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj Γ(U, ⊤))
  simp only [ModuleCat.hom_comp] at h2
  unfold twGen ofRings.sec
  rw [← Finsupp.mapDomain_single]
  exact h2.symm

theorem twGen_zero_eq {q : ℕ} {V : Scheme.{0}} (ζ ξ : Prim q Γ(V, ⊤)) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) : twGen 0 ξ = twGen 0 ζ := by
  unfold twGen
  congr 1
  refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨ζ, ξ, a, h, ?_⟩)
  simp
  rfl

theorem prim_pow {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  obtain ⟨c, hc⟩ := cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (aeval ζ.1) hc
  rw [map_mul, ζ.2.2, zero_mul] at h
  simpa [sub_eq_zero] using h

theorem prim_isPrimitiveRoot {q : ℕ} {K : Type} [Field K] (μ : Prim q K) : IsPrimitiveRoot μ.1 q := by
  obtain ⟨z, hz1, hz2⟩ := μ
  have : NeZero (q : K) := ⟨hz1.ne_zero⟩
  refine (isRoot_cyclotomic_iff).1 ?_
  rw [aeval_def, algebraMap_int_eq] at hz2
  show Polynomial.eval z (cyclotomic q K) = 0
  rw [← map_cyclotomic_int, Polynomial.eval_map]
  exact hz2

theorem local_pow {q : ℕ} [NeZero q] {U : Scheme.{0}} (ζ ξ : Prim q Γ(U, ⊤)) (x : U) :
    ∃ (h : Γ(U, ⊤)) (a : (ZMod q)ˣ), x ∈ U.basicOpen h ∧ h * (ξ.1 - ζ.1 ^ (a : ZMod q).val) = 0 := by
  let e := (U.evaluation ⊤ x trivial).hom
  have hζ := prim_isPrimitiveRoot (Prim.map e ζ)
  have hξ := prim_isPrimitiveRoot (Prim.map e ξ)
  obtain ⟨i, hi, hie⟩ := hζ.eq_pow_of_pow_eq_one hξ.pow_eq_one
  have hcop : i.Coprime q := (hζ.pow_iff_coprime (NeZero.pos q) i).1 (hie ▸ hξ)
  have hav : ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val = i := by
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt hi]
  obtain ⟨k, hk⟩ := binomExpansion ((X : Polynomial Γ(U, ⊤)) ^ q - 1) ξ.1
    (ζ.1 ^ ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val - ξ.1)
  have hξq := prim_pow ξ
  have hζq : (ζ.1 ^ ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val) ^ q = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, prim_pow ζ, one_pow]
  refine ⟨(q : Γ(U, ⊤)) * ξ.1 ^ (q - 1) + k * (ζ.1 ^ ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val - ξ.1),
    ZMod.unitOfCoprime i hcop, ?_, ?_⟩
  · rw [← Scheme.evaluation_ne_zero_iff_mem_basicOpen (X := U) (U := ⊤) x (show x ∈ (⊤ : U.Opens) from trivial)]
    have hy : e (ζ.1 ^ ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val - ξ.1) = 0 := by
      rw [map_sub, map_pow, hav, sub_eq_zero]
      exact hie
    have hq : ((q : ℕ) : U.residueField x) ≠ 0 := (Prim.map e ξ).2.1.ne_zero
    change e _ ≠ 0
    rw [map_add (f := _), map_mul, map_mul, hy, mul_zero, add_zero, map_pow, map_natCast]
    exact mul_ne_zero hq (pow_ne_zero _ (hξ.ne_zero (NeZero.ne q)))
  · have hs : ξ.1 + (ζ.1 ^ ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val - ξ.1) =
        ζ.1 ^ ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val := by ring
    rw [hs] at hk
    simp only [eval_sub, eval_pow, eval_X, eval_one, hζq, hξq, sub_self, derivative_sub, derivative_X_pow,
      derivative_one, sub_zero, eval_mul, eval_C] at hk
    linear_combination hk

theorem sec_eq_of_cover {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} {ι : Type} (V : ι → U.Opens)
    (hV : TopologicalSpace.IsOpenCover V) (s t : Sec F U) (h : ∀ i, Sec.res (V i).ι s = Sec.res (V i).ι t) :
    s = t := by
  let S : Sieve U := {
    arrows := fun W f => Sec.res f s = Sec.res f t
    downward_closed := by
      intro W W' f hf g
      simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at hf ⊢
      rw [hf] }
  have hS : S ∈ Scheme.etaleTopology U := by
    apply Scheme.zariskiTopology_le_etaleTopology
    refine Scheme.zariskiTopology.superset_covering ?_
      (Scheme.Cover.mem_grothendieckTopology (U.openCoverOfIsOpenCover V hV))
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro W f ⟨i⟩
    exact h i
  have hsh : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget _) :=
    (isSheaf_iff_isSheaf_of_type _ _).1 (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget _) F.property)
  exact (hsh S hS).isSeparatedFor.ext fun W f hf => hf

theorem twGen_zero_indep {q : ℕ} [NeZero q] {U : Scheme.{0}} (ζ ξ : Prim q Γ(U, ⊤)) :
    twGen 0 ξ = twGen 0 ζ := by
  choose h a hx hh using fun x : U => local_pow ζ ξ x
  refine sec_eq_of_cover (fun x => U.basicOpen (h x)) ?_ _ _ fun x => ?_
  · refine eq_top_iff.2 fun y _ => ?_
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨y, hx y⟩
  rw [twGen_res, twGen_res]
  apply twGen_zero_eq _ _ (a x)
  change (U.basicOpen (h x)).ι.appTop.hom ξ.1 = (U.basicOpen (h x)).ι.appTop.hom ζ.1 ^ _
  rw [← map_pow, ← sub_eq_zero, ← map_sub]
  have hu : IsUnit ((U.basicOpen (h x)).ι.appTop.hom (h x)) := by
    rw [Scheme.Opens.ι_appTop]
    have key : ∀ (W : U.Opens) (hW : W = U.basicOpen (h x)) (hle : W ≤ ⊤),
        IsUnit (U.presheaf.map (homOfLE hle).op (h x)) := by
      rintro W rfl hle
      exact RingedSpace.isUnit_res_basicOpen U.toRingedSpace (h x)
    exact key _ (Scheme.Opens.ι_image_top _) _
  exact hu.mul_right_eq_zero.1 (by rw [← map_mul, hh x, map_zero])

theorem TwRes0_of : TwRes0 := by
  intro q _ U X x ζ₀ ζ
  rw [twGen_res]
  exact twGen_zero_indep _ _

end LateralTheory.KummerTheory
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.LHCut

theorem bcMap_comp' {X : Scheme.{0}} {R A B C : CommRingCat.{0}} (p : X ⟶ Spec R) (f : R ⟶ A) (g : R ⟶ B) (g' : R ⟶ C)
    (h : A ⟶ B) (h' : B ⟶ C) (e : f ≫ h = g) (e' : g ≫ h' = g') :
    bcMap p g g' h' e' ≫ bcMap p f g h e = bcMap p f g' (h ≫ h') (by rw [← Category.assoc, e, e']) := by
  apply pullback.hom_ext <;>
    simp only [bcMap, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc, Category.comp_id, Spec.map_comp]

theorem bcMap_eq {X : Scheme.{0}} {R A B : CommRingCat.{0}} (p : X ⟶ Spec R) (f : R ⟶ A) (g : R ⟶ B)
    (h h' : A ⟶ B) (e : f ≫ h = g) (hh : h = h') : bcMap p f g h e = bcMap p f g h' (hh ▸ e) := by
  subst hh; rfl

theorem CokAff_of (hS : StrictHenselization) (hC : Cont) (hL : LhNat) : CokAff := by
  classical
  intro h2 h6 hb1 q _ X R p _ _ hq i r c M N n hiso B s b x
  obtain ⟨J, _, _, D, cc, hcc, u, hSH, hu⟩ := hS B b
  have hun : ∀ {j k : J} (f : j ⟶ k), u.app j ≫ D.map f = u.app k := by
    intro j k f
    have := u.naturality f
    simpa using this.symm
  let j0 : J := (IsFiltered.nonempty (C := J)).some
  let w : B ⟶ cc.pt := u.app j0 ≫ cc.ι.app j0
  have hw : ∀ j, u.app j ≫ cc.ι.app j = w := by
    intro j
    show _ = u.app j0 ≫ cc.ι.app j0
    rw [← cc.w (IsFiltered.leftToMax j j0), ← cc.w (IsFiltered.rightToMax j j0), ← Category.assoc,
      ← Category.assoc, hun, hun]
  let v : R ⟶ cc.pt := s ≫ w
  obtain ⟨y, hy⟩ := (hiso cc.pt v hSH).2 (pull _ (sch.map (bcMap p s v w rfl)) _ _ x)
  have hqc : IsUnit ((q : ℕ) : cc.pt) := by simpa using hq.map v.hom
  have hB := fun n' i' => (hb1 q D cc hcc n' i').1
  choose jj z hz using fun (a : Fin (M + 1)) (t : Fin (r a)) => hB _ _ (y a t) hqc
  obtain ⟨k0, hk0⟩ := IsFiltered.sup_objs_exists
    (Finset.univ.image (fun pr : (Σ a : Fin (M + 1), Fin (r a)) => jj pr.1 pr.2))
  have fk : ∀ a t, jj a t ⟶ k0 := fun a t => (hk0 (Finset.mem_image.2 ⟨⟨a, t⟩, Finset.mem_univ _, rfl⟩)).some
  let y0 : ∀ a : Fin (M + 1), Fin (r a) → Ht q (sch.obj (Spec (D.obj k0))) (n - ((a : ℕ) : ℤ)) 0 :=
    fun a t => pull _ (sch.map (Spec.map (D.map (fk a t)))) _ _ (z a t)
  have hy0 : ∀ a t, pull _ (sch.map (Spec.map (cc.ι.app k0))) _ _ (y0 a t) = y a t := by
    intro a t
    rw [← hz a t]
    simp only [y0]
    rw [← pull_comp, ← Functor.map_comp, ← Spec.map_comp, cc.w]
    rfl
  let g : Over.mk (Spec.map v) ⟶ Over.mk (Spec.map (s ≫ u.app k0)) :=
    Over.homMk (Spec.map (cc.ι.app k0)) (by
      show Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp, Category.assoc, hw])
  have hrst : rst p g = bcMap p (s ≫ u.app k0) v (cc.ι.app k0) (by rw [Category.assoc, hw]) := rfl
  have h0 := hL h6 q p i r c M n g y0
  rw [hrst] at h0
  have hyy : (fun a t => pull _ (sch.map g.left) _ _ (y0 a t)) = y := by
    funext a t; exact hy0 a t
  rw [hyy] at h0
  let e := lh q p (Spec.map (s ≫ u.app k0)) i r c M n y0 -
    N • pull _ (sch.map (bcMap p s (s ≫ u.app k0) (u.app k0) rfl)) _ _ x
  have he : pull _ (sch.map (bcMap p (s ≫ u.app k0) v (cc.ι.app k0) (by rw [Category.assoc, hw]))) _ _ e = 0 := by
    simp only [e, map_sub, map_nsmul]
    erw [h0, hy, ← pull_comp, ← Functor.map_comp, bcMap_comp', bcMap_eq _ _ _ _ _ _ (hw k0)]
    exact sub_self _
  have hC2 := (hC h2 hb1 q p hq D cc hcc (fun j => s ≫ u.app j)
    (fun {j k} f => by simp only [Category.assoc, hun]) v (fun j => by simp only [v, Category.assoc, hw]) n i).2 k0 e he
  obtain ⟨k1, f1, hk1⟩ := hC2
  obtain ⟨het, 𝔮, h𝔮⟩ := hu k1
  refine ⟨D.obj k1, u.app k1, het, ⟨(by exact 𝔮 : Spec (D.obj k1)), ?_⟩, fun a t => pull _ (sch.map (Spec.map (D.map f1))) _ _ (y0 a t), ?_⟩
  · exact (PrimeSpectrum.ext h𝔮 : PrimeSpectrum.comap (u.app k1).hom 𝔮 = b)
  · let g' : Over.mk (Spec.map (s ≫ u.app k1)) ⟶ Over.mk (Spec.map (s ≫ u.app k0)) :=
      Over.homMk (Spec.map (D.map f1)) (by
        show Spec.map _ ≫ Spec.map _ = Spec.map _
        rw [← Spec.map_comp, Category.assoc, hun])
    have h1 := hL h6 q p i r c M n g' y0
    have hrst' : rst p g' = bcMap p (s ≫ u.app k0) (s ≫ u.app k1) (D.map f1) (by rw [Category.assoc, hun]) := rfl
    rw [hrst'] at h1
    beta_reduce at hk1
    simp only [e, map_sub, map_nsmul, sub_eq_zero] at hk1
    erw [h1] at hk1
    refine hk1.trans ?_
    erw [← pull_comp, ← Functor.map_comp, bcMap_comp', bcMap_eq _ _ _ _ _ _ (hun f1)]

end LateralTheory.KummerTheory.LHCut
end
end

section

noncomputable section

open IsLocalRing Algebra

namespace LateralTheory.KummerTheory

def PlaceResGood : Prop := ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra k K] (A : LocalSubring K),
  PlaceGood k K A → ∀ (y : K) (S : Subring K) (hAS : A.toSubring ≤ S),
    S = (Algebra.adjoin A.toSubring {y}).toSubring → ∀ (Q : Ideal S) [Q.IsMaximal],
      (maximalIdeal A.toSubring).map (Subring.inclusion hAS) ≤ Q →
        PlaceGood k K (LocalSubring.ofPrime S Q)

theorem PlaceStep_of (hR : PlaceResGood) : PlaceStep := by
  intro k K _ _ _ _ A hA hmax x

  have collapse : ∀ (y : K) (S : Subring K) (hAS : A.toSubring ≤ S),
      S = (Algebra.adjoin A.toSubring {y}).toSubring → ∀ (Q : Ideal S) [Q.IsMaximal],
      (maximalIdeal A.toSubring).map (Subring.inclusion hAS) ≤ Q → S ≤ A.toSubring := by
    intro y S hAS hS Q _ hQ
    have hle : A ≤ LocalSubring.ofPrime S Q := by
      refine ⟨hAS.trans (LocalSubring.le_ofPrime ..), ((local_hom_tfae _).out 3 1).mp ?_⟩
      conv_rhs => rw [← IsLocalization.AtPrime.map_eq_maximalIdeal Q]
      refine .trans ?_ (Ideal.map_mono hQ)
      rw [Ideal.map_map]; rfl
    exact (LocalSubring.le_ofPrime S Q).trans (hmax _ hle (hR k K A hA y S hAS hS Q hQ)).1
  have top : ∀ y ∉ A.toSubring,
      (maximalIdeal A.toSubring).map
        (Subring.inclusion (T := (Algebra.adjoin A.toSubring {y}).toSubring)
          (fun r hr => algebraMap_mem (Algebra.adjoin A.toSubring {y}) ⟨r, hr⟩)) = ⊤ := by
    intro y hy
    by_contra hne
    obtain ⟨Q, hQm, hQ⟩ := Ideal.exists_le_maximal _ hne
    exact hy (collapse y _ _ rfl Q hQ (self_mem_adjoin_singleton _ _))
  have intmem : ∀ z : K, IsIntegral A.toSubring z → z ∈ A.toSubring := by
    intro z hz
    let S := A.toSubring[z]
    have : Algebra.IsIntegral A.toSubring S := Algebra.IsIntegral.adjoin (by simpa)
    obtain ⟨Q : Ideal S.toSubring, hQ, e⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
      (S := S) (maximalIdeal A.toSubring) (le_maximalIdeal (by set_option synthInstance.maxHeartbeats 400000 in simp))
    exact collapse z S.toSubring (fun r hr => algebraMap_mem S ⟨r, hr⟩) rfl Q
      (Ideal.map_le_iff_le_comap.mpr e.ge) (self_mem_adjoin_singleton _ _)
  by_cases hx : x ∈ A.toSubring
  · exact Or.inl hx
  right
  refine intmem _ ?_
  have hx0 : x ≠ 0 := fun e => hx (e ▸ zero_mem _)
  let := invertibleOfNonzero hx0
  have ⟨p, hp, hpx⟩ := exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top x _
    (maximalIdeal.isMaximal A.toSubring).ne_top (top_unique ((top x hx).ge.trans le_self_add))
  have H : IsUnit p.leadingCoeff := of_not_not fun h => by simpa using sub_mem h hp
  exact ⟨.C H.unit⁻¹.1 * p, by simp [Polynomial.Monic], by simpa using .inr hpx⟩

end LateralTheory.KummerTheory
end
end
