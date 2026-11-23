module

public import Development.EtaleCohomology.TateTwists.Bundle006
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
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
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.MkPf

variable {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}

noncomputable def eta (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) :
    (freeP R).obj (E.obj (op (SimplexCategory.mk p))) ⟶ (I.X s).obj where
  app U := ModuleCat.freeDesc (R := ULift.{1} R) (X := ULift.{1} (Sx E p U.unop))
    (M := (I.X s).obj.obj U) (TypeCat.ofHom fun (y : ULift.{1} (Sx E p U.unop)) => a p s h U.unop y.down)
  naturality U V f := by
    refine ModuleCat.free_hom_ext (X := ULift.{1} (Sx E p U.unop)) (fun y => ?_)
    have := ha p s h V.unop U.unop f.unop y.down
    simp only [Sec.res, Sx.res, Quiver.Hom.op_unop] at this
    change (ModuleCat.freeDesc (M := (I.X s).obj.obj V)
        (TypeCat.ofHom fun (z : ULift.{1} (Sx E p V.unop)) => a p s h V.unop z.down))
        ((ModuleCat.free (ULift.{1} R)).map (TypeCat.ofHom fun (z : ULift.{1} (Sx E p U.unop)) =>
          ULift.up.{1} ((E.obj (op (SimplexCategory.mk p))).map f z.down)) (ModuleCat.freeMk y)) =
      ((I.X s).obj.map f) (ModuleCat.freeDesc (M := (I.X s).obj.obj U)
        (TypeCat.ofHom fun (z : ULift.{1} (Sx E p U.unop)) => a p s h U.unop z.down) (ModuleCat.freeMk y))
    rw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
    exact this.symm

noncomputable def mF (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) :
    (free R).obj (E.obj (op (SimplexCategory.mk p))) ⟶ I.X s :=
  ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ (I.X s)).symm
    (eta a ha p s h)

lemma mF_gen (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ((mF a ha p s h).hom.app (op U)).hom (freeGen R _ U x) = a p s h U x := by
  have e := toSheafify_sheafifyLift Scheme.etaleTopology.{0} (eta a ha p s h) (I.X s).property
  have e2 := congrArg (fun φ => (φ.app (op U)).hom (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} x))) e
  simp only [NatTrans.comp_app, ModuleCat.hom_comp] at e2
  exact e2.trans (ModuleCat.freeDesc_apply _ _)

noncomputable def mC (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) :
    Cochain ((chains R).obj E) I n :=
  Cochain.mk fun i j hij => if hi : i ≤ 0 then
    (((chains R).obj E).XIsoOfEq (show i = -(((-i).toNat : ℕ) : ℤ) by omega)).hom ≫
      (chainsXIso R E (-i).toNat).hom ≫ mF a ha (-i).toNat j (by omega)
  else 0

lemma mC_v (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) :
    (mC a ha).v _ _ h = (chainsXIso R E p).hom ≫ mF a ha p s h := by
  have key : ∀ (q : ℕ), q = p → ∀ (e : -(p : ℤ) = -(q : ℤ)) (h' : -(q : ℤ) + n = s),
      (((chains R).obj E).XIsoOfEq e).hom ≫ (chainsXIso R E q).hom ≫ mF a ha q s h' =
        (chainsXIso R E p).hom ≫ mF a ha p s h := by
    rintro q rfl e h'
    simp
  rw [mC, Cochain.mk_v, dite_eq_left (by omega)]
  exact key _ (by omega) _ _

end LateralTheory.EtaleFoundations.MkPf

open LateralTheory.EtaleFoundations LateralTheory.EtaleFoundations.MkPf in
theorem LateralTheory.EtaleFoundations.etale_simplicial_chains_cochain_mk_of_compatible_sections : EtaleSimplicialCochainExistsFromNaturalSections := by
  intro R _ E I n a ha
  refine ⟨mC a ha, fun p s h U x => ?_⟩
  unfold ev
  rw [mC_v, Iso.inv_hom_id_assoc]
  exact mF_gen a ha p s h U x
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.SubdivisionComposition

lemma subint_comp (N j l j' l' : ℕ) (h : j + l ≤ N) (h' : j' + l' ≤ l) :
    SimplexCategory.subinterval j' l' h' ≫ SimplexCategory.subinterval j l h =
      SimplexCategory.subinterval (n := N) (j + j') l' (by omega) := by
  ext i
  change ((i : ℕ) + j' + j) = (i : ℕ) + (j + j')
  omega

lemma subint_id (N : ℕ) :
    SimplexCategory.subinterval (n := N) 0 N (by omega) = 𝟙 _ := by
  ext i
  simp [SimplexCategory.subinterval]

lemma along_comp {E : Spc} {U : Scheme.{0}} {N p r : ℕ} (x : Sx E N U)
    (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk p) :
    (x.along a).along b = x.along (b ≫ a) := by
  simp only [Sx.along, op_comp, Functor.map_comp, NatTrans.comp_app, types_comp_apply]

end LateralTheory.EtaleFoundations.SubdivisionComposition

open LateralTheory.EtaleFoundations.SubdivisionComposition in
theorem LateralTheory.EtaleFoundations.simplicial_subinterval_of_subinterval_along_etale : LateralTheory.EtaleFoundations.EtaleSimplexSubfaceComposition := by
  intro E U N x
  have hsa : ∀ (j l : ℕ) (h : j + l ≤ N), x.sub j l h = x.along (SimplexCategory.subinterval j l h) :=
    fun _ _ _ => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j l j' l' h h'
    change (x.along _).along _ = x.along _
    rw [along_comp, subint_comp]
  · rw [hsa, subint_id]
    simp [Sx.along]
  · intro j l h
    refine ⟨?_, ?_, hsa j l h⟩
    · intro V g
      simp only [Sx.sub, Sx.res]
      have hn := ConcreteCategory.congr_hom ((E.map (SimplexCategory.subinterval j l h).op).naturality g.op) x
      simp only [ConcreteCategory.comp_apply] at hn
      exact hn
    · intro E' f
      simp only [Sx.sub, Sx.map]
      have hn := congrArg (fun t => t.app (op U)) (f.naturality (SimplexCategory.subinterval j l h).op)
      simp only [NatTrans.comp_app] at hn
      first
        | (have hm := ConcreteCategory.congr_hom hn x
           simp only [ConcreteCategory.comp_apply] at hm
           first | exact hm | exact hm.symm)
        | exact (congrFun hn x).symm
        | (rw [← types_comp_apply, ← hn]; rfl)
  · intro p r a b
    exact along_comp x a b
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

lemma cob_altsum (k : ℕ) : ∑ i : Fin k, (-1 : ℤ) ^ (i : ℕ) = if k % 2 = 0 then 0 else 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (-1 : ℤ) ^ i) k]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · have : (j + j) % 2 = 0 := by omega
      have h2 : (j + j + 1) % 2 ≠ 0 := by omega
      simp [this, h2, ← two_mul, pow_mul]
    · have : (2 * j + 1) % 2 ≠ 0 := by omega
      have h2 : (2 * j + 1 + 1) % 2 = 0 := by omega
      simp [this, h2, pow_succ, pow_mul]

lemma cob_map_zsmul {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (c : ℤ) (z : Sec F U) :
    Sec.map φ (c • z) = c • Sec.map φ z := by
  simp [Sec.map]

lemma cob_map_zero {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} :
    Sec.map φ (0 : Sec F U) = 0 := by
  simp [Sec.map]

lemma cob_res_zsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (c : ℤ) (z : Sec F U) :
    Sec.res g (c • z) = c • Sec.res g z := by
  simp [Sec.res]

end LateralTheory.EtaleFoundations

namespace LateralTheory.EtaleFoundations

noncomputable def cobB {R : Type} [CommRing R] (X : Scheme.{0}) (I : Cx R) (m n : ℤ) (hmn : m + 1 = n)
    (α : Cochain ((chains R).obj (sch.obj X)) I n) :
    ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + m = s → ∀ U : Scheme.{0}, Sx (sch.obj X) p U → Sec (I.X s) U :=
  fun p s h U x => if p % 2 = 1 then ((n.negOnePow : ℤ)) • ev α (p + 1) s (by push_cast; omega) U
    (show Sx (sch.obj X) (p + 1) U from (x : U ⟶ X)) else 0

end LateralTheory.EtaleFoundations

open LateralTheory.EtaleFoundations in
theorem LateralTheory.EtaleFoundations.etaleSimplicialScheme_cocycle_vanishing_at_id_isCoboundary_of_evaluati (hmk : EtaleSimplicialCochainExistsFromNaturalSections) (hdl : EtaleSimplicialCochainEvaluationDifferentialFormula)
    (hb : EtaleSimplicialCochainEvaluationProperties) : EtaleSimplicialSchemeCocycleVanishingAtIdIsCoboundary := by
  intro R _ X I m n hmn α h0
  have hεε : (n.negOnePow : ℤ) * (n.negOnePow : ℤ) = 1 := by
    rw [← Units.val_mul, ← Int.negOnePow_add, ← two_mul, Int.negOnePow_two_mul]; rfl

  have hnat : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx (sch.obj X) p U),
      Sec.res g (cobB X I m n hmn α.1 p s h U x) = cobB X I m n hmn α.1 p s h V (x.res g) := by
    intro p s h V U g x
    unfold cobB
    split_ifs
    · rw [cob_res_zsmul]
      exact congrArg (((n.negOnePow : ℤ)) • ·) ((hb R).2.1 α.1 (p + 1) s _ V U g (show Sx (sch.obj X) (p + 1) U from (x : U ⟶ X)))
    · simp [Sec.res]
  obtain ⟨β, hβ⟩ := hmk R (cobB X I m n hmn α.1) hnat
  refine ⟨β, ?_⟩

  have hα0 : ∀ U (x : Sx (sch.obj X) 0 U), ev α.1 0 n (by simp) U x = 0 := by
    intro U x
    have e : ev α.1 0 n (by simp) U x = Sec.res (x : U ⟶ X) (ev α.1 0 n (by simp) X (𝟙 X)) := by
      rw [(hb R).2.1 α.1 0 n (by simp) U X x (𝟙 X)]; rfl
    rw [e, h0]; simp [Sec.res]

  have hcyc : ∀ (p : ℕ) (s t : ℤ) (hs : -((p + 2 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + n = t) U
      (x : Sx (sch.obj X) (p + 2) U), p % 2 = 0 →
      Sec.map (I.d s t) (ev α.1 (p + 2) s hs U x) = (n.negOnePow : ℤ) • ev α.1 (p + 1) t ht U
        (show Sx (sch.obj X) (p + 1) U from (x : U ⟶ X)) := by
    intro p s t hs ht U x hp
    have e := (hdl R rfl α.1 U).2 (p + 1) s t hs (by push_cast at ht ⊢; omega) x
    rw [Cocycle.δ_eq_zero, ((hb R (E := sch.obj X) (I := I) (n := n + 1)).1 0 0 (p + 1 + 1) t _ U x).2.2.1] at e
    have hsum : ∑ i : Fin (p + 1 + 2), (-1 : ℤ) ^ (i : ℕ) • ev α.1 (p + 1) t (by push_cast at ht ⊢; omega) U (x.face i)
        = (∑ i : Fin (p + 1 + 2), (-1 : ℤ) ^ (i : ℕ)) • ev α.1 (p + 1) t ht U
          (show Sx (sch.obj X) (p + 1) U from (x : U ⟶ X)) := by
      rw [Finset.sum_smul]; rfl
    rw [hsum, cob_altsum, if_neg (by omega), one_smul, Int.negOnePow_succ, Units.smul_def] at e
    rw [eq_comm, add_eq_zero_iff_eq_neg] at e
    rw [e]; simp
  apply (hb R).2.2.1
  intro p s h U x
  cases p with
  | zero =>
    obtain rfl : s = n := by omega
    rw [(hdl R hmn β U).1 x, hβ, hα0]
    simp [cobB, cob_map_zero]
  | succ p =>
    rw [(hdl R hmn β U).2 p (-((p + 1 : ℕ) : ℤ) + m) s rfl h x]
    simp only [hβ]
    have hsum : ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • cobB X I m n hmn α.1 p s (by push_cast at h ⊢; omega) U (x.face i)
        = (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ)) • cobB X I m n hmn α.1 p s (by push_cast at h ⊢; omega) U
          (show Sx (sch.obj X) p U from (x : U ⟶ X)) := by
      rw [Finset.sum_smul]; rfl
    rw [hsum, cob_altsum, Units.smul_def]
    rcases Nat.even_or_odd p with ⟨j, rfl⟩ | ⟨j, rfl⟩
    ·
      have h1 : (j + j + 1) % 2 = 1 := by omega
      have h2 : (j + j + 2) % 2 = 0 := by omega
      simp only [cobB, h1, h2, ↓reduceIte, zero_smul, smul_zero, add_zero]
      rw [cob_map_zsmul]
      have hc := hcyc (j + j) (-((j + j + 1 : ℕ) : ℤ) + m) s (by push_cast; omega) (by push_cast at h ⊢; omega) U x (by omega)
      erw [hc]
      rw [smul_smul, hεε, one_smul]
    · have h1 : (2 * j + 1 + 1) % 2 = 0 := by omega
      have h2 : (2 * j + 1 + 2) % 2 = 1 := by omega
      have h3 : (2 * j + 1) % 2 = 1 := by omega
      simp only [cobB, h1, h2, h3, ↓reduceIte, one_ne_zero, one_smul, smul_smul]
      rw [if_neg (by omega), cob_map_zero, zero_add, one_mul, hεε, one_smul]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.TensFam

theorem res_res {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res h (Sec.res g y) = Sec.res (h ≫ g) y := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem loc_and {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P) (hQ : Loc U Q) :
    Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, h1⟩ := hP
  obtain ⟨T, hT, h2⟩ := hQ
  exact ⟨S ⊓ T, (Scheme.etaleTopology).intersection_covering hS hT, fun V g hg => ⟨h1 V g hg.1, h2 V g hg.2⟩⟩

theorem loc_top {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, (Scheme.etaleTopology).top_mem U, fun V g _ => h V g⟩

theorem sep {S : Type} [CommRing S] (M : Shv S) {U : Scheme.{0}} (s s' : Sec M U)
    (h : Loc U fun V g => Sec.res g s = Sec.res g s') : s = s' := by
  obtain ⟨T, hT, h1⟩ := h
  have hM := (isSheaf_iff_isSheaf_of_type _ _).mp ((Presheaf.isSheaf_iff_isSheaf_forget Scheme.etaleTopology M.obj (forget _)).mp M.2)
  exact (hM T hT).isSeparatedFor.ext fun V g hg => h1 V g hg

theorem glue {S : Type} [CommRing S] (M : Shv S) {U : Scheme.{0}} (T : Sieve U) (hT : T ∈ Scheme.etaleTopology U)
    (t : ∀ (V : Scheme.{0}) (g : V ⟶ U), T.arrows g → Sec M V)
    (ht : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : T.arrows g),
      t W (k ≫ g) (T.downward_closed hg k) = Sec.res k (t V g hg)) :
    ∃ s : Sec M U, ∀ V g (hg : T.arrows g), Sec.res g s = t V g hg := by
  have hM := (isSheaf_iff_isSheaf_of_type _ _).mp ((Presheaf.isSheaf_iff_isSheaf_forget Scheme.etaleTopology M.obj (forget _)).mp M.2)
  let x : Presieve.FamilyOfElements (M.obj ⋙ forget _) T.arrows := fun V g hg => t V g hg
  have hx : x.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro V W g k hg
    exact ht V W g k hg
  exact ⟨(hM T hT).amalgamate x hx, fun V g hg => (hM T hT).valid_glue hx g hg⟩

theorem lift_res {R : Type} [CommRing R] {I J K : Cx R} (τ : Pair I J K) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ)
    (x : Tens I J U w) : Sec.res g (τ.lift U w x) = τ.lift V w (Tens.res g w x) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | add a b ha hb => simp only [Sec.res, map_add (f := _)] at *; rw [ha, hb]
  | of i z =>
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [Sec.res, map_add (f := _)] at *; rw [ha, hb]
    | tmul a c =>
      rw [← DirectSum.lof_eq_of (ULift.{1} R)]
      simp only [Pair.lift, Tens.res, DirectSum.lmap_lof, DirectSum.toModule_lof, TensorProduct.lift.tmul, TensorProduct.map_tmul]
      exact τ.nat g _ _ w _ a c

theorem res_add {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (a c : Sec F U) :
    Sec.res g (a + c) = Sec.res g a + Sec.res g c := map_add _ _ _

section Main
variable {R S : Type} [CommRing R] [CommRing S] {I J K : Cx R}

def Good (τ : Pair I J K) (w : ℤ) (M : Shv S) (b : ∀ U : Scheme.{0}, Tens I J U w →+ Sec M U)
    (U : Scheme.{0}) (y : Sec (K.X w) U) (s : Sec M U) : Prop :=
  Loc U fun V g => ∃ x, τ.lift V w x = Sec.res g y ∧ Sec.res g s = b V x

variable (τ : Pair I J K) (hτ : τ.IsTensor) (w : ℤ) (M : Shv S) (b : ∀ U : Scheme.{0}, Tens I J U w →+ Sec M U)
  (hb : ∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (b U x) = b V (Tens.res g w x))
include hτ hb

theorem key {U : Scheme.{0}} (x1 x2 : Tens I J U w) (h : τ.lift U w x1 = τ.lift U w x2) : b U x1 = b U x2 := by
  have h0 : τ.lift U w (x1 - x2) = 0 := by rw [map_sub, h, sub_self]
  obtain ⟨T, hT, hT'⟩ := hτ.2 U w _ h0
  apply sep M
  refine ⟨T, hT, fun V g hg => ?_⟩
  have h1 : Tens.res g w (x1 - x2) = 0 := hT' V g hg
  rw [map_sub, sub_eq_zero] at h1
  show Sec.res g (b U x1) = Sec.res g (b U x2)
  rw [hb, hb, h1]

theorem uniq {U : Scheme.{0}} {y : Sec (K.X w) U} {s s' : Sec M U}
    (h1 : Good τ w M b U y s) (h2 : Good τ w M b U y s') : s = s' := by
  apply sep M
  obtain ⟨T, hT, h⟩ := loc_and h1 h2
  refine ⟨T, hT, fun V g hg => ?_⟩
  obtain ⟨⟨x, hx, hs⟩, ⟨x', hx', hs'⟩⟩ := h V g hg
  rw [hs, hs']
  exact key τ hτ w M b hb x x' (hx.trans hx'.symm)

theorem good_exists (U : Scheme.{0}) (y : Sec (K.X w) U) : ∃ s, Good τ w M b U y s := by
  obtain ⟨T, hT, hc⟩ := hτ.1 U w y
  let t : ∀ (V : Scheme.{0}) (g : V ⟶ U), T.arrows g → Sec M V := fun V g hg => b V (hc V g hg).choose
  obtain ⟨s, hs⟩ := glue M T hT t (by
    intro V W g k hg
    simp only [t]
    rw [hb]
    apply key τ hτ w M b hb
    rw [(hc W (k ≫ g) (T.downward_closed hg k)).choose_spec, ← lift_res, (hc V g hg).choose_spec, res_res])
  exact ⟨s, T, hT, fun V g hg => ⟨(hc V g hg).choose, (hc V g hg).choose_spec, hs V g hg⟩⟩

omit hτ in
theorem good_add {U : Scheme.{0}} {y1 y2 : Sec (K.X w) U} {s1 s2 : Sec M U}
    (h1 : Good τ w M b U y1 s1) (h2 : Good τ w M b U y2 s2) : Good τ w M b U (y1 + y2) (s1 + s2) := by
  obtain ⟨T, hT, h⟩ := loc_and h1 h2
  refine ⟨T, hT, fun V g hg => ?_⟩
  obtain ⟨⟨x, hx, hs⟩, ⟨x', hx', hs'⟩⟩ := h V g hg
  exact ⟨x + x', by rw [map_add (f := _), hx, hx', res_add], by rw [res_add, hs, hs', map_add (f := _)]⟩

omit hτ hb in
theorem good_zero (U : Scheme.{0}) : Good τ w M b U 0 0 :=
  loc_top fun V g => ⟨0, by simp, by simp⟩

omit hτ in
theorem good_nat {V U : Scheme.{0}} (g : V ⟶ U) {y : Sec (K.X w) U} {s : Sec M U}
    (h : Good τ w M b U y s) : Good τ w M b V (Sec.res g y) (Sec.res g s) := by
  obtain ⟨T, hT, h1⟩ := h
  refine ⟨T.pullback g, (Scheme.etaleTopology).pullback_stable g hT, fun W k hk => ?_⟩
  obtain ⟨x, hx, hs⟩ := h1 W (k ≫ g) hk
  exact ⟨x, by rw [res_res, hx], by rw [res_res, hs]⟩

omit hτ in
theorem good_lift (U : Scheme.{0}) (x : Tens I J U w) : Good τ w M b U (τ.lift U w x) (b U x) :=
  loc_top fun V g => ⟨Tens.res g w x, (lift_res τ g w x).symm, hb V U g x⟩

end Main

end LateralTheory.EtaleFoundations.TensFam

open LateralTheory.EtaleFoundations.TensFam in
theorem LateralTheory.EtaleFoundations.etale_tensor_hom_descends_along_tensor_pairing : LateralTheory.EtaleFoundations.EtaleTensorComplexDescendsNaturalFamily := by
  intro R S _ _ I J K τ hτ w M b hb
  have ex := good_exists τ hτ w M b hb
  let φ : ∀ U : Scheme.{0}, Sec (K.X w) U →+ Sec M U := fun U =>
    { toFun := fun y => (ex U y).choose
      map_zero' := uniq τ hτ w M b hb (ex U 0).choose_spec (good_zero τ w M b U)
      map_add' := fun y1 y2 => uniq τ hτ w M b hb (ex U _).choose_spec
        (good_add τ w M b hb (ex U y1).choose_spec (ex U y2).choose_spec) }
  refine ⟨φ, fun V U g y => ?_, fun U x => ?_⟩
  · exact uniq τ hτ w M b hb (good_nat τ w M b hb g (ex U y).choose_spec) (ex V _).choose_spec
  · exact uniq τ hτ w M b hb (ex U _).choose_spec (good_lift τ w M b hb U x)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleTensorTripleProductFamilyExists : Prop :=
  ∀ (R : Type) [CommRing R] {I J K T : Cx R} (τ : Pair I J T), τ.IsTensor → ∀ {M L : Cx R} (μ' : Pair J K M) (ν' : Pair I M L),
    ∃ m : ∀ (U : Scheme.{0}) (s t w : ℤ), s + t = w → Sec (T.X s) U →ₗ[ULift.{1} R] Sec (K.X t) U →ₗ[ULift.{1} R] Sec (L.X w) U,
      (∀ {V U : Scheme.{0}} (g : V ⟶ U) (s t w : ℤ) (h : s + t = w) (a : Sec (T.X s) U) (b : Sec (K.X t) U),
        Sec.res g (m U s t w h a b) = m V s t w h (Sec.res g a) (Sec.res g b)) ∧
      ∀ (U : Scheme.{0}) (s t u st tu w : ℤ) (h1 : s + t = st) (h2 : st + u = w) (h3 : t + u = tu) (h4 : s + tu = w) a b c,
        m U st u w h2 (τ.mul U s t st h1 a b) c = ν'.mul U s tu w h4 a (μ'.mul U t u tu h3 b c)

def LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibniz : Prop :=
  ∀ (R : Type) [CommRing R] {I J K T : Cx R} (τ : Pair I J T), τ.IsTensor → ∀ {M L : Cx R} (μ' : Pair J K M) (ν' : Pair I M L)
    (m : ∀ (U : Scheme.{0}) (s t w : ℤ), s + t = w → Sec (T.X s) U →ₗ[ULift.{1} R] Sec (K.X t) U →ₗ[ULift.{1} R] Sec (L.X w) U),
      (∀ {V U : Scheme.{0}} (g : V ⟶ U) (s t w : ℤ) (h : s + t = w) (a : Sec (T.X s) U) (b : Sec (K.X t) U),
        Sec.res g (m U s t w h a b) = m V s t w h (Sec.res g a) (Sec.res g b)) →
      (∀ (U : Scheme.{0}) (s t u st tu w : ℤ) (h1 : s + t = st) (h2 : st + u = w) (h3 : t + u = tu) (h4 : s + tu = w) a b c,
        m U st u w h2 (τ.mul U s t st h1 a b) c = ν'.mul U s tu w h4 a (μ'.mul U t u tu h3 b c)) →
      ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (T.X s) U) (b : Sec (K.X t) U),
        Sec.map (L.d w (w + 1)) (m U s t w h a b) = m U (s + 1) t (w + 1) (by omega) (Sec.map (T.d s (s + 1)) a) b +
          s.negOnePow • m U s (t + 1) (w + 1) (by omega) a (Sec.map (K.d t (t + 1)) b)

theorem LateralTheory.EtaleFoundations.etale_tensor_triple_product_of_family_and_leibniz (hfam : LateralTheory.EtaleFoundations.EtaleTensorTripleProductFamilyExists)
    (hleib : LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibniz) : LateralTheory.EtaleFoundations.EtaleTensorPairProductAssociative := by
  intro R _ I J K T T3 τ τ' hτ _ M L μ' ν'
  obtain ⟨m, hnat, heq⟩ := hfam R τ hτ μ' ν'
  refine ⟨⟨m, hnat, hleib R τ hτ μ' ν' m hnat heq⟩, ?_⟩
  intro U s t u st tu w h1 h2 h3 h4 a b c
  exact heq U s t u st tu w h1 h2 h3 h4 a b c
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.tqis

def acyc : Prop :=
  ∀ (R : Type) [CommRing R] {C J T : Cx R} (a b : ℤ) [C.IsStrictlyGE a] [J.IsStrictlyGE b] (τ : Pair C J T),
    τ.IsTensor → (∀ t, FlatS (J.X t)) → C.Acyclic → T.Acyclic

def cone : Prop :=
  ∀ (R : Type) [CommRing R] {I I' J T T' : Cx R} (τ : Pair I J T) (τ' : Pair I' J T') (f : I ⟶ I') (u : T ⟶ T'),
    τ.IsTensor → τ'.IsTensor → τ.Compat τ' f (𝟙 J) u → ∃ σ : Pair (mappingCone f) J (mappingCone u), σ.IsTensor

end LateralTheory.EtaleFoundations.tqis

theorem qis_iff_cone {R : Type} [CommRing R] {K L : Cx R} (f : K ⟶ L) : QuasiIso f ↔ (mappingCone f).Acyclic := by
  have h : HomotopyCategory.quasiIso (Shv R) (ComplexShape.up ℤ) ((HomotopyCategory.quotient _ _).map f) ↔ (HomotopyCategory.subcategoryAcyclic (Shv R)).trW ((HomotopyCategory.quotient _ _).map f) := by
    rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  rw [HomotopyCategory.quotient_map_mem_quasiIso_iff] at h
  change HomologicalComplex.quasiIso (Shv R) (ComplexShape.up ℤ) f ↔ _
  exact h.trans ((ObjectProperty.trW_iff_of_distinguished (HomotopyCategory.subcategoryAcyclic (Shv R)) _
    (HomotopyCategory.mappingCone_triangleh_distinguished f)).trans
    (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _))

theorem cone_ge {R : Type} [CommRing R] {I I' : Cx R} [I.IsStrictlyGE 0] [I'.IsStrictlyGE 0] (f : I ⟶ I') :
    (mappingCone f).IsStrictlyGE (-1) :=
  CochainComplex.isStrictlyGE_mappingCone f 0 0 (-1)

theorem LateralTheory.EtaleFoundations.etale_tensor_preserves_quasiIso_of_acyclic_and_cone (hA : LateralTheory.EtaleFoundations.tqis.acyc) (hC : LateralTheory.EtaleFoundations.tqis.cone) :
    LateralTheory.EtaleFoundations.EtaleTensorPairQuasiIsoOfFlatQuasiIso := by
  intro R _ I I' J T T' _ _ _ τ τ' hτ hτ' hJ f _ u hc
  obtain ⟨σ, hσ⟩ := hC R τ τ' f u hτ hτ' hc
  have := cone_ge f
  rw [qis_iff_cone]
  exact hA R (-1) 0 σ hσ hJ ((qis_iff_cone f).1 inferInstance)
end
