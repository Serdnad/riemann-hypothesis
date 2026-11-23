module

public import Development.EtaleCohomology.EtaleSheaves.Bundle011
public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import Development.EtaleCohomology.EtaleSheaves.Bundle012
public import Development.EtaleCohomology.EtaleSheaves.Bundle004
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
import Mathlib.Data.Finsupp.Pointwise
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.t_D3Cut

theorem slantHom_neg (R : Type) [CommRing R] {Γ : Type} [Group Γ] (X : Scheme.{0}) {m : ℕ} :
    ∃ f : ((Fin m → Γ) →₀ R) →+ _, ∀ c, f c = slantHom R X c :=
  ⟨AddMonoidHom.mk' (slantHom R X) (slantHom_add R X), fun _ => rfl⟩

theorem homD_of (h : Faces) : HomD := by
  intro R _ Γ _ X m b
  induction b using Finsupp.induction_linear with
  | zero => rw [slantHom_zero, show bd R (0 : (Fin (m + 1) → Γ) →₀ R) = 0 from map_zero _, slantHom_zero]; exact zero_comp
  | add a b ha hb =>
    rw [slantHom_add, show bd R (a + b) = bd R a + bd R b from map_add _ _ _, slantHom_add, ← ha, ← hb]
    exact Preadditive.add_comp _ _ _ _ _ _
  | single g r =>
    obtain ⟨f, hf⟩ := slantHom_neg R X (Γ := Γ) (m := m)
    have e : bd R (Finsupp.single g r) = Finsupp.single (fun i => g i.succ) r +
        ∑ j : Fin (m + 1), (-1 : ℤ) ^ ((j : ℕ) + 1) • Finsupp.single (j.contractNth (· * ·) g) r := by
      have := groupHomology.inhomogeneousChains.d_single (A := Rep.trivial R Γ R) m g r
      refine this.trans ?_
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Int.cast_smul_eq_zsmul R]
      simp
    have d : ((chainsN R).obj (BX Γ X)).d (m + 1) m =
        ∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map ((BX Γ X).δ i) :=
      AlgebraicTopology.alternatingFaceMapComplex_obj_d _ m

    rw [e, ← hf (_ + _), map_add (f := _), map_sum, d, slantHom_single]
    have e2 : ∀ j : Fin (m + 1), f ((-1 : ℤ) ^ ((j : ℕ) + 1) • Finsupp.single (j.contractNth (· * ·) g) r) =
        (-1 : ℤ) ^ ((j : ℕ) + 1) • (ULift.up r : ULift.{1} R) • (free R).map (grpPt X (j.contractNth (· * ·) g)) :=
      fun j => by rw [map_zsmul, hf, slantHom_single]
    rw [Finset.sum_congr rfl fun j _ => e2 j, hf, slantHom_single]
    erw [Preadditive.comp_sum]
    rw [Fin.sum_univ_succ]
    congr 1
    · erw [Preadditive.comp_zsmul, Linear.smul_comp, ← Functor.map_comp, (h Γ X m g).1]
      exact one_smul ℤ _
    · refine Finset.sum_congr rfl fun j _ => ?_
      erw [Preadditive.comp_zsmul, Linear.smul_comp, ← Functor.map_comp, (h Γ X m g).2 j]
      rfl

theorem sch_d (R : Type) [CommRing R] (X : Scheme.{0}) : ((chains R).obj (sch.obj X)).d (-1) 0 = 0 := by
  have d : ((chainsN R).obj (sch.obj X)).d (0 + 1) 0 =
      ∑ i : Fin (0 + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map ((sch.obj X).δ i) :=
    AlgebraicTopology.alternatingFaceMapComplex_obj_d _ 0
  have d0 : ((chainsN R).obj (sch.obj X)).d (0 + 1) 0 = 0 := by
    rw [d, Fin.sum_univ_two]
    have : (sch.obj X).δ (0 : Fin (0 + 2)) = (sch.obj X).δ 1 := rfl
    rw [this]; simp; rfl
  have := ((chainsN R).obj (sch.obj X)).extend_d_eq ComplexShape.embeddingDownNat (i := 0 + 1) (j := 0) (i' := -1) (j' := 0)
    (by simp) (by simp)
  refine this.trans ?_
  rw [d0]; simp; rfl

theorem single_congr {C : Type*} [Category C] [Preadditive C] {K L : CochainComplex C ℤ} {p q q' : ℤ} (f : K.X p ⟶ L.X q)
    (n m : ℤ) (hm : n + 1 = m) (hq : q + 1 = q') (hK : K.d (p - 1) p = 0) :
    δ n m (Cochain.single f n) = Cochain.single (f ≫ L.d q q') m := by
  rw [Cochain.δ_single f n m hm (p - 1) q' (by omega) hq, hK]
  simp

theorem deltaCo_of (h : HomD) : DeltaCo := by
  intro R _ Γ _ X
  refine ⟨fun c => ?_, fun m b => ?_⟩
  · unfold slantCo
    rw [single_congr _ _ _ rfl rfl (sch_d R X)]
    have z : IsZero (((chains R).obj (BX Γ X)).X (-((0 : ℕ) : ℤ) + 1)) :=
      ((chainsN R).obj (BX Γ X)).isZero_extend_X ComplexShape.embeddingDownNat _ (fun i hi => by
        simp at hi; omega)
    rw [z.eq_of_tgt (_ ≫ _) 0]
    simp
  · unfold slantCo
    rw [single_congr (q' := -(m : ℤ)) _ _ _ (by omega) (by omega) (sch_d R X)]
    congr 1
    have := ((chainsN R).obj (BX Γ X)).extend_d_eq ComplexShape.embeddingDownNat (i := m + 1) (j := m)
      (i' := -((m + 1 : ℕ) : ℤ)) (j' := -(m : ℤ)) (by simp) (by simp)
    unfold slantV
    rw [← h R Γ X m b]
    erw [this, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, Category.assoc]
    rfl

theorem gmap1 {Γ : Type} [Group Γ] {n : ℕ} (g : Fin n → Γ) (a b : Fin (n + 1)) (f : a ⟶ b) (c : Fin n) (ha : a.val = c.val)
    (hb : b.val = c.val + 1) : (show Γ from (grpSimplex g).map f) = (g c)⁻¹ := by
  obtain ⟨a, _⟩ := a
  obtain ⟨b, _⟩ := b
  obtain ⟨c, hc⟩ := c
  obtain rfl : a = c := ha
  obtain rfl : b = a + 1 := hb
  exact ComposableArrows.mkOfObjOfMapSucc_map_succ (fun _ => SingleObj.star Γ) (fun i => (g i)⁻¹) a hc

theorem gmap2 {Γ : Type} [Group Γ] {n : ℕ} (g : Fin n → Γ) (a b : Fin (n + 1)) (f : a ⟶ b) (c d : Fin n) (ha : a.val = c.val)
    (hd : d.val = c.val + 1) (hb : b.val = c.val + 2) : (show Γ from (grpSimplex g).map f) = (g c * g d)⁻¹ := by
  have h1 : a ≤ d.castSucc := by rw [Fin.le_def]; simp; omega
  have h2 : d.castSucc ≤ b := by rw [Fin.le_def]; simp; omega
  have e := (grpSimplex g).map_comp (homOfLE h1) (homOfLE h2)
  have e1 := gmap1 g _ _ (homOfLE h1) c ha (by simpa using hd)
  have e2 := gmap1 g _ _ (homOfLE h2) d (by simp) (by omega)
  rw [mul_inv_rev, ← e1, ← e2]
  exact e

theorem nerve_ext {Γ : Type} [Group Γ] {m : ℕ} (g : Fin (m + 1) → Γ) (g' : Fin m → Γ) (j : Fin (m + 2))
    (h : ∀ (i : Fin m) (f : j.succAbove i.castSucc ⟶ j.succAbove i.succ), (show Γ from (grpSimplex g).map f) = (g' i)⁻¹) :
    (nerve (SingleObj Γ)).δ j (grpSimplex g) = grpSimplex g' := by
  refine ComposableArrows.ext (fun _ => rfl) fun i hi => ?_
  erw [Category.id_comp, Category.comp_id]
  exact (h ⟨i, hi⟩ _).trans (gmap1 g' _ _ _ ⟨i, hi⟩ rfl rfl).symm

theorem nerve_zero {Γ : Type} [Group Γ] {m : ℕ} (g : Fin (m + 1) → Γ) :
    (nerve (SingleObj Γ)).δ 0 (grpSimplex g) = grpSimplex (fun i => g i.succ) :=
  nerve_ext g _ 0 fun i f => gmap1 g _ _ f i.succ (by simp) (by simp)

theorem val_succAbove {n : ℕ} (j : Fin (n + 1)) (i : Fin n) : (j.succAbove i).val = if i.val < j.val then i.val else i.val + 1 := by
  unfold Fin.succAbove
  by_cases h : i.val < j.val
  · rw [if_pos h, if_pos (show i.castSucc < j from h)]; rfl
  · rw [if_neg h, if_neg (show ¬ i.castSucc < j from h)]; rfl

theorem nerve_succ {Γ : Type} [Group Γ] {m : ℕ} (g : Fin (m + 1) → Γ) (j : Fin (m + 1)) :
    (nerve (SingleObj Γ)).δ j.succ (grpSimplex g) = grpSimplex (j.contractNth (· * ·) g) := by
  refine nerve_ext g _ _ fun i f => ?_
  have a := val_succAbove j.succ i.castSucc
  have b := val_succAbove j.succ i.succ
  simp only [Fin.val_succ, Fin.val_castSucc] at a b
  rcases lt_trichotomy i.val j.val with h | h | h
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ h]
    exact gmap1 g _ _ f _ (by rw [a, if_pos (by omega)]; rfl) (by rw [b, if_pos (by omega)]; rfl)
  · rw [Fin.contractNth_apply_of_eq _ _ _ _ h]
    exact gmap2 g _ _ f _ _ (by rw [a, if_pos (by omega)]; rfl) rfl (by rw [b, if_neg (by omega)]; rfl)
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ h]
    exact gmap1 g _ _ f _ (by rw [a, if_neg (by omega)]; rfl) (by rw [b, if_neg (by omega)]; rfl)

theorem ev_pres (P Q : Spc) (n : SimplexCategoryᵒᵖ) : PreservesLimit (pair P Q) ((evaluation SimplexCategoryᵒᵖ PSh).obj n) :=
  (evaluation_preservesLimitsOfShape (J := Discrete WalkingPair) _).preservesLimit

theorem lift_fst {P Q : Spc} {n : SimplexCategoryᵒᵖ} {W : PSh} (u : W ⟶ P.obj n) (v : W ⟶ Q.obj n) :
    haveI := ev_pres P Q n
    (prod.lift u v ≫ (PreservesLimitPair.iso ((evaluation SimplexCategoryᵒᵖ PSh).obj n) P Q).inv) ≫
      (prod.fst : P ⨯ Q ⟶ P).app n = u ∧
    (prod.lift u v ≫ (PreservesLimitPair.iso ((evaluation SimplexCategoryᵒᵖ PSh).obj n) P Q).inv) ≫
      (prod.snd : P ⨯ Q ⟶ Q).app n = v := by
  haveI := ev_pres P Q n
  constructor
  · erw [Category.assoc, PreservesLimitPair.iso_inv_fst, prod.lift_fst]
  · erw [Category.assoc, PreservesLimitPair.iso_inv_snd, prod.lift_snd]

theorem prod_ext {P Q : Spc} {n : SimplexCategoryᵒᵖ} {W : PSh} (u v : W ⟶ (P ⨯ Q).obj n)
    (h1 : u ≫ (prod.fst : P ⨯ Q ⟶ P).app n = v ≫ (prod.fst : P ⨯ Q ⟶ P).app n)
    (h2 : u ≫ (prod.snd : P ⨯ Q ⟶ Q).app n = v ≫ (prod.snd : P ⨯ Q ⟶ Q).app n) : u = v := by
  haveI := ev_pres P Q n
  exact BinaryFan.IsLimit.hom_ext
    (isLimitOfHasBinaryProductOfPreservesLimit ((evaluation SimplexCategoryᵒᵖ PSh).obj n) P Q) h1 h2

theorem face_of {Γ : Type} [Group Γ] (X : Scheme.{0}) {m : ℕ} (g : Fin (m + 1) → Γ) (g' : Fin m → Γ) (j : Fin (m + 2))
    (h : (nerve (SingleObj Γ)).δ j (grpSimplex g) = grpSimplex g') : grpPt X g ≫ (BX Γ X).δ j = grpPt X g' := by
  have a := lift_fst (P := cst (SingleObj Γ)) (Q := sch.obj X) (n := op (SimplexCategory.mk (m + 1))) (W := yoneda.obj X)
    { app := fun U => TypeCat.ofHom fun _ => grpSimplex g, naturality := fun _ _ _ => rfl } (𝟙 (yoneda.obj X))
  have b := lift_fst (P := cst (SingleObj Γ)) (Q := sch.obj X) (n := op (SimplexCategory.mk m)) (W := yoneda.obj X)
    { app := fun U => TypeCat.ofHom fun _ => grpSimplex g', naturality := fun _ _ _ => rfl } (𝟙 (yoneda.obj X))
  refine prod_ext _ _ ?_ ?_
  · refine Eq.trans ?_ b.1.symm
    rw [Category.assoc, SimplicialObject.δ_naturality, ← Category.assoc]
    refine (congrArg (· ≫ (cst (SingleObj Γ)).δ j) a.1).trans ?_
    ext U x
    exact h
  · refine Eq.trans ?_ b.2.symm
    rw [Category.assoc, SimplicialObject.δ_naturality, ← Category.assoc]
    exact congrArg (· ≫ (sch.obj X).δ j) a.2

theorem faces : Faces := fun _ _ X _ g =>
  ⟨face_of X g _ _ (nerve_zero g), fun j => face_of X g _ _ (nerve_succ g j)⟩

theorem goal : LateralTheory.E.EtaleChapterDThree := goal_of (deltaCo_of (homD_of faces))

end LateralTheory.E.t_D3Cut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LevelIdentPf

def FreeSingleHomotopyEquivDiscreteChains : Prop := ∀ (R : Type) [CommRing R], ∃ e : ∀ P : PSh, HomotopyEquiv (sgl ((free R).obj P)) ((chains R).obj (disc.obj P)),
  (∀ P, sglι _ ≫ (e P).hom.f 0 = (chainsXIso R (disc.obj P) 0).inv) ∧
  ∀ {P Q : PSh} (f : P ⟶ Q), (e P).hom ≫ (chains R).map (disc.map f) =
    (CochainComplex.singleFunctor (Shv R) 0).map ((free R).map f) ≫ (e Q).hom

variable {R : Type} [CommRing R]

theorem cpull_comp {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (I : Cx R) (n : ℤ) (x : CohomologyClass M I n) :
    cpull (f ≫ g) I n x = cpull f I n (cpull g I n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem cpull_id (K I : Cx R) (n : ℤ) (x : CohomologyClass K I n) : cpull (𝟙 K) I n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

theorem cpull_homotopy {K L : Cx R} {f g : K ⟶ L} (h : Homotopy f g) (I : Cx R) (n : ℤ) (x : CohomologyClass L I n) :
    cpull f I n x = cpull g I n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk (zcomp _ x _) = CohomologyClass.mk (zcomp _ x _)
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff]
  refine ⟨n - 1, by omega, n.negOnePow • (Cochain.ofHomotopy h).comp x.1 (by omega), ?_⟩
  rw [δ_units_smul, δ_comp _ _ (by omega) 0 (n + 1) n (by omega) (by omega) (by omega), δ_ofHomotopy]
  simp [zcomp, Cocycle.δ_eq_zero, Cochain.sub_comp, smul_smul, Int.units_mul_self]

theorem cpull_iso_bij {K L : Cx R} (e : HomotopyEquiv K L) (I : Cx R) (n : ℤ) :
    Function.Bijective (cpull e.hom I n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨cpull e.inv I n, fun x => ?_, fun x => ?_⟩
  · rw [← cpull_comp, cpull_homotopy e.homotopyInvHomId, cpull_id]
  · rw [← cpull_comp, cpull_homotopy e.homotopyHomInvId, cpull_id]

theorem sq_iff {A B C D : Type*} {a : B → D} {b : A → B} {c : C → D} {d : A → C}
    (w : ∀ x, a (b x) = c (d x)) (ha : Function.Bijective a) (hd : Function.Bijective d) :
    (Function.Bijective b ↔ Function.Bijective c) ∧ (Function.Injective b ↔ Function.Injective c) := by
  have w' : a ∘ b = c ∘ d := funext w
  obtain ⟨d', hd1, hd2⟩ := Function.bijective_iff_has_inverse.1 hd
  have hc : c = a ∘ b ∘ d' := by
    funext y; simp only [Function.comp_apply, w, hd2 y]
  have hd'b : Function.Bijective d' := Function.bijective_iff_has_inverse.2 ⟨d, hd2, hd1⟩
  refine ⟨⟨fun hb => hc ▸ ha.comp (hb.comp hd'b), fun hc' => ?_⟩, ⟨fun hb => hc ▸ ha.1.comp (hb.comp hd'b.1), fun hc' => ?_⟩⟩
  · have : a ∘ b = c ∘ d := w'
    have hab : Function.Bijective (a ∘ b) := this ▸ hc'.comp hd
    obtain ⟨a', ha1, ha2⟩ := Function.bijective_iff_has_inverse.1 ha
    have : b = a' ∘ (a ∘ b) := by funext x; simp [ha1 (b x)]
    rw [this]; exact (Function.bijective_iff_has_inverse.2 ⟨a, ha2, ha1⟩).comp hab
  · intro x y hxy
    apply hd.1; apply hc'
    rw [← w, ← w, hxy]

theorem chains_f {E E' : Spc} (f : E ⟶ E') (n : ℕ) : ((chains R).map f).f (-(n : ℤ)) =
    (chainsXIso R E n).hom ≫ (free R).map (f.app (op (SimplexCategory.mk n))) ≫ (chainsXIso R E' n).inv := by
  dsimp only [chains, chainsXIso, Functor.comp_map]
  erw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat (i := n) rfl]
  rfl

theorem cpull_isoHom_bij {K L : Cx R} (i : K ≅ L) (I : Cx R) (n : ℤ) : Function.Bijective (cpull i.hom I n) :=
  cpull_iso_bij (HomotopyEquiv.ofIso i) I n

theorem pull_eq {E E' : Spc} (f : E ⟶ E') (F : Shv R) (n : ℤ) (x : H R E' F n) :
    pull R f F n x = cpull ((chains R).map f) (res R F) n x := rfl

theorem LevelIdent_of (hS : FreeSingleHomotopyEquivDiscreteChains) : LateralTheory.E.DescStepPf.LevelIdent := by
  intro R _ F E E' f p j
  obtain ⟨e, -, he⟩ := hS R
  let S := CochainComplex.singleFunctor (Shv R) 0
  let g := f.app (op (SimplexCategory.mk p))
  have sq1 : S.map (((chains R).map f).f (-(p : ℤ))) ≫ S.map (chainsXIso R E' p).hom =
      S.map (chainsXIso R E p).hom ≫ S.map ((free R).map g) := by
    rw [← S.map_comp, ← S.map_comp, chains_f]; simp [g]
  have w1 : ∀ x, cpull (S.map (chainsXIso R E p).hom) (res R F) j (cpull (S.map ((free R).map g)) (res R F) j x) =
      cpull (S.map (((chains R).map f).f (-(p : ℤ)))) (res R F) j (cpull (S.map (chainsXIso R E' p).hom) (res R F) j x) := by
    intro x; rw [← cpull_comp, ← cpull_comp, sq1]
  have w2 : ∀ x, cpull (e (E.obj (op (SimplexCategory.mk p)))).hom (res R F) j (pull R (disc.map g) F j x) =
      cpull (S.map ((free R).map g)) (res R F) j (cpull (e (E'.obj (op (SimplexCategory.mk p)))).hom (res R F) j x) := by
    intro x; rw [pull_eq, ← cpull_comp, ← cpull_comp, he g]
  obtain ⟨b1, i1⟩ := sq_iff w1 (cpull_isoHom_bij (S.mapIso (chainsXIso R E p)) _ _)
    (cpull_isoHom_bij (S.mapIso (chainsXIso R E' p)) _ _)
  obtain ⟨b2, i2⟩ := sq_iff w2 (cpull_iso_bij _ _ _) (cpull_iso_bij _ _ _)
  exact ⟨b2.trans b1, i2.trans i1⟩

end LateralTheory.E.LevelIdentPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.CxDescPf

abbrev tr {R : Type} [CommRing R] (K : Cx R) (N : ℕ) : Cx R :=
  K.stupidTrunc (ComplexShape.embeddingUpIntGE (-(N : ℤ)))

abbrev trm {R : Type} [CommRing R] {K L : Cx R} (g : K ⟶ L) (N : ℕ) : tr K N ⟶ tr L N :=
  HomologicalComplex.stupidTruncMap g (ComplexShape.embeddingUpIntGE (-(N : ℤ)))

def Good {R : Type} [CommRing R] {K L : Cx R} (g : K ⟶ L) (I : Cx R) (m : ℤ) : Prop :=
  (∀ j : ℤ, j < m → Function.Bijective (cpull g I j)) ∧ Function.Injective (cpull g I m)

def stupid : Prop := ∀ (R : Type) [CommRing R] (I : Cx R) [I.IsStrictlyGE 0], (∀ m, Injective (I.X m)) →
  ∀ {K L : Cx R} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (g : K ⟶ L),
  ((∀ j : ℤ, Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (g.f (-((0 : ℕ) : ℤ)))) I j)) →
    ∀ j : ℤ, Function.Bijective (cpull (trm g 0) I j)) ∧
  ∀ (m : ℤ) (N : ℕ), m + 1 ≤ (N : ℤ) → Good (trm g N) I m → Good g I m

def long : Prop := ∀ (R : Type) [CommRing R] (I : Cx R) [I.IsStrictlyGE 0], (∀ m, Injective (I.X m)) →
  ∀ {K L : Cx R} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (g : K ⟶ L) (m : ℤ) (N : ℕ),
  Good ((CochainComplex.singleFunctor (Shv R) (-((N + 1 : ℕ) : ℤ))).map (g.f (-((N + 1 : ℕ) : ℤ)))) I m →
  Good (trm g N) I m → Good (trm g (N + 1)) I m

def shift : Prop := ∀ (R : Type) [CommRing R] (I : Cx R) {A B : Shv R} (φ : A ⟶ B) (p : ℕ) (j : ℤ),
  (Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map φ) I (j - p)) →
    Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) (-(p : ℤ))).map φ) I j)) ∧
  (Function.Injective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map φ) I (j - p)) →
    Function.Injective (cpull ((CochainComplex.singleFunctor (Shv R) (-(p : ℤ))).map φ) I j))

theorem CxDesc_of (hS : stupid) (hL : long) (hH : shift) : LateralTheory.E.DescStepPf.CxDesc := by
  intro R _ I _ hI K L _ _ g n hlow hn h0
  obtain ⟨hb, hlim⟩ := hS R I hI g
  have base : Good (trm g 0) I (n + 1) := ⟨fun j _ => hb h0 j, (hb h0 (n + 1)).1⟩
  have step : ∀ N : ℕ, Good (trm g N) I (n + 1) := by
    intro N
    induction N with
    | zero => exact base
    | succ N ih =>
      refine hL R I hI g (n + 1) N ⟨fun j hj => ?_, ?_⟩ ih
      · exact (hH R I (g.f (-((N + 1 : ℕ) : ℤ))) (N + 1) j).1 (hlow (N + 1) (j - ((N + 1 : ℕ) : ℤ)) (by omega))
      · apply (hH R I (g.f (-((N + 1 : ℕ) : ℤ))) (N + 1) (n + 1)).2
        rcases Nat.eq_zero_or_pos N with h | h
        · subst h
          have e : n + 1 - ((0 + 1 : ℕ) : ℤ) = n := by omega
          rw [e]; exact hn (0 + 1)
        · exact (hlow (N + 1) _ (by omega)).1
  have hg := hlim (n + 1) (n + 2).toNat (by omega) (step _)
  exact ⟨hg.1, hg.2⟩

end LateralTheory.E.CxDescPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.SHEqvPf
open LateralTheory.E.t_E3Cut

def SecBij : Prop := SHSection → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B), IsUnit (q : A) →
  SH A → SH B → Function.Bijective (fun s : Sec (tw q i) (Spec A) => Sec.res (Spec.map f) s)

def SecPre : Prop := SHSection → ∀ (q : ℕ) (i : ℤ) (A : CommRingCat.{0}), SH A →
  Function.Bijective (ofRings.sec (twF q i) (Spec A))

def TwFBij : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B), IsUnit (q : A) → SH A → SH B →
  Function.Bijective ((twF q i).map (Spec.map f).appTop).hom

theorem sec_res {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) {V U : Scheme.{0}} (j : V ⟶ U)
    (m : M.obj Γ(U, ⊤)) : Sec.res j (ofRings.sec M U m) = ofRings.sec M V ((M.map j.appTop).hom m) := by
  have h := (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality j.op
  have h2 := congrArg (fun φ => φ.hom m) h
  exact h2.symm

theorem SecBij_of (hP : SecPre) (hT : TwFBij) : SecBij := by
  intro hSec q _ i A B f hq hA hB
  have key : (fun s : Sec (tw q i) (Spec A) => Sec.res (Spec.map f) s) =
      ofRings.sec (twF q i) (Spec B) ∘ ((twF q i).map (Spec.map f).appTop).hom ∘
        (Equiv.ofBijective _ (hP hSec q i A hA)).symm := by
    funext s
    obtain ⟨m, rfl⟩ := (hP hSec q i A hA).2 s
    simp only [Function.comp]
    rw [Equiv.ofBijective_symm_apply_apply]
    exact sec_res _ _ _
  rw [key]
  exact (hP hSec q i B hB).comp ((hT q i f hq hA hB).comp (Equiv.bijective (Equiv.ofBijective _ (hP hSec q i A hA)).symm))

theorem bij_of_subsingleton {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Subsingleton M] [Subsingleton N]
    (g : M →+ N) : Function.Bijective g :=
  ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

theorem SHEqv_of_secBij (hSec : SHSection) (hB : SecBij) : SHEqv := by
  intro hyp q _ i A B f hq hA hBs n
  obtain ⟨_, _, _, _, _, hA9, _, hB2, _⟩ := hyp
  obtain ⟨hneg, e, he, -⟩ := hA9 (ZMod q) (tw q i)
  rcases lt_trichotomy n 0 with h | h | h
  · haveI := hneg (sch.obj (Spec A)) n h
    haveI := hneg (sch.obj (Spec B)) n h
    exact bij_of_subsingleton _
  · subst h
    have key : ⇑(pull (ZMod q) (sch.map (Spec.map f)) (tw q i) 0) =
        (e (Spec B)) ∘ (fun s : Sec (tw q i) (Spec A) => Sec.res (Spec.map f) s) ∘ (e (Spec A)).symm := by
      funext x
      simp only [Function.comp]
      rw [← he]
      simp
    show Function.Bijective (pull (ZMod q) (sch.map (Spec.map f)) (tw q i) 0)
    rw [key]
    exact (e _).bijective.comp ((hB hSec q i f hq hA hBs).comp (e _).symm.bijective)
  · haveI := hB2 (ZMod q) A hA (tw q i) n h
    haveI := hB2 (ZMod q) B hBs (tw q i) n h
    exact bij_of_subsingleton _

end LateralTheory.E.SHEqvPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafUnitPairGPf
open LateralTheory.E.CupProductRingLaws LateralTheory.E.LeafRingUnitPf LateralTheory.E.LeafUnitPairPf

def IsAct (q : ℕ) (i : ℤ) (L : ∀ (U : Scheme.{0}) (t : ℤ), Sec (tw q 0) U →ₗ[ULift.{1} (ZMod q)]
    Sec ((res _ (tw q i)).X t) U →ₗ[ULift.{1} (ZMod q)] Sec ((res _ (tw q i)).X t) U) : Prop :=
  (∀ {V U : Scheme.{0}} (g : V ⟶ U) (t : ℤ) (a : Sec (tw q 0) U) (b : Sec ((res _ (tw q i)).X t) U),
      Sec.res g (L U t a b) = L V t (Sec.res g a) (Sec.res g b)) ∧
    ∀ (U : Scheme.{0}) (t : ℤ) (a : Sec (tw q 0) U) (b : Sec ((res _ (tw q i)).X t) U),
      Sec.map ((res _ (tw q i)).d t (t + 1)) (L U t a b) = L U (t + 1) a (Sec.map ((res _ (tw q i)).d t (t + 1)) b)

def LeafUnitAct : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ), ∃ L, IsAct q i L ∧
  ∀ (U : Scheme.{0}) (t : ℤ) (ζ : Prim q Γ(U, ⊤)) (b : Sec ((res _ (tw q i)).X t) U), L U t (twGen 0 ζ) b = b

def LeafPairExt : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) L, IsAct q i L →
  ∃ ν : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q i)),
    ∀ (U : Scheme.{0}) (t : ℤ) (a : Sec (tw q 0) U) (b : Sec ((res _ (tw q i)).X t) U),
      ν.mul U 0 t t (zero_add t) (Sec.map (resι _ (tw q 0)) a) b = L U t a b

theorem LeafUnitPairG_of (hact : LeafUnitAct) (hext : LeafPairExt) : LeafUnitPairG := by
  intro q _ i
  obtain ⟨L, hL, hLζ⟩ := hact q i
  obtain ⟨ν, hν⟩ := hext q i L hL
  refine ⟨ν, fun U t ζ b => ?_⟩
  exact (hν U t (twGen 0 ζ) b).trans (hLζ U t ζ b)

end LateralTheory.E.LeafUnitPairGPf
end
end

section

namespace LateralTheory.E.LeafA6ringCut

theorem goal_of (h5 : LateralTheory.E.CupProductRingLaws.LeafRingUnit) (h6 : LateralTheory.E.CupProductRingLaws.LeafRingAssoc)
    (h7 : LateralTheory.E.CupProductRingLaws.LeafRingComm) : LateralTheory.E.D2.LeafA6ring :=
  fun q _ E => ⟨h5 q E, h6 q E, h7 q E⟩

end LateralTheory.E.LeafA6ringCut
end
