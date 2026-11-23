module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricSeriesSectionsL2Limit
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle339
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle297
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle372
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle371
public import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle340
public import Development.AbelianVarietyTheory.Definitions.Divisors.CechDeRhamCoefMapOneFormsRestrictAlongFunctor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle335
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingSumThreeTerms
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.CartanZero
variable {T : Type 1} [Category.{0} T]

def cyc (C : T ⥤ AbCx) (i j : ℤ) : T ⥤ AddCommGrpCat.{1} where
  obj U := AddCommGrpCat.of ((C.obj U).d i j).hom.ker
  map {U V} f := AddCommGrpCat.ofHom
    { toFun := fun x => ⟨(C.map f).f i x.1, by
        have e := ConcreteCategory.congr_hom ((C.map f).comm i j) x.1
        simp only [ConcreteCategory.comp_apply] at e
        change (C.obj V).d i j ((C.map f).f i x.1) = 0
        rw [e, show (C.obj U).d i j x.1 = 0 from x.2, map_zero]⟩
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp }
  map_id U := by ext x; simp
  map_comp f g := by ext x; simp

def incl (C : T ⥤ AbCx) (i j : ℤ) : cyc C i j ⟶ term C i where
  app U := AddCommGrpCat.ofHom (AddSubgroup.subtype _)
  naturality U V f := by ext x; rfl

def dN (C : T ⥤ AbCx) (i j : ℤ) : term C i ⟶ term C j where
  app U := (C.obj U).d i j
  naturality U V f := (C.map f).comm i j

def pN (C : T ⥤ AbCx) (i j k : ℤ) : term C i ⟶ cyc C j k where
  app U := AddCommGrpCat.ofHom
    { toFun := fun y => ⟨(C.obj U).d i j y, by
        change (C.obj U).d j k ((C.obj U).d i j y) = 0
        exact ConcreteCategory.congr_hom ((C.obj U).d_comp_d i j k) y⟩
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp }
  naturality U V f := by
    ext y
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((C.map f).comm i j) y

end GlobalTheory.CartanZero

namespace GlobalTheory.CartanZero
variable {T : Type 1} [Category.{0} T]

def Good (C : T ⥤ AbCx) (j : ℤ) : Prop :=
  ∀ i, i + 1 = j → ∀ (U : T) (X : CosimplicialObject T) (a : (CosimplicialObject.const T).obj U ⟶ X),
    (∀ n, WExact (term C n) a) → ∀ k : ℕ,
      ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj (X ⋙ cyc C i j)).ExactAt (k + 1)

theorem good_of_le (C : T ⥤ AbCx) (b : ℤ) (hb : ∀ n : ℤ, n < b → ∀ U, IsZero ((C.obj U).X n))
    (j : ℤ) (hj : j ≤ b) : Good C j := by
  intro i hi U X a _ k
  have hs : ∀ V, Subsingleton ((cyc C i j).obj V) := fun V => by
    have : Subsingleton ((C.obj V).X i) := AddCommGrpCat.subsingleton_of_isZero (hb i (by omega) V)
    change Subsingleton (((C.obj V).d i j).hom.ker)
    infer_instance
  rw [HomologicalComplex.exactAt_iff' _ k (k + 1) (k + 2) (by simp) (by simp), ShortComplex.ab_exact_iff]
  intro x _
  exact ⟨0, (hs _).elim _ _⟩

theorem step (T : Type 1) [Category.{0} T] (Cov : MorphismProperty T) (C : T ⥤ AbCx)
    (hR : Refines Cov (fun U X a => ∀ n, WExact (term C n) a)) (hL : LocExact Cov C)
    (j : ℤ) (hG : Good C j) (U : T) (z : (C.obj U).X j) (hz : (C.obj U).d j (j + 1) z = 0) :
    ∃ y : (C.obj U).X (j - 1), (C.obj U).d (j - 1) j y = z := by
  obtain ⟨V, g, hg, y, hy⟩ := hL j U z hz
  obtain ⟨X, a, h, hgh, hW⟩ := hR U V g hg
  have hZ := hG (j - 1) (by omega) U X a hW 0
  refine GlobalTheory.CartanStep.cartan_step T U X a (cyc C (j - 1) j) (term C (j - 1)) (term C j) (incl C (j - 1) j)
    (dN C (j - 1) j) (fun V => Subtype.val_injective) (fun V y => ⟨fun h => ⟨⟨y, h⟩, rfl⟩, ?_⟩) (hW _) (hW _) hZ z
    ((C.map h).f (j - 1) y) ?_
  · rintro ⟨w, rfl⟩
    exact w.2
  · change (C.obj _).d (j - 1) j ((C.map h).f (j - 1) y) = (C.map (a.app _)).f j z
    have e := ConcreteCategory.congr_hom ((C.map h).comm (j - 1) j) y
    simp only [ConcreteCategory.comp_apply] at e
    rw [e, hy, ← hgh, Functor.map_comp, HomologicalComplex.comp_f, ConcreteCategory.comp_apply]

end GlobalTheory.CartanZero

namespace GlobalTheory.CartanZero

theorem good_succ (T : Type 1) [Category.{0} T] (Cov : MorphismProperty T) (C : T ⥤ AbCx)
    (hR : Refines Cov (fun U X a => ∀ n, WExact (term C n) a)) (hL : LocExact Cov C)
    (j : ℤ) (hG : Good C j) : Good C (j + 1) := by
  intro i hi U X a hW
  obtain rfl : i = j := by omega
  refine cosimplicial_ses_exactAt_succ (X ⋙ cyc C (i - 1) i) (X ⋙ term C (i - 1)) (X ⋙ cyc C i (i + 1))
    (Functor.whiskerLeft X (incl C (i - 1) i)) (Functor.whiskerLeft X (pN C (i - 1) i (i + 1)))
    (fun k => Subtype.val_injective) (fun k y => ⟨fun h => ⟨⟨y, congrArg Subtype.val h⟩, rfl⟩, ?_⟩) ?_
    (hG (i - 1) (by omega) U X a hW) (hW (i - 1)).2.2
  · rintro ⟨w, rfl⟩
    exact Subtype.ext w.2
  · intro k c
    obtain ⟨y, hy⟩ := step T Cov C hR hL i hG (X.obj k) c.1 c.2
    exact ⟨y, Subtype.ext hy⟩

theorem cartan_zero : ∀ (T : Type 1) [Category.{0} T] (Cov : MorphismProperty T) (C : T ⥤ AbCx), (∃ b : ℤ, ∀ n : ℤ, n < b → ∀ U, IsZero ((C.obj U).X n)) → Refines Cov (fun U X a => ∀ n, WExact (term C n) a) → LocExact Cov C → ∀ (U : T) (n : ℤ) (z : (C.obj U).X n), (C.obj U).d n (n + 1) z = 0 → ∃ y : (C.obj U).X (n - 1), (C.obj U).d (n - 1) n y = z := by
  intro T _ Cov C ⟨b, hb⟩ hR hL U n z hz
  have hall : ∀ t : ℕ, Good C (b + t) := by
    intro t
    induction t with
    | zero => simpa using good_of_le C b hb b le_rfl
    | succ t ih =>
      have := good_succ T Cov C hR hL _ ih
      simpa [add_assoc] using this
  have hGn : Good C n := by
    by_cases h : n ≤ b
    · exact good_of_le C b hb n h
    · have e : b + ((n - b).toNat : ℤ) = n := by omega
      have h2 := hall (n - b).toNat
      rw [e] at h2
      exact h2
  exact step T Cov C hR hL n hGn U z hz

end GlobalTheory.CartanZero
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne

namespace GlobalTheory.CechOne

theorem cobd_of_isCls_zero :
    ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (s : (free R).obj (E.obj (op ⦋1⦌)) ⟶ F),
      IsCls (R := R) s (0 : H R E F ((1 : ℕ) : ℤ)) →
        ∃ t : (free R).obj (E.obj (op ⦋0⦌)) ⟶ F, s = cobd (R := R) (E := E) (n := 0) t := by
  intro R _ F E s hs
  obtain ⟨-, hneg, hmono, ⟨w, hex⟩, -, hpos⟩ := GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties R F
  obtain ⟨z, hz0, hz⟩ := hs
  rw [CohomologyClass.mk_eq_zero_iff] at hz0
  obtain ⟨m, hm, β, hβ⟩ := hz0
  obtain rfl : m = 0 := by push_cast at hm; omega
  have hzv : ∀ (p q : ℤ) (hpq : p + ((1 : ℕ) : ℤ) = q),
      (↑z : Cochain ((chains R).obj E) (res R F) ((1 : ℕ) : ℤ)).v p q hpq =
        (Cochain.single (p := -((1 : ℕ) : ℤ)) (q := 0)
          ((chainsXIso R E 1).hom ≫ s ≫ resι R F) ((1 : ℕ) : ℤ)).v p q hpq := by
    intro p q hpq
    rw [show (↑z : Cochain ((chains R).obj E) (res R F) ((1 : ℕ) : ℤ)) = z.1 from rfl, hz]
  let b := β.v 0 0 (by omega)
  have hb : b ≫ (res R F).d 0 1 = 0 := by
    have e := Cochain.congr_v hβ 0 1 (by norm_num)
    rw [δ_v 0 _ (by norm_num) β 0 1 _ 0 1 (by omega) rfl,
      (hpos E 1 (by norm_num)).eq_of_tgt (((chains R).obj E).d 0 1) 0, zero_comp, smul_zero, add_zero, hzv,
      Cochain.single_v_eq_zero _ _ _ _ _ (by omega)] at e
    exact e
  haveI : Mono (ShortComplex.mk _ _ w).f := hmono
  let t' : ((chains R).obj E).X 0 ⟶ F := hex.lift b hb
  have ht' : t' ≫ resι R F = b := hex.lift_f b hb
  have e := Cochain.congr_v hβ (-((1 : ℕ) : ℤ)) 0 (by omega)
  have h1 : β.v (-((1 : ℕ) : ℤ)) (-1) (by omega) = 0 := (hneg (-1) (by norm_num)).eq_of_tgt _ _
  rw [δ_v 0 _ (by norm_num) β _ 0 _ (-1) 0 (by omega) (by norm_num), h1,
    zero_comp, zero_add, hzv, Cochain.single_v] at e
  rw [show β.v 0 0 (by omega) = b from rfl, ← ht'] at e
  let D : (free R).obj (E.obj (op ⦋1⦌)) ⟶ (free R).obj (E.obj (op ⦋0⦌)) :=
    ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (free R).map (SimplicialObject.δ E i)
  have hd : ((chains R).obj E).d (-((1 : ℕ) : ℤ)) 0 = (chainsXIso R E 1).hom ≫ D ≫ (chainsXIso R E 0).inv :=
    GlobalTheory.EtC.ClsBasic.chains_d (R := R) E 0
  rw [hd] at e
  have hs : s = (((1 : ℕ) : ℤ).negOnePow : ℤ) • (D ≫ (chainsXIso R E 0).inv ≫ t') := by
    apply (cancel_epi (chainsXIso R E 1).hom).1
    apply (cancel_mono (resι R F)).1
    rw [Category.assoc, ← e]
    simp only [Units.smul_def, Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc]
  refine ⟨(((1 : ℕ) : ℤ).negOnePow : ℤ) • ((chainsXIso R E 0).inv ≫ t'), ?_⟩
  rw [hs]
  simp only [D, cobd, Preadditive.sum_comp, Preadditive.comp_zsmul, Preadditive.zsmul_comp, Finset.smul_sum,
    smul_smul, Category.assoc]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]

end GlobalTheory.CechOne
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne

theorem _root_.GlobalTheory.T.simplicialCochain_coboundary_of_class_zero :
    ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc)
      (s : (free R).obj (E.obj (op ⦋1⦌)) ⟶ F),
      IsCls (R := R) s (0 : H R E F ((1 : ℕ) : ℤ)) →
        ∃ t : (free R).obj (E.obj (op ⦋0⦌)) ⟶ F, s = cobd (R := R) (E := E) (n := 0) t := by
  intro R _ F E s hs
  obtain ⟨-, hneg, hmono, ⟨w, hex⟩, -, hpos⟩ := GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties R F
  obtain ⟨z, hz0, hz⟩ := hs
  rw [CohomologyClass.mk_eq_zero_iff] at hz0
  obtain ⟨m, hm, β, hβ⟩ := hz0
  obtain rfl : m = 0 := by push_cast at hm; omega
  have hzv : ∀ (p q : ℤ) (hpq : p + ((1 : ℕ) : ℤ) = q),
      (↑z : Cochain ((chains R).obj E) (res R F) ((1 : ℕ) : ℤ)).v p q hpq =
        (Cochain.single (p := -((1 : ℕ) : ℤ)) (q := 0)
          ((chainsXIso R E 1).hom ≫ s ≫ resι R F) ((1 : ℕ) : ℤ)).v p q hpq := by
    intro p q hpq
    rw [show (↑z : Cochain ((chains R).obj E) (res R F) ((1 : ℕ) : ℤ)) = z.1 from rfl, hz]
  let b := β.v 0 0 (by omega)
  have hb : b ≫ (res R F).d 0 1 = 0 := by
    have e := Cochain.congr_v hβ 0 1 (by norm_num)
    rw [δ_v 0 _ (by norm_num) β 0 1 _ 0 1 (by omega) rfl,
      (hpos E 1 (by norm_num)).eq_of_tgt (((chains R).obj E).d 0 1) 0, zero_comp, smul_zero, add_zero, hzv,
      Cochain.single_v_eq_zero _ _ _ _ _ (by omega)] at e
    exact e
  have : Mono (ShortComplex.mk _ _ w).f := hmono
  let t' : ((chains R).obj E).X 0 ⟶ F := hex.lift b hb
  have ht' : t' ≫ resι R F = b := hex.lift_f b hb
  have e := Cochain.congr_v hβ (-((1 : ℕ) : ℤ)) 0 (by omega)
  have h1 : β.v (-((1 : ℕ) : ℤ)) (-1) (by omega) = 0 := (hneg (-1) (by norm_num)).eq_of_tgt _ _
  rw [δ_v 0 _ (by norm_num) β _ 0 _ (-1) 0 (by omega) (by norm_num), h1,
    zero_comp, zero_add, hzv, Cochain.single_v] at e
  rw [show β.v 0 0 (by omega) = b from rfl, ← ht'] at e
  let D : (free R).obj (E.obj (op ⦋1⦌)) ⟶ (free R).obj (E.obj (op ⦋0⦌)) :=
    ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (free R).map (SimplicialObject.δ E i)
  have hd : ((chains R).obj E).d (-((1 : ℕ) : ℤ)) 0 = (chainsXIso R E 1).hom ≫ D ≫ (chainsXIso R E 0).inv :=
    GlobalTheory.EtC.ClsBasic.chains_d (R := R) E 0
  rw [hd] at e
  have hs_eq : s = (((1 : ℕ) : ℤ).negOnePow : ℤ) • (D ≫ (chainsXIso R E 0).inv ≫ t') := by
    apply (cancel_epi (chainsXIso R E 1).hom).1
    apply (cancel_mono (resι R F)).1
    rw [Category.assoc, ← e]
    simp only [Units.smul_def, Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc]
  refine ⟨(((1 : ℕ) : ℤ).negOnePow : ℤ) • ((chainsXIso R E 0).inv ≫ t'), ?_⟩
  rw [hs_eq]
  simp only [D, cobd, Preadditive.sum_comp, Preadditive.comp_zsmul, Preadditive.zsmul_comp, Finset.smul_sum,
    smul_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.ContFin

theorem term_preserves (N : CommRingCat.{0} ⥤ AbCx) (hN : PreservesFilteredColimitsOfSize.{0, 0} N) (n : ℤ) :
    PreservesFilteredColimitsOfSize.{0, 0} (term N n) := by
  constructor
  intro J _ _
  unfold term
  have : PreservesColimitsOfShape J N := hN.preserves_filtered_colimits J
  infer_instance

theorem cohomology_filteredColimit : ∀ (N : CommRingCat.{0} ⥤ AbCx), PreservesFilteredColimitsOfSize.{0, 0} N → (∀ n, PreservesFilteredColimitsOfSize.{0, 0} (term N n)) ∧ (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : ((N).obj c.pt).X n, ((N).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : ((N).obj (D.obj j)).X n) (y : ((N).obj c.pt).X (n - 1)), ((N).obj (D.obj j)).d n (n + 1) w = 0 ∧ ((N).map (c.ι.app j)).f n w = z + ((N).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : ((N).obj (D.obj j)).X n), ((N).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : ((N).obj c.pt).X (n - 1), ((N).map (c.ι.app j)).f n w = ((N).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : ((N).obj (D.obj k)).X (n - 1)), ((N).map (D.map f)).f n w = ((N).obj (D.obj k)).d (n - 1) n y) := by
  intro N hN
  refine ⟨term_preserves N hN, ?_⟩
  intro J _ _ D c hc n
  have E : ∀ m : ℤ, (∀ x : ((N).obj c.pt).X m, ∃ j y, ((N).map (c.ι.app j)).f m y = x) ∧
      ∀ j (y : ((N).obj (D.obj j)).X m), ((N).map (c.ι.app j)).f m y = 0 → ∃ (k : J) (f : j ⟶ k), ((N).map (D.map f)).f m y = 0 :=
    fun m => ((GlobalTheory.T.preservesFilteredColimits_addCommGrp_iff_elements CommRingCat.{0} (term N m)).mp (term_preserves N hN m)) J D c hc

  have nat : ∀ {a b : CommRingCat.{0}} (g : a ⟶ b) (p q : ℤ) (x : ((N).obj a).X p),
      ((N).map g).f q (((N).obj a).d p q x) = ((N).obj b).d p q (((N).map g).f p x) := by
    intro a b g p q x
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ((N).map g).comm]
  have mapf : ∀ {j k : J} (f : j ⟶ k) (m : ℤ) (x : ((N).obj (D.obj j)).X m),
      ((N).map (c.ι.app k)).f m (((N).map (D.map f)).f m x) = ((N).map (c.ι.app j)).f m x := by
    intro j k f m x
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, ← Functor.map_comp, c.w f]
  have mapcomp : ∀ {j k l : J} (f : j ⟶ k) (g : k ⟶ l) (m : ℤ) (x : ((N).obj (D.obj j)).X m),
      ((N).map (D.map (f ≫ g))).f m x = ((N).map (D.map g)).f m (((N).map (D.map f)).f m x) := by
    intro j k l f g m x
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, ← Functor.map_comp, ← D.map_comp]
  constructor
  · intro z hz
    obtain ⟨j, w, hw⟩ := (E n).1 z
    have h1 : ((N).map (c.ι.app j)).f (n + 1) (((N).obj (D.obj j)).d n (n + 1) w) = 0 := by
      rw [nat, hw]
      exact hz
    obtain ⟨k, f, hf⟩ := (E (n + 1)).2 j _ h1
    refine ⟨k, ((N).map (D.map f)).f n w, 0, ?_, ?_⟩
    · rw [← nat, hf]
    · rw [mapf, hw, map_zero, add_zero]
  · intro j w _ ⟨y, hy⟩
    obtain ⟨j', y', rfl⟩ := (E (n - 1)).1 y
    let k := IsFiltered.max j j'
    let fa : j ⟶ k := IsFiltered.leftToMax j j'
    let fb : j' ⟶ k := IsFiltered.rightToMax j j'
    set u := ((N).map (D.map fa)).f n w - ((N).obj (D.obj k)).d (n - 1) n (((N).map (D.map fb)).f (n - 1) y') with hu
    have h0 : ((N).map (c.ι.app k)).f n u = 0 := by
      rw [hu, map_sub, mapf, ← nat, mapf, hy, nat]
      exact sub_self _
    obtain ⟨l, g, hg⟩ := (E n).2 k u h0
    refine ⟨l, fa ≫ g, ((N).map (D.map g)).f (n - 1) (((N).map (D.map fb)).f (n - 1) y'), ?_⟩
    rw [hu, map_sub, sub_eq_zero] at hg
    rw [mapcomp, hg, nat]

end GlobalTheory.EtC.ContFin
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.LocSurjFT

theorem etFF_id (A : CommRingCat.{0}) : EtFF (𝟙 A) := by
  refine ⟨?_, ?_⟩
  · change (algebraMap A A).Etale
    exact RingHom.etale_algebraMap.2 inferInstance
  · change (algebraMap A A).FaithfullyFlat
    exact RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance

theorem locSurj_of_iso_on_finiteType : ∀ (N M : CommRingCat.{0} ⥤ AbCx) (ε : N ⟶ M) (F0 : CommRingCat.{0} ⥤ AddCommGrpCat.{1}) (ι : F0 ⟶ term M 0), PreservesFilteredColimitsOfSize.{0, 0} F0 → (∀ A, Function.Injective (ι.app A) ∧ ∀ z : (M.obj A).X 0, (M.obj A).d 0 (0 + 1) z = 0 ↔ ∃ x, ι.app A x = z) → (∀ n : ℤ, n < 0 → ∀ A, IsZero ((M.obj A).X n)) → (∀ n : ℤ, 0 < n → ∀ (A : CommRingCat.{0}) (z : (M.obj A).X n), (M.obj A).d n (n + 1) z = 0 → ∃ (B : CommRingCat.{0}) (g : A ⟶ B), EtFF g ∧ ∃ y : (M.obj B).X (n - 1), (M.obj B).d (n - 1) n y = (M.map g).f n z) → PreservesFilteredColimitsOfSize.{0, 0} N → (∀ A : CommRingCat.{0}, Algebra.FiniteType ℤ A → IsIso (ε.app A)) → LocSurj EtFF ε := by
  intro N M ε F0 ι hF0 hι hneg hpos _hN hiso n A z hz
  rcases lt_trichotomy n 0 with hn | rfl | hn
  ·
    haveI := AddCommGrpCat.subsingleton_of_isZero (hneg n hn A)
    refine ⟨A, 𝟙 A, etFF_id A, 0, 0, by simp, Subsingleton.elim _ _⟩
  ·
    obtain ⟨x, rfl⟩ := ((hι A).2 z).1 hz
    obtain ⟨J, _, _, D, κ, ⟨hc⟩, hft⟩ := GlobalTheory.T.exists_filteredColimit_finiteType_int_rings A
    obtain ⟨j, x0, hx0⟩ := ((GlobalTheory.T.preservesFilteredColimits_addCommGrp_iff_elements CommRingCat.{0} F0).1 hF0 J D (Cocone.mk A κ) hc).1 x
    haveI := hiso (D.obj j) (hft j)
    set z0 : (M.obj (D.obj j)).X 0 := ι.app (D.obj j) x0 with hz0
    set c0 : (N.obj (D.obj j)).X 0 := (inv (ε.app (D.obj j))).f 0 z0 with hc0
    have hεc0 : (ε.app (D.obj j)).f 0 c0 = z0 := by
      have := congrArg (fun h => (h.f 0).hom z0) (IsIso.inv_hom_id (ε.app (D.obj j)))
      simpa [hc0] using this
    have hdz0 : (M.obj (D.obj j)).d 0 (0 + 1) z0 = 0 := ((hι (D.obj j)).2 z0).2 ⟨x0, rfl⟩
    have hdc0 : (N.obj (D.obj j)).d 0 (0 + 1) c0 = 0 := by
      have := congrArg (fun h => h.hom z0) ((inv (ε.app (D.obj j))).comm 0 (0 + 1))
      simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply] at this
      rw [hc0, this, hdz0, map_zero]
    have h2 : (M.map (κ.app j)).f 0 z0 = ι.app A x := by
      have := ConcreteCategory.congr_hom (ι.naturality (κ.app j)) x0
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
      rw [hz0, ← hx0]
      exact this.symm
    clear_value c0 z0
    refine ⟨A, 𝟙 A, etFF_id A, (N.map (κ.app j)).f 0 c0, 0, ?_, ?_⟩
    · have := ConcreteCategory.congr_hom ((N.map (κ.app j)).comm 0 (0 + 1)) c0
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hdc0, map_zero] at this
      exact this
    · have h1 := ConcreteCategory.congr_hom (congrArg (fun h => h.f 0) (ε.naturality (κ.app j))) c0
      simp only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply] at h1
      have h1' : (ε.app A).f 0 ((N.map (κ.app j)).f 0 c0) = (M.map (κ.app j)).f 0 ((ε.app (D.obj j)).f 0 c0) := h1
      rw [h1', hεc0, h2]
      simp only [CategoryTheory.Functor.map_id, HomologicalComplex.id_f, map_zero, add_zero]
      rfl
  ·
    obtain ⟨B, g, hg, y, hy⟩ := hpos n hn A z hz
    refine ⟨B, g, hg, 0, -y, by simp, ?_⟩
    rw [map_neg, hy]
    simp

end GlobalTheory.EtC.LocSurjFT
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.geometric_series_sections_l2_limit : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (la : La) (F : ℕ → ι → Y → ℂ) (K : ℝ), 0 ≤ K → (∀ m, A.IsSSec (A.kap + la) (F m)) → (∀ m, n0 A la (F m - F (m + 1)) ≤ ENNReal.ofReal (K / 4 ^ m)) → ∃ f : ι → Y → ℂ, (∀ i j y, y ∈ (A.chart i).source → y ∈ (A.chart j).source → f i y = A.g (A.kap + la) i j y * f j y) ∧ (∀ i, AEMeasurable (f i ∘ (A.chart i).symm) (volume.restrict (A.chart i).target)) ∧ ∀ m, n0 A la (F m - f) ≤ ENNReal.ofReal (4 * K / 4 ^ m) := by
  first | exact @GlobalTheory.L2Limit.exists_l2_limit | exact GlobalTheory.L2Limit.exists_l2_limit | (intros; apply GlobalTheory.L2Limit.exists_l2_limit <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.bijective_HC_component_eval_of_maps : ∀ (R : Type) [CommRing R] (F : Shv R) (n : ℤ), ∃ π : ∀ k : ℕ, (HC R F ⋙ HomologicalComplex.eval _ _ n) ⟶ ((evaluation _ PSh).obj (op (SimplexCategory.mk (k)))).op ⋙ (free R).op ⋙ preadditiveYoneda.obj ((res R F).X (n - k)), ∀ E : Spcᵒᵖ, Function.Bijective (fun (x : ((HC R F).obj E).X n) (k : ℕ) => (π k).app E x) := by
  first | (exact @GlobalTheory.EtC.HCTerms.HC_X_bijective) | (exact GlobalTheory.EtC.HCTerms.HC_X_bijective) | (intros; apply GlobalTheory.EtC.HCTerms.HC_X_bijective  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem wExact_preadditiveYoneda_of_injective (R : Type) [CommRing R] (T : Type 1) [Category.{0} T]
    (Ψ : T ⥤ PShᵒᵖ) (U : T) (X : CosimplicialObject T) (a : (CosimplicialObject.const T).obj U ⟶ X)
    (J : Shv R) (hJ : Injective J) (hq : QuasiIso ((chains R).map (lev Ψ a))) :
    WExact (Ψ ⋙ (free R).op ⋙ preadditiveYoneda.obj J) a := by
  let K : SimplicialObject (Shv R) := ((SimplicialObject.whiskering _ _).obj (free R)).obj ((X ⋙ Ψ).leftOp)
  let B : Shv R := (free R).obj (Ψ.obj U).unop
  let f : K ⟶ (SimplicialObject.const (Shv R)).obj B :=
    ((SimplicialObject.whiskering _ _).obj (free R)).map (lev Ψ a) ≫ (Functor.constComp _ _ _).hom
  haveI h1 : QuasiIso ((chainsN R).map (lev Ψ a)) :=
    (HomologicalComplex.quasiIso_extendMap_iff _ _).1 hq
  have hq' : QuasiIso ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map f) := by
    have e : (AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map f =
        (AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (((SimplicialObject.whiskering _ _).obj (free R)).map (lev Ψ a)) ≫
        (AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (Functor.constComp _ _ _).hom :=
      Functor.map_comp _ _ _
    rw [e]
    haveI : IsIso ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (Functor.constComp SimplexCategoryᵒᵖ (Ψ.obj U).unop (free R)).hom) :=
      Functor.map_isIso _ _
    haveI h2 : QuasiIso ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (((SimplicialObject.whiskering _ _).obj (free R)).map (lev Ψ a))) := h1
    haveI h3 : QuasiIso ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (Functor.constComp SimplexCategoryᵒᵖ (Ψ.obj U).unop (free R)).hom) :=
      quasiIso_of_isIso _
    exact quasiIso_comp (hφ := h2) (hφ' := h3) _ _
  obtain ⟨hepi, ⟨w, hex⟩, hn⟩ := (GlobalTheory.T.face_map_complex_quasi_iso_iff_epi_exact _ K B f).1 hq'
  have hepi' : Epi ((free R).map (Ψ.map (a.app (SimplexCategory.mk 0))).unop) := by
    have e : f.app (op (SimplexCategory.mk 0)) = (free R).map (Ψ.map (a.app (SimplexCategory.mk 0))).unop :=
      Category.comp_id _
    rw [← e]; exact hepi
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    change (free R).map (Ψ.map (a.app (SimplexCategory.mk 0))).unop ≫ x =
      (free R).map (Ψ.map (a.app (SimplexCategory.mk 0))).unop ≫ y at hxy
    exact (cancel_epi _).1 hxy
  · intro y hy
    change (free R).map (Ψ.map (X.δ (n := 0) 0)).unop ≫ y = (free R).map (Ψ.map (X.δ (n := 0) 1)).unop ≫ y at hy
    let y' : K.obj (op (SimplexCategory.mk 0)) ⟶ J := y
    have hy' : (K.δ (n := 0) 0 - K.δ (n := 0) 1) ≫ y' = 0 := by
      refine (Preadditive.sub_comp _ _ _).trans (sub_eq_zero.2 ?_)
      exact hy
    refine ⟨hex.descToInjective (J := J) y' hy', ?_⟩
    exact hex.comp_descToInjective (J := J) y' hy'
  · intro n
    exact GlobalTheory.alternatingCofaceMapComplex_preadditiveYoneda_exactAt_succ K J n (hn n)

end GlobalTheory.EtC
end

section

open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology

theorem _root_.GlobalTheory.T.exists_quaternion_normOne_near_re_sq_ne_one : ∀ (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K], (2 : K) ≠ 0 → (𝓝[≠] (0 : K)).NeBot → ∀ a b : K, a ≠ 0 → ∀ g : ℍ[K, a, b], nrm g = 1 → ∀ W : Set ℍ[K, a, b], W ∈ 𝓝 g → ∃ g' : ℍ[K, a, b], nrm g' = 1 ∧ g'.re ^ 2 ≠ 1 ∧ W ∈ 𝓝 g' := by
  first | exact @GlobalTheory.QSA.exists_nrm_one_re_sq_ne_one | exact GlobalTheory.QSA.exists_nrm_one_re_sq_ne_one | (intros; apply GlobalTheory.QSA.exists_nrm_one_re_sq_ne_one <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

theorem _root_.GlobalTheory.T.comma_first_order_cocycle_lift : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), Function.Injective (CoefMap.restrict F G).pull2 → Function.Surjective (CoefMap.restrict F G).pull1 → (∀ κ : A1 F, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), κ T T'' (φ ≫ ψ) = p1 F ψ (κ T T' φ) + κ T' T'' ψ) → ∀ θ' : ∀ t, Ω[F.obj (G.obj t)⁄R], (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), κ _ _ (G.map a) = θ' t' - p1 F (G.map a) (θ' t)) → ∃ θ : A0 F, ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), κ T T' φ = θ T' - p1 F φ (θ T)) → Function.Surjective (pullGlob1 (CoefMap.restrict F G)) → (∀ (T : C) (x : Om R (F.obj T) 2), (∀ t (u : T ⟶ G.obj t), pOm F 2 u x = 0) → x = 0) → Function.Injective (pullHyp2 (CoefMap.restrict F G)) := by
  first | exact @GlobalTheory.CechDR.pullHyp2_restrict_injective | exact GlobalTheory.CechDR.pullHyp2_restrict_injective | (intros; apply GlobalTheory.CechDR.pullHyp2_restrict_injective <;> assumption)
end
