module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle359
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle405
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

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec

namespace GlobalTheory.EtC.CotSheaf

def evF (p : ℕ) (V : Scheme.{0}) : Spc ⥤ Type :=
  (evaluation SimplexCategoryᵒᵖ PSh).obj (op (SimplexCategory.mk p)) ⋙ (evaluation Scheme.{0}ᵒᵖ Type).obj (op V)

instance (A B : Spc) (p : ℕ) (V : Scheme.{0}) : PreservesLimit (pair A B) (evF p V) := by
  unfold evF; infer_instance

def prodEquiv (A B : Spc) (p : ℕ) (V : Scheme.{0}) : Sx (A ⨯ B) p V ≃ Sx A p V × Sx B p V :=
  ((PreservesLimitPair.iso (evF p V) A B) ≪≫ Types.binaryProductIso _ _).toEquiv

theorem prodEquiv_apply {A B : Spc} {p : ℕ} {V : Scheme.{0}} (y : Sx (A ⨯ B) p V) :
    prodEquiv A B p V y = (Sx.map prod.fst y, Sx.map prod.snd y) := by
  have e1 := ConcreteCategory.congr_hom (prodComparison_fst (evF p V) A B) y
  have e2 := ConcreteCategory.congr_hom (prodComparison_snd (evF p V) A B) y
  simp only [prodEquiv, Iso.toEquiv, Iso.trans_hom, PreservesLimitPair.iso_hom]
  ext
  · simp
    exact e1
  · simp
    exact e2

variable {p : ℕ}

theorem map_res' {E E' : Spc} (φ : E ⟶ E') {V W : Scheme.{0}} (k : W ⟶ V) (y : Sx E p V) :
    Sx.map φ (y.res k) = (Sx.map φ y).res k :=
  ConcreteCategory.congr_hom ((φ.app (op (SimplexCategory.mk p))).naturality k.op) y

theorem map_comp' {E E' E'' : Spc} (φ : E ⟶ E') (ψ : E' ⟶ E'') {V : Scheme.{0}} (y : Sx E p V) :
    Sx.map (φ ≫ ψ) y = Sx.map ψ (Sx.map φ y) := rfl

theorem res_res {E : Spc} {V W W' : Scheme.{0}} (k : W ⟶ V) (g : W' ⟶ W) (y : Sx E p V) :
    (y.res k).res g = y.res (g ≫ k) :=
  (ConcreteCategory.congr_hom ((E.obj (op (SimplexCategory.mk p))).map_comp k.op g.op) y).symm

theorem res_id {E : Spc} {V : Scheme.{0}} (y : Sx E p V) : y.res (𝟙 V) = y :=
  ConcreteCategory.congr_hom ((E.obj (op (SimplexCategory.mk p))).map_id (op V)) y

theorem prod_ext {A B : Spc} {V : Scheme.{0}} {y y' : Sx (A ⨯ B) p V} (h1 : Sx.map prod.fst y = Sx.map prod.fst y')
    (h2 : Sx.map prod.snd y = Sx.map prod.snd y') : y = y' :=
  (prodEquiv A B p V).injective (by rw [prodEquiv_apply, prodEquiv_apply, h1, h2])

def mkS {A B : Spc} {V : Scheme.{0}} (a : Sx A p V) (b : Sx B p V) : Sx (A ⨯ B) p V := (prodEquiv A B p V).symm (a, b)

theorem fst_mkS {A B : Spc} {V : Scheme.{0}} (a : Sx A p V) (b : Sx B p V) : Sx.map prod.fst (mkS a b) = a := by
  have := (prodEquiv A B p V).apply_symm_apply (a, b)
  rw [prodEquiv_apply] at this
  exact congrArg Prod.fst this

theorem snd_mkS {A B : Spc} {V : Scheme.{0}} (a : Sx A p V) (b : Sx B p V) : Sx.map prod.snd (mkS a b) = b := by
  have := (prodEquiv A B p V).apply_symm_apply (a, b)
  rw [prodEquiv_apply] at this
  exact congrArg Prod.snd this

def mk1 {F : Spc} {W : Scheme.{0}} (z : Sx F p W) : Sx (sch.obj W ⨯ F) p W := mkS (A := sch.obj W) (𝟙 W) z

theorem simplexImage_fst_schemeProductSimplexIdFirst {F : Spc} {W : Scheme.{0}} (z : Sx F p W) : (Sx.map prod.fst (mk1 z) : W ⟶ W) = 𝟙 W :=
  fst_mkS (A := sch.obj W) _ _

theorem simplexImage_snd_schemeProductSimplexIdFirst {F : Spc} {W : Scheme.{0}} (z : Sx F p W) : Sx.map prod.snd (mk1 z) = z :=
  snd_mkS (A := sch.obj W) _ _

theorem fst_pm {F : Spc} {U U' V : Scheme.{0}} (f : U' ⟶ U) (y : Sx (sch.obj U' ⨯ F) p V) :
    (Sx.map prod.fst (Sx.map (prod.map (sch.map f) (𝟙 F)) y) : V ⟶ U) = (Sx.map prod.fst y : V ⟶ U') ≫ f := by
  rw [← map_comp', prod.map_fst, map_comp']
  rfl

theorem snd_pm {F : Spc} {U U' V : Scheme.{0}} (f : U' ⟶ U) (y : Sx (sch.obj U' ⨯ F) p V) :
    Sx.map prod.snd (Sx.map (prod.map (sch.map f) (𝟙 F)) y) = Sx.map prod.snd y := by
  rw [← map_comp', prod.map_snd, Category.comp_id]

theorem fst_res {F : Spc} {U V W : Scheme.{0}} (k : W ⟶ V) (y : Sx (sch.obj U ⨯ F) p V) :
    (Sx.map prod.fst (y.res k) : W ⟶ U) = k ≫ (Sx.map prod.fst y : V ⟶ U) := by
  rw [map_res']
  rfl

theorem snd_res {F : Spc} {U V W : Scheme.{0}} (k : W ⟶ V) (y : Sx (sch.obj U ⨯ F) p V) :
    Sx.map prod.snd (y.res k) = (Sx.map prod.snd y).res k :=
  map_res' _ _ _

theorem yres_eq {F : Spc} {U V W : Scheme.{0}} (k : W ⟶ V) (y : Sx (sch.obj U ⨯ F) p V) :
    y.res k = Sx.map (prod.map (sch.map (k ≫ (Sx.map prod.fst y : V ⟶ U))) (𝟙 F)) (mk1 ((Sx.map prod.snd y).res k)) :=
  prod_ext (by rw [fst_pm, simplexImage_fst_schemeProductSimplexIdFirst, Category.id_comp, fst_res]) (by rw [snd_pm, simplexImage_snd_schemeProductSimplexIdFirst, snd_res])

theorem cotPre_isSheaf (R : Type) [CommRing R] (q N : ℕ) (I : Cx R) (n : ℤ) :
    Presheaf.IsSheaf Scheme.etaleTopology.{0} (cotPre R q N I n) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} R))), isSheaf_iff_isSheaf_of_type]
  have hQ : ∀ s, Presieve.IsSheaf Scheme.etaleTopology.{0} ((I.X s).obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
    fun s => (isSheaf_iff_isSheaf_of_type _ _).1 ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).1 (I.X s).property)
  have sres_res : ∀ (s : ℤ) {V W W' : Scheme.{0}} (k : W ⟶ V) (g : W' ⟶ W) (v : Sec (I.X s) V),
      Sec.res g (Sec.res k v) = Sec.res (g ≫ k) v := fun s V W W' k g v =>
    (ConcreteCategory.congr_hom (((I.X s).obj).map_comp k.op g.op) v).symm
  have sres_id : ∀ (s : ℤ) {V : Scheme.{0}} (v : Sec (I.X s) V), Sec.res (𝟙 V) v = v := fun s V v =>
    ConcreteCategory.congr_hom (((I.X s).obj).map_id (op V)) v
  intro U S hS
  have hsep : Presieve.IsSeparatedFor (cotPre R q N I n ⋙ forget _) S.arrows := by
    intro x α β hα hβ
    have hc : ∀ (W : Scheme.{0}) (c : W ⟶ U), S.arrows c →
        (Cochain.ofHom ((chains R).map (prod.map (sch.map c) (𝟙 (fibQ q N))))).comp α (zero_add n) =
        (Cochain.ofHom ((chains R).map (prod.map (sch.map c) (𝟙 (fibQ q N))))).comp β (zero_add n) :=
      fun W c hc => (hα c hc).trans (hβ c hc).symm
    refine ev_ext _ _ fun p s h V y => ?_
    refine (hQ s _ (Scheme.etaleTopology.pullback_stable (Sx.map prod.fst y : V ⟶ U) hS)).isSeparatedFor.ext
      fun W k hk => ?_
    have e1 := ev_res (R := R) (E := sch.obj U ⨯ fibQ q N) (I := I) (n := n) α p s h k y
    have e2 := ev_res (R := R) (E := sch.obj U ⨯ fibQ q N) (I := I) (n := n) β p s h k y
    refine e1.trans (Eq.trans ?_ e2.symm)
    have e3 := ev_pull (R := R) (I := I) (n := n) (prod.map (sch.map (k ≫ (Sx.map prod.fst y : V ⟶ U))) (𝟙 (fibQ q N))) α
      p s h W (mk1 ((Sx.map prod.snd y).res k))
    have e4 := ev_pull (R := R) (I := I) (n := n) (prod.map (sch.map (k ≫ (Sx.map prod.fst y : V ⟶ U))) (𝟙 (fibQ q N))) β
      p s h W (mk1 ((Sx.map prod.snd y).res k))
    rw [yres_eq k y, ← e3, ← e4, hc _ _ hk]
  refine hsep.isSheafFor fun x hx => ?_
  have hx' := (Presieve.compatible_iff_sieveCompatible x).1 hx
  have evx : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) {V W : Scheme.{0}} (c c' : W ⟶ U) (hc : S.arrows c)
      (hc' : S.arrows c') (w w' : Sx (sch.obj W ⨯ fibQ q N) p V), c = c' → w = w' →
        ev (x c hc) p s h V w = ev (x c' hc') p s h V w' := by
    rintro p s h V W c c' hc hc' w w' rfl rfl
    rfl
  have gen : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) {V W : Scheme.{0}} (c : W ⟶ U) (hc : S.arrows c)
      (w : Sx (sch.obj W ⨯ fibQ q N) p V), ev (x c hc) p s h V w =
        ev (x ((Sx.map prod.fst w : V ⟶ W) ≫ c) (S.downward_closed hc _)) p s h V (mk1 (Sx.map prod.snd w)) := by
    intro p s h V W c hc w
    have e2 := ev_pull (R := R) (I := I) (n := n) (E := sch.obj W ⨯ fibQ q N)
      (prod.map (sch.map (Sx.map prod.fst w : V ⟶ W)) (𝟙 (fibQ q N))) (x c hc) p s h V (mk1 (Sx.map prod.snd w))
    rw [hx' c (Sx.map prod.fst w : V ⟶ W) hc]
    refine Eq.trans ?_ e2.symm
    congr 1
    exact (prod_ext ((fst_pm (Sx.map prod.fst w : V ⟶ W) (mk1 (Sx.map prod.snd w))).trans (by rw [simplexImage_fst_schemeProductSimplexIdFirst]; exact Category.id_comp _))
      ((snd_pm (Sx.map prod.fst w : V ⟶ W) (mk1 (Sx.map prod.snd w))).trans (simplexImage_snd_schemeProductSimplexIdFirst _))).symm
  let φ : ∀ (p : ℕ) (s : ℤ) (_ : -(p : ℤ) + n = s) (V : Scheme.{0}) (y : Sx (sch.obj U ⨯ fibQ q N) p V),
      Presieve.FamilyOfElements ((I.X s).obj ⋙ forget (ModuleCat.{1} (ULift.{1} R)))
        (S.pullback (Sx.map prod.fst y : V ⟶ U)).arrows :=
    fun p s h V y W k hk => ev (x (k ≫ Sx.map prod.fst y) hk) p s h W (mk1 ((Sx.map prod.snd y).res k))
  have hφ : ∀ p s h V y, (φ p s h V y).Compatible := by
    intro p s h V y
    rw [Presieve.compatible_iff_sieveCompatible]
    intro W W' k g hk
    change ev (x (g ≫ k ≫ _) _) p s h W' (mk1 _) = Sec.res g (ev (x (k ≫ _) hk) p s h W (mk1 _))
    refine Eq.trans ?_ (ev_res (R := R) (E := sch.obj W ⨯ fibQ q N) (I := I) (n := n) (x (k ≫ _) hk) p s h g _).symm
    refine Eq.trans ?_ (gen p s h _ hk _).symm
    apply evx
    · rw [fst_res, simplexImage_fst_schemeProductSimplexIdFirst, Category.comp_id]
    · rw [snd_res, simplexImage_snd_schemeProductSimplexIdFirst, res_res]
  let val : ∀ (p : ℕ) (s : ℤ) (_ : -(p : ℤ) + n = s) (V : Scheme.{0}), Sx (sch.obj U ⨯ fibQ q N) p V → Sec (I.X s) V :=
    fun p s h V y => (hQ s _ (Scheme.etaleTopology.pullback_stable (Sx.map prod.fst y : V ⟶ U) hS)).amalgamate
      (φ p s h V y) (hφ p s h V y)
  have hval : ∀ p s h V y {W : Scheme.{0}} (k : W ⟶ V) (hk : S.arrows (k ≫ Sx.map prod.fst y)),
      Sec.res k (val p s h V y) = ev (x (k ≫ Sx.map prod.fst y) hk) p s h W (mk1 ((Sx.map prod.snd y).res k)) :=
    fun p s h V y W k hk =>
      (hQ s _ (Scheme.etaleTopology.pullback_stable (Sx.map prod.fst y : V ⟶ U) hS)).valid_glue (hφ p s h V y) k hk
  have hnat : ∀ p s h (V V' : Scheme.{0}) (g : V' ⟶ V) (y : Sx (sch.obj U ⨯ fibQ q N) p V),
      Sec.res g (val p s h V y) = val p s h V' (y.res g) := by
    intro p s h V V' g y
    refine (hQ s _ (Scheme.etaleTopology.pullback_stable (Sx.map prod.fst (y.res g) : V' ⟶ U) hS)).isSeparatedFor.ext
      fun W k hk => ?_
    change Sec.res k (Sec.res g _) = Sec.res k (val p s h V' (y.res g))
    have hk' : S.arrows ((k ≫ g) ≫ Sx.map prod.fst y) := by
      have : S.arrows (k ≫ Sx.map prod.fst (y.res g)) := hk
      rw [fst_res] at this
      convert this using 2
      exact Category.assoc _ _ _
    rw [sres_res, hval _ _ _ _ _ _ hk', hval _ _ _ _ _ _ hk]
    apply evx
    · rw [fst_res]
      exact Category.assoc _ _ _
    · rw [snd_res, res_res]
  obtain ⟨α, hα⟩ := ev_exists (E := sch.obj U ⨯ fibQ q N) (I := I) (n := n) val
    (fun p s h V' V g y => hnat p s h V V' g y)
  refine ⟨α, fun W c hc => ?_⟩
  change (Cochain.ofHom ((chains R).map (prod.map (sch.map c) (𝟙 (fibQ q N))))).comp α (zero_add n) = x c hc
  refine ev_ext _ _ fun p s h V w => ?_
  have h1 : S.arrows (𝟙 V ≫ Sx.map prod.fst (Sx.map (prod.map (sch.map c) (𝟙 (fibQ q N))) w)) := by
    have := S.downward_closed hc (Sx.map prod.fst w : V ⟶ W)
    convert this using 2
    exact (Category.id_comp _).trans (fst_pm c w)
  refine (ev_pull (R := R) (I := I) (n := n) (E := sch.obj U ⨯ fibQ q N) _ α p s h V w).trans ?_
  rw [hα]
  refine (sres_id s _).symm.trans ((hval _ _ _ _ _ _ h1).trans ?_)
  refine Eq.trans ?_ (gen p s h c hc w).symm
  apply evx
  · exact (Category.id_comp _).trans (fst_pm c w)
  · rw [res_id, snd_pm]

end GlobalTheory.EtC.CotSheaf

end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec

noncomputable section
namespace GlobalTheory.EtC.GlueDisc

def pe (k : ℕ) (V : Scheme.{0}) : Spc ⥤ Type :=
  (evaluation _ _).obj (op (SimplexCategory.mk k)) ⋙ (evaluation _ _).obj (op V)

instance (k : ℕ) (V : Scheme.{0}) : PreservesLimitsOfShape (Discrete WalkingPair) (pe k V) := by
  unfold pe; infer_instance

def pairE (A B : Spc) (k : ℕ) (V : Scheme.{0}) : Sx (A ⨯ B) k V ≃ Sx A k V × Sx B k V :=
  ((PreservesLimitPair.iso (pe k V) A B) ≪≫ Types.binaryProductIso _ _).toEquiv

theorem pairE_apply (A B : Spc) (k : ℕ) (V : Scheme.{0}) (z : Sx (A ⨯ B) k V) :
    pairE A B k V z = (Sx.map prod.fst z, Sx.map prod.snd z) := by
  apply Prod.ext
  · change ((Types.binaryProductIso _ _).hom ((prodComparison (pe k V) A B) z)).1 = _
    rw [Types.binaryProductIso_hom_comp_fst_apply]
    exact ConcreteCategory.congr_hom (prodComparison_fst (pe k V) A B) z
  · change ((Types.binaryProductIso _ _).hom ((prodComparison (pe k V) A B) z)).2 = _
    rw [Types.binaryProductIso_hom_comp_snd_apply]
    exact ConcreteCategory.congr_hom (prodComparison_snd (pe k V) A B) z

theorem prod_ext {A B : Spc} {k : ℕ} {V : Scheme.{0}} (z z' : Sx (A ⨯ B) k V)
    (h₁ : Sx.map prod.fst z = Sx.map prod.fst z') (h₂ : Sx.map prod.snd z = Sx.map prod.snd z') : z = z' :=
  (pairE A B k V).injective (by rw [pairE_apply, pairE_apply, h₁, h₂])

def mk {A B : Spc} {k : ℕ} {V : Scheme.{0}} (a : Sx A k V) (b : Sx B k V) : Sx (A ⨯ B) k V :=
  (pairE A B k V).symm (a, b)

theorem mk_fst {A B : Spc} {k : ℕ} {V : Scheme.{0}} (a : Sx A k V) (b : Sx B k V) : Sx.map prod.fst (mk a b) = a := by
  have h := (pairE A B k V).apply_symm_apply (a, b)
  rw [pairE_apply] at h
  exact congrArg Prod.fst h

theorem mk_snd {A B : Spc} {k : ℕ} {V : Scheme.{0}} (a : Sx A k V) (b : Sx B k V) : Sx.map prod.snd (mk a b) = b := by
  have h := (pairE A B k V).apply_symm_apply (a, b)
  rw [pairE_apply] at h
  exact congrArg Prod.snd h

theorem map_res {E E' : Spc} (f : E ⟶ E') {V W : Scheme.{0}} (h : W ⟶ V) {k : ℕ} (a : Sx E k V) :
    Sx.map f (Sx.res h a) = Sx.res h (Sx.map f a) :=
  ConcreteCategory.congr_hom ((f.app (op (SimplexCategory.mk k))).naturality h.op) a

theorem map_prodMap_fst {A A' B B' : Spc} (f : A ⟶ A') (g : B ⟶ B') {k : ℕ} {V : Scheme.{0}} (z : Sx (A ⨯ B) k V) :
    Sx.map prod.fst (Sx.map (prod.map f g) z) = Sx.map f (Sx.map prod.fst z) := by
  change Sx.map (prod.map f g ≫ prod.fst) z = Sx.map (prod.fst ≫ f) z
  rw [prod.map_fst]

theorem map_prodMap_snd {A A' B B' : Spc} (f : A ⟶ A') (g : B ⟶ B') {k : ℕ} {V : Scheme.{0}} (z : Sx (A ⨯ B) k V) :
    Sx.map prod.snd (Sx.map (prod.map f g) z) = Sx.map g (Sx.map prod.snd z) := by
  change Sx.map (prod.map f g ≫ prod.snd) z = Sx.map (prod.snd ≫ g) z
  rw [prod.map_snd]

variable {F : PSh} {B : Spc}

def lift {k : ℕ} {V : Scheme.{0}} (z : Sx (disc.obj F ⨯ B) k V) : Sx (sch.obj V ⨯ B) k V :=
  mk (show Sx (sch.obj V) k V from 𝟙 V) (Sx.map prod.snd z)

theorem lift_spec {k : ℕ} {V : Scheme.{0}} (z : Sx (disc.obj F ⨯ B) k V) :
    Sx.map (E := sch.obj V ⨯ B) (prod.map (disc.map (yonedaEquiv.symm (Sx.map prod.fst z))) (𝟙 B)) (lift z) = z := by
  apply prod_ext
  · have h := map_prodMap_fst (A := sch.obj V)
      (show sch.obj V ⟶ disc.obj F from disc.map (yonedaEquiv.symm (Sx.map prod.fst z))) (𝟙 B) (lift z)
    rw [lift, mk_fst] at h
    refine h.trans ?_
    change F.map (𝟙 V).op (Sx.map prod.fst z) = _
    simp
  · have h := map_prodMap_snd (A := sch.obj V)
      (show sch.obj V ⟶ disc.obj F from disc.map (yonedaEquiv.symm (Sx.map prod.fst z))) (𝟙 B) (lift z)
    rw [lift, mk_snd] at h
    exact h

theorem lift_res {k : ℕ} {V W : Scheme.{0}} (g : W ⟶ V) (z : Sx (disc.obj F ⨯ B) k V) :
    Sx.res g (lift z) = Sx.map (prod.map (sch.map g) (𝟙 B)) (lift (Sx.res g z)) := by
  apply prod_ext
  · rw [map_prodMap_fst, map_res, lift, lift, mk_fst, mk_fst]
    change g ≫ 𝟙 V = 𝟙 W ≫ g
    rw [Category.comp_id, Category.id_comp]
  · rw [map_prodMap_snd, map_res, lift, lift, mk_snd, mk_snd, map_res]
    rfl

theorem fst_pull {k : ℕ} {U W : Scheme.{0}} (x : F.obj (op U)) (y : Sx (sch.obj U ⨯ B) k W) :
    Sx.map prod.fst (Sx.map (E := sch.obj U ⨯ B) (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 B)) y) =
      F.map (Quiver.Hom.op (Sx.map prod.fst y : W ⟶ U)) x :=
  map_prodMap_fst (A := sch.obj U)
    (show sch.obj U ⟶ disc.obj F from disc.map (yonedaEquiv.symm x)) (𝟙 B) y

theorem lift_pull {k : ℕ} {U W : Scheme.{0}} (x : F.obj (op U)) (y : Sx (sch.obj U ⨯ B) k W) :
    Sx.map (prod.map (sch.map (Sx.map prod.fst y : W ⟶ U)) (𝟙 B))
      (lift (Sx.map (E := sch.obj U ⨯ B) (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 B)) y)) = y := by
  apply prod_ext
  · rw [map_prodMap_fst, lift, mk_fst]
    exact Category.id_comp (Sx.map prod.fst y : W ⟶ U)
  · rw [map_prodMap_snd, lift, mk_snd]
    exact map_prodMap_snd (A := sch.obj U)
      (show sch.obj U ⟶ disc.obj F from disc.map (yonedaEquiv.symm x)) (𝟙 B) y

end GlobalTheory.EtC.GlueDisc

namespace GlobalTheory.EtC
open GlueDisc

theorem cochain_disc_glue (R : Type) [CommRing R] (q N : ℕ) (I : Cx R) (F : PSh) (n : ℤ)
    (c : ∀ U : Scheme.{0}, F.obj (op U) → Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n)
    (hc : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : F.obj (op U)),
      c V (F.map g.op x) = (Cochain.ofHom ((chains R).map (prod.map (sch.map g) (𝟙 (fibQ q N))))).comp (c U x) (zero_add n)) :
    ∃! γ : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n, ∀ (U : Scheme.{0}) (x : F.obj (op U)),
      (Cochain.ofHom ((chains R).map (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 (fibQ q N))))).comp γ (zero_add n) =
        c U x := by
  obtain ⟨γ, hγ⟩ := ev_exists (R := R) (E := disc.obj F ⨯ fibQ q N) (I := I) (n := n)
    (fun p s h V z => ev (c V (Sx.map prod.fst z)) p s h V (lift z)) (by
      intro p s h V U g z
      rw [ev_res, lift_res, map_res]
      refine (ev_pull (prod.map (sch.map g) (𝟙 (fibQ q N))) (c U (Sx.map prod.fst z)) p s h V
        (lift (Sx.res g z))).symm.trans ?_
      rw [← hc]
      rfl)
  refine ⟨γ, fun U x => ev_ext (E := sch.obj U ⨯ fibQ q N) _ _ fun p s h W y => ?_, fun γ' hγ' => ev_ext _ _ fun p s h V z => ?_⟩
  · refine (ev_pull (E' := sch.obj U ⨯ fibQ q N) (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 (fibQ q N))) γ
      p s h W y).trans ?_
    rw [hγ, fst_pull]
    refine (congrArg (fun α => ev α p s h W _) (hc W U (Sx.map prod.fst y : W ⟶ U) x)).trans ?_
    rw [ev_pull, lift_pull]
  · rw [hγ, ← hγ' V (Sx.map prod.fst z)]
    refine (congrArg (ev γ' p s h V) (lift_spec z)).symm.trans ?_
    exact (ev_pull (E' := sch.obj V ⨯ fibQ q N) _ γ' p s h V (lift z)).symm

end GlobalTheory.EtC
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.Stair

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (s : Sec F U) :
    Sec.res (k ≫ g) s = Sec.res k (Sec.res g s) := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (s : Sec F U) :
    Sec.map φ (Sec.res g s) = Sec.res g (Sec.map φ s) :=
  LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (φ.hom.naturality g.op)) s

theorem map_nsmul' {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (n : ℕ) (s : Sec F U) :
    Sec.map φ (n • s) = n • Sec.map φ s := map_nsmul _ _ _

theorem res_nsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (n : ℕ) (s : Sec F U) :
    Sec.res g (n • s) = n • Sec.res g s := map_nsmul _ _ _

theorem map_add' {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (s t : Sec F U) :
    Sec.map φ (s + t) = Sec.map φ s + Sec.map φ t := map_add _ _ _

theorem map_zero' {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} :
    Sec.map φ (0 : Sec F U) = 0 := map_zero _

theorem res_sub {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (s t : Sec F U) :
    Sec.res g (s - t) = Sec.res g s - Sec.res g t := map_sub _ _ _

theorem map_d_d {R : Type} [CommRing R] (K : Cx R) (h i j : ℤ) {U : Scheme.{0}} (w : Sec (K.X h) U) :
    Sec.map (K.d i j) (Sec.map (K.d h i) w) = 0 := by
  change ((K.d h i ≫ K.d i j).hom.app (op U)).hom w = 0
  rw [K.d_comp_d h i j]; rfl

theorem loc_of {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  loc_calculus.1 U P h

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (h : ∀ V g, P V g → Q V g) : Loc U Q :=
  loc_calculus.2.1 U P Q hP h

theorem loc_bind {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (h : ∀ V g, P V g → Loc V fun W k => Q W (k ≫ g)) : Loc U Q :=
  loc_calculus.2.2.2.2.1 U Q (loc_mono hP h)

def StairP {R : Type} [CommRing R] (K : Cx R) (r : ℕ) (i : ℤ) : Prop :=
  ∀ (h j : ℤ), h + 1 = i → i + 1 = j → ∀ (U : Scheme.{0}) (x : Sec (K.X i) U),
    (Loc U fun V g => ∃ y : Sec (K.X j) V, Sec.map (K.d i j) (Sec.res g x) = r • y) →
    Loc U fun V g => ∃ (u : Sec (K.X h) V) (y : Sec (K.X i) V), Sec.res g x = Sec.map (K.d h i) u + r • y

theorem stair_step {R : Type} [CommRing R] (K : Cx R) (r s : ℕ)
    (hrs : ∀ (n : ℤ) (U : Scheme.{0}) (y : Sec (K.X n) U), (r * s) • y = 0)
    (hfl : ∀ (n : ℤ) (U : Scheme.{0}) (x : Sec (K.X n) U), s • x = 0 →
      Loc U fun V g => ∃ y : Sec (K.X n) V, Sec.res g x = r • y)
    (hex : ∀ (h i j : ℤ), h + 1 = i → i + 1 = j → ∀ (U : Scheme.{0}) (b : Sec (K.X i) U),
      Sec.map (K.d i j) b = 0 → Loc U fun V g => ∃ c : Sec (K.X h) V, Sec.map (K.d h i) c = Sec.res g b)
    (i : ℤ) (ih : StairP K s (i - 1)) : StairP K r i := by
  intro h j hh hj U x hL
  obtain rfl : h = i - 1 := by omega
  refine loc_bind hL fun V g hy => ?_
  obtain ⟨y, hy⟩ := hy
  have hcyc : Sec.map (K.d i j) (s • Sec.res g x) = 0 := by
    rw [map_nsmul', hy, smul_smul, mul_comm, hrs]
  refine loc_bind (hex (i - 1) i j (by omega) hj V _ hcyc) fun W k hc => ?_
  obtain ⟨c, hc⟩ := hc
  rw [res_nsmul] at hc
  have hP := ih (i - 1 - 1) i (by omega) (by omega) W c
    (loc_of fun W' k' => ⟨Sec.res k' (Sec.res k (Sec.res g x)), by rw [map_res, hc, res_nsmul]⟩)
  refine loc_bind hP fun W' k' hw => ?_
  obtain ⟨w, u', hw⟩ := hw
  have hz : s • (Sec.res k' (Sec.res k (Sec.res g x)) - Sec.map (K.d (i - 1) i) u') = 0 := by
    rw [smul_sub, ← res_nsmul, ← hc, ← map_res, hw, map_add', map_nsmul', map_d_d, zero_add, sub_self]
  refine loc_mono (hfl i W' _ hz) fun W'' k'' hy' => ?_
  obtain ⟨y', hy'⟩ := hy'
  refine ⟨Sec.res k'' u', y', ?_⟩
  rw [res_sub, ← map_res, sub_eq_iff_eq_add] at hy'
  simp only [res_comp]
  rw [hy', add_comm]

end GlobalTheory.EtC.Stair

namespace GlobalTheory.EtC


open Stair in
theorem staircase_loc : ∀ (R : Type) [CommRing R] (q e : ℕ) (K : Cx R) (a : ℤ),
    (∀ n, n < a → ∀ (U : Scheme.{0}) (x : Sec (K.X n) U), x = 0) →
    (∀ (n : ℤ) (U : Scheme.{0}) (y : Sec (K.X n) U), (q * e) • y = 0) →
    (∀ (n : ℤ) (U : Scheme.{0}) (x : Sec (K.X n) U), e • x = 0 → Loc U fun V g => ∃ y : Sec (K.X n) V, Sec.res g x = q • y) →
    (∀ (n : ℤ) (U : Scheme.{0}) (x : Sec (K.X n) U), q • x = 0 → Loc U fun V g => ∃ y : Sec (K.X n) V, Sec.res g x = e • y) →
    (∀ (n : ℤ) (U : Scheme.{0}) (b : Sec (K.X n) U), Sec.map (K.d n (n + 1)) b = 0 →
      Loc U fun V g => ∃ c : Sec (K.X (n - 1)) V, Sec.map (K.d (n - 1) n) c = Sec.res g b) →
    ∀ (n : ℤ) (U : Scheme.{0}) (x : Sec (K.X n) U),
      (Loc U fun V g => ∃ y : Sec (K.X (n + 1)) V, Sec.map (K.d n (n + 1)) (Sec.res g x) = q • y) →
      Loc U fun V g => ∃ (u : Sec (K.X (n - 1)) V) (y : Sec (K.X n) V), Sec.res g x = Sec.map (K.d (n - 1) n) u + q • y := by
  intro R _ q e K a hbd hqe hq he hex n U x hx
  have hex' : ∀ (h i j : ℤ), h + 1 = i → i + 1 = j → ∀ (U : Scheme.{0}) (b : Sec (K.X i) U),
      Sec.map (K.d i j) b = 0 → Loc U fun V g => ∃ c : Sec (K.X h) V, Sec.map (K.d h i) c = Sec.res g b := by
    intro h i j hh hj U b hb
    obtain rfl : h = i - 1 := by omega
    obtain rfl : j = i + 1 := by omega
    exact hex i U b hb
  have hqe' : ∀ (n : ℤ) (U : Scheme.{0}) (y : Sec (K.X n) U), (e * q) • y = 0 := fun n U y => by
    rw [mul_comm]; exact hqe n U y
  have base : ∀ (r : ℕ) (i : ℤ), i < a → StairP K r i := by
    intro r i hi h j _ _ U x _
    exact loc_of fun V g => ⟨0, 0, by rw [hbd i hi V (Sec.res g x), map_zero', smul_zero, add_zero]⟩
  have key : ∀ k : ℕ, ∀ i : ℤ, i < a + k → StairP K q i ∧ StairP K e i := by
    intro k
    induction k with
    | zero => intro i hi; exact ⟨base q i (by simpa using hi), base e i (by simpa using hi)⟩
    | succ k ih =>
      intro i hi
      obtain ⟨h1, h2⟩ := ih (i - 1) (by push_cast at hi; omega)
      exact ⟨stair_step K q e hqe hq hex' i h2, stair_step K e q hqe' he hex' i h1⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n < a + k := ⟨(n - a + 1).toNat, by omega⟩
  exact (key k n hk).1 (n - 1) (n + 1) (by omega) rfl U x hx

end GlobalTheory.EtC

end
end
