module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle001
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle013
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle015
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.Henselian
public import Mathlib.NumberTheory.SumFourSquares
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBTransport
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.GenBase

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory.SimilUnit

section Rep

variable {X Y Y' : Scheme.{0}} (L : LB X)

def IsVal (F : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U)
    (v : ∀ y : Y, ((Y ⟶ X) → L.ι) → (Y.presheaf.stalk y)ˣ) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)), t.IsGen ∧
    (∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = F U h) ∧
    ∀ y J, Good L y J → val t (𝟙 Y) y J = v y J

variable {L} {F F' : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U}
  {v v' : ∀ y : Y, ((Y ⟶ X) → L.ι) → (Y.presheaf.stalk y)ˣ}

theorem IsVal.pull {K : Type} [Fintype K] {φ : K → (Y' ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    (ht : t.IsGen) (r : Y ⟶ Y') :
    IsVal L (fun _ _ h => ∏ k, h (r ≫ φ k) ^ ε k) (fun y J => val t r y J) :=
  ⟨K, inferInstance, _, ε, LB.pullGen L φ ε t r, DVR.pullGen_isGen _ _ _ _ ht _, fun _ _ _ => rfl,
    fun y J hJ => by rw [val_pull hJ, Category.id_comp]⟩

theorem IsVal.one : IsVal L (Y := Y) (fun _ _ _ => 1) (fun _ _ => 1) :=
  ⟨PEmpty, inferInstance, _, _, LB.oneGen L, fun i j => by
    refine (map_one _).trans (Eq.symm ?_)
    exact (congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _), fun _ _ _ => Fintype.prod_empty _, fun _ _ _ => val_one _⟩

theorem IsVal.mul (a : IsVal L F v) (b : IsVal L F' v') :
    IsVal L (fun U _ h => F U h * F' U h) (fun y J => v y J * v' y J) := by
  obtain ⟨K, _, φ, ε, t, ht, hF, hv⟩ := a
  obtain ⟨K', _, φ', ε', t', ht', hF', hv'⟩ := b
  refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L _ _ _ _ t t', DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht',
    fun U _ h => ?_, fun y J hJ => ?_⟩
  · exact (Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (hF U h) (hF' U h))
  · rw [val_mul hJ, hv y J hJ, hv' y J hJ]

theorem IsVal.inv (a : IsVal L F v) : IsVal L (fun U _ h => (F U h)⁻¹) (fun y J => (v y J)⁻¹) := by
  obtain ⟨K, _, φ, ε, t, ht, hF, hv⟩ := a
  refine ⟨K, inferInstance, _, _, LB.invGen L _ _ t, DVR.invGen_isGen _ _ _ _ ht,
    fun U _ h => ?_, fun y J hJ => ?_⟩
  · simp only [zpow_neg, Finset.prod_inv_distrib, hF]
  · rw [val_inv, hv y J hJ]

theorem IsVal.pow (a : IsVal L F v) (n : ℕ) : IsVal L (fun U _ h => F U h ^ n) (fun y J => v y J ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using IsVal.one
  | succ n ih => simpa only [pow_succ] using ih.mul a

theorem IsVal.zpow (a : IsVal L F v) (n : ℤ) : IsVal L (fun U _ h => F U h ^ n) (fun y J => v y J ^ n) := by
  obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa only [zpow_natCast] using a.pow k
  · simpa only [zpow_neg, zpow_natCast] using (a.pow k).inv

theorem IsVal.prod {I : Type} {G : I → ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U}
    {u : I → ∀ y : Y, ((Y ⟶ X) → L.ι) → (Y.presheaf.stalk y)ˣ} (a : ∀ i, IsVal L (G i) (u i)) (s : Finset I) :
    IsVal L (fun U _ h => ∏ i ∈ s, G i U h) (fun y J => ∏ i ∈ s, u i y J) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using IsVal.one
  | insert d s hd ih => simpa only [Finset.prod_insert hd] using (a d).mul ih

theorem IsVal.exists_unit (hL : L.IsLB) (a : IsVal L F v)
    (h1 : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), F U h = 1) :
    ∃ u : Γ(Y, ⊤)ˣ, ∀ y J, Good L y J → (v y J).val = gs (𝟙 Y) y ⊤ u.val := by
  obtain ⟨K, _, φ, ε, t, ht, hF, hv⟩ := a
  obtain ⟨t', -, hv'⟩ := exists_gen hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun U _ h => ((hF U h).trans (h1 U h)).trans (Fintype.prod_empty _).symm) t ht
  have le : (⊤ : Y.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t'.s PEmpty.elim), fun y J hJ => ?_⟩
  rw [← hv y J hJ, ← hv' _ _ y J hJ, val_of t' _ y J PEmpty.elim (fun k => k.elim)]
  exact (congrArg Units.val (gm_res _ y le trivial _)).symm.trans (gs_unit _ y ⊤ trivial _).symm

end Rep

theorem pow_eq_one_of_similitude {A I : Type} [CommGroup A] [Fintype I] [DecidableEq I] (m : ℕ) (hm : m ≠ 0)
    (al : Matrix I I ℤ) (hal : al.transpose * al = (m : ℤ) • (1 : Matrix I I ℤ)) (ξ : I → A)
    (hk : ∀ c, ∏ r, ξ r ^ al r c = 1) (r : I) : ξ r ^ m = 1 := by
  have hm' : (m : ℤ) ≠ 0 := Int.natCast_ne_zero.2 hm
  have hd : al.det ≠ 0 := fun h0 => by
    have := congrArg Matrix.det hal
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_smul, Matrix.det_one, _root_.mul_one] at this
    exact pow_ne_zero _ hm' this.symm
  have h2 : al * al.transpose = (m : ℤ) • (1 : Matrix I I ℤ) := by
    have e : (al * al.transpose) * al = ((m : ℤ) • (1 : Matrix I I ℤ)) * al := by
      rw [Matrix.mul_assoc, hal, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
    have e' := congrArg (· * al.adjugate) e
    simp only [Matrix.mul_assoc (_ : Matrix I I ℤ) al al.adjugate, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at e'
    exact smul_right_injective _ hd e'
  have e : ∏ c, (∏ r', ξ r' ^ al r' c) ^ al r c = ξ r ^ m := by
    simp only [← Finset.prod_zpow, ← zpow_mul]
    rw [Finset.prod_comm]
    have : ∀ r', ∏ c, ξ r' ^ (al r' c * al r c) = ξ r' ^ (if r' = r then (m : ℤ) else 0) := fun r' => by
      have := congrFun (congrFun h2 r') r
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
        mul_ite, _root_.mul_one, mul_zero] at this
      rw [← this]
      exact (map_prod (zpowersHom A (ξ r')) (fun c => Multiplicative.ofAdd (al r' c * al r c)) Finset.univ).symm
    simp only [this, pow_ite, zpow_zero, Finset.prod_ite_eq', Finset.mem_univ, if_true, zpow_natCast]
  rw [← e]
  simp only [hk, one_zpow, Finset.prod_const_one]

theorem exists_normalising_unit : ∀ (R : Type) [CommRing R] (x : KeyIn R) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (ξ : Fin 4 → Pt x) (mu : LB.Gen (LB.LinComb x.P.L (K := Fin 2) ![((𝟙 x.P.A) ^ m).left, 𝟙 x.P.A.left] ![1, -(m : ℤ) ^ 2])) (w : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ))))), m ≠ 0 → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → (∀ c, (List.ofFn fun r : Fin 4 => ξ r ^ al r c).prod = 1) → mu.IsGen → w.IsGen → ∃ rho : Rˣ, ∀ (p : (𝟙_ (Over (Sp R))).left) J, Good x.P.L p J → (val w (eSec (Out.powObj x.P.A 4)) p J ^ (m ^ 2) * ∏ r, val mu (ξ r).left p J).val = gs (𝟙_ (Over (Sp R))).hom p ⊤ (cst (𝟙 (Sp R)) ⊤ rho) * (val x.rig (𝟙 _) p J ^ (4 - 4 * (m : ℤ) ^ 3)).val := by
  intro R _ x m al ξ mu w hm hal hk hmu hw
  haveI := x.P.isAb.comm
  have hξ : ∀ r, ξ r ^ m = 1 := pow_eq_one_of_similitude m hm al hal ξ fun c => by
    simpa only [List.prod_ofFn] using hk c
  have e₁ : ∀ c, eSec (Out.powObj x.P.A 4) ≫ (Out.powPr x.P.A c).left = eSec x.P.A := fun c =>
    congrArg CommaMorphism.left (IsMonHom.one_hom (Out.powPr x.P.A c))
  have e₂ : ∀ r, eSec (Out.powObj x.P.A 4) ≫ (alMap x al r (ξ r)).left = (ξ r).left := fun r => by
    have h1 : ∀ c, η[Out.powObj x.P.A 4] ≫ Out.powPr x.P.A c = 1 := fun c => by
      rw [IsMonHom.one_hom, Hom.one_def, toUnit_unit, Category.id_comp]
    have : η[Out.powObj x.P.A 4] ≫ alMap x al r (ξ r) = ξ r := by
      simp only [alMap, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, MonObj.comp_mul, GrpObj.comp_zpow,
        MonObj.comp_one, h1, one_zpow, _root_.one_mul]
      rw [← Category.assoc, toUnit_unique (η[_] ≫ toUnit _) (𝟙 _), Category.id_comp]
    exact congrArg CommaMorphism.left this
  have e₃ : ∀ r, (ξ r).left ≫ ((𝟙 x.P.A) ^ m).left = eSec x.P.A := fun r => by
    have : ξ r ≫ (𝟙 x.P.A) ^ m = η[x.P.A] := by
      rw [MonObj.comp_pow, Category.comp_id, hξ, Hom.one_def, toUnit_unit, Category.id_comp]
    exact congrArg CommaMorphism.left this
  obtain ⟨u, hu⟩ := ((((IsVal.pull hw (eSec (Out.powObj x.P.A 4))).pow (m ^ 2)).mul
    (IsVal.prod (fun r => IsVal.pull hmu (ξ r).left) Finset.univ)).mul
    ((IsVal.pull x.rig_gen (𝟙 _)).zpow (4 - 4 * (m : ℤ) ^ 3)).inv).exists_unit x.P.isLB (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, e₁, e₂, Fin.prod_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, e₃, Category.comp_id, Category.id_comp, Fintype.prod_unique, zpow_one,
        Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.card_unique, Finset.prod_zpow]
      generalize h (eSec x.P.A) = a
      generalize (∏ r, h (ξ r).left) = b
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow, ofMul_one]
      module)
  let E := RingEquiv.ofBijective _ (cst_bijective (𝟙 (Sp R)) (W := ⊤) rfl)
  refine ⟨Units.map E.symm.toMonoidHom u, fun p J hJ => ?_⟩
  have e : cst (𝟙 (Sp R)) ⊤ (Units.map E.symm.toMonoidHom u : Rˣ) = u.val := E.apply_symm_apply u.val
  rw [e]
  have := hu p J hJ
  rw [Units.val_mul, Units.mul_inv_eq_iff_eq_mul] at this
  exact this

end GlobalTheory.SimilUnit
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyVia

variable {X Y : Scheme.{0}} {L : LB X} {L' : LB Y} {φ : Y ⟶ X}

def Via (w : LB.Iso L' (L.pull φ)) (l : ℕ) (a' : ∀ i, Γ(Y, L'.U i)) (a : ∀ j, Γ(X, L.U j)) : Prop :=
  ∀ (j : (L.pull φ).ι) (i : L'.ι) (h : (L.pull φ).U j ⊓ L'.U i ≤ φ ⁻¹ᵁ L.U (j PUnit.unit)),
    (φ.appLE _ _ h).hom (a (j PUnit.unit)) =
      (show Γ(Y, (L.pull φ).U j ⊓ L'.U i) from (w.s (j, i)).val) ^ l * resG _ inf_le_right (a' i)

theorem chart_le (j : (L.pull φ).ι) : (L.pull φ).U j ≤ φ ⁻¹ᵁ L.U (j PUnit.unit) :=
  LB.wchart_le L (fun _ => φ) j PUnit.unit

theorem Via.unique (hL : L.IsLB) {w : LB.Iso L' (L.pull φ)} {l : ℕ} {a' b' : ∀ i, Γ(Y, L'.U i)}
    {a : ∀ j, Γ(X, L.U j)} (ha : Via w l a' a) (hb : Via w l b' a) : a' = b' := by
  funext i
  apply TopCat.Presheaf.section_ext Y.sheaf (L'.U i) (a' i) (b' i)
  intro y hy
  have hc := (DVR.linComb_isLB L hL (fun _ : PUnit => φ) (fun _ => 1)).cover
  have hyc : y ∈ ⨆ j, (L.pull φ).U j := by rw [hc]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hyc
  have h : (L.pull φ).U j ⊓ L'.U i ≤ φ ⁻¹ᵁ L.U (j PUnit.unit) := inf_le_left.trans (chart_le j)
  have e := (ha j i h).symm.trans (hb j i h)
  have hu : IsUnit ((show Γ(Y, (L.pull φ).U j ⊓ L'.U i) from (w.s (j, i)).val) ^ l) :=
    (Units.isUnit (w.s (j, i))).pow l
  have e' := hu.mul_left_cancel e
  have hm : y ∈ (L.pull φ).U j ⊓ L'.U i := ⟨hj, hy⟩
  rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE inf_le_right) y hm,
      ← TopCat.Presheaf.germ_res_apply _ (homOfLE inf_le_right) y hm]
  exact congrArg (fun v => (Y.presheaf.germ _ y hm).hom v) e'

def pwIso {A B : LB Y} (w : LB.Iso A B) (t : ℤ) : LB.Iso (pw A t) (pw B t) := ⟨fun p => w.s p ^ t⟩

theorem pwIso_isGen {A B : LB Y} {w : LB.Iso A B} (hw : w.IsGen) (t : ℤ) : (pwIso w t).IsGen := by
  intro p q
  have e := congrArg (· ^ t) (hw p q)
  simp only [mul_zpow, ← map_zpow] at e
  refine e.trans (congrArg₂ (· * ·) ?_ rfl)
  exact (mul_zpow _ _ t).trans (congrArg₂ (· * ·) (map_zpow _ _ t).symm
    ((inv_zpow _ t).trans (congrArg (·⁻¹) (map_zpow _ _ t).symm)))

theorem res_appLE {U : X.Opens} {V W : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U) (h' : W ≤ V) (a : Γ(X, U)) :
    resG Y h' ((φ.appLE U V h).hom a) = (φ.appLE U W (h'.trans h)).hom a := by
  have e := congrArg (fun q => q.hom a) (φ.appLE_map h (homOfLE h').op)
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using e

theorem appLE_res {U U' : X.Opens} {V : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U') (h' : U' ≤ U) (a : Γ(X, U)) :
    (φ.appLE U' V h).hom (resG X h' a) = (φ.appLE U V (h.trans fun _ hy => h' hy)).hom a := by
  have e := congrArg (fun q => q.hom a) (φ.map_appLE h (homOfLE h').op)
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using e

theorem pull_g (j j' : (L.pull φ).ι) (h : (L.pull φ).U j ⊓ (L.pull φ).U j' ≤ φ ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit))) :
    (L.pull φ).g j j' = Units.map (φ.appLE _ _ h).hom.toMonoidHom (L.g (j PUnit.unit) (j' PUnit.unit)) := by
  dsimp only [LB.pull, LB.LinComb]
  rw [Fintype.prod_unique]
  exact (zpow_one (Units.map (φ.appLE _ _ h).hom.toMonoidHom (L.g (j PUnit.unit) (j' PUnit.unit))))

def pullSec (φ : Y ⟶ X) {t : ℤ} (s : LB.Sec (pw L t)) : LB.Sec (pw (L.pull φ) t) where
  f j := (φ.appLE _ _ (chart_le j)).hom (s.f (j PUnit.unit))
  compat j j' := by
    have h : (L.pull φ).U j ⊓ (L.pull φ).U j' ≤ φ ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit)) :=
      fun _ hy => ⟨chart_le j hy.1, chart_le j' hy.2⟩
    have e := (congrArg (φ.appLE _ _ h).hom (s.compat (j PUnit.unit) (j' PUnit.unit))).trans (map_mul _ _ _)
    refine (res_appLE _ _ _).trans ((appLE_res h _ _).symm.trans (e.trans (congrArg₂ (· * ·) ?_
      ((appLE_res h _ _).trans (res_appLE _ _ _).symm))))
    exact (congrArg Units.val ((congrArg (· ^ t) (pull_g j j' h)).trans (map_zpow _ _ t).symm)).symm

theorem exists_via (hL : L.IsLB) (hL' : L'.IsLB) {w : LB.Iso L' (L.pull φ)} (hw : w.IsGen) (l : ℕ)
    (s : LB.Sec (pw L (l : ℤ))) : ∃ s' : LB.Sec (pw L' (l : ℤ)), Via w l s'.f s.f := by
  have isLB_pw {Z : Scheme.{0}} {H : LB Z} (hH : H.IsLB) (t : ℤ) : (pw H t).IsLB := by
    refine ⟨hH.cover, ?_, ?_⟩
    · intro i
      have e := congrArg (· ^ t) (hH.g_self i)
      simp only [one_zpow, ← map_zpow] at e
      exact e
    · intro i j k
      have e := congrArg (· ^ t) (hH.cocycle i j k)
      simp only [mul_zpow, ← map_zpow] at e
      exact e
  have hu := pwIso_isGen hw (l : ℤ)
  have hA := isLB_pw hL' (l : ℤ)
  have hB := isLB_pw (DVR.linComb_isLB L hL (fun _ : PUnit => φ) (fun _ => 1)) (l : ℤ)
  refine ⟨DVR.secOfIso (pullSec φ s) hu hA hB, fun j i h => ?_⟩
  have hV : (L.pull φ).U j ⊓ L'.U i ≤ (pw L' (l : ℤ)).U i ⊓ (pw (L.pull φ) (l : ℤ)).U j := fun _ hy => ⟨hy.2, hy.1⟩
  have h₁ := congrArg (DVR.rs hV) (DVR.secOfIso_spec (pullSec φ s) hu hA hB i j)
  have h₂ := ((DVR.rs_rs _ _ _).symm.trans h₁).trans (DVR.isoCand_rs (pwIso w l) (pullSec φ s) i j hV)
  let u : Γ(Y, (L.pull φ).U j ⊓ L'.U i)ˣ := w.s (j, i)
  have h₃ : res (hV.trans (DVR.divLe i j)) ((pwIso w (l : ℤ)).s (j, i)) = u ^ l :=
    (Units.ext (rs_self le_rfl (u ^ (l : ℤ)).val)).trans (zpow_natCast u l)
  have h₄ : resG Y (inf_le_right : (L.pull φ).U j ⊓ L'.U i ≤ L'.U i) ((DVR.secOfIso (pullSec φ s) hu hA hB).f i) =
      ((u ^ l)⁻¹).val * (φ.appLE _ _ h).hom (s.f (j PUnit.unit)) :=
    h₂.trans (congrArg₂ (· * ·) (congrArg (fun v => (v⁻¹).val) h₃) (res_appLE _ _ _))
  exact ((congrArg₂ (· * ·) (Units.val_pow_eq_pow_val u l).symm h₄).trans (Units.mul_inv_cancel_left _ _)).symm

theorem appLE_cst {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (p : X ⟶ Sp R) (p' : Y ⟶ Sp R')
    (hφ : φ ≫ p = p' ≫ spMap f) {U : X.Opens} {V : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U) (r : R) :
    (φ.appLE U V h).hom (cst p U r) = cst p' V (f r) := by
  refine (appLE_res h le_top _).trans ?_
  have e₁ : p.appTop ≫ φ.appTop = (spMap f).appTop ≫ p'.appTop := by
    rw [← Scheme.Hom.comp_appTop, hφ, Scheme.Hom.comp_appTop]
  have e₂ := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)
  have e₃ : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop ≫ φ.appTop =
      CommRingCat.ofHom f ≫ (Scheme.ΓSpecIso (CommRingCat.of R')).inv ≫ p'.appTop := by
    rw [e₁, ← Category.assoc, ← e₂, Category.assoc]
  exact congrArg (fun q => rs Y (le_top : V ≤ ⊤) (q.hom r)) e₃

theorem Via.comb {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (p : X ⟶ Sp R) (p' : Y ⟶ Sp R')
    (hφ : φ ≫ p = p' ≫ spMap f) {w : LB.Iso L' (L.pull φ)} {l N : ℕ} {b' : Fin N → ∀ i, Γ(Y, L'.U i)}
    {b : Fin N → ∀ j, Γ(X, L.U j)} (hb : ∀ k, Via w l (b' k) (b k)) (c : Fin N → R) :
    Via w l (fun i => ∑ k, cst p' _ (f (c k)) * b' k i) (fun j => ∑ k, cst p _ (c k) * b k j) := by
  intro j i h

  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_mul, hb k j i h, appLE_cst f p p' hφ, rs_cst, mul_left_comm]

theorem main : ∀ (R R' : Type) [CommRing R] [CommRing R'] (x : KeyIn R) (x' : KeyIn R') (f : R →+* R'), (KeyPB x' x f ↔ ∃ φ w, KeyVia x' x f φ w) ∧ ∀ φ w, KeyVia x' x f φ w → (∀ (l : ℕ) (s : RR x l), ∃! s' : RR x' l, SecVia x' x φ w s' s) ∧ (∀ z : Pt x, ∃! z' : Pt x', z'.left ≫ φ = spMap f ≫ z.left) ∧ ∀ (l N : ℕ) (b : Fin N → RR x l) (b' : Fin N → RR x' l) (s : RR x l) (s' : RR x' l) (c : Fin N → R), (∀ k, SecVia x' x φ w (b' k) (b k)) → SecVia x' x φ w s' s → Coords x b c s.f → Coords x' b' (fun k => f (c k)) s'.f := by
  intro R R' _ _ x x' f
  refine ⟨⟨fun ⟨φ, he, w, hg, F, H⟩ => ⟨φ, w, he, hg, F, H⟩, fun ⟨φ, w, he, hg, F, H⟩ => ⟨φ, he, w, hg, F, H⟩⟩, ?_⟩
  rintro φ w ⟨he, hg, F, ⟨hP, -⟩, hw, -⟩
  refine ⟨fun l s => ?_, fun z => ?_, fun l N b b' s s' c hb hs hc => ?_⟩
  · obtain ⟨s', hs'⟩ := exists_via x.P.isLB x'.P.isLB hw l s
    refine ⟨s', hs', fun t ht => ?_⟩
    have e : t.f = s'.f := Via.unique (w := w) (l := l) x.P.isLB ht hs'
    obtain ⟨tf, _⟩ := t
    obtain ⟨sf, _⟩ := s'
    obtain rfl : tf = sf := e
    rfl
  · have hz : z.left ≫ x.P.A.hom = 𝟙 (Sp R) := Over.w z
    have hc : (spMap f ≫ z.left) ≫ x.P.A.hom = 𝟙 (Sp R') ≫ spMap f := by
      rw [Category.assoc, hz, Category.comp_id, Category.id_comp]
    refine ⟨Over.homMk (hP.lift _ _ hc) (hP.lift_snd _ _ hc), hP.lift_fst _ _ hc, fun t ht => ?_⟩
    ext1
    exact hP.hom_ext (ht.trans (hP.lift_fst _ _ hc).symm) ((Over.w t).trans (hP.lift_snd _ _ hc).symm)
  · have H := Via.comb (w := w) (l := l) (b' := fun k => (b' k).f) (b := fun k => (b k).f) f x.P.A.hom x'.P.A.hom hP.w hb c
    have e : s.f = fun j => ∑ k, cst x.P.A.hom (x.P.L.U j) (c k) * (show Γ(x.P.A.left, x.P.L.U j) from (b k).f j) :=
      funext hc
    have hs' : Via w l s'.f s.f := hs
    have hs'' := (congrArg (Via w l s'.f) e).mp hs'
    have e' := Via.unique x.P.isLB hs'' H
    exact fun i => congrFun e' i

end GlobalTheory.KeyVia
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam

theorem GeomInt.baseChange {K R : Type} [Field K] [CommRing R] [Algebra K R] (h : GeomInt K R)
    (K' : Type) [Field K'] [Algebra K K'] : GeomInt K' (K' ⊗[K] R) := by
  haveI := h.1
  refine ⟨inferInstance, fun L _ _ => ?_⟩
  letI : Algebra K L := ((algebraMap K' L).comp (algebraMap K K')).toAlgebra
  haveI : IsScalarTower K K' L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI := h.2 L
  exact (Algebra.TensorProduct.cancelBaseChange K K' L L R).toMulEquiv.isDomain _

theorem GeomInt.away {K R : Type} [Field K] [CommRing R] [Algebra K R] (h : GeomInt K R)
    {r : R} (hr : r ≠ 0) : GeomInt K (Localization.Away r) := by
  haveI := h.1
  haveI : Algebra.Smooth R (Localization.Away r) := Algebra.Smooth.of_isLocalization_Away r
  refine ⟨Algebra.Smooth.comp K R _, fun L _ _ => ?_⟩
  haveI := h.2 L
  letI : Algebra (L ⊗[K] R) (L ⊗[K] Localization.Away r) :=
    (Algebra.TensorProduct.map (AlgHom.id L L)
      (IsScalarTower.toAlgHom K R (Localization.Away r))).toAlgebra
  haveI : IsScalarTower L (L ⊗[K] R) (L ⊗[K] Localization.Away r) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      simp [RingHom.algebraMap_toAlgebra]
  have hloc := IsLocalization.tensorProduct_tensorProduct_right K L (Submonoid.powers r)
    (Localization.Away r) (by ext; simp [RingHom.algebraMap_toAlgebra])
  refine IsLocalization.isDomain_of_le_nonZeroDivisors (hM := ?_) (S := L ⊗[K] Localization.Away r)
    (M := (Submonoid.powers r).map (Algebra.TensorProduct.includeRight (R := K) (A := L)))
  rw [Submonoid.map_powers]
  apply powers_le_nonZeroDivisors_of_noZeroDivisors
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := R)) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective
  exact fun h0 => hr (hinj (by rw [h0, map_zero]))

theorem geomInt_baseChange_and_away :
    ∀ (K K' R : Type) [Field K] [Field K'] [Algebra K K'] [CommRing R] [Algebra K R],
      GeomInt K R → GeomInt K' (K' ⊗[K] R) ∧ ∀ r : R, r ≠ 0 → GeomInt K (Localization.Away r) :=
  fun _ K' _ _ _ _ _ _ h => ⟨h.baseChange K', fun _ hr => h.away hr⟩

end GlobalTheory.KeyFam
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

namespace GlobalTheory.KeyKa

theorem exists_quaternion_matrix (m : ℕ) : ∃ A : Matrix (Fin 4) (Fin 4) ℤ,
    A.transpose * A = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares m
  have h' : (m : ℤ) = (a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 + (d : ℤ) ^ 2 := by
    rw [← h]; push_cast; ring
  refine ⟨!![(a : ℤ), -b, -c, -d; b, a, -d, c; c, d, a, -b; d, -c, b, a], ?_⟩
  rw [h']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply, Matrix.one_apply] <;> ring

theorem exists_admissibleKeyNumericalData_prime_to : ∀ g p : ℕ, 1 ≤ g → p.Prime → ∃ (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ), admitted g n l l' al ∧ ¬ p ∣ degProd g n l l' ∧ 1 ≤ degProd g n l l' ∧ 1 ≤ kaExp g n l l' := by
  intro g p hg hp
  choose al hal using exists_quaternion_matrix
  have hp0 := hp.pos
  have hnd : ¬ p ∣ degProd g (4 * p) (g * (4 * p) + 1) (g * (4 * p) + 1 + p) := by
    unfold degProd
    rw [Prime.dvd_finsetProd_iff hp.prime]
    rintro ⟨j, hj, hd⟩
    have hj' : j ≤ g := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj'
    have e1 : (j + k) * (4 * p) + 1 - j * (4 * p) = p * (4 * k) + 1 := by
      apply Nat.sub_eq_of_eq_add; ring
    have e2 : (j + k) * (4 * p) + 1 + p - j * (4 * p) = p * (4 * k + 1) + 1 := by
      apply Nat.sub_eq_of_eq_add; ring
    rw [e1, e2] at hd
    rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
    · exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right (dvd_mul_right _ _)).mp h))
    · exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right (dvd_mul_right _ _)).mp h))
  have hpos : 0 < degProd g (4 * p) (g * (4 * p) + 1) (g * (4 * p) + 1 + p) :=
    Nat.pos_of_ne_zero fun h => hnd (h ▸ dvd_zero p)
  refine ⟨4 * p, g * (4 * p) + 1, g * (4 * p) + 1 + p, al, ⟨by omega, by omega, by omega, hal⟩,
    hnd, hpos, ?_⟩
  unfold kaExp
  have h1 : 0 < g * (4 * p) + 1 + p - (g * (4 * p) + 1) := by omega
  have h2 := Nat.factorial_pos g
  apply Nat.succ_le_of_lt
  positivity

end GlobalTheory.KeyKa
end

section

namespace GlobalTheory.KeyPow


open Matrix ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi in
theorem exists_thetaLaw_zero_of_even (hInv : ReciprocityTheory.ChartRestriction.G.Key.Chi.InversionStatement) (g : ℕ)
    (n n' : Fin g → ℤ) (h : Even (n ⬝ᵥ n')) :
    ∃ sp ∈ Matrix.symplecticGroup (Fin g) ℤ, GlobalTheory.KeyPow.ThetaLaw g sp n n' 0 0 := by
  obtain ⟨S, hS, hd⟩ := GlobalTheory.exists_isSymm_mulVec_add_diag_mod_two g n n' h
  have h1 : ThetaLaw g (spTransl S) n n' n 0 :=
    (thetaLaw_generators hInv g n 0).1 S n' hS fun i => by simpa using hd i
  have h2 : ThetaLaw g (Matrix.J (Fin g) ℤ) n 0 0 n := (thetaLaw_generators hInv g 0 n).2
  have hD : (Matrix.diagonal n).IsSymm := Matrix.isSymm_diagonal _
  have h3 : ThetaLaw g (spTransl (Matrix.diagonal n)) 0 n 0 0 :=
    (thetaLaw_generators hInv g 0 0).1 _ n hD fun i => by simp
  have m1 : spTransl S ∈ Matrix.symplecticGroup (Fin g) ℤ := spTransl_mem_sp hS
  have m2 : Matrix.J (Fin g) ℤ ∈ Matrix.symplecticGroup (Fin g) ℤ := SymplecticGroup.J_mem _ _
  have m3 : spTransl (Matrix.diagonal n) ∈ Matrix.symplecticGroup (Fin g) ℤ := spTransl_mem_sp hD
  exact ⟨_, mul_mem m3 (mul_mem m2 m1), thetaLaw_mul g _ _ _ _ _ _ _ _ m3 (mul_mem m2 m1)
    (thetaLaw_mul g _ _ _ _ _ _ _ _ m2 m1 h1 h2) h3⟩

end GlobalTheory.KeyPow
end
