module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle002
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle010
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.SubConjTransposeOfSymm
public import ReciprocityTheory.ThetaQuasiPeriods.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.Blocks
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.SpGenStatement

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.RelBasis

variable {X Y T : Scheme.{0}} {L : LB X} {t : ℤ} {N : ℕ}

def comb (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) (W : T.Opens) (c : Fin N → Γ(T, W)) (y : Y)
    (i : L.ι) : Y.presheaf.stalk y :=
  ∑ k, gs p₁ y W (c k) * gs p₂ y (L.U i) ((b k).f i)

def IndepOn (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) (W : T.Opens) : Prop :=
  ∀ c : Fin N → Γ(T, W), (∀ (y : Y) (i : L.ι), p₁ y ∈ W → p₂ y ∈ L.U i → comb b p₁ p₂ W c y i = 0) → c = 0

def SpanOn (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) (W : T.Opens) : Prop :=
  ∀ σ : ∀ i : L.ι, Γ(Y, p₁ ⁻¹ᵁ W ⊓ p₂ ⁻¹ᵁ L.U i),
    (∀ (y : Y) (i i' : L.ι), p₁ y ∈ W → p₂ y ∈ L.U i → p₂ y ∈ L.U i' →
      gs (𝟙 Y) y _ (σ i) = (gm p₂ y (L.U i ⊓ L.U i') (L.g i i') ^ t).val * gs (𝟙 Y) y _ (σ i')) →
    ∃ c : Fin N → Γ(T, W), ∀ (y : Y) (i : L.ι), p₁ y ∈ W → p₂ y ∈ L.U i →
      gs (𝟙 Y) y _ (σ i) = comb b p₁ p₂ W c y i

def BoxSpan (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) : Prop :=
  ∀ (K : Type) [Fintype K] (φ : K → (T ⟶ X)) (ε : K → ℤ)
    (s : LB.Sec (LB.LinComb L (K := K ⊕ PUnit) (Sum.elim (fun k => p₁ ≫ φ k) (fun _ => p₂)) (Sum.elim ε (fun _ => t)))),
    ∃ a : Fin N → LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      sval s r z J = ∑ k, sval (a k) (r ≫ p₁) z J * gs (r ≫ p₂) z (L.U (J (r ≫ p₂))) ((b k).f (J (r ≫ p₂)))

theorem gs_comp {Z : Scheme.{0}} (r : Z ⟶ Y) (f : Y ⟶ X) (z : Z) (U : X.Opens) (h : f (r z) ∈ U) (a : Γ(X, U)) :
    gs (r ≫ f) z U a = (r.stalkMap z).hom (gs f (r z) U a) := by
  rw [← gs_pull r f z U h, gs_eq f (r z) U h, gs_eq r z (f ⁻¹ᵁ U) h]
  exact (Scheme.Hom.germ_stalkMap_apply r (f ⁻¹ᵁ U) z h _).symm

def gsHom (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) : Γ(X, U) →+* Y.presheaf.stalk y :=
  (Y.presheaf.germ (f ⁻¹ᵁ U) y h).hom.comp (f.app U).hom

theorem gs_eq_gsHom (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) :
    gs f y U a = gsHom f y U h a := gs_eq f y U h a

theorem comb_comp {Z : Scheme.{0}} (b : Fin N → LB.Sec (pw L t)) (r : Z ⟶ Y) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) (W : T.Opens)
    (c : Fin N → Γ(T, W)) (z : Z) (i : L.ι) (h₁ : p₁ (r z) ∈ W) (h₂ : p₂ (r z) ∈ L.U i) :
    comb b (r ≫ p₁) (r ≫ p₂) W c z i = (r.stalkMap z).hom (comb b p₁ p₂ W c (r z) i) := by

  rw [comb, comb, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, gs_comp r p₁ z W h₁]
  exact congrArg _ (gs_comp r p₂ z (L.U i) h₂ _)

end GlobalTheory.RelBasis
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.BoxDetUnique
variable {X Y Z : Scheme.{0}} {R : Type} [CommRing R]

def kv (q : Z ⟶ Sp R) (z : Z) : R →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ ⊤ z trivial).hom.comp (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

def gsH (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) : Γ(X, U) →+* Y.presheaf.stalk y :=
  (Y.presheaf.germ (f ⁻¹ᵁ U) y h).hom.comp (f.app U).hom

theorem gs_eqH (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) : gs f y U a = gsH f y U h a :=
  gs_eq f y U h a

theorem gs_sum' (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {N : Type} (s : Finset N) (a : N → Γ(X, U)) :
    gs f y U (∑ i ∈ s, a i) = ∑ i ∈ s, gs f y U (a i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gs_eqH f y U h, map_sum]

theorem gs_prod' (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {N : Type} (s : Finset N) (a : N → Γ(X, U)) :
    gs f y U (∏ i ∈ s, a i) = ∏ i ∈ s, gs f y U (a i) := by
  simp only [gs_eqH f y U h, map_prod]

theorem gs_zero' (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) : gs f y U 0 = 0 := by
  simp only [gs_eqH f y U h, map_zero]

theorem gs_cst (p : Y ⟶ Sp R) (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) (a : R) :
    gs r z U (cst p U a) = kv (r ≫ p) z a :=
  (gs_res r z le_top h _).trans ((gs_pull r p z ⊤ trivial _).trans (gs_eq (r ≫ p) z ⊤ trivial _))

theorem gen_ratio {K : Type} [Field K] {M : LB X} (hM : M.IsLB) {N : Type} [Fintype N] {φ : N → (Y ⟶ X)} {ε : N → ℤ}
    (p : Y ⟶ Sp K) (hp : Function.Surjective p.appTop.hom)
    {u u' : LB.Gen (LB.LinComb M φ ε)} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ c : K, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      (val u' r z J).val = kv (r ≫ p) z c * (val u r z J).val := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u' (LB.invGen M _ _ u)) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu' (DVR.invGen_isGen _ _ _ _ hu))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  obtain ⟨a, ha⟩ := hp (res le (t.s PEmpty.elim)).val
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2 a
  refine ⟨c, fun Z r z J hJ => ?_⟩
  have key : (val u' r z J * (val u r z J)⁻¹).val = kv (r ≫ p) z c := by
    rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
    exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans ((gs_unit r z ⊤ trivial _).symm.trans
      ((congrArg (gs r z ⊤) ha.symm).trans ((gs_pull r p z ⊤ trivial _).trans (gs_eq (r ≫ p) z ⊤ trivial _))))
  rw [← key, ← Units.val_mul, inv_mul_cancel_right]

theorem gs_sec_pw {L : LB X} {m : ℤ} (s : LB.Sec (pw L m)) (r : Z ⟶ X) (z : Z) (i j : L.ι) (hi : r z ∈ L.U i)
    (hj : r z ∈ L.U j) :
    gs r z (L.U i) (s.f i) = (gm r z (L.U i ⊓ L.U j) (L.g i j) ^ m).val * gs r z (L.U j) (s.f j) := by
  have hm : r z ∈ L.U i ⊓ L.U j := ⟨hi, hj⟩
  refine (gs_res r z _ hm _).symm.trans ((congrArg (gs r z _) (s.compat i j)).trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) ?_ (gs_res r z _ hm _))))
  exact (gs_unit r z _ hm _).trans (congrArg Units.val (map_zpow _ _ _))

theorem exists_boxSec {L : LB X} {m : ℤ} {N I : Type} [Fintype N] [Fintype I] (φ : N → (Y ⟶ X)) (p : Y ⟶ Sp R)
    (q : I → R) (s : I → N → LB.Sec (pw L m)) : ∃ S : LB.Sec (LB.LinComb L φ (fun _ => m)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : N → L.ι), r z ∈ LB.wchart L φ j →
        gs r z (LB.wchart L φ j) (S.f j) =
          ∑ a, kv (r ≫ p) z (q a) * ∏ c, gs (r ≫ φ c) z (L.U (j c)) ((s a c).f (j c)) := by
  obtain ⟨F, hF⟩ : ∃ F : ∀ j : N → L.ι, Γ(Y, LB.wchart L φ j),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : N → L.ι), r z ∈ LB.wchart L φ j →
        gs r z (LB.wchart L φ j) (F j) =
          ∑ a, kv (r ≫ p) z (q a) * ∏ c, gs (r ≫ φ c) z (L.U (j c)) ((s a c).f (j c)) := by
    refine ⟨fun j => ∑ a, cst p _ (q a) * ∏ c, rs Y (LB.wchart_le L φ j c) (((φ c).app (L.U (j c))).hom ((s a c).f (j c))),
      fun Z r z j h => ?_⟩
    rw [gs_sum' r z _ h]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [gs_mul r z _ h, gs_cst p r z _ h, gs_prod' r z _ h]
    refine congrArg _ (Finset.prod_congr rfl fun c _ => ?_)
    exact (gs_res r z _ h _).trans (gs_pull r (φ c) z _ (LB.wchart_le L φ j c h) _)
  refine ⟨⟨F, fun j j' => fn_ext fun y hy => ?_⟩, hF⟩
  refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L φ _ (𝟙 Y) y j j' hy.1 hy.2)))
      (gs_res (𝟙 Y) y _ hy _))).symm)
  refine (hF _ (𝟙 Y) y j hy.1).trans (Eq.trans ?_ (congrArg _ (hF _ (𝟙 Y) y j' hy.2)).symm)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_left_comm, Units.coe_prod, ← Finset.prod_mul_distrib]
  refine congrArg _ (Finset.prod_congr rfl fun c _ => ?_)
  exact gs_sec_pw _ _ y _ _ (LB.wchart_le L φ j c hy.1) (LB.wchart_le L φ j' c hy.2)

theorem exists_perm (hN : Out.MulNSt) {K : Type} [Field K] (P : Out.PolAV (Sp K)) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ)
    (hm : (m : K) ≠ 0) (hal : al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
    (ξ ξ' : (Fin 4 → Fin (m ^ P.g)) → Fin 4 → (𝟙_ (Over (Sp K)) ⟶ P.A))
    (h : Function.Injective ξ) (h' : Function.Injective ξ')
    (e : ∀ I c, (List.ofFn fun r : Fin 4 => ξ I r ^ al r c).prod = 1)
    (e' : ∀ I c, (List.ofFn fun r : Fin 4 => ξ' I r ^ al r c).prod = 1) :
    ∃ σ : Equiv.Perm (Fin 4 → Fin (m ^ P.g)), ξ' = fun I => ξ (σ I) := by
  haveI := P.isAb.comm
  let k := AlgebraicClosure K
  let t : Spec (CommRingCat.of k) ⟶ Sp K := Spec.map (CommRingCat.ofHom (algebraMap K k))
  have hm1 : 1 ≤ m := Nat.pos_of_ne_zero fun h0 => hm (by rw [h0, Nat.cast_zero])
  have hc := GlobalTheory.card_ker_int_matrix_four (Over.mk t ⟶ P.A) m (2 * P.g) al hm1 hal (fun n hn => by
    have hn0 : (n : K) ≠ 0 := fun h0 => hm (by obtain ⟨d, rfl⟩ := hn; rw [Nat.cast_mul, h0, zero_mul])
    refine (hN _ P n (Nat.pos_of_ne_zero fun h0 => hn0 (by rw [h0, Nat.cast_zero]))).2.2.2.2 k t ?_
    rw [← map_natCast (algebraMap K k)]
    exact (map_ne_zero _).2 hn0)
  have hepi : Epi t := by
    haveI : Flat t := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact RingHom.flat_algebraMap_iff.2 inferInstance
    haveI : Surjective t := ⟨fun y => ⟨IsLocalRing.closedPoint k, Subsingleton.elim _ _⟩⟩
    exact Flat.epi_of_flat_of_surjective t
  let f : (𝟙_ (Over (Sp K)) ⟶ P.A) →* (Over.mk t ⟶ P.A) := preHom (toUnit (Over.mk t))
  have hf : Function.Injective f := fun a b hab => by
    have h1 : (toUnit (Over.mk t)).left ≫ a.left = (toUnit (Over.mk t)).left ≫ b.left := congrArg (·.left) hab
    have h2 : (toUnit (Over.mk t)).left = t := (Category.comp_id _).symm.trans (Over.w (toUnit (Over.mk t)))
    haveI : Epi (toUnit (Over.mk t)).left := h2 ▸ hepi
    exact Over.OverMorphism.ext ((cancel_epi _).1 h1)
  have bij : ∀ (ζ : (Fin 4 → Fin (m ^ P.g)) → Fin 4 → (𝟙_ (Over (Sp K)) ⟶ P.A)), Function.Injective ζ →
      (∀ I c, (List.ofFn fun r : Fin 4 => ζ I r ^ al r c).prod = 1) →
      ∃ E : (Fin 4 → Fin (m ^ P.g)) ≃ {ξ : Fin 4 → (Over.mk t ⟶ P.A) // ∀ c, ∏ r', ξ r' ^ al r' c = 1},
        ∀ I r, (E I).1 r = f (ζ I r) := by
    intro ζ hζ he
    let g : (Fin 4 → Fin (m ^ P.g)) → {ξ : Fin 4 → (Over.mk t ⟶ P.A) // ∀ c, ∏ r', ξ r' ^ al r' c = 1} :=
      fun I => ⟨fun r => f (ζ I r), fun c => by
        have := congrArg f (he I c)
        rw [List.prod_ofFn, map_prod, map_one] at this
        simpa only [map_zpow] using this⟩
    have hg : Function.Injective g := fun I I' hI => hζ (funext fun r => hf (congrFun (congrArg Subtype.val hI) r))
    haveI : Finite {ξ : Fin 4 → (Over.mk t ⟶ P.A) // ∀ c, ∏ r', ξ r' ^ al r' c = 1} :=
      Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
    refine ⟨Equiv.ofBijective g (hg.bijective_of_nat_card_le ?_), fun _ _ => rfl⟩
    rw [hc, Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_fin, ← pow_mul]
    exact le_of_eq (by congr 1; ring)
  obtain ⟨E, hE⟩ := bij ξ h e
  obtain ⟨E', hE'⟩ := bij ξ' h' e'
  refine ⟨E'.trans E.symm, funext fun I => funext fun r => hf ?_⟩
  rw [← hE, ← hE']
  simp

theorem det_calc {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I] (σ : Equiv.Perm I) (Q Q' T : Matrix I I K)
    (c rho rho' : I → K) (n : ℕ) (hQ : ∀ a b, Q (σ a) b = c a * ∑ d, Q' a d * T b d)
    (hr : ∀ a, rho' a = c a ^ n * rho (σ a)) :
    Q.det ^ (2 * n) * ∏ a, rho a ^ 2 = (Q'.det ^ (2 * n) * ∏ a, rho' a ^ 2) * T.det ^ (2 * n) := by
  have h1 : Q.submatrix σ id = Matrix.diagonal c * (Q' * T.transpose) := by
    ext a b
    rw [Matrix.diagonal_mul, Matrix.mul_apply]
    exact hQ a b
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_permute, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at h2
  have h3 : Q.det ^ 2 = ((∏ a, c a) * (Q'.det * T.det)) ^ 2 := by
    rw [← h2, mul_pow]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  have h4 : ∏ a, rho' a ^ 2 = (∏ a, c a) ^ (2 * n) * ∏ a, rho a ^ 2 := by
    rw [← Equiv.prod_comp σ (fun a => rho a ^ 2), ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun a _ => by rw [hr]; ring
  rw [h4, pow_mul, h3]
  ring

end GlobalTheory.BoxDetUnique
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.KeyPow

theorem IsKeyPow.dim_eq {R : Type} [CommRing R] {y x : KeyIn R} {j : ℕ} (h : IsKeyPow y x j) :
    y.P.g = j * x.P.g := by
  obtain ⟨_, hg, -⟩ := h
  exact hg.symm

theorem exists_int_half {g : ℕ} {a : Fin g → ℂ} (h : ∀ i, a i = 0 ∨ a i = 1 / 2) :
    ∃ n : Fin g → ℤ, a = fun i => (((n i : ℝ) / 2 : ℝ) : ℂ) := by
  have : ∀ i, ∃ m : ℤ, a i = (((m : ℝ) / 2 : ℝ) : ℂ) := fun i => by
    rcases h i with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
  choose n hn using this
  exact ⟨n, funext hn⟩

theorem even_dot_double {g g' : ℕ} (e : Fin 2 × Fin g ≃ Fin g') (n n' : Fin g → ℤ) :
    Even ((fun p => n (e.symm p).2) ⬝ᵥ (fun p => n' (e.symm p).2)) := by
  refine ⟨n ⬝ᵥ n', ?_⟩
  unfold dotProduct
  rw [← e.sum_comp]
  simp [Fintype.sum_prod_type, two_mul]

end GlobalTheory.KeyPow
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KeyPow


open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi in
theorem thetaLaw_mul : ∀ (g : ℕ) (sp sq : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (n n' m m' k k' : Fin g → ℤ), sp ∈ Matrix.symplecticGroup (Fin g) ℤ → sq ∈ Matrix.symplecticGroup (Fin g) ℤ → GlobalTheory.KeyPow.ThetaLaw g sq n n' m m' → GlobalTheory.KeyPow.ThetaLaw g sp m m' k k' → GlobalTheory.KeyPow.ThetaLaw g (sp * sq) n n' k k' := by
  intro g x y n n' m m' k k' hx hy Hy Hx
  obtain ⟨c₁, hc₁, h₁⟩ := Hy
  obtain ⟨c₂, hc₂, h₂⟩ := Hx
  refine ⟨c₂ * c₁, by rw [mul_pow, hc₁, hc₂, _root_.one_mul], fun τ hτ z => ?_⟩
  have hjy := jAut_isUnit hy hτ
  have hτ₂ := spAct_mem hy hτ
  have hjx := jAut_isUnit hx hτ₂
  rw [spAct_mul x y τ hjy, zAct_mul x y τ hjy z, h₂ _ hτ₂, h₁ τ hτ z, det_jAut_mul x y τ hjy,
    expArg_mul x y τ hjy hjx (sp_A hy hτ.1 hjy) z, eC_add]
  ring

end GlobalTheory.KeyPow
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PowChange

open GlobalTheory.PowLie

variable {R : Type} [CommRing R]

theorem sc_zero_comp {G : Over (Sp R)} [GrpObj G] {v : epsR R ⟶ G} (hv : IsTangent v) :
    sc 0 ≫ v = 1 := by
  have h : sc (0 : R) = toUnit _ ≫ zeroPt R := by
    refine Over.OverMorphism.ext ?_
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  rw [h, Category.assoc, (isTangent_iff v).1 hv, Hom.one_def]

theorem exists_block_basis {G' G : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]
    {j g n : ℕ} (p : Out.IsPowGrp G' G j) (hg : j * g = n) {v v' : Fin g → (epsR R ⟶ G)}
    (hv : IsLieBasis v) (hv' : IsLieBasis v') (M : Matrix (Fin g) (Fin g) R)
    (hM : ∀ i, IsLieComb (M i) v (v' i)) (u : Fin n → (epsR R ⟶ G'))
    (hu : ∀ (i i' : Fin j) (k : Fin g),
      u ((finProdFinEquiv (i, k)).cast hg) ≫ p.pr i' = if i = i' then v k else 1) :
    ∃ (w : Fin n → (epsR R ⟶ G')) (M' : Matrix (Fin n) (Fin n) R), IsLieBasis w ∧
      (∀ (i i' : Fin j) (k : Fin g),
        w ((finProdFinEquiv (i, k)).cast hg) ≫ p.pr i' = if i = i' then v' k else 1) ∧
      (∀ i, IsLieComb (M' i) u (w i)) ∧ M'.det = M.det ^ j := by
  subst hg
  obtain ⟨w, hw, hw'⟩ := isLieBasis_pow R G' G j g p v' hv'
  let e : Fin g × Fin j ≃ Fin (j * g) := (Equiv.prodComm _ _).trans finProdFinEquiv
  refine ⟨w, Matrix.reindex e e (Matrix.blockDiagonal fun _ => M), hw, hw', fun m => ?_, ?_⟩
  · obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective m
    rw [isLieComb_iff_prod]
    refine p.lim.hom_ext fun ⟨i'⟩ => ?_
    have := p.hom i'
    change _ ≫ p.pr i' = _ ≫ p.pr i'
    refine Eq.trans ?_ (map_prod (IsMonHom.monoidHom (p.pr i') (epsR R)) _ _).symm
    have hu' : ∀ (i : Fin j) (k : Fin g), u (finProdFinEquiv (i, k)) ≫ p.pr i' = if i = i' then v k else 1 :=
      fun i k => hu i i' k
    rw [hw', ← finProdFinEquiv.prod_comp, Fintype.prod_prod_type, Finset.prod_eq_single i']
    · have h₁ : ∀ k', (IsMonHom.monoidHom (p.pr i') (epsR R))
          (sc (Matrix.reindex e e (Matrix.blockDiagonal fun _ => M) (finProdFinEquiv (i, k))
            (finProdFinEquiv (i', k'))) ≫ u (finProdFinEquiv (i', k'))) =
          sc (if i = i' then M k k' else 0) ≫ v k' := fun k' => by
        change (sc _ ≫ u _) ≫ p.pr i' = _
        rw [Category.assoc, hu', if_pos rfl]
        congr 2
        simp [e, Matrix.blockDiagonal_apply]
      rw [Finset.prod_congr rfl fun k' _ => h₁ k']
      split_ifs with h
      · exact (isLieComb_iff_prod _ _ _).1 (hM k)
      · exact (Finset.prod_eq_one fun k' _ => sc_zero_comp (hv.1 k')).symm
    · intro i'' _ hi
      refine Finset.prod_eq_one fun k' _ => ?_
      change (sc _ ≫ u _) ≫ p.pr i' = _
      rw [Category.assoc, hu', if_neg hi, comp_one]
    · simp
  · rw [Matrix.det_reindex_self, Matrix.det_blockDiagonal]
    simp

theorem appLE_constFn {X Y : Scheme.{0}} (q : X ⟶ Sp R) (q' : Y ⟶ Sp R) (f : Y ⟶ X) (hf : f ≫ q = q')
    (U : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U) (a : R) :
    (f.appLE U V h).hom (constFn q U a) = constFn q' V a := by
  subst hf
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_comp_appLE f q ⊤ U V (fun _ _ => trivial) h)

theorem res_constFn {X : Scheme.{0}} (q : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (a : R) :
    (X.presheaf.map (homOfLE h).op).hom (constFn q U a) = constFn q V a :=
  congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map q (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)

theorem constFn_pow {X : Scheme.{0}} (q : X ⟶ Sp R) (U : X.Opens) (a : R) (n : ℕ) :
    constFn q U (a ^ n) = constFn q U a ^ n := by
  simp only [constFn, map_pow]

def constMul {X : Scheme.{0}} (q : X ⟶ Sp R) {L : LB X} (a : R) (s : L.Sec) : L.Sec where
  f i := constFn q _ a * s.f i
  compat i j := by
    rw [map_mul, map_mul, res_constFn, res_constFn, s.compat, mul_left_comm]

theorem nonzeroLocus_constMul {X : Scheme.{0}} (q : X ⟶ Sp R) {L : LB X} {a : R} (ha : IsUnit a) (s : L.Sec) :
    Out.nonzeroLocus (constMul q a s) = Out.nonzeroLocus s := by
  refine iSup_congr fun i => ?_
  have h : IsUnit (constFn q (L.U i) a) := (ha.map _).map _
  change X.basicOpen (constFn q _ a * s.f i) = _
  rw [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ h]
  exact inf_eq_right.2 (X.basicOpen_le _)

theorem isKeyPow_change : ∀ (K : Type) [Field K] (P : Out.PolAV (Sp K)) (hg rig hr th hth v hv th' hth' v' hv') (a : K) (M : Matrix (Fin P.g) (Fin P.g) K) (j : ℕ) (y : KeyIn K), (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) → (∀ i, IsLieComb (M i) v (v' i)) → GlobalTheory.KeyPow.IsKeyPow y ⟨P, hg, rig, hr, th, hth, v, hv⟩ j → ∃ (t : y.P.L.Sec) (ht : _) (w : _) (hw : _) (M' : Matrix (Fin y.P.g) (Fin y.P.g) K), GlobalTheory.KeyPow.IsKeyPow ⟨y.P, y.g_pos, y.rig, y.rig_gen, t, ht, w, hw⟩ ⟨P, hg, rig, hr, th', hth', v', hv'⟩ j ∧ (∀ i, t.f i = constFn y.P.A.hom _ (a ^ j) * y.th.f i) ∧ (∀ i, IsLieComb (M' i) y.v (w i)) ∧ M'.det = M.det ^ j := by
  intro K _ P hg rig hr th hth v hv th' hth' v' hv' a M j y ha hM ⟨p, hj, h₁, h₂, h₃⟩
  have h0 : a ≠ 0 := by
    rintro rfl
    obtain ⟨x, -, hx⟩ := hth' (default : PrimeSpectrum K)
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    rw [ha i, constFn, map_zero, map_zero, zero_mul, Scheme.basicOpen_zero] at hi
    exact hi
  haveI := y.P.isAb.comm
  haveI := P.isAb.comm
  obtain ⟨w, M', hw, hw', hM', hdet⟩ := exists_block_basis p.toIsPowGrp hj hv hv' M hM y.v h₃
  refine ⟨constMul y.P.A.hom (a ^ j) y.th, fun s => ?_, w, hw, M', ⟨p, hj, h₁, fun jj b h => ?_, hw'⟩,
    fun _ => rfl, hM', hdet⟩
  · rw [nonzeroLocus_constMul _ (pow_ne_zero j h0).isUnit]
    exact y.th_ne s
  · have h₄ := h₂ jj b h
    have h₅ : ∀ i, ((p.pr i).left.appLE _ _ (h i)).hom (th'.f (jj i)) =
        constFn y.P.A.hom _ a * ((p.pr i).left.appLE _ _ (h i)).hom (th.f (jj i)) := fun i => by
      rw [ha, map_mul, appLE_constFn _ _ _ (Over.w (p.pr i))]
    refine (Finset.prod_congr rfl fun i _ => h₅ i).trans ?_
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    refine (congrArg (_ * ·) h₄).trans ?_
    have h₆ : resG _ (inf_le_right : (Out.boxLB P.L p.pr).U jj ⊓ y.P.L.U b ≤ _)
        ((constMul y.P.A.hom (a ^ j) y.th).f b) =
        constFn y.P.A.hom _ a ^ j * resG _ inf_le_right (y.th.f b) := by
      rw [← constFn_pow, ← res_constFn y.P.A.hom (inf_le_right : (Out.boxLB P.L p.pr).U jj ⊓ y.P.L.U b ≤ _)]
      exact map_mul _ _ _
    exact (mul_left_comm _ _ _).trans (congrArg (_ * ·) h₆.symm)

end GlobalTheory.PowChange
end
end
