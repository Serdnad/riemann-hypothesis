module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle019
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle013
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open ReciprocityTheory.ChartRestriction.G.Chart (sp fstD scaleD prodPts isTan_iff isLieComb_iff comp_one' isTan_mul isTan_one
  isTan_scale)
open GlobalTheory.UnifDifferential GlobalTheory.SqZero

noncomputable section

namespace GlobalTheory.KaScale

section Lin

variable {K : Type} [Field K] {A : Over (Spec (CommRingCat.of K))}

theorem valT_comp {T : Type} [CommRing T] {X Y : Scheme.{0}} (w : Sp T ⟶ X) (φ : X ⟶ Y) (U : Y.Opens)
    (f : Γ(Y, U)) : valT (w ≫ φ) U f = valT w (φ ⁻¹ᵁ U) ((φ.app U).hom f) := by
  unfold valT
  by_cases h : ⊤ ≤ w ⁻¹ᵁ (φ ⁻¹ᵁ U)
  · rw [dif_pos h, dif_pos (show ⊤ ≤ (w ≫ φ) ⁻¹ᵁ U from h)]
    rfl
  · rw [dif_neg h, dif_neg (show ¬ ⊤ ≤ (w ≫ φ) ⁻¹ᵁ U from h)]

def der (v : sp (R₀ := K) (DualNumber K) ⟶ A) (U : A.left.Opens) (f : Γ(A.left, U)) : K :=
  TrivSqZeroExt.snd (valT (T := DualNumber K) v.left U f)

theorem der_pos (v : sp (R₀ := K) (DualNumber K) ⟶ A) (U : A.left.Opens) (f : Γ(A.left, U))
    (h : ⊤ ≤ v.left ⁻¹ᵁ U) : der v U f = (pullFn v U h f).snd := congrArg _ (dif_pos h)

theorem der_neg (v : sp (R₀ := K) (DualNumber K) ⟶ A) (U : A.left.Opens) (f : Γ(A.left, U))
    (h : ¬ ⊤ ≤ v.left ⁻¹ᵁ U) : der v U f = 0 := congrArg _ (dif_neg h)

theorem der_scale (v : sp (R₀ := K) (DualNumber K) ⟶ A) (c : K) (U : A.left.Opens) (f : Γ(A.left, U)) :
    der (Chart.spMap (scaleD c) ≫ v) U f = c * der v U f := by
  have : Subsingleton (PrimeSpectrum (DualNumber K)) := subsingleton_primeSpectrum K K
  by_cases h : ⊤ ≤ v.left ⁻¹ᵁ U
  · have h' := le_preimage_comp (scaleD c) v _ rfl U h
    rw [der_pos _ _ _ h, der_pos _ _ _ h', pullFn_comp (scaleD c) v _ rfl U h h' f, scaleD_eq]
    simp [epsTo, dualTo_apply, Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl, mul_comm]
  · rw [der_neg _ _ _ h, der_neg _ _ _ (fun h' => h (le_preimage_of_comp (scaleD c) v _ rfl U h')), mul_zero]

variable [GrpObj A]

theorem le_of_isTan {v v' : sp (R₀ := K) (DualNumber K) ⟶ A} (hv : Chart.IsTan v) (hv' : Chart.IsTan v')
    (U : A.left.Opens) (h : ⊤ ≤ v.left ⁻¹ᵁ U) : ⊤ ≤ v'.left ⁻¹ᵁ U := by
  have : Subsingleton (PrimeSpectrum (DualNumber K)) := subsingleton_primeSpectrum K K
  exact le_preimage_of_comp (fstD K) v' 1 hv'.symm U (le_preimage_comp (fstD K) v 1 hv.symm U h)

theorem der_mul {v v' : sp (R₀ := K) (DualNumber K) ⟶ A} (hv : Chart.IsTan v) (hv' : Chart.IsTan v')
    (U : A.left.Opens) (f : Γ(A.left, U)) : der (v * v') U f = der v U f + der v' U f := by
  by_cases h : ⊤ ≤ (v * v').left ⁻¹ᵁ U
  · obtain ⟨h₁, h₂, e⟩ := snd_pullFn_mul hv hv' U h
    rw [der_pos _ _ _ h, der_pos _ _ _ h₁, der_pos _ _ _ h₂, e]
  · rw [der_neg _ _ _ h, der_neg _ _ _ (fun h' => h (le_of_isTan hv (isTan_mul hv hv') U h')),
      der_neg _ _ _ (fun h' => h (le_of_isTan hv' (isTan_mul hv hv') U h')), add_zero]

theorem der_one (U : A.left.Opens) (f : Γ(A.left, U)) :
    der (1 : sp (R₀ := K) (DualNumber K) ⟶ A) U f = 0 := by
  rw [← comp_one' (Chart.spMap (scaleD (0 : K))), der_scale, zero_mul]

theorem der_prod (U : A.left.Opens) (f : Γ(A.left, U)) :
    ∀ {n : ℕ} (v : Fin n → (sp (R₀ := K) (DualNumber K) ⟶ A)), (∀ i, Chart.IsTan (v i)) →
      Chart.IsTan (List.ofFn v).prod ∧ der (List.ofFn v).prod U f = ∑ i, der (v i) U f := by
  intro n
  induction n with
  | zero =>
    intro v _
    rw [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty]
    exact ⟨isTan_one, der_one U f⟩
  | succ n ih =>
    intro v hv
    obtain ⟨h₁, h₂⟩ := ih (fun i => v i.succ) (fun i => hv i.succ)
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ, der_mul (hv 0) h₁, h₂]
    exact ⟨isTan_mul (hv 0) h₁, rfl⟩

theorem der_comb {n : ℕ} {c : Fin n → K} {v : Fin n → (epsR K ⟶ A)} {w : epsR K ⟶ A}
    (hv : ∀ i, IsTangent (v i)) (hw : IsLieComb c v w) (U : A.left.Opens) (f : Γ(A.left, U)) :
    der w U f = ∑ i, c i * der (v i) U f := by
  rw [(isLieComb_iff c v w).1 hw]
  refine (der_prod U f _ (fun i => isTan_scale (c i) ((isTan_iff _).2 (hv i)))).2.trans ?_
  exact Finset.sum_congr rfl fun i _ => der_scale _ _ _ _

theorem translate_left (z : 𝟙_ (Over (Sp K)) ⟶ A) (v : epsR K ⟶ A) :
    ((toUnit (epsR K) ≫ z) * v).left = v.left ≫ ((toUnit A ≫ z) * 𝟙 A).left := by
  rw [← Over.comp_left, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]

theorem snd_valT_comb {n : ℕ} {c : Fin n → K} {v : Fin n → (epsR K ⟶ A)} {w : epsR K ⟶ A}
    (hv : ∀ i, IsTangent (v i)) (hw : IsLieComb c v w) (z : 𝟙_ (Over (Sp K)) ⟶ A)
    (U : A.left.Opens) (f : Γ(A.left, U)) :
    TrivSqZeroExt.snd (valT (T := DualNumber K) ((toUnit (epsR K) ≫ z) * w).left U f) =
      ∑ i, c i * TrivSqZeroExt.snd (valT (T := DualNumber K) ((toUnit (epsR K) ≫ z) * v i).left U f) := by
  simp only [translate_left]
  exact (congrArg _ (valT_comp _ _ _ _)).trans ((der_comb hv hw _ _).trans
    (Finset.sum_congr rfl fun i _ => congrArg (fun t => c i * TrivSqZeroExt.snd t) (valT_comp _ _ _ _).symm))

end Lin

def cS {K : Type} [CommRing K] {Y : Scheme.{0}} (p : Y ⟶ Sp K) (y : Y) : K →+* Y.presheaf.stalk y :=
  (Y.presheaf.germ (p ⁻¹ᵁ ⊤) y trivial).hom.comp
    ((p.app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)

theorem gs_constFn' {K : Type} [CommRing K] {X Y : Scheme.{0}} (p : X ⟶ Sp K) (W : X.Opens) (r : Y ⟶ X)
    (y : Y) (hy : r y ∈ W) (a : K) : gs r y W (constFn p W a) = cS (r ≫ p) y a :=
  ((gs_res r y (fun _ _ => trivial : W ≤ p ⁻¹ᵁ ⊤) hy _).trans (gs_pull r p y ⊤ trivial _)).trans
    (gs_eq (r ≫ p) y ⊤ trivial _)

theorem gs_cst' {K : Type} [CommRing K] {Y : Scheme.{0}} (p : Y ⟶ Sp K) (y : Y) (a : K) :
    gs (𝟙 Y) y ⊤ (AbLaw.cst p ⊤ a) = cS p y a :=
  (gs_constFn' p ⊤ (𝟙 Y) y trivial a).trans (by rw [Category.id_comp])

variable {K : Type} [Field K] {P : Out.PolAV (Sp K)} {hg rig hr th hth v hv th' hth' v' hv'}

theorem isSquareDetComparison_scale_sec (a : Kˣ) (hth₀ : ∀ i, LB.Sec.f th' i = constFn P.A.hom _ (a : K) * LB.Sec.f th i)
    (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (b) (lam : Kˣ)
    (h : IsSquareDeterminantComparison ⟨P, hg, rig, hr, th, hth, v, hv⟩ m al b lam) :
    IsSquareDeterminantComparison ⟨P, hg, rig, hr, th', hth', v', hv'⟩ m al b (lam * a ^ (8 * m ^ (4 * P.g + 2))) := by
  obtain ⟨ξ, mu, w, Q, rho, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := h
  refine ⟨ξ, mu, w, (a : K) ^ 4 • Q, rho, h₁, h₂, h₃, h₄, h₅, fun I y J hJ => ?_, ?_⟩
  · have e := h₆ I y J hJ
    simp only [gs_cst'] at e ⊢
    have e₂ : ∀ r : Fin 4, gs (alMap ⟨P, hg, rig, hr, th', hth', v', hv'⟩ al r (ξ I r)).left y _
        (LB.Sec.f th' (J (alMap ⟨P, hg, rig, hr, th', hth', v', hv'⟩ al r (ξ I r)).left)) =
        cS (Out.powObj P.A 4).hom y a * gs (alMap ⟨P, hg, rig, hr, th, hth, v, hv⟩ al r (ξ I r)).left y _
        (LB.Sec.f th (J (alMap ⟨P, hg, rig, hr, th, hth, v, hv⟩ al r (ξ I r)).left)) := fun r => by
      rw [hth₀, gs_mul _ _ _ (hJ _), gs_constFn' _ _ _ _ (hJ _), Over.w]
      rfl
    refine (Finset.prod_congr rfl fun r _ => e₂ r).trans ?_
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    refine (congrArg _ e).trans ?_
    rw [mul_left_comm, Finset.mul_sum]
    refine congrArg _ (Finset.sum_congr rfl fun I' _ => ?_)
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, _root_.mul_assoc]
  · rw [Units.val_mul, h₇, Matrix.det_smul, Units.val_pow_eq_pow_val]
    simp only [Fintype.card_fun, Fintype.card_fin]
    ring

theorem jac_scale (M : Matrix (Fin P.g) (Fin P.g) K) (hM : ∀ i, IsLieComb (M i) v (v' i)) {n : ℕ}
    (s : Fin P.g → LB.Sec (pw P.L (n : ℤ))) (z) (c) :
    jac ⟨P, hg, rig, hr, th', hth', v', hv'⟩ s z c = jac ⟨P, hg, rig, hr, th, hth, v, hv⟩ s z c * M.det := by
  unfold jac
  rw [← Matrix.det_transpose M, ← Matrix.det_mul]
  congr 1
  ext i k
  rw [Matrix.mul_apply, Matrix.of_apply]
  refine (snd_valT_comb hv.1 (hM k) z _ _).trans (Finset.sum_congr rfl fun j _ => ?_)
  exact mul_comm _ _

theorem kaVal_scale : ∀ (K : Type) [Field K] (P : Out.PolAV (Sp K)) (hg rig hr th hth v hv th' hth' v' hv') (a : K) (M : Matrix (Fin P.g) (Fin P.g) K) (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (s : Fin P.g → LB.Sec (pw P.L (n : ℤ))) (κ : Kˣ), admitted P.g n l l' al → (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) → (∀ i, IsLieComb (M i) v (v' i)) → KaVal ⟨P, hg, rig, hr, th, hth, v, hv⟩ n l l' al s κ → ∃ κ' : Kˣ, KaVal ⟨P, hg, rig, hr, th', hth', v', hv'⟩ n l l' al s κ' ∧ a ^ (8 * kaExp P.g n l l') * (κ' : K) = M.det ^ (4 * kaExp P.g n l l') * κ := by
  intro K _ P hg rig hr th hth v hv th' hth' v' hv' a M n l l' al s κ hadm hth₀ hM hκ
  have ha : a ≠ 0 := by
    rintro rfl
    obtain ⟨y, -, hy⟩ := hth' (IsLocalRing.closedPoint K)
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    rw [hth₀, constFn, map_zero, map_zero, zero_mul, Scheme.basicOpen_zero] at hi
    exact hi
  have : IsCommMonObj P.A := P.isAb.comm
  have hdet : IsUnit M.det := ((LieComb.lieComb_algebra K P.A P.g v hv.1).2.2.2.2 M v' hv hM).1 hv'
  lift a to Kˣ using ha.isUnit
  obtain ⟨D, hD⟩ := hdet
  obtain ⟨z, ch, b, b', t, t', J, lam, lam', ⟨e₁, e₂, e₃, e₄, e₅⟩, hJ, hb, hb', ht, ht', rfl⟩ := hκ
  refine ⟨_, ⟨z, ch, b, b', t, t', J * D ^ (P.g.factorial * n ^ P.g),
    fun j => lam j * a ^ (8 * (l - j * n) ^ (4 * P.g + 2)),
    fun j => lam' j * a ^ (8 * (l' - j * n) ^ (4 * P.g + 2)), ⟨e₁, e₂, fun k => ?_, e₄, e₅⟩, ?_,
    fun j hj => ⟨(hb j hj).1, isSquareDetComparison_scale_sec a hth₀ _ _ _ _ (hb j hj).2⟩,
    fun j hj => ⟨(hb' j hj).1, isSquareDetComparison_scale_sec a hth₀ _ _ _ _ (hb' j hj).2⟩, ht, ht', rfl⟩, ?_⟩
  · rw [jac_scale (th := th) (hth := hth) (hv := hv) M hM, ← hD]
    exact (e₃ k).mul D.isUnit
  · rw [Units.val_mul, hJ, Units.val_pow_eq_pow_val, hD]
    simp only [jac_scale (th := th) (hth := hth) (hv := hv) (th' := th') (hth' := hth') (hv' := hv') M hM]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · have key := kaForm_homogeneous K P.g n l l' t t' J 1 a 1 lam lam' (fun _ => 1) (fun _ => 1)
      hadm.2.1 hadm.2.2.1
    simp only [one_zpow, one_pow, _root_.mul_one, Finset.prod_const_one] at key
    rw [← hD]
    norm_cast
    rw [← key]
    unfold kaForm kaExp
    generalize tComb P.g n l _ t _ = X
    generalize tComb P.g n l' _ t' _ = X'
    generalize degProd P.g n l l' ^ (3 * P.g + 2) = N
    generalize P.g.factorial * n ^ P.g = F
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_pow, ← natCast_zsmul]
    push_cast [Nat.cast_sub hadm.2.2.1.le]
    module

end GlobalTheory.KaScale
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory.KeyKa

section
variable {R : Type} [CommRing R] (x : KeyIn R) (al : Matrix (Fin 4) (Fin 4) ℤ) (r₀ : Fin 4)

def rowEmb : x.P.A ⟶ Out.powObj x.P.A 4 :=
  (Out.powIsLimit x.P.A 4).lift (Fan.mk x.P.A fun c => (𝟙 x.P.A) ^ al r₀ c)

theorem rowEmb_pr (c : Fin 4) : rowEmb x al r₀ ≫ Out.powPr x.P.A c = (𝟙 x.P.A) ^ al r₀ c :=
  (Out.powIsLimit x.P.A 4).fac (Fan.mk x.P.A fun c => (𝟙 x.P.A) ^ al r₀ c) ⟨c⟩

theorem rowEmb_alMap {m : ℕ} (hal : al * al.transpose = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (r : Fin 4)
    (ζ : Pt x) : rowEmb x al r₀ ≫ alMap x al r ζ =
      (if r = r₀ then (𝟙 x.P.A) ^ m else 1) * (toUnit x.P.A ≫ ζ) := by
  have := x.P.isAb.comm
  have h : al r₀ 0 * al r 0 + (al r₀ 1 * al r 1 + (al r₀ 2 * al r 2 + al r₀ 3 * al r 3)) =
      if r = r₀ then (m : ℤ) else 0 := by
    have := congrFun (congrFun hal r₀) r
    simp only [Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, mul_ite, _root_.mul_one, mul_zero, eq_comm (a := r₀)] at this
    rw [← this]; ring
  rw [alMap, MonObj.comp_mul, ← Category.assoc, comp_toUnit]
  congr 1
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, MonObj.comp_mul, GrpObj.comp_zpow,
    rowEmb_pr, _root_.mul_one, ← zpow_mul, ← zpow_add]
  refine (congrArg (fun n : ℤ => (𝟙 x.P.A) ^ n) h).trans ?_
  split_ifs
  · exact zpow_natCast _ _
  · exact zpow_zero _

theorem transl_rowEmb (δ : Pt x) : ((toUnit x.P.A ≫ δ) * 𝟙 x.P.A) ≫ rowEmb x al r₀ =
    rowEmb x al r₀ ≫ ((toUnit (Out.powObj x.P.A 4) ≫ δ ≫ rowEmb x al r₀) * 𝟙 (Out.powObj x.P.A 4)) := by
  have := x.P.isAb.comm
  refine (Out.powIsLimit x.P.A 4).hom_ext fun ⟨c⟩ => ?_
  change (_ ≫ _) ≫ Out.powPr x.P.A c = (_ ≫ _) ≫ Out.powPr x.P.A c
  rw [Category.assoc, Category.assoc, rowEmb_pr, MonObj.mul_comp _ _ (Out.powPr x.P.A c), MonObj.comp_mul, Category.id_comp, Category.assoc,
    Category.assoc, rowEmb_pr, ← Category.assoc (rowEmb x al r₀), comp_toUnit]
  simp only [GrpObj.comp_zpow, Category.comp_id, mul_zpow]

end

theorem eq_of_similitude_invariant : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (ξ ξ' : Fin 4 → Pt x) (w : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ))))) (w' : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ' r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ))))), (m : K) ≠ 0 → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → w.IsGen → w'.IsGen → (∀ v : 𝟙_ (Over (Sp K)) ⟶ Out.powObj x.P.A 4, (∀ r, v ≫ alMap x al r 1 = 1) → ∀ (Z : Scheme.{0}) (r : Z ⟶ (Out.powObj x.P.A 4).left) (z : Z) J, Good x.P.L z J → val w (r ≫ ((toUnit (Out.powObj x.P.A 4) ≫ v) * 𝟙 (Out.powObj x.P.A 4)).left) z J * val w' r z J = val w' (r ≫ ((toUnit (Out.powObj x.P.A 4) ≫ v) * 𝟙 (Out.powObj x.P.A 4)).left) z J * val w r z J) → ξ = ξ' := by
  intro laws K _ _ x m al ξ ξ' w w' hm hal hw hw' hinv
  have hL := x.P.isLB
  have hm0 : (m : ℤ) ≠ 0 := fun h => hm (by rw [Int.natCast_eq_zero.1 h, Nat.cast_zero])
  have hal' : al * al.transpose = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
    have hd : al.det ≠ 0 := fun h => by
      have := congrArg Matrix.det hal
      rw [Matrix.det_mul, h, mul_zero, Matrix.det_smul, Matrix.det_one, _root_.mul_one] at this
      exact pow_ne_zero _ hm0 this.symm
    have h1 : (al * al.transpose - (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) * al = 0 := by
      rw [sub_mul, _root_.mul_assoc, hal, Matrix.mul_smul, Matrix.smul_mul, _root_.mul_one,
        _root_.one_mul, sub_self]
    have h2 := congrArg (· * al.adjugate) h1
    simp only [_root_.mul_assoc, Matrix.mul_adjugate, zero_mul, Matrix.mul_smul, _root_.mul_one] at h2
    exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_left hd)
  funext r₀
  obtain ⟨g, hg⟩ := DVR.exists_gen_of_local (V := K) x.P.L hL (K := Fin 4 ⊕ Fin 4)
    (Sum.elim (fun r => (ξ r).left) (fun r => (ξ' r).left))
    (Sum.elim (fun r => if r = r₀ then 0 else -1) (fun r => if r = r₀ then 0 else 1))
  let i := rowEmb x al r₀
  have hu₀ := DVR.mulGen_isGen x.P.L _ _ _ _ _ _
    (DVR.mulGen_isGen x.P.L _ _ _ _ _ _ (DVR.pullGen_isGen x.P.L _ _ w hw i.left)
      (DVR.invGen_isGen x.P.L _ _ _ (DVR.pullGen_isGen x.P.L _ _ w' hw' i.left)))
    (DVR.pullGen_isGen x.P.L _ _ g hg (toUnit x.P.A).left)
  obtain ⟨u, hu, hval⟩ := exists_gen hL (K' := Fin 2)
    (φ' := ![((𝟙 x.P.A) ^ m * (toUnit x.P.A ≫ ξ r₀)).left, ((𝟙 x.P.A) ^ m * (toUnit x.P.A ≫ ξ' r₀)).left])
    (ε' := ![1, -1]) (by
      intro U _ h
      have e : ∀ (r : Fin 4) (ζ : Pt x), i.left ≫ (alMap x al r ζ).left =
          ((if r = r₀ then (𝟙 x.P.A) ^ m else 1) * (toUnit x.P.A ≫ ζ)).left := fun r ζ =>
        congrArg (fun q => q.left) (rowEmb_alMap x al r₀ hal' r ζ)
      have e' : ∀ ζ : Pt x, (toUnit x.P.A).left ≫ ζ.left = (toUnit x.P.A ≫ ζ).left := fun _ => rfl
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, e, Fin.prod_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, neg_neg]
      simp only [← Finset.prod_mul_distrib]
      rw [Finset.prod_eq_single r₀ (fun r _ hr => ?_) (fun hr => absurd (Finset.mem_univ _) hr)]
      · simp only [if_true, zpow_zero, _root_.mul_one, zpow_neg]
        rw [_root_.mul_mul_mul_comm, inv_mul_cancel, _root_.mul_one]
      · simp only [if_neg hr, _root_.one_mul, zpow_one, zpow_neg, e']
        rw [_root_.mul_mul_mul_comm, mul_inv_cancel_comm, inv_mul_cancel_comm, inv_mul_cancel]) _ hu₀
  refine GlobalTheory.eq_of_invariantGen_translates laws K x.P m (ξ r₀) (ξ' r₀) u hm hu fun δ hδ y J hJ => ?_
  have hv := hinv (δ ≫ i) (fun r => by
    rw [Category.assoc, rowEmb_alMap x al r₀ hal', MonObj.comp_one, _root_.mul_one]
    split_ifs
    · rw [MonObj.comp_pow, Category.comp_id, hδ]
    · exact MonObj.comp_one _) _ i.left y J hJ
  have e₁ : ((toUnit x.P.A ≫ δ) * 𝟙 x.P.A).left ≫ i.left =
      i.left ≫ ((toUnit (Out.powObj x.P.A 4) ≫ δ ≫ i) * 𝟙 (Out.powObj x.P.A 4)).left :=
    congrArg (fun q => q.left) (transl_rowEmb x al r₀ δ)
  have e₂ : ((toUnit x.P.A ≫ δ) * 𝟙 x.P.A).left ≫ (toUnit x.P.A).left = (toUnit x.P.A).left :=
    congrArg (fun q => q.left) (comp_toUnit ((toUnit x.P.A ≫ δ) * 𝟙 x.P.A))
  rw [hval _ _ y J hJ, hval _ _ y J hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv,
    val_pull hJ, val_pull hJ, val_pull hJ, val_pull hJ, val_pull hJ, val_pull hJ, e₁, Category.id_comp,
    Category.id_comp]
  erw [e₂]
  congr 1
  rw [mul_inv_eq_iff_eq_mul, mul_right_comm, eq_mul_inv_iff_mul_eq, hv, mul_comm]

end GlobalTheory.KeyKa

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.SimilTheta
open Matrix

variable {g : ℕ}

def lat (τ : Matrix (Fin g) (Fin g) ℂ) (k n : Fin g → ℤ) : Fin g → ℂ :=
  (fun i => (k i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))

def aut (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (k n : Fin g → ℤ) (z : Fin g → ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (a ⬝ᵥ (fun i => (k i : ℂ)) - b ⬝ᵥ (fun i => (n i : ℂ)) -
    ((fun i => (n i : ℂ)) ⬝ᵥ τ.mulVec (fun i => (n i : ℂ))) / 2 - (fun i => (n i : ℂ)) ⬝ᵥ z))

def tors (τ : Matrix (Fin g) (Fin g) ℂ) (al : Matrix (Fin 4) (Fin 4) ℤ) (m : ℕ) (k n : Fin 4 → Fin g → ℤ) (r : Fin 4) :
    Fin g → ℂ := (m : ℂ)⁻¹ • ∑ c, al r c • lat τ (k c) (n c)

def simTheta (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (al : Matrix (Fin 4) (Fin 4) ℤ) (m : ℕ)
    (k n : Fin 4 → Fin g → ℤ) (y : Fin 4 → Fin g → ℂ) : ℂ :=
  (∏ r, thetaChar τ a b (∑ c, al r c • y c + tors τ al m k n r)) *
    Complex.exp (2 * Real.pi * Complex.I * ∑ c, (fun i => (n c i : ℂ)) ⬝ᵥ y c)

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
variable {g : ℕ} in
theorem _root_.GlobalTheory.SimilTheta.aut_ne_zero (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (k n : Fin g → ℤ) (z : Fin g → ℂ) :
    _root_.GlobalTheory.SimilTheta.aut τ a b k n z ≠ 0 :=
  Complex.exp_ne_zero _

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
variable {g : ℕ} in
theorem _root_.GlobalTheory.SimilTheta.isLevel_iff_aut (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (l : ℕ) (F : (Fin g → ℂ) → ℂ) :
    _root_.GlobalTheory.KeyKa.IsLevel τ a b l F ↔ Differentiable ℂ F ∧ ∀ k n z, F (z + _root_.GlobalTheory.SimilTheta.lat τ k n) = _root_.GlobalTheory.SimilTheta.aut τ a b k n z ^ l * F z :=
  Iff.rfl

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
variable {g : ℕ} in
theorem _root_.GlobalTheory.SimilTheta.lat_add (τ : Matrix (Fin g) (Fin g) ℂ) (k n k' n' : Fin g → ℤ) :
    _root_.GlobalTheory.SimilTheta.lat τ (k + k') (n + n') = _root_.GlobalTheory.SimilTheta.lat τ k n + _root_.GlobalTheory.SimilTheta.lat τ k' n' := by
  have h : (fun i => ((n + n') i : ℂ)) = (fun i => (n i : ℂ)) + fun i => (n' i : ℂ) := by
    ext i; simp
  unfold _root_.GlobalTheory.SimilTheta.lat
  rw [h, Matrix.mulVec_add]
  ext i
  simp only [Pi.add_apply, Int.cast_add]
  ring

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
variable {g : ℕ} in
theorem _root_.GlobalTheory.SimilTheta.lat_zsmul (τ : Matrix (Fin g) (Fin g) ℂ) (s : ℤ) (k n : Fin g → ℤ) :
    _root_.GlobalTheory.SimilTheta.lat τ (s • k) (s • n) = s • _root_.GlobalTheory.SimilTheta.lat τ k n := by
  have h : (fun i => ((s • n) i : ℂ)) = (s : ℂ) • fun i => (n i : ℂ) := by
    ext i; simp
  unfold _root_.GlobalTheory.SimilTheta.lat
  rw [h, Matrix.mulVec_smul]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zsmul_eq_mul, Int.cast_mul]
  ring

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
variable {g : ℕ} in
private theorem lat_zero_zero (τ : Matrix (Fin g) (Fin g) ℂ) :
    _root_.GlobalTheory.SimilTheta.lat τ 0 0 = 0 := by
  have h : (fun i : Fin g => (((0 : Fin g → ℤ) i : ℤ) : ℂ)) = 0 := by
    ext i; simp
  unfold _root_.GlobalTheory.SimilTheta.lat
  rw [h, Matrix.mulVec_zero]
  ext i
  simp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
variable {g : ℕ} in
theorem _root_.GlobalTheory.SimilTheta.lat_sum (τ : Matrix (Fin g) (Fin g) ℂ) {K : Type} (s : Finset K) (k n : K → Fin g → ℤ) :
    _root_.GlobalTheory.SimilTheta.lat τ (∑ c ∈ s, k c) (∑ c ∈ s, n c) = ∑ c ∈ s, _root_.GlobalTheory.SimilTheta.lat τ (k c) (n c) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using lat_zero_zero τ
  | insert c s hc ih =>
    rw [Finset.sum_insert hc, Finset.sum_insert hc, Finset.sum_insert hc, _root_.GlobalTheory.SimilTheta.lat_add, ih]

end GlobalTheory.SimilTheta
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa


theorem _root_.GlobalTheory.T.pullbackSections_basis_affine_baseChange_of_affine : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (p : X ⟶ Sp R) (L : LB X) (t : ℤ) (N : ℕ) (b : Fin N → LB.Sec (pw L t)), (∀ (R' : Type) [CommRing R'] (f : R →+* R'), ∃ (Y : Scheme.{0}) (p₁ : Y ⟶ Sp R') (p₂ : Y ⟶ X), IsPullback p₂ p₁ p (spMap f) ∧ GlobalTheory.RelBasis.IndepOn b p₁ p₂ ⊤ ∧ GlobalTheory.RelBasis.SpanOn b p₁ p₂ ⊤) → ∀ (T Y : Scheme.{0}) (q : T ⟶ Sp R) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X), IsPullback p₂ p₁ p q → ∀ W : T.Opens, IsAffineOpen W → GlobalTheory.RelBasis.IndepOn b p₁ p₂ W ∧ GlobalTheory.RelBasis.SpanOn b p₁ p₂ W := by
  first | exact @GlobalTheory.RelBasis.indepOn_spanOn_of_affine | exact GlobalTheory.RelBasis.indepOn_spanOn_of_affine | (intros; apply GlobalTheory.RelBasis.indepOn_spanOn_of_affine <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa


theorem _root_.GlobalTheory.T.pullbackSections_basis_of_affine_opens : ∀ (X Y T : Scheme.{0}) (L : LB X) (t : ℤ) (N : ℕ) (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X), (∀ W : T.Opens, IsAffineOpen W → GlobalTheory.RelBasis.IndepOn b p₁ p₂ W ∧ GlobalTheory.RelBasis.SpanOn b p₁ p₂ W) → ∀ W : T.Opens, GlobalTheory.RelBasis.IndepOn b p₁ p₂ W ∧ GlobalTheory.RelBasis.SpanOn b p₁ p₂ W := by
  first | exact @GlobalTheory.RelBasis.basis_of_affine | exact GlobalTheory.RelBasis.basis_of_affine | (intros; apply GlobalTheory.RelBasis.basis_of_affine <;> assumption)
end
