module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.GeneratorPullback.PullAlong
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents

@[expose] public section

section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.QkShift

section Alg

variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ)
include h

theorem cubN_one_mul (k : ℕ) (b m x : A) :
    cubN θ k 1 (b * m) x * θ m b x ^ k = θ (m ^ k) (b ^ k) x * cubN θ k 1 b x * cubN θ k 1 m x := by
  induction k with
  | zero => simp [cubN, h.face]
  | succ k ih =>
    have c₁ := h.coc (b ^ k * m ^ k) m b x
    have c₂ := h.coc (b ^ k) (m ^ k) m x
    have c₃ := h.coc (m ^ k * m) (b ^ k) b x
    rw [mul_comm m b] at c₁
    rw [h.s01 (b ^ k) (m ^ k), h.s01 (b ^ k) (m ^ k * m)] at c₂
    rw [mul_comm (m ^ k * m) (b ^ k), ← _root_.mul_assoc] at c₃
    simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
    rw [mul_pow b m k, pow_succ m, pow_succ b, pow_succ (θ m b x)]
    apply Additive.ofMul.injective
    have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
    have a₀ := E ih; have a₁ := E c₁; have a₂ := E c₂; have a₃ := E c₃
    simp only [ofMul_mul] at a₀ a₁ a₂ a₃ ⊢
    linear_combination (norm := abel) a₀ - a₁ + a₂ + a₃

theorem cub_shift (k : ℕ) (a m b x : A) (Sa Sm Sam Sq τ P w : U) (h₁ : Sam * cubN θ k a m b = Sa * Sm ^ k)
    (h₂ : Sq * θ a b m = Sa * τ) :
    cubN θ k a m (x * b) * (θ a (x * b) m)⁻¹ * (τ * P) *
        (cubN θ k (a * m ^ k) b x * (θ (a * m ^ k) x b)⁻¹ * (Sam * w)) =
      cubN θ k a (b * m) x * (θ a x (b * m))⁻¹ * (Sq * (w * P * Sm ^ k)) := by
  have e₁ := h.N_add k a m x b
  have e₂ := cubN_one_mul h k b m x
  have e₃ := h.N_split k (a * m ^ k) b x
  have e₄ := h.N_split k a (b * m) x
  have e₅ := h.N_split k a m x
  have e₆ := h.coc a (m ^ k) (b ^ k) x
  have e₇ := h.coc x b m a
  rw [h.s12 m x b] at e₁
  rw [← mul_pow, mul_comm m b] at e₆
  rw [h.s12 (x * b), h.s01 (x * b), h.s12 x b a, h.s01 x a b, h.s12 x (b * m), h.s01 x a, h.s12 b m a,
    h.s01 b a m] at e₇
  apply Additive.ofMul.injective
  have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
  have a₁ := E e₁; have a₂ := E e₂; have a₃ := E e₃; have a₄ := E e₄; have a₅ := E e₅; have a₆ := E e₆
  have a₇ := E e₇; have c₁ := E h₁; have c₂ := E h₂
  simp only [ofMul_mul, ofMul_inv] at *
  linear_combination (norm := abel) a₁ - a₂ + a₃ - a₄ + a₅ + a₆ - a₇ + c₁ - c₂

end Alg

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem trPt_comp (m m' : TF (R := R) F ⟶ D.P.A) :
    DegPre.trPt D F m ≫ DegPre.trPt D F m' = DegPre.trPt D F (m * m') := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, tr_fst, tr_fst, tr_fst]
  · refine Eq.trans ?_ (tr_pr D F (m * m')).symm
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (tr_pr D F m')).trans ?_)
    rw [MonObj.comp_mul, tr_pr, ← Category.assoc, tr_fst, MonObj.comp_mul, _root_.mul_assoc]

theorem exists_shift_gen (n : ℕ) (g : GtPtF D F) (z : D.X) (b' : TF (R := R) F ⟶ D.P.A)
    (hb : b' = g.b * cP D _ z)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε n))) (hw : w.IsGen) :
    ∃ w₂ : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F b') (DegPre.lineε n)), w₂.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (y : Z) (J), Good D.P.L y J →
        val w₂ r y J = val w r y J *
          (val (GeneratorPullback.powGen D.P.L _ _ (D.psi z) n) (r ≫ jFK (R := R) F) y J *
            val (GeneratorPullback.powGen D.P.L _ _ D.rigK n) (r ≫ jFK (R := R) F) y J) * val (g.s z) r y J ^ n := by
  subst hb
  obtain ⟨w₂, h₂, v₂⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F (g.b * cP D _ z)) (ε' := DegPre.lineε n)
    (fun U _ h => by
      have a₁ : ∀ χ, jFK (R := R) F ≫ D.xK χ = (cP D (TF (R := R) F) χ).left := fun χ => (Category.assoc _ _ _).symm
      have a₂ : jFK (R := R) F ≫ (toUnit (TK R)).left ≫ eSec D.P.A = (1 : TF (R := R) F ⟶ D.P.A).left :=
        (Category.assoc _ _ _).symm
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, a₁, a₂]
      rw [Fin.prod_univ_four, Fin.prod_univ_two, Fin.prod_univ_two]
      show h (1 : TF (R := R) F ⟶ D.P.A).left ^ (n : ℤ) * h g.b.left ^ (-(n : ℤ)) * _ *
        (h (cP D _ z * g.b).left ^ ((n : ℤ) * -1) * h (cP D _ z).left ^ ((n : ℤ) * 1) * h g.b.left ^ ((n : ℤ) * 1) *
          h (1 : TF (R := R) F ⟶ D.P.A).left ^ ((n : ℤ) * -1)) =
        h (1 : TF (R := R) F ⟶ D.P.A).left ^ (n : ℤ) * h (g.b * cP D _ z).left ^ (-(n : ℤ))
      rw [mul_comm g.b]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ w (LB.pullGen D.P.L _ _
      (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ (D.psi z) n) (GeneratorPullback.powGen D.P.L _ _ D.rigK n)) (jFK (R := R) F)))
      (GeneratorPullback.powGen D.P.L _ _ (g.s z) n))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hw (pullGen_isGen _ _ _ _
      (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ (D.psi_gen z) n)
        (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.rig_gen _) n)) _)) (powGen_isGen _ _ _ _ (g.isGen z) n))
  refine ⟨w₂, h₂, fun Z r y J hJ => (v₂ Z r y J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans (val_mul hJ _ _ _)))) ?_))⟩
  exact map_pow _ _ _

theorem qk_shift : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℕ), 1 ≤ n → ∀ (p q : QkPt D F n) (z : D.X) (h : GtPtF D F), q.y = p.y + n • z → GtPtF.IsIota z h → GtPtF.IsAdd p.g h q.g → ∀ w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε n)), w.IsGen → ∃ w₂ : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F q.g.b) (DegPre.lineε n)), w₂.IsGen ∧ ∀ s s' : Fam D F n, PhiRel D F n p w s s' → PhiRel D F n q w₂ s s' := by
  intro hG R _ _ D _ F _ _ n _ p q z h hy hι hadd w hw
  have hh : h.b = cP D _ z := hι.1
  have hb : q.g.b = p.g.b * cP D _ z := hadd.1.trans (congrArg (p.g.b * ·) hh)
  obtain ⟨w₂, h₂, v₂⟩ := exists_shift_gen n p.g z q.g.b hb w hw
  refine ⟨w₂, h₂, fun s t H => ?_⟩
  rw [phiRel_iff hG p w hw] at H
  rw [phiRel_iff hG q w₂ h₂]
  intro α β hβ T ρ y J hJ
  have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
  have e₁ := H (α + n • z) β (by rw [← hβ, hy]; abel) T ρ y J hJ
  obtain ⟨⟨u', hu', hc'⟩, hv'⟩ := gen_fe (D := D) (F := F) hG n z α
  have e₄ := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u').1 (s.fe z α u' hu' hc') _
    (ρ ≫ DegPre.trPt D F p.g.b).left y J hJ
  rw [hv' u' hu' hc' _ (ρ ≫ DegPre.trPt D F p.g.b) y J hJ, trF_eq, ← Over.comp_left, Category.assoc, trPt_comp, ← hb,
    Category.assoc, tr_fst] at e₄
  rw [e₁, e₄, _root_.mul_assoc, ← Units.val_mul]
  congr 2
  have t₁ := gt_nsmul (ρ ≫ fst (TF (R := R) F) D.P.A) hJ p.g α z n
  have t₂ := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl
    (val_cub D.cub (ρ ≫ fst (TF (R := R) F) D.P.A) hJ _ _ _))).symm.trans
    ((val_corr hJ (hadd.2 α) (ρ ≫ fst (TF (R := R) F) D.P.A).left).trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl ((val_corr hJ (hι.2 α) _).trans (val_pull hJ _ _ _)))))
  have c₁ : (ρ ≫ fst (TF (R := R) F) D.P.A) ≫ DegPre.cF D F α = cP D T α := comp_cP D _ α
  have c₂ : (ρ ≫ fst (TF (R := R) F) D.P.A) ≫ cP D _ z = cP D T z := comp_cP D _ z
  rw [hh, c₁, c₂] at t₂
  have key := cub_shift C n _ _ _ (ρ ≫ DegPre.prB D F) _ _ _ _ _
    (val (GeneratorPullback.powGen D.P.L _ _ (D.psi z) n) ((ρ ≫ fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F) y J *
      val (GeneratorPullback.powGen D.P.L _ _ D.rigK n) ((ρ ≫ fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F) y J)
    (val w (ρ ≫ fst (TF (R := R) F) D.P.A).left y J) t₁ t₂
  have d₁ : (ρ ≫ DegPre.trPt D F p.g.b) ≫ fst _ _ ≫ cP D _ z = cP D T z := by
    rw [← Category.assoc]; exact comp_cP D _ z
  have d₂ : (ρ ≫ DegPre.trPt D F p.g.b) ≫ DegPre.prB D F =
      (ρ ≫ DegPre.prB D F) * ((ρ ≫ fst (TF (R := R) F) D.P.A) ≫ p.g.b) := by
    rw [Category.assoc, tr_pr, MonObj.comp_mul, Category.assoc]
  have d₃ : ρ ≫ fst _ _ ≫ q.g.b = ((ρ ≫ fst (TF (R := R) F) D.P.A) ≫ p.g.b) * cP D T z := by
    rw [← Category.assoc, hb, MonObj.comp_mul, c₂]
  rw [val_famMult _ hJ, val_mul hJ, val_mul hJ, v₂ _ _ y J hJ, uVal, uVal, uVal, d₁, d₂, d₃, cPoint_add, cPoint_nsmul,
    ← Category.assoc ρ]
  exact key

end GlobalTheory.QkShift
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BoxCubical

open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (gU unit_ext gU_res gU_pullU gU_pullU_res)

section Box

variable {X X' Y Z : Scheme.{0}} (L : LB X) {J K K' : Type} [Fintype J] [Fintype K] [Fintype K']

lemma gU_boxGen (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε))
    (jj : K → (LB.LinComb L F (fun _ => 1)).ι) (y : Y)
    (hy : y ∈ LB.wchart (LB.LinComb L F (fun _ => 1)) φ jj) :
    gU y hy ((GeneratorPullback.boxGen L F φ ε t).s jj) =
      ∏ i, gU y (GeneratorPullback.box_le L F φ jj i hy) ((t i).s (fun k _ => jj k i)) := by
  show gU y hy (∏ i, _) = _
  exact (map_prod (gU y hy) _ _).trans (Finset.prod_congr rfl fun i _ => gU_res _ _ _ _)

lemma gU_pullGen (M : LB X') (φ : K → (Y ⟶ X')) (ε : K → ℤ) (t : LB.Gen (LB.LinComb M φ ε))
    (a : Z ⟶ Y) (j : K → M.ι) (z : Z) (hz : z ∈ LB.wchart M (fun k => a ≫ φ k) j) :
    gU z hz ((LB.pullGen M φ ε t a).s j) =
      Units.map (RingHom.toMonoidHom (a.stalkMap z).hom)
        (gU (a.base z) (LBxP.wpl M φ a j hz) (t.s j)) :=
  (gU_res _ _ _ _).trans (gU_pullU a _ z _ _)

lemma pullGen_boxGen (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε)) (a : Z ⟶ Y) :
    LB.pullGen (LB.LinComb L F (fun _ => 1)) φ ε (GeneratorPullback.boxGen L F φ ε t) a =
      GeneratorPullback.boxGen L F (fun k => a ≫ φ k) ε (fun i => LB.pullGen (L.pull (F i)) φ ε (t i) a) := by
  apply LBxP.gen_ext
  intro jj z hz
  refine (gU_pullGen _ φ ε _ a jj z hz).trans ?_
  refine Eq.trans ?_ (gU_boxGen L F (fun k => a ≫ φ k) ε _ jj z hz).symm
  refine (congrArg (Units.map (RingHom.toMonoidHom (a.stalkMap z).hom))
    (gU_boxGen L F φ ε t jj (a.base z) _)).trans ?_
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ => ?_)
  exact (gU_pullGen (L.pull (F i)) φ ε (t i) a _ z _).symm

lemma mulGen_boxGen (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (φ' : K' → (Y ⟶ X')) (ε' : K' → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε))
    (t' : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ' ε')) :
    LB.mulGen (LB.LinComb L F (fun _ => 1)) φ ε φ' ε' (GeneratorPullback.boxGen L F φ ε t)
        (GeneratorPullback.boxGen L F φ' ε' t') =
      GeneratorPullback.boxGen L F (Sum.elim φ φ') (Sum.elim ε ε')
        (fun i => LB.mulGen (L.pull (F i)) φ ε φ' ε' (t i) (t' i)) := by
  apply LBxP.gen_ext
  intro jj y hy
  refine (LBxP.gU_mulGen _ φ ε φ' ε' _ _ jj y hy).trans ?_
  refine Eq.trans ?_ (gU_boxGen L F (Sum.elim φ φ') (Sum.elim ε ε') _ jj y hy).symm
  refine (congrArg₂ (· * ·) (gU_boxGen L F φ ε t _ y _) (gU_boxGen L F φ' ε' t' _ y _)).trans ?_
  refine Finset.prod_mul_distrib.symm.trans (Finset.prod_congr rfl fun i _ => ?_)
  exact (LBxP.gU_mulGen (L.pull (F i)) φ ε φ' ε' (t i) (t' i) (fun k _ => jj k i) y _).symm

lemma oneGen_boxGen (F : J → (X' ⟶ X)) :
    LB.oneGen (Y := Y) (LB.LinComb L F (fun _ => 1)) =
      GeneratorPullback.boxGen L F PEmpty.elim PEmpty.elim (fun i => LB.oneGen (L.pull (F i))) := by
  apply LBxP.gen_ext
  intro jj y hy
  refine Eq.trans ?_ (gU_boxGen L F PEmpty.elim PEmpty.elim _ jj y hy).symm
  refine (map_one (gU y hy)).trans (Finset.prod_eq_one fun i _ => ?_).symm
  exact map_one (gU y _)

lemma corr_boxGen (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (φ' : K' → (Y ⟶ X')) (ε' : K' → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε))
    (t' : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ' ε'))
    (h : ∀ i, LB.Gen.Corr (L.pull (F i)) φ ε φ' ε' (t i) (t' i)) :
    LB.Gen.Corr (LB.LinComb L F (fun _ => 1)) φ ε φ' ε' (GeneratorPullback.boxGen L F φ ε t)
      (GeneratorPullback.boxGen L F φ' ε' t') := by
  intro jj jj' h1 h2 h12
  apply unit_ext
  intro y hy
  refine ((gU_res _ y hy _).trans (gU_boxGen L F φ ε t jj y hy.1)).trans ?_
  refine Eq.trans ?_ ((gU_res _ y hy _).trans (gU_boxGen L F φ' ε' t' jj' y hy.2)).symm
  refine Finset.prod_congr rfl fun i _ => ?_
  have H := h i (fun k _ => jj k i) (fun k _ => jj' k i)
    (fun k₁ k₂ e => funext fun _ => congrFun (h1 k₁ k₂ e) i)
    (fun k₁ k₂ e => funext fun _ => congrFun (h2 k₁ k₂ e) i)
    (fun k₁ k₂ e => funext fun _ => congrFun (h12 k₁ k₂ e) i)
  have hy' : y ∈ LB.wchart (L.pull (F i)) φ (fun k _ => jj k i) ⊓
      LB.wchart (L.pull (F i)) φ' (fun k _ => jj' k i) :=
    ⟨GeneratorPullback.box_le L F φ jj i hy.1, GeneratorPullback.box_le L F φ' jj' i hy.2⟩
  exact (gU_res _ y hy' _).symm.trans ((congrArg (gU y hy') H).trans (gU_res _ y hy' _))

lemma gU_pull_lcg (F : J → (X' ⟶ X)) (δ : J → ℤ) (a : Y ⟶ X') (i j : J → L.ι) (y : Y)
    (hy : y ∈ a ⁻¹ᵁ ((LB.LinComb L F δ).U i ⊓ (LB.LinComb L F δ).U j)) :
    gU y hy (pullU a _ ((LB.LinComb L F δ).g i j)) =
      ∏ n, (gU y (show y ∈ (a ≫ F n) ⁻¹ᵁ (L.U (i n) ⊓ L.U (j n)) from
        ⟨LB.wchart_le L F i n hy.1, LB.wchart_le L F j n hy.2⟩)
        (pullU (a ≫ F n) _ (L.g (i n) (j n)))) ^ δ n := by
  refine (gU_pullU a _ y hy _).trans ?_
  refine (congrArg (Units.map (RingHom.toMonoidHom (a.stalkMap y).hom))
    (LBxP.gU_lcg L F δ i j (a.base y) hy)).trans ?_
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun n _ => ?_)
  refine (map_zpow _ _ _).trans (congrArg (· ^ δ n) ?_)
  refine (gU_pullU a _ y _ _).symm.trans ?_
  exact LBxP.gU_pullU_comp a (F n) _ _ y _ _

lemma isGen_boxGen (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε)) (h : ∀ i, (t i).IsGen) :
    (GeneratorPullback.boxGen L F φ ε t).IsGen := by
  intro jj jj'
  apply unit_ext
  intro y hy
  have hy' : ∀ i, y ∈ (LB.LinComb (L.pull (F i)) φ ε).U (fun k _ => jj k i) ⊓
      (LB.LinComb (L.pull (F i)) φ ε).U (fun k _ => jj' k i) := fun i =>
    ⟨GeneratorPullback.box_le L F φ jj i hy.1, GeneratorPullback.box_le L F φ jj' i hy.2⟩
  have hg : gU y hy ((LB.LinComb (LB.LinComb L F (fun _ => 1)) φ ε).g jj jj') =
      ∏ i, gU y (hy' i) ((LB.LinComb (L.pull (F i)) φ ε).g (fun k _ => jj k i)
        (fun k _ => jj' k i)) := by
    refine (LBxP.gU_lcg _ φ ε jj jj' y hy).trans ?_
    refine Eq.trans ?_ (Finset.prod_congr rfl fun i _ =>
      LBxP.gU_lcg (L.pull (F i)) φ ε _ _ y (hy' i)).symm
    refine Eq.trans ?_ Finset.prod_comm
    refine Finset.prod_congr rfl fun k _ => ?_
    refine Eq.trans ?_ (Finset.prod_zpow _ _ _).symm
    refine congrArg (· ^ ε k) ?_
    refine (gU_pull_lcg L F (fun _ => 1) (φ k) (jj k) (jj' k) y _).trans ?_
    refine Finset.prod_congr rfl fun i _ => ?_
    refine (zpow_one _).trans ?_
    exact (LBxP.gU_pull_g L (F i) (φ k) (fun _ => jj k i) (fun _ => jj' k i) y _ _).symm
  refine ((gU_res _ y hy _).trans (gU_boxGen L F φ ε t jj y hy.1)).trans ?_
  refine Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) hg
    ((gU_res _ y hy _).trans (gU_boxGen L F φ ε t jj' y hy.2)))).symm
  refine Eq.trans ?_ Finset.prod_mul_distrib
  refine Finset.prod_congr rfl fun i _ => ?_
  have H := congrArg (gU y (hy' i)) (h i (fun k _ => jj k i) (fun k _ => jj' k i))
  exact (gU_res _ y (hy' i) _).symm.trans (H.trans ((map_mul _ _ _).trans
    (congrArg (_ * ·) (gU_res _ y (hy' i) _))))

end Box

section Cub

variable {S : Scheme.{0}} {G' : Over S} [GrpObj G'] [IsCommMonObj G'] {X : Scheme.{0}}
  {J : Type} [Fintype J]

def prodCubical (L : LB X) (F : J → (G'.left ⟶ X))
    (r : ∀ i, LB.Gen ((L.pull (F i)).pull (eSec G'))) (hL : ∀ i, (L.pull (F i)).IsLB)
    (hr : ∀ i, (r i).IsGen) (c : ∀ i, CubicalStr G' ⟨L.pull (F i), r i, hL i, hr i⟩)
    (r' : LB.Gen ((LB.LinComb L F (fun _ => 1)).pull (eSec G')))
    (hL' : (LB.LinComb L F (fun _ => 1)).IsLB) (hr' : r'.IsGen) :
    CubicalStr G' ⟨LB.LinComb L F (fun _ => 1), r', hL', hr'⟩ where
  t := GeneratorPullback.boxGen L F (thφ G' (x3 G')) thε (fun i => (c i).t)
  isGen := isGen_boxGen L F (thφ G' (x3 G')) thε (fun i => (c i).t) (fun i => (c i).isGen)
  face := fun n =>
    LBxP.corr_of_eq (pullGen_boxGen L F (thφ G' (x3 G')) thε (fun i => (c i).t) _)
      (oneGen_boxGen L F) (corr_boxGen L F _ _ _ _ _ _ (fun i => (c i).face n))
  cubeSymmetric_swap_first :=
    LBxP.corr_of_eq rfl (pullGen_boxGen L F (thφ G' (x3 G')) thε (fun i => (c i).t) _)
      (corr_boxGen L F (thφ G' (x3 G')) thε _ _ (fun i => (c i).t) _ (fun i => (c i).cubeSymmetric_swap_first))
  cubeSymmetric_swap_last :=
    LBxP.corr_of_eq rfl (pullGen_boxGen L F (thφ G' (x3 G')) thε (fun i => (c i).t) _)
      (corr_boxGen L F (thφ G' (x3 G')) thε _ _ (fun i => (c i).t) _ (fun i => (c i).cubeSymmetric_swap_last))
  cocycle :=
    LBxP.corr_of_eq
      ((congrArg₂ (LB.mulGen (LB.LinComb L F (fun _ => 1)) _ _ _ _)
        (pullGen_boxGen L F (thφ G' (x3 G')) thε (fun i => (c i).t) _)
        (pullGen_boxGen L F (thφ G' (x3 G')) thε (fun i => (c i).t) _)).trans
        (mulGen_boxGen L F _ _ _ _ _ _))
      ((congrArg₂ (LB.mulGen (LB.LinComb L F (fun _ => 1)) _ _ _ _)
        (pullGen_boxGen L F (thφ G' (x3 G')) thε (fun i => (c i).t) _)
        (pullGen_boxGen L F (thφ G' (x3 G')) thε (fun i => (c i).t) _)).trans
        (mulGen_boxGen L F _ _ _ _ _ _))
      (corr_boxGen L F _ _ _ _ _ _ (fun i => (c i).cocycle))

end Cub

end GlobalTheory.BoxCubical

namespace GlobalTheory

theorem boxCubical : ∀ S : Scheme.{0}, BoxCubicalSt (S := S) := by
  intro S G' G _ _ _ _ j p L c hL hr
  let m : Fin j → CubeMap G' G := fun i => letI := p.hom i; CubeMap.ofHom (p.pr i)
  have hLi : ∀ i, (L.L.pull (m i).F).IsLB := fun i => LB.isLB_pull L.isLB (m i).F
  have hri : ∀ i, ((m i).rigPull L.L L.rig).IsGen := fun i =>
    LBxP.isGen_pullAlong L.L (m i).F (m i).e (fun _ : PUnit => eSec G) (fun _ => 1)
      (fun _ => eSec G') (fun _ => (m i).e_comm) L.rig L.rigGen
  exact ⟨BoxCubical.prodCubical L.L (fun i => (p.pr i).left) (fun i => (m i).rigPull L.L L.rig)
    hLi hri (fun i => CubePf.cubical (m i) L c (hLi i) (hri i)) _ hL hr, rfl⟩

end GlobalTheory
end
end
