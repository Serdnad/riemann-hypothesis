module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MulLeftCompOfPullbackPointEquivMul
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsPullbackCompIsoMonHom
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory

theorem splitTorus_hom_pullback_local_trivial {S : Scheme.{0}} (A : CommRingCat.{0}) [IsLocalRing A]
    [IsNoetherianRing A] (p : Spec A ⟶ S) (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (B : Over S) [GrpObj B] [IsProper B.hom] (f : splitTorus S X ⟶ B)
    (hf : IsMonHom f) :
    (Over.pullback p).map f = (Over.pullback p).map (toUnit _ ≫ η[B]) := by
  obtain ⟨A⟩ := A
  refine TorusLocal.pullback_map_eq_one p X B f hf fun g hg ↦ ?_
  have : IsProper ((Over.pullback p).obj B).hom := inferInstanceAs (IsProper (pullback.snd _ _))
  exact splitTorus_hom_proper_trivial_local A X _ g hg

theorem splitTorus_hom_abelian_eq_one : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over S) [GrpObj B], IsAbelianScheme B → ∀ f : splitTorus S X ⟶ B, IsMonHom f → f = 1 := by
  intro S _ X _ _ _ B _ hB f hf
  have := hB.proper
  refine Over.OverMorphism.ext (hom_ext_of_fromSpecStalk fun t ↦ ?_)
  let p := S.fromSpecStalk ((splitTorus S X).hom t)
  have h : (Over.pullback p).map f = (Over.pullback p).map (toUnit _ ≫ η[B]) :=
    splitTorus_hom_pullback_local_trivial _ p X B f hf
  have h₁ : ∀ u : splitTorus S X ⟶ B, ((Over.pullback p).map u).left ≫ pullback.fst B.hom p =
      pullback.fst (splitTorus S X).hom p ≫ u.left := fun u ↦ pullback.lift_fst _ _ _
  have h₂ : pullback.fst (splitTorus S X).hom p ≫ f.left =
      pullback.fst (splitTorus S X).hom p ≫ (1 : splitTorus S X ⟶ B).left := by
    rw [← h₁, ← h₁, h, Hom.one_def]
  have h₃ : pullback.lift ((splitTorus S X).left.fromSpecStalk t)
      (Spec.map ((splitTorus S X).hom.stalkMap t)) (Scheme.SpecMap_stalkMap_fromSpecStalk _).symm ≫
      pullback.fst (splitTorus S X).hom p = (splitTorus S X).left.fromSpecStalk t :=
    pullback.lift_fst _ _ _
  rw [← h₃, Category.assoc, Category.assoc, h₂]

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TauBalAdd

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {Lr : RigLB A} (c : CubicalStr A Lr)

theorem val₂_one (f g : A ⟶ A) (u : LB.Gen (LB.LinComb Lr.L (rosatiφ A f g) rosatiε))
    (h₀ : LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (zero2 A)) (LB.oneGen Lr.L))
    {y : (𝟙_ (Over S)).left} {J} (hJ : Good Lr.L y J) : val₂ u y J (1 : 𝟙_ (Over S) ⟶ A) 1 = 1 := by
  have e : lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A) = lift η[A] η[A] := by simp [Hom.one_def]
  have := val_corr hJ h₀ (𝟙 _)
  rw [val_pull hJ, Category.id_comp, val_one] at this
  rw [val₂, e]; exact this

omit [IsCommMonObj A] in
theorem val_pull₂ (f g : A ⟶ A) (u : LB.Gen (LB.LinComb Lr.L (rosatiφ A f g) rosatiε)) {T T' : Over S} (ρ : T' ⟶ T)
    {z : T'.left} {J} (hJ : Good Lr.L z J) (a b : T ⟶ A) :
    val (LB.pullGen Lr.L _ _ u (lift a b).left) ρ.left z J = val₂ u z J (ρ ≫ a) (ρ ≫ b) := by
  rw [val_pull hJ, ← Over.comp_left, comp_lift]; rfl

theorem ros_sum (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (f g f' g' : A ⟶ A) [IsMonHom f] [IsMonHom g]
    (u : LB.Gen (LB.LinComb Lr.L (rosatiφ A f g) rosatiε)) (hu : u.IsGen)
    (h₀ : LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (zero2 A)) (LB.oneGen Lr.L))
    (u' : LB.Gen (LB.LinComb Lr.L (rosatiφ A f' g') rosatiε)) (hu' : u'.IsGen)
    (h₀' : LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u' (zero2 A)) (LB.oneGen Lr.L))
    (w : LB.Gen (LB.LinComb Lr.L (rosatiφ A (f * f') (g * g')) rosatiε)) (hw : w.IsGen)
    (w₀ : LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ w (zero2 A)) (LB.oneGen Lr.L))
    {T : Over S} {z : T.left} {J} (hJ : Good Lr.L z J) (x y : T ⟶ A) :
    val₂ w z J x y * cubV c z J x (y ≫ g) (y ≫ g') =
      cubV c z J (x ≫ f) (x ≫ f') y * (val₂ u z J x y * val₂ u' z J x y) := by
  let p : A ⊗ A ⟶ A := fst A A
  let q : A ⊗ A ⟶ A := snd A A
  let e : 𝟙_ (Over S) ⟶ A ⊗ A := lift 1 1
  have e₀ : e ≫ p = 1 := lift_fst _ _
  have e₁ : e ≫ q = 1 := lift_snd _ _
  have sj : Function.Surjective ((snd A A).left ≫ A.hom).appTop.hom :=
    surj_comp (surj_snd hG hA _) (hG _ _ hA).2
  have he : e.left ≫ (snd A A).left ≫ A.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w e
  have ev : ∀ {T' : Over S} (σ : T' ⟶ A ⊗ A) {z : T'.left} {J}, Good Lr.L z J →
      val (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ w (lift p q).left)
        (LB.pullGen Lr.L (thφ A (x3 A)) thε c.t (lift p (lift (q ≫ g) (q ≫ g'))).left)) σ.left z J =
        val₂ w z J (σ ≫ p) (σ ≫ q) * cubV c z J (σ ≫ p) (σ ≫ q ≫ g) (σ ≫ q ≫ g') ∧
      val (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L (thφ A (x3 A)) thε c.t (lift (p ≫ f) (lift (p ≫ f') q)).left)
        (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (lift p q).left) (LB.pullGen Lr.L _ _ u' (lift p q).left)))
        σ.left z J = cubV c z J (σ ≫ p ≫ f) (σ ≫ p ≫ f') (σ ≫ q) *
          (val₂ u z J (σ ≫ p) (σ ≫ q) * val₂ u' z J (σ ≫ p) (σ ≫ q)) := fun σ z J hJ =>
    ⟨(val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull₂ _ _ w σ hJ _ _) (val_cub c σ hJ _ _ _)),
      (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_cub c σ hJ _ _ _)
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull₂ _ _ u σ hJ _ _) (val_pull₂ _ _ u' σ hJ _ _))))⟩
  have key := (ev (lift x y) hJ).1.symm.trans (Eq.trans (gen_unique' Lr.isLB (fun V _ k => by
      refine (prod_sum₂ (K := thK) (K' := Fin 6 ⊕ Fin 6) (U := V) _ (prod_cub (p ≫ f) (p ≫ f') q k)
        (prod_sum₂ (K := Fin 6) (K' := Fin 6) (U := V) _ (prod_ros f g p q k) (prod_ros f' g' p q k))).trans
        (Eq.trans ?_ (prod_sum₂ (K := Fin 6) (K' := thK) (U := V) _ (prod_ros (f * f') (g * g') p q k)
          (prod_cub p (q ≫ g) (q ≫ g') k)).symm)
      rw [MonObj.comp_mul, MonObj.comp_mul, _root_.mul_assoc p]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) _ e.left he sj
      (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hw _) (pullGen_isGen _ _ _ _ c.isGen _))
      (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ c.isGen _) (mulGen_isGen _ _ _ _ _ _ _
        (pullGen_isGen _ _ _ _ hu _) (pullGen_isGen _ _ _ _ hu' _))) (fun y I hI => by
      have C : IsCub (cubV c y I) := isCub_cubV c hI
      refine (ev e hI).1.trans (Eq.trans ?_ (ev e hI).2.symm)
      rw [e₀, e₁, val₂_one _ _ w w₀ hI, val₂_one _ _ u h₀ hI, val₂_one _ _ u' h₀' hI, C.face, C.face₃]
      simp) _ (lift x y).left z J hJ) (ev (lift x y) hJ).2)
  have r₀ : lift x y ≫ p = x := lift_fst _ _
  have r₁ : lift x y ≫ q = y := lift_snd _ _
  simp only [← Category.assoc, r₀, r₁] at key
  exact key

end GlobalTheory.TauBalAdd
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory

section RationalValues

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

theorem le_iff_of_pow_eq_zpow {t a b : Γ} (h0 : 0 < t) (h1 : t < 1) {n n' : ℕ} (hn : 0 < n)
    (hn' : 0 < n') {m m' : ℤ} (ha : a ^ n = t ^ m) (hb : b ^ n' = t ^ m') :
    b ≤ a ↔ (m : ℚ) / n ≤ (m' : ℚ) / n' := by
  have e1 : a ^ (n * n') = t ^ (m * n') := by rw [pow_mul, ha, zpow_mul, zpow_natCast]
  have e2 : b ^ (n * n') = t ^ (m' * n) := by rw [mul_comm n, pow_mul, hb, zpow_mul, zpow_natCast]
  rw [← pow_le_pow_iff_left₀ zero_le' zero_le' (Nat.mul_pos hn hn').ne', e1, e2,
    zpow_le_zpow_iff_right_of_lt_one₀ h0 h1, div_le_div_iff₀ (by exact_mod_cast hn)
      (by exact_mod_cast hn')]
  norm_cast

theorem exists_ratAddValuation_of_pow_eq_zpow {F : Type*} [Field F] (w : Valuation F Γ) {t : Γ}
    (h0 : 0 < t) (h1 : t < 1) (h : ∀ x : F, x ≠ 0 → ∃ (n : ℕ) (m : ℤ), 0 < n ∧ w x ^ n = t ^ m) :
    ∃ v : AddValuation F (WithTop ℚ), ∀ (x : F) (m : ℤ), w x = t ^ m →
      v x = ((m : ℚ) : WithTop ℚ) := by
  classical
  choose! n m hn hnm using h
  let f : F → WithTop ℚ := fun x => if x = 0 then ⊤ else (((m x : ℚ) / n x : ℚ) : WithTop ℚ)
  have f0 : f 0 = ⊤ := if_pos rfl
  have key : ∀ (x : F) (a : ℕ) (b : ℤ), 0 < a → w x ^ a = t ^ b →
      f x = (((b : ℚ) / a : ℚ) : WithTop ℚ) := by
    intro x a b ha hab
    have hx : x ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_pow ha.ne'] at hab
      exact (zpow_pos h0 b).ne hab
    simp only [f, if_neg hx, WithTop.coe_inj]
    exact le_antisymm ((le_iff_of_pow_eq_zpow h0 h1 (hn x hx) ha (hnm x hx) hab).1 le_rfl)
      ((le_iff_of_pow_eq_zpow h0 h1 ha (hn x hx) hab (hnm x hx)).1 le_rfl)
  have mono : ∀ x y : F, w y ≤ w x → f x ≤ f y := by
    intro x y hxy
    by_cases hy : y = 0
    · rw [hy, f0]; exact le_top
    have hx : x ≠ 0 := by
      rintro rfl
      rw [map_zero, le_zero_iff, Valuation.zero_iff] at hxy
      exact hy hxy
    simp only [f, if_neg hx, if_neg hy, WithTop.coe_le_coe]
    exact (le_iff_of_pow_eq_zpow h0 h1 (hn x hx) (hn y hy) (hnm x hx) (hnm y hy)).1 hxy
  refine ⟨AddValuation.of f f0 ?_ ?_ ?_, fun x b hb => ?_⟩
  · rw [key 1 1 0 one_pos (by simp)]
    simp
  · intro x y
    rcases le_max_iff.1 (w.map_add x y) with h | h
    · exact min_le_of_left_le (mono _ _ h)
    · exact min_le_of_right_le (mono _ _ h)
  · intro x y
    by_cases hx : x = 0
    · rw [hx, MulZeroClass.zero_mul, f0, top_add]
    by_cases hy : y = 0
    · rw [hy, MulZeroClass.mul_zero, f0, add_top]
    have hx' := hn x hx
    have hy' := hn y hy
    rw [key (x * y) (n x * n y) (m x * n y + m y * n x) (Nat.mul_pos hx' hy') (by
      rw [map_mul, mul_pow, pow_mul, mul_comm (n x), pow_mul, hnm x hx, hnm y hy,
        zpow_add₀ h0.ne', zpow_mul, zpow_mul, zpow_natCast, zpow_natCast])]
    simp only [f, if_neg hx, if_neg hy, ← WithTop.coe_add, WithTop.coe_inj]
    have : (n x : ℚ) ≠ 0 := by exact_mod_cast hx'.ne'
    have : (n y : ℚ) ≠ 0 := by exact_mod_cast hy'.ne'
    push_cast
    field_simp
  · change f x = _
    rw [key x 1 b one_pos (by simpa using hb)]
    simp

theorem exists_valuation_pow_eq_of_isAlgebraic {K F : Type*} [Field K] [Field F] [Algebra K F]
    (w : Valuation F Γ) {x : F} (hx : IsAlgebraic K x) (hx0 : x ≠ 0) :
    ∃ (n : ℕ) (c : K), 0 < n ∧ c ≠ 0 ∧ w x ^ n = w (algebraMap K F c) := by
  classical
  obtain ⟨p, hp0, hp⟩ := hx
  let g : ℕ → F := fun i => algebraMap K F (p.coeff i) * x ^ i
  have hsum : ∑ i ∈ p.support, g i = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def] at hp
    exact hp
  have hc : ∀ i ∈ p.support, w (algebraMap K F (p.coeff i)) ≠ 0 := fun i hi => by
    simpa using hi
  have hw : w x ≠ 0 := by simpa using hx0
  have aux : ∀ i ∈ p.support, ∀ j ∈ p.support, j < i → w (g i) = w (g j) →
      ∃ (n : ℕ) (c : K), 0 < n ∧ c ≠ 0 ∧ w x ^ n = w (algebraMap K F c) := by
    intro i hi j hj hji e
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hji
    refine ⟨d + 1, p.coeff j / p.coeff (j + d + 1), Nat.succ_pos d,
      div_ne_zero (Polynomial.mem_support_iff.1 hj) (Polynomial.mem_support_iff.1 hi), ?_⟩
    simp only [g, map_mul, map_pow] at e
    rw [map_div₀, map_div₀, eq_div_iff (hc _ hi)]
    apply mul_right_cancel₀ (pow_ne_zero j hw)
    rw [← e, _root_.add_assoc j, pow_add (w x) j]
    ac_rfl
  obtain ⟨i, hi, hmax⟩ := p.support.exists_max_image (fun i => w (g i))
    (Polynomial.support_nonempty.2 hp0)
  by_contra hne
  have hlt : ∀ j ∈ p.support \ {i}, w (g j) < w (g i) := by
    intro j hj
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hj
    refine lt_of_le_of_ne (hmax j hj.1) fun e => hne ?_
    rcases lt_or_gt_of_ne hj.2 with h | h
    · exact aux i hi j hj.1 h e.symm
    · exact aux j hj.1 i hi h e
  have hgi : w (g i) ≠ 0 := by
    simp only [g, map_mul, map_pow]
    exact mul_ne_zero (hc i hi) (pow_ne_zero i hw)
  have := w.map_sum_eq_of_lt hi hlt
  rw [hsum, map_zero] at this
  exact hgi this.symm

end RationalValues

theorem exists_valOver_of_isAlgebraic {V : Type} [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ) (F : Type) [Field F]
    [Algebra (FractionRing V) F] [Algebra.IsAlgebraic (FractionRing V) F] :
    ∃ v : AddValuation F (WithTop ℚ), ValOver ϖ F v := by
  let K := FractionRing V
  let f : V →+* F := (algebraMap K F).comp (algebraMap V K)
  have hf : Function.Injective f := (algebraMap K F).injective.comp (IsFractionRing.injective V K)
  obtain ⟨W, hW⟩ := (LocalSubring.range f).exists_le_valuationSubring
  obtain ⟨hW1, hW2⟩ := (localSubring_range_le_valuationSubring_iff f W).1 hW
  let w := W.valuation
  have h0 : 0 < w (f ϖ) := by
    rw [Valuation.pos_iff]
    exact (map_ne_zero_iff _ hf).2 hϖ.ne_zero
  have h1 : w (f ϖ) < 1 := (W.mem_nonunits_iff).1 (hW2 ϖ hϖ.not_isUnit)
  have hu : ∀ u : Vˣ, w (f u) = 1 := fun u =>
    W.valuation_unit (Units.map (f.codRestrict W hW1 : V →* W) u)
  have hval : ∀ (c : K) (n : ℤ), HasVal ϖ c n → w (algebraMap K F c) = w (f ϖ) ^ n := by
    rintro c n ⟨u, rfl⟩
    rw [map_mul, map_mul, map_zpow₀, map_zpow₀]
    change w (f ϖ) ^ n * w (f u) = _
    rw [hu, _root_.mul_one]
  obtain ⟨v, hv⟩ := exists_ratAddValuation_of_pow_eq_zpow w h0 h1 fun x hx => by
    obtain ⟨n, c, hn, hc, e⟩ := exists_valuation_pow_eq_of_isAlgebraic (K := K) w
      (Algebra.IsAlgebraic.isAlgebraic x) hx
    obtain ⟨m, hm⟩ := hasVal_of_ne_zero hϖ hc
    exact ⟨n, m, hn, e.trans (hval c m hm)⟩
  exact ⟨v, fun c n hc => hv _ n (hval c n hc)⟩

theorem exists_complete_discreteValuationRing_map_le {R : Type} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] {I : Ideal R} (hI : I ≠ ⊤) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (φ : R →+* V),
      IsAdicComplete (maximalIdeal V) V ∧ Function.Injective φ ∧ I.map φ ≤ maximalIdeal V := by
  by_cases h : I = ⊥
  · let K := FractionRing R
    refine ⟨PowerSeries K, inferInstance, inferInstance, inferInstance,
      (PowerSeries.C (R := K)).comp (algebraMap R K), ?_,
      PowerSeries.C_injective.comp (IsFractionRing.injective R K), by simp [h]⟩
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  · obtain ⟨p, hp, hIp⟩ := I.exists_le_maximal hI
    have := hp.isPrime
    obtain ⟨O, _, _, _, hO, φ, h1, h2⟩ := exists_complete_discreteValuationRing_of_prime_lt
      (⊥ : Ideal R) p (lt_of_lt_of_le (bot_lt_iff_ne_bot.2 h) hIp)
    exact ⟨O, inferInstance, inferInstance, inferInstance, φ, hO,
      (RingHom.injective_iff_ker_eq_bot φ).2 h1, Ideal.map_le_iff_le_comap.2 (h2 ▸ hIp)⟩

theorem adic_base_embeds_valuation_algebraic_closure :
    (∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (φ : R →+* V), IsAdicComplete (maximalIdeal V) V ∧ Function.Injective φ ∧ I.map φ ≤ maximalIdeal V) ∧ ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∃ v : AddValuation (AlgebraicClosure (FractionRing V)) (WithTop ℚ), ValOver ϖ (AlgebraicClosure (FractionRing V)) v := by
  refine ⟨fun R _ _ _ I hR => ?_, fun V _ _ _ ϖ hϖ => exists_valOver_of_isAlgebraic hϖ _⟩
  obtain ⟨hN, -, -, hc⟩ := hR
  refine exists_complete_discreteValuationRing_map_le ?_
  rintro rfl
  exact not_subsingleton R (IsHausdorff.subsingleton hc.toIsHausdorff)

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace TorusExtBaseChange

theorem isPullback_pullback_map {S S' : Scheme.{0}} (f : S' ⟶ S) {G B : Over S} (q : G ⟶ B) :
    IsPullback (pullback.fst G.hom f) ((Over.pullback f).map q).left q.left (pullback.fst B.hom f) := by
  have h1 : ((Over.pullback f).map q).left ≫ pullback.fst B.hom f = pullback.fst G.hom f ≫ q.left :=
    pullback.lift_fst _ _ _
  have h2 : ((Over.pullback f).map q).left ≫ pullback.snd B.hom f = pullback.snd G.hom f :=
    pullback.lift_snd _ _ _
  refine IsPullback.of_bot ?_ h1.symm (IsPullback.of_hasPullback B.hom f)
  rw [h2, Over.w q]
  exact IsPullback.of_hasPullback _ _

theorem exists_extension {S S' : Scheme.{0}} (f : S' ⟶ S) {T G B : Over S} [GrpObj T] [GrpObj G] [GrpObj B]
    {T' G' B' : Over S'} [GrpObj T'] [GrpObj G'] [GrpObj B']
    (eT : T' ≅ (Over.pullback f).obj T) (eG : G' ≅ (Over.pullback f).obj G)
    (eB : B' ≅ (Over.pullback f).obj B) [IsMonHom eT.hom] [IsMonHom eG.hom] [IsMonHom eB.hom]
    (i : T ⟶ G) (q : G ⟶ B) [IsMonHom i] [IsMonHom q] (hf : Flat q.left) (hs : Surjective q.left)
    (ha : IsAffineHom q.left) (hk : IsPullback i (toUnit _) q η[B]) :
    ∃ (q' : G' ⟶ B') (i' : T' ⟶ G'), IsMonHom q' ∧ Flat q'.left ∧ Surjective q'.left ∧
      IsAffineHom q'.left ∧ IsMonHom i' ∧ IsPullback i' (toUnit _) q' η[B'] ∧
      q'.left ≫ eB.hom.left ≫ pullback.fst B.hom f = (eG.hom.left ≫ pullback.fst G.hom f) ≫ q.left ∧
      i'.left ≫ eG.hom.left ≫ pullback.fst G.hom f = (eT.hom.left ≫ pullback.fst T.hom f) ≫ i.left := by
  have pq := isPullback_pullback_map f q
  have pi := isPullback_pullback_map f i
  have iG : IsIso eG.hom.left := inferInstanceAs (IsIso ((Over.forget _).map eG.hom))
  have iB : IsIso eB.inv.left := inferInstanceAs (IsIso ((Over.forget _).map eB.inv))
  have hf' : Flat ((Over.pullback f).map q).left := MorphismProperty.of_isPullback pq hf
  have hs' : Surjective ((Over.pullback f).map q).left := MorphismProperty.of_isPullback pq hs
  have ha' : IsAffineHom ((Over.pullback f).map q).left := MorphismProperty.of_isPullback pq ha
  refine ⟨eG.hom ≫ (Over.pullback f).map q ≫ eB.inv, eT.hom ≫ (Over.pullback f).map i ≫ eG.inv,
    inferInstance, ?_, ?_, ?_, inferInstance, ?_, ?_, ?_⟩
  · rw [Over.comp_left, Over.comp_left]; infer_instance
  · rw [Over.comp_left, Over.comp_left]; infer_instance
  · rw [Over.comp_left, Over.comp_left]; infer_instance
  · refine (hk.map (Over.pullback f)).of_iso eT.symm eG.symm
      (Functor.Monoidal.εIso (Over.pullback f)).symm eB.symm ?_ (toUnit_unique _ _) ?_ ?_
    · simp
    · simp
    · have : η[(Over.pullback f).obj B] ≫ eB.inv = η[B'] := IsMonHom.one_hom _
      rw [← this, Functor.obj.η_def]
      simp
  · rw [← Over.comp_left_assoc, Category.assoc, Category.assoc, eB.inv_hom_id, Category.comp_id,
      Over.comp_left, Category.assoc, Category.assoc, pq.w]
  · rw [← Over.comp_left_assoc, Category.assoc, Category.assoc, eG.inv_hom_id, Category.comp_id,
      Over.comp_left, Category.assoc, Category.assoc, pi.w]

theorem exists_iso_of_square {S S' S₀ S₀' : Scheme.{0}} (f : S' ⟶ S) (f₀ : S₀' ⟶ S₀) (j : S₀ ⟶ S)
    (j' : S₀' ⟶ S') (w : j' ≫ f = f₀ ≫ j) (G : Over S) [GrpObj G] (G' : Over S') [GrpObj G']
    (bc : G' ≅ (Over.pullback f).obj G) [IsMonHom bc.hom] :
    ∃ e : (Over.pullback j').obj G' ≅ (Over.pullback f₀).obj ((Over.pullback j).obj G), IsMonHom e.hom ∧
      e.hom.left ≫ pullback.fst ((Over.pullback j).obj G).hom f₀ ≫ pullback.fst G.hom j =
        pullback.fst G'.hom j' ≫ bc.hom.left ≫ pullback.fst G.hom f :=
  Geo.Tor.grpPullback_iso
    (((Geo.Tor.isGrpPullback_pullback G' j').comp
      (((Geo.Tor.isGrpPullback_of_iso bc).comp (Geo.Tor.isGrpPullback_pullback G f)).congr
        (Category.id_comp _) rfl)).congr w rfl)
    ((Geo.Tor.isGrpPullback_pullback _ f₀).comp (Geo.Tor.isGrpPullback_pullback G j))

theorem exists_splitTorus_iso {S S' : Scheme.{0}} (f : S' ⟶ S) {X X' : Type} [AddCommGroup X]
    [AddCommGroup X'] (xe : X' ≃+ X) :
    ∃ e : splitTorus S' X' ≅ (Over.pullback f).obj (splitTorus S X), IsMonHom e.hom ∧
      ∀ x : X', (e.hom.left ≫ pullback.fst (splitTorus S X).hom f).appTop.hom (charUnit S X (xe x)).val =
        (charUnit S' X' x).val := by
  obtain ⟨e, he, hc⟩ := splitTorus_baseChange S S' f X
  let e₀ : splitTorus S' X' ≅ splitTorus S' X :=
    { hom := SplitTorus.torusMap S' xe.symm.toAddMonoidHom
      inv := SplitTorus.torusMap S' xe.toAddMonoidHom
      hom_inv_id := by
        rw [← SplitTorus.torusMap_comp, ← SplitTorus.torusMap_id]; congr 1; ext; simp
      inv_hom_id := by
        rw [← SplitTorus.torusMap_comp, ← SplitTorus.torusMap_id]; congr 1; ext; simp }
  have : IsMonHom e₀.hom := SplitTorus.isMonHom_torusMap _
  refine ⟨e₀ ≪≫ e, inferInstanceAs (IsMonHom (e₀.hom ≫ e.hom)), fun x => ?_⟩
  rw [Iso.trans_hom, Over.comp_left, Category.assoc, Rosenlicht.appTop_comp_apply, hc,
    SplitTorus.charUnit_val, SplitTorus.charUnit_val]
  refine (SplitTorus.torusMap_appTop_chi xe.symm.toAddMonoidHom (xe x)).trans ?_
  simp

end TorusExtBaseChange


open TorusExtBaseChange in
theorem gtCoord_baseChange_maps : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (I : Ideal R) (I' : Ideal R'), I.map φ ≤ I' → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G), IsMonHom bc.hom → ∀ (e : ℕ) (g : GtCoord I D e G), ∃ (h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left) (q' : thickObj R' I' e G' ⟶ thickObj R' I' e D'.P.A) (i' : splitTorus (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1)))) D'.X ⟶ thickObj R' I' e G'), h ≫ (fstG I e G).left = (fstG I' e G').left ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) ∧ IsMonHom q' ∧ Flat q'.left ∧ Surjective q'.left ∧ IsAffineHom q'.left ∧ IsMonHom i' ∧ IsPullback i' (toUnit _) q' (η[thickObj R' I' e D'.P.A]) ∧ ((Over.map (thick R' I' e)).map q' ≫ D'.prBe I' e).left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h ≫ g.pG.left ∧ ∃ hT : (splitTorus (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1)))) D'.X).left ⟶ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X).left, i'.left ≫ h = hT ≫ g.i.left ∧ ∀ x : D'.X, hT.appTop.hom (charUnit _ D.X (hD.xe x)).val = (charUnit _ D'.X x).val := by
  intro R R' _ _ _ _ φ D D' hD I I' hI G _ _ G' _ _ bc hbc e g
  have hle : I ^ (e + 1) ≤ (I' ^ (e + 1)).comap φ := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hI _
  let f₀ : Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) :=
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ φ hle))
  have w : thick R' I' e ≫ specOf φ = f₀ ≫ thick R I e := by
    simp only [f₀, thick, specOf, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.quotientMap_comp_mk]
  have := hD.e_hom
  have := g.q_hom
  have := g.i_hom
  obtain ⟨eG, mG, hG⟩ := exists_iso_of_square _ f₀ _ _ w G G' bc
  obtain ⟨eB, mB, hB⟩ := exists_iso_of_square _ f₀ _ _ w D.P.A D'.P.A hD.e
  obtain ⟨eT, mT, hT⟩ := exists_splitTorus_iso f₀ hD.xe
  obtain ⟨q', i', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    exists_extension f₀ eT eG eB g.i g.q g.q_flat g.q_surj g.q_affine g.isKernel
  refine ⟨eG.hom.left ≫ pullback.fst _ f₀, q', i', ?_, h1, h2, h3, h4, h5, h6, ?_, _, h8, hT⟩
  · exact (Category.assoc _ _ _).trans hG
  · change (q'.left ≫ pullback.fst D'.P.A.hom (thick R' I' e)) ≫ _ =
      _ ≫ g.q.left ≫ pullback.fst D.P.A.hom (thick R I e)
    rw [Category.assoc, ← hB, ← Category.assoc _ g.q.left, ← h7]
    simp only [Category.assoc]

end GlobalTheory
end
