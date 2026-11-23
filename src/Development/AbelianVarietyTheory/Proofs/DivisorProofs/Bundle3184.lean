module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle220
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2934
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSpreadUniversalAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2939
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedModelTransportDeeperSetup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2955
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2985
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2956
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3125
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3124
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle043
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsMonHomSplitTorusOfSqEqBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2988
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2979
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3127
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.TensMono

def tensForm {X Y : Type} [AddCommGroup X] [AddCommGroup Y] {r : ℕ} (S : Matrix (Fin r) (Fin r) ℤ) (xe : Y ≃+ (Fin r → X))
    (b : LinearMap.BilinForm ℤ X) : LinearMap.BilinForm ℤ Y :=
  ∑ i, ∑ j, S i j • b.compl₁₂ ((LinearMap.proj i).comp xe.toIntLinearEquiv.toLinearMap)
    ((LinearMap.proj j).comp xe.toIntLinearEquiv.toLinearMap)

theorem tensForm_apply {X Y : Type} [AddCommGroup X] [AddCommGroup Y] {r : ℕ} (S : Matrix (Fin r) (Fin r) ℤ)
    (xe : Y ≃+ (Fin r → X)) (b : LinearMap.BilinForm ℤ X) (y z : Y) :
    tensForm S xe b y z = ∑ i, ∑ j, S i j * b (xe y i) (xe z j) := by
  simp [tensForm, LinearMap.sum_apply]

theorem zpow_sum_local {G κ : Type} [CommGroup G] (a : G) (s : Finset κ) (f : κ → ℤ) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]

theorem tensForm_self {X Y : Type} [AddCommGroup X] [AddCommGroup Y] {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (xe : Y ≃+ (Fin r → X)) (b : LinearMap.BilinForm ℤ X) (hb : ∀ y z, b y z = b z y) (y : Y) :
    tensForm (W + W.transpose) xe b y y = 2 * ∑ i, ∑ j, W i j * b (xe y i) (xe y j) := by
  rw [tensForm_apply]
  simp only [Matrix.add_apply, Matrix.transpose_apply, add_mul, Finset.sum_add_distrib]
  rw [two_mul]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hb]

theorem tensForm_symm {X Y : Type} [AddCommGroup X] [AddCommGroup Y] {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (xe : Y ≃+ (Fin r → X)) (b : LinearMap.BilinForm ℤ X) (hb : ∀ y z, b y z = b z y) (y z : Y) :
    tensForm (W + W.transpose) xe b y z = tensForm (W + W.transpose) xe b z y := by
  rw [tensForm_apply, tensForm_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hb]; simp only [Matrix.add_apply, Matrix.transpose_apply]; ring

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)) (xe : D'.X ≃+ (Fin r → Q.X)), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsTens Q D' W pr xe → ∀ (m : ℕ) (t : Fin m → R) (β : Fin m → LinearMap.BilinForm ℤ Q.X), Q.IsMonomialTau t β → (∀ i, t i ≠ 0) → (∀ i y z, β i y z = β i z y) → (∀ i y, 0 ≤ β i y y) → (∀ y, y ≠ 0 → ∃ i, 0 < β i y y) → ∃ β' : Fin m → LinearMap.BilinForm ℤ D'.X, IsMonomial D' t β' ∧ (∀ i y z, β' i y z = β' i z y) ∧ ∀ y, y ≠ 0 → ∃ i, 0 < β' i y y := by
  intro R _ _ _ Q D' r W pr xe hW hT m t β hmono ht hsym hnn hdef
  have hreal : ∀ l y, ((tensForm (W + W.transpose) xe (β l) y y : ℤ) : ℝ) =
      ∑ i, ∑ j, ((W + W.transpose).map (Int.cast : ℤ → ℝ)) i j *
        (Matrix.of fun i j => (β l (xe y i) (xe y j) : ℝ)) i j := by
    intro l y; rw [tensForm_apply]; push_cast; simp [Matrix.map_apply]
  have hpos : ∀ l y, 0 ≤ tensForm (W + W.transpose) xe (β l) y y := fun l y => by
    have := (GlobalTheory.T.sum_mul_nonneg_and_pos_of_posDef_of_posSemidef _ _ hW (GlobalTheory.T.gram_posSemidef_of_symm_nonneg_int_bilinForm (β l) (hsym l) (hnn l) (fun i => xe y i))).1
    rw [← hreal] at this; exact_mod_cast this
  refine ⟨fun l => tensForm (W + W.transpose) xe (β l), ?_, fun l y z => tensForm_symm W xe (β l) (hsym l) y z, ?_⟩
  · intro y
    have hn : ∀ l, (∑ i, ∑ j, W i j * β l (xe y i) (xe y j)) = ((∑ i, ∑ j, W i j * β l (xe y i) (xe y j)).toNat : ℤ) :=
      fun l => (Int.toNat_of_nonneg (by have := hpos l y; rw [tensForm_self W xe (β l) (hsym l)] at this; omega)).symm
    choose k hk hkc using fun i j => hmono (xe y i) (xe y j)
    obtain ⟨x, hx⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.exists_isPsiCoord D' y
    obtain ⟨u, hu⟩ := GlobalTheory.T.tensorDegeneration_psiCoord_eq_unit_mul_prod R Q D' W pr xe hT y k hkc x hx
    have ht' : ∀ l, algebraMap R (FractionRing R) (t l) ≠ 0 := fun l =>
      (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 (ht l)
    let a : Fin m → (FractionRing R)ˣ := fun l => Units.mk0 _ (ht' l)
    have hk' : ∀ i j, k i j = ∏ l, a l ^ β l (xe y i) (xe y j) := fun i j => Units.ext (by
      rw [hk, Units.coe_prod]
      exact Finset.prod_congr rfl fun l _ => by rw [Units.val_zpow_eq_zpow_val]; rfl)
    have hprod : ∏ i, ∏ j, k i j ^ W i j = ∏ l, a l ^ (∑ i, ∑ j, W i j * β l (xe y i) (xe y j)) := by
      calc ∏ i, ∏ j, k i j ^ W i j = ∏ i, ∏ j, ∏ l, a l ^ (β l (xe y i) (xe y j) * W i j) := by
            refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
            rw [hk', ← Finset.prod_zpow]
            exact Finset.prod_congr rfl fun l _ => (zpow_mul _ _ _).symm
        _ = ∏ i, ∏ l, ∏ j, a l ^ (β l (xe y i) (xe y j) * W i j) :=
            Finset.prod_congr rfl fun i _ => Finset.prod_comm
        _ = ∏ l, ∏ i, ∏ j, a l ^ (β l (xe y i) (xe y j) * W i j) := Finset.prod_comm
        _ = _ := Finset.prod_congr rfl fun l _ => by
            rw [zpow_sum_local]
            refine Finset.prod_congr rfl fun i _ => ?_
            rw [zpow_sum_local]
            exact Finset.prod_congr rfl fun j _ => by rw [mul_comm]
    refine ⟨u, fun l => (∑ i, ∑ j, W i j * β l (xe y i) (xe y j)).toNat, fun l => by
      rw [tensForm_self W xe (β l) (hsym l), hn l], (GlobalTheory.PeriodFormCompare.psiCoord_iff D' y _).2 ⟨x, hx, ?_⟩⟩
    rw [hu, hprod]
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, Units.coe_prod, map_mul, map_prod, map_pow]
    congr 1
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [hn l, zpow_natCast, Units.val_pow_eq_pow_val]; rfl
  · intro y hy
    obtain ⟨j, hj⟩ : ∃ j, xe y j ≠ 0 := by
      by_contra h; push_neg at h
      exact hy (xe.injective (by rw [map_zero]; exact funext h))
    obtain ⟨l, hl⟩ := hdef _ hj
    refine ⟨l, ?_⟩
    have hG : (Matrix.of fun i j => (β l (xe y i) (xe y j) : ℝ)) ≠ 0 := fun h => by
      have := congrFun (congrFun h j) j
      simp at this; omega
    have := (GlobalTheory.T.sum_mul_nonneg_and_pos_of_posDef_of_posSemidef _ _ hW (GlobalTheory.T.gram_posSemidef_of_symm_nonneg_int_bilinForm (β l) (hsym l) (hnn l) (fun i => xe y i))).2 hG
    rw [← hreal] at this; exact_mod_cast this

end GlobalTheory.TensMono
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor


theorem _root_.GlobalTheory.T.exists_torus_components_of_unimodular_tensor : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F), TensFacts W φ e wv → IsUnit (W + W.transpose).det → ∀ v' : N'.Gt, ∃ vs : Fin r → N.Gt, GtRelV W φ e wv v' vs := by
  first | exact @GlobalTheory.Mum.TensTor.gtRelV_onto | exact GlobalTheory.Mum.TensTor.gtRelV_onto | (intros; apply GlobalTheory.Mum.TensTor.gtRelV_onto <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam


theorem _root_.GlobalTheory.T.of_twisted_adjoint_comp : ∀ (R : Type) [CommRing R] [IsDomain R] (Q₁ Q₂ : Data R) (a : Q₁.B ⟶ Q₂.B) (a₁ a₁' : Q₁.B ⟶ Q₁.B) (a' : Q₂.B ⟶ Q₁.B) (h : Q₁.X →+ Q₂.X) (h₁ h₁' : Q₁.X →+ Q₁.X) (h' : Q₂.X →+ Q₁.X), IsMonHom a → IsMonHom a' → (∀ y, Q₂.c (h y) = Q₁.c y ≫ a) → (∀ z, Q₁.c (h' z) = Q₂.c z ≫ a') → Adj Q₁ Q₁ a₁ a₁' h₁ h₁' → (∃ w : LB.Iso (cubeLB Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] Q₂.M.L) (cubeLB Q₁.B ![fst Q₁.B Q₂.B ≫ a₁, snd Q₁.B Q₂.B ≫ a'] Q₁.M.L), w.IsGen ∧ ∀ y y' z J₁ J₂, Good Q₁.M.L z J₁ → Good Q₂.M.L z J₂ → val (Q₂.tau (h y) y') (𝟙 _) z J₂ = adjVal w (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₂.c y')).left z J₁ J₂ * val (Q₁.tau (h₁ y) (h' y')) (𝟙 _) z J₁) → Adj Q₁ Q₂ a (a' ≫ a₁') h (h₁'.comp h') := by
  first | exact @GlobalTheory.MumFam.Adj.of_twisted_comp | exact GlobalTheory.MumFam.Adj.of_twisted_comp | (intros; apply GlobalTheory.MumFam.Adj.of_twisted_comp <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

namespace GlobalTheory.Mum.TensTor

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
  {F : Type} [Field F] [Algebra (FractionRing R) F] {N N' : NumD F}

theorem cmp_mul (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (x y : N'.A) (j : Fin r) :
    cmp T ν ν' (x * y) j = cmp T ν ν' x j * cmp T ν ν' y j := by
  haveI := T.pr_hom j
  simp only [TensTor.cmp, map_mul]
  rw [← map_mul ν.eA.symm]
  congr 1
  exact GlobalTheory.TorusDefect.mul_comp_of_pullback (jK R) (T.pr j) (jFK F) (jFK F ≫ jK R) rfl (ν'.eA x) (ν'.eA y)

theorem cmp_bijective (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') : Function.Bijective (cmp T ν ν') := by
  constructor
  · intro x y h
    apply ν'.eA.injective
    refine Fan.IsLimit.hom_ext T.lim _ _ fun j => ?_
    have := congrFun h j
    simpa [TensTor.cmp] using this
  · intro f
    refine ⟨ν'.eA.symm (Fan.IsLimit.lift T.lim fun j => ν.eA (f j)), funext fun j => ?_⟩
    simp only [TensTor.cmp, MulEquiv.apply_symm_apply]
    refine (congrArg ν.eA.symm (Fan.IsLimit.fac T.lim _ j)).trans ?_
    simp

theorem chi_add (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (χ χ' : N'.X) (i : Fin r) :
    chi T ν ν' (χ + χ') i = chi T ν ν' χ i + chi T ν ν' χ' i := by
  simp [TensTor.chi, map_add (f := _)]

theorem chi_bijective (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') : Function.Bijective (chi T ν ν') := by
  have : chi T ν ν' = ν'.eX.trans (T.xe.trans (AddEquiv.piCongrRight fun _ => ν.eX.symm)) := by
    funext χ i; rfl
  rw [this]; exact AddEquiv.bijective _

theorem cmp_c (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (χ' : N'.X) (j : Fin r) :
    cmp T ν ν' (N'.c χ') j = N.c (chi T ν ν' χ' j) := by
  simp only [TensTor.cmp, TensTor.chi]
  rw [ν.eA.symm_apply_eq, ν.c_eq, ν'.c_eq, ν.eX.apply_symm_apply]
  simp only [DegPre.cF, Category.assoc, T.c_pr]

theorem wv_ne_zero (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (x : N'.A) : wv T ν ν' x ≠ 0 := by
  unfold TensTor.wv valF
  rw [dite_eq_left]
  · exact (((T.w.s _).isUnit.map _).map _).ne_zero
  · intro p _
    refine ⟨Set.mem_iInter.2 fun k => ?_, ν'.good _ trivial⟩
    exact ν.good ((ν'.eA x).left ≫ tensφ T.pr k) (show p ∈ (⊤ : (Sp F).Opens) from trivial)

end GlobalTheory.Mum.TensTor


open GlobalTheory.Mum.TensTor in
theorem GlobalTheory.Mum.TensTor.tensFacts_holds : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N'), TensFacts W (cmp T ν ν') (chi T ν ν') (wv T ν ν') := by
  intro R _ _ _ hB D D' r W T F _ _ _ N N' ν ν'
  exact ⟨cmp_mul T ν ν', cmp_bijective T ν ν', chi_add T ν ν', chi_bijective T ν ν', cmp_c T ν ν', wv_ne_zero T ν ν',
    GlobalTheory.T.tensorData_cubicalStructure_values R hB D D' W T F N N' ν ν', GlobalTheory.T.tensorData_psi_values_through_bundleIso R hB D D' W T F N N' ν ν'⟩

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ZH GlobalTheory.UPoinc GlobalTheory.UCovSep
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_local_spread_universal_abelian_scheme : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (o₁ Ω : Type) [CommRing o₁] [Field Ω] [Algebra o₁ Ω] [ArithBase o₁ Ω] (M : RatModel o₁ Ω) (π : M.Z ⟶ C.Z) (uη : Sp Ω ⟶ Xo.XF c), GlobalTheory.IsNormalScheme M.Z → M.pt ≫ π = uη ≫ C.i → ∀ (A₁ : PolAV (Sp Ω)) (m : ℕ) (ze : o₁ˣ), IsUnit (m : o₁) → UOver Xo c A₁ (RingHom.id Ω) uη → Out.Level A₁ m (unitOn (Units.map (algebraMap o₁ Ω).toMonoidHom ze)) → ∀ (K : Type) [Field K] (yM : Sp K ⟶ M.Z) (y : Sp K ⟶ Xo.XF c), yM ≫ π = y ≫ C.i → ∃ (R : Subalgebra o₁ Ω) (P : PolAV (Sp R)) (act : 𝓞 E → (P.A ⟶ P.A)) (u : Sp (ratHull R) ⟶ Xo.XF c) (𝔭 : Ideal R), R.FG ∧ (∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) ∧ P.g = A₁.g ∧ HypS P.A P.L ∧ Nonempty (Out.Level P m (unitOn (Units.map (algebraMap o₁ R).toMonoidHom ze))) ∧ (∀ a, IsMonHom (act a)) ∧ GlobalTheory.UCovSep.UAct Xo c P act (toRat R) u ∧ spMap (ratHull R).val.toRingHom ≫ u = uη ∧ 𝔭.IsPrime ∧ ∀ a b : R, b ∉ 𝔭 → (a : Ω) / (b : Ω) ∈ M.O (yM (closedPoint K)) := by
  first | exact @GlobalTheory.UCovSep.LocalSpread.exists_local_spread | exact GlobalTheory.UCovSep.LocalSpread.exists_local_spread | (intros; apply GlobalTheory.UCovSep.LocalSpread.exists_local_spread <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.unitaryRecharting_classicalTrait_same_geometric_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (p : ℕ) [Fact p.Prime] (z : X.M.Z) (ct : UCTrait X p z) (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X.o₁ X.Ω₁) (fg : R'.FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ R') (hev : ∀ x k, c₀ * X.S.ev x k ∈ R') (ρ' : (X.S.rechart c₀ hc R' fg frac hth hev).Real), USame X.ρ ρ' (fun x => x) (RingHom.id _) → R' ≤ X.M.O ((gPt p ≫ ct.y) (closedPoint (PadicAlgCl p))) → ∀ (y₀ : R' →+* PadicAlgCl p), (∀ a : R', y₀ a = X.M.val (gPt p ≫ ct.y) a) → ∀ (c₁ : X.Ω₁) (hc₁ : c₁ ≠ 0) (R'' : Subalgebra X.o₁ X.Ω₁) (fg₁ : R''.FG) (frac₁ : ∀ x : X.Ω₁, ∃ a ∈ R'', ∃ b ∈ R'', x = a / b) (hth₁ : ∀ x, c₁ * X.S.th x ∈ R'') (hev₁ : ∀ x k, c₁ * X.S.ev x k ∈ R'') (ρ'' : (X.S.rechart c₁ hc₁ R'' fg₁ frac₁ hth₁ hev₁).Real), USame X.ρ ρ'' (fun x => x) (RingHom.id _) → R'' ≤ X.M.O ((gPt p ≫ ct.y) (closedPoint (PadicAlgCl p))) → ∀ (y₁ : R'' →+* PadicAlgCl p), (∀ a : R'', y₁ a = X.M.val (gPt p ≫ ct.y) a) → ∀ (u : ρ'.UTest p y₀) (u' : ρ''.UTest p y₁), ∃ (P₀ : PolAV (Sp (PadicAlgCl p))) (a : P₀.A.left ⟶ u.A.A.left) (a' : P₀.A.left ⟶ u'.A.A.left), IsGrpPullback P₀.A u.A.A (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p))) a ∧ IsGrpPullback P₀.A u'.A.A (spMap (algebraMap (FractionRing u'.V) (PadicAlgCl p))) a' ∧ LBIso P₀.L (u.A.L.pull a) ∧ LBIso P₀.L (u'.A.L.pull a') ∧ ∀ b : X.S.Gam, ∃ (w : Sp (PadicAlgCl p) ⟶ P₀.A.left) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (x' : TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A), w ≫ P₀.A.hom = 𝟙 _ ∧ w ≫ a = x.left ∧ w ≫ a' = x'.left ∧ x.left ≫ u.φ = spMap y₀ ≫ (ρ'.pt b).left ∧ x'.left ≫ u'.φ = spMap y₁ ≫ (ρ''.pt b).left := by
  first | exact @GlobalTheory.UPoinc.USpread.main | exact GlobalTheory.UPoinc.USpread.main | (intros; apply GlobalTheory.UPoinc.USpread.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.uniformisedModel_transport_deeper_setup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X₁ : USetup C) (D : UDeep X₁) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (ct : UCTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y) (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (u' : Sp (ratHull R') ⟶ Xo.XF cf), USame X₁.ρ ρ' (fun x => x) (RingHom.id _) → ρ'.i₀ = X₁.ρ.i₀ → spMap (ratHull R').val.toRingHom ≫ u' = X₁.uΩ → R' ≤ X₁.M.O ((gPt p ≫ ct.y) (closedPoint (PadicAlgCl p))) → ∀ (G : Over (Sp (ratHull R'))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ'.P.A (spMap (toRat R')) α → IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β → LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) → ∀ (y₀ : R' →+* PadicAlgCl p), (∀ a : R', y₀ a = X₁.M.val (gPt p ≫ ct.y) a) → ∀ (u : ρ'.UTest p y₀) (c₂ : D.X.Ω₁) (hc₂ : c₂ ≠ 0) (R₂ : Subalgebra D.X.o₁ D.X.Ω₁) (fg₂ : R₂.FG) (frac₂ : ∀ x : D.X.Ω₁, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b) (hth₂ : ∀ x, c₂ * D.X.S.th x ∈ R₂) (hev₂ : ∀ x k, c₂ * D.X.S.ev x k ∈ R₂) (ρ₂ : (D.X.S.rechart c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂).Real) (u₂' : Sp (ratHull R₂) ⟶ Xo.XF cf), USame D.X.ρ ρ₂ (fun x => x) (RingHom.id _) → ρ₂.i₀ = D.X.ρ.i₀ → spMap (ratHull R₂).val.toRingHom ≫ u₂' = D.X.uΩ → R₂ ≤ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))) → ∀ (G₂ : Over (Sp (ratHull R₂))) (_ : GrpObj G₂) (α₂ : G₂.left ⟶ ρ₂.P.A.left) (β₂ : G₂.left ⟶ Xo.univ.t.G.left), IsGrpPullback G₂ ρ₂.P.A (spMap (toRat R₂)) α₂ → IsGrpPullback G₂ Xo.univ.t.G (u₂' ≫ pullback.fst _ _) β₂ → LBIso (ρ₂.P.L.pull α₂) (Xo.univ.t.PP.L.pull β₂) → ∀ (y₂ : R₂ →+* PadicAlgCl p), (∀ a : R₂, y₂ a = D.X.M.val (gPt p ≫ y) a) → (∀ a : D.X.o₁, ‖y₂ (algebraMap D.X.o₁ R₂ a)‖ ≤ 1) → (∃ (P₀ : Over (Sp D.X.Ω₁)) (_ : GrpObj P₀) (a : P₀.left ⟶ G.left) (a₂ : P₀.left ⟶ G₂.left), IsGrpPullback P₀ G (spMap ((algebraMap X₁.Ω₁ D.X.Ω₁).comp (ratHull R').val.toRingHom)) a ∧ IsGrpPullback P₀ G₂ (spMap (ratHull R₂).val.toRingHom) a₂ ∧ a ≫ β = a₂ ≫ β₂ ∧ ∀ x, ∃ w : Sp D.X.Ω₁ ⟶ P₀.left, w ≫ a ≫ α = spMap ((algebraMap X₁.Ω₁ D.X.Ω₁).comp R'.val.toRingHom) ≫ (ρ'.pt x).left ∧ w ≫ a₂ ≫ α₂ = spMap R₂.val.toRingHom ≫ (ρ₂.pt (D.lab x)).left) → ∃ (u₂ : ρ₂.UTest p y₂) (e : u₂.D.toPre.X ≃+ u.D.toPre.X) (T : (TFK (R := u₂.V) (PadicAlgCl p) ⟶ u₂.A.A) ≃ (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), (∀ χ r, u.PsiNorm (e χ) r → u₂.PsiNorm χ r) ∧ (∀ x₂ a, x₂.left ≫ u₂.φ = spMap y₂ ≫ (ρ₂.pt (D.lab a)).left ↔ (T x₂).left ≫ u.φ = spMap y₀ ≫ (ρ'.pt a).left) ∧ (∀ x₂ (w₂ : Sp (PadicAlgCl p) ⟶ G₂.left), w₂ ≫ α₂ = x₂.left ≫ u₂.φ → ∃ w : Sp (PadicAlgCl p) ⟶ G.left, w ≫ α = (T x₂).left ≫ u.φ ∧ w ≫ β = w₂ ≫ β₂) ∧ (∀ (m : ℕ) (pk₂ : QkPt u₂.D.toPre (PadicAlgCl p) m) x₂, 1 ≤ m → QkToAkU u₂.U.toUnifPre (PadicAlgCl p) m pk₂ x₂ → ∃ pk : QkPt u.D.toPre (PadicAlgCl p) m, pk.y = e pk₂.y ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk (T x₂)) ∧ (∀ (m : ℕ) (pk : QkPt u.D.toPre (PadicAlgCl p) m) x, 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → ∃ pk₂ : QkPt u₂.D.toPre (PadicAlgCl p) m, e pk₂.y = pk.y ∧ QkToAkU u₂.U.toUnifPre (PadicAlgCl p) m pk₂ (T.symm x)) := by
  first | exact @GlobalTheory.UPoinc.uTest_transport | exact GlobalTheory.UPoinc.uTest_transport | (intros; apply GlobalTheory.UPoinc.uTest_transport <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.DescKP

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S} [GrpObj G]

theorem ι_mem {X : Scheme.{0}} (U : X.Opens) (x : U.toScheme) : U.ι x ∈ U := x.2

theorem surjective_Wk (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π)
    (V : (N.U ⊗ N.U).left.Opens) (h : Surjective ((VT N V).ι ≫ (Desc.UT N ⊗ Desc.UT N).hom)) :
    Surjective ((Wk N p hp V).ι ≫ (Pk N p hp).hom) := by
  obtain ⟨z, h1, h2⟩ := exists_lift N p hp (VT N V).toScheme (VT N V).ι (VT N V).ι rfl
  have hr : Set.range z ⊆ Set.range (Wk N p hp V).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine ⟨?_, ?_⟩
    · show (abP N p hp).left (z x) ∈ VT N V
      rw [← Scheme.Hom.comp_apply, h1]; exact ι_mem _ x
    · show (cdP N p hp).left (z x) ∈ VT N V
      rw [← Scheme.Hom.comp_apply, h2]; exact ι_mem _ x
  let z' := IsOpenImmersion.lift (Wk N p hp V).ι z hr
  have e : z' ≫ (Wk N p hp V).ι ≫ (Pk N p hp).hom = (VT N V).ι ≫ (Desc.UT N ⊗ Desc.UT N).hom := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac, ← h1, Category.assoc, Over.w (abP N p hp)]
  have : Surjective (z' ≫ (Wk N p hp V).ι ≫ (Pk N p hp).hom) := by rw [e]; exact h
  exact Surjective.of_comp z' _

theorem agree_Wk (N : Near π G) (V : (N.U ⊗ N.U).left.Opens) (m : V.toScheme ⟶ N.U.left)
    (hm : m ≫ N.U.hom = V.ι ≫ (N.U ⊗ N.U).hom) (p p' : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π)
    (hp' : p' ≫ π = pullback.fst π π ≫ π)
    (h : (VT N V).ι ≫ (Desc.sum N p hp).left = mT N V m hm ≫ (Desc.emb N p hp).left)
    (h' : (VT N V).ι ≫ (Desc.sum N p' hp').left = mT N V m hm ≫ (Desc.emb N p' hp').left) :
    (Wk N p hp V).ι ≫ (abP N p hp ≫ Desc.sum N p' hp').left =
      (Wk N p hp V).ι ≫ (cdP N p hp ≫ Desc.sum N p' hp').left := by
  let a' := IsOpenImmersion.lift (VT N V).ι ((Wk N p hp V).ι ≫ (abP N p hp).left) (by
    rintro _ ⟨x, rfl⟩; rw [Scheme.Opens.range_ι]; exact (ι_mem _ x).1)
  let c' := IsOpenImmersion.lift (VT N V).ι ((Wk N p hp V).ι ≫ (cdP N p hp).left) (by
    rintro _ ⟨x, rfl⟩; rw [Scheme.Opens.range_ι]; exact (ι_mem _ x).2)
  have ea : a' ≫ (VT N V).ι = (Wk N p hp V).ι ≫ (abP N p hp).left := IsOpenImmersion.lift_fac _ _ _
  have ec : c' ≫ (VT N V).ι = (Wk N p hp V).ι ≫ (cdP N p hp).left := IsOpenImmersion.lift_fac _ _ _
  have e0 := congrArg (fun f => (Wk N p hp V).ι ≫ Over.Hom.left f) (abP_sum N p hp)
  simp only [Over.comp_left] at e0
  have hemb := GlobalTheory.Mum.DescHom.isOpenImmersion_emb N p hp
  have e2 : a' ≫ mT N V m hm = c' ≫ mT N V m hm := by
    refine (cancel_mono (Desc.emb N p hp).left).1 ?_
    simp only [Category.assoc]
    rw [← h, ← Category.assoc, ea, ← Category.assoc, ec, Category.assoc, Category.assoc]
    exact e0
  simp only [Over.comp_left]
  rw [← Category.assoc, ← ea, Category.assoc, h', ← Category.assoc, e2, Category.assoc, ← h', ← Category.assoc, ec,
    Category.assoc]

end GlobalTheory.Mum.DescKP


open GlobalTheory.Mum.DescKP in
theorem GlobalTheory.Mum.DescKP.sum_eq_of_sum_eq : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → ∀ (p p' : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) (hp' : p' ≫ π = pullback.fst π π ≫ π), ∀ (Z : Scheme.{0}) (g g' : Z ⟶ (Desc.UT N ⊗ Desc.UT N).left), g ≫ (Desc.sum N p hp).left = g' ≫ (Desc.sum N p hp).left → g ≫ (Desc.sum N p' hp').left = g' ≫ (Desc.sum N p' hp').left := by
  intro R _ _ _ _ S π _ _ _ G _ _ hG N hLaw p p' hp hp' Z g g' hgg
  obtain ⟨V, m, hV, hm, hL⟩ := hLaw
  have hlaw := fun (q : pullback π π ⟶ S) (hq : q ≫ π = pullback.fst π π ≫ π) => GlobalTheory.T.nearOpen_sum_eq_embedding_descendedMultiplication N V m hm hL q hq
  have : Smooth N.U.hom := N.smooth
  have : Surjective N.U.hom := DescHom.surjective_near N
  have : Smooth G.hom := hG.smooth
  have : IsSeparated G.hom := hG.separated
  have := DescHom.geometricallyIrreducible_of_semiAbelian G hG

  have sV := GlobalTheory.T.surjective_open_containing_closedFibre_smooth_square N.U N.smooth inferInstance V hV
  have sq : IsPullback (DescKP.pairU N ∣_ V) ((VT N V).ι ≫ (Desc.UT N ⊗ Desc.UT N).hom)
      (V.ι ≫ (N.U ⊗ N.U).hom) (pullback.fst π π ≫ π) :=
    (isPullback_morphismRestrict (DescKP.pairU N) V).paste_vert (GlobalTheory.T.isPullback_descentSquarePairToOpenSquare N)
  have sVT : Surjective ((VT N V).ι ≫ (Desc.UT N ⊗ Desc.UT N).hom) :=
    MorphismProperty.of_isPullback (P := @Surjective) sq sV
  have sW := DescKP.surjective_Wk N p hp V sVT

  have : Smooth (Desc.UT N).hom := inferInstanceAs (Smooth (pullback.snd N.U.hom (pullback.fst π π ≫ π)))
  have : Surjective (Desc.UT N).hom := inferInstanceAs (Surjective (pullback.snd N.U.hom (pullback.fst π π ≫ π)))
  have hGp : GeometricallyIrreducible ((Over.pullback p).obj G).hom :=
    inferInstanceAs (GeometricallyIrreducible (pullback.snd G.hom p))
  have := DescHom.isOpenImmersion_emb N p hp
  have : GeometricallyIrreducible (Desc.UT N).hom := by
    have e : (Desc.emb N p hp).left ≫ ((Over.pullback p).obj G).hom = (Desc.UT N).hom := Over.w _
    have h := GlobalTheory.T.geometricallyIrreducible_comp_of_isOpenImmersion_surjective _ _ _ (Desc.emb N p hp).left inferInstance _ hGp (by rw [e]; infer_instance)
    rwa [e] at h
  have : Smooth (Desc.UT N ⊗ Desc.UT N).hom :=
    inferInstanceAs (Smooth (pullback.fst (Desc.UT N).hom (Desc.UT N).hom ≫ (Desc.UT N).hom))
  have : GeometricallyIrreducible (Desc.UT N ⊗ Desc.UT N).hom :=
    GeometricallyIrreducible.comp (pullback.fst (Desc.UT N).hom (Desc.UT N).hom) (Desc.UT N).hom
  have : Smooth ((Desc.UT N ⊗ Desc.UT N) ⊗ Desc.UT N).hom :=
    inferInstanceAs (Smooth (pullback.fst (Desc.UT N ⊗ Desc.UT N).hom (Desc.UT N).hom ≫ (Desc.UT N ⊗ Desc.UT N).hom))
  have h3 : GeometricallyIrreducible ((Desc.UT N ⊗ Desc.UT N) ⊗ Desc.UT N).hom :=
    GeometricallyIrreducible.comp (pullback.fst (Desc.UT N ⊗ Desc.UT N).hom (Desc.UT N).hom) (Desc.UT N ⊗ Desc.UT N).hom
  have : Surjective (DescKP.Pk N p hp).hom := Surjective.of_comp (DescKP.Wk N p hp V).ι _
  have : Smooth (DescKP.Pk N p hp).hom :=
    inferInstanceAs (Smooth (pullback.snd (Desc.emb N p hp).left (DescKP.trip N p hp).left ≫
      ((Desc.UT N ⊗ Desc.UT N) ⊗ Desc.UT N).hom))
  have : GeometricallyIrreducible (DescKP.Pk N p hp).hom :=
    GlobalTheory.T.geometricallyIrreducible_comp_of_isOpenImmersion_surjective _ _ _ (pullback.snd (Desc.emb N p hp).left (DescKP.trip N p hp).left) inferInstance _ h3
      (inferInstanceAs (Surjective (DescKP.Pk N p hp).hom))
  have : IsSeparated ((Over.pullback p').obj G).hom := inferInstanceAs (IsSeparated (pullback.snd G.hom p'))

  let j : Over.mk ((DescKP.Wk N p hp V).ι ≫ (DescKP.Pk N p hp).hom) ⟶ DescKP.Pk N p hp :=
    Over.homMk (DescKP.Wk N p hp V).ι rfl
  have : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion (DescKP.Wk N p hp V).ι)
  have : Surjective (Over.mk ((DescKP.Wk N p hp V).ι ≫ (DescKP.Pk N p hp).hom)).hom := sW
  have hF : DescKP.abP N p hp ≫ Desc.sum N p' hp' = DescKP.cdP N p hp ≫ Desc.sum N p' hp' := by
    refine DescHom.ext_of_open j ?_
    ext1
    exact DescKP.agree_Wk N V m hm p p' hp hp' (hlaw p hp) (hlaw p' hp')
  obtain ⟨z, hz, hz'⟩ := DescKP.exists_lift N p hp Z g g' hgg
  rw [← hz, ← hz', Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, hF]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

theorem _root_.GlobalTheory.T.pullbackThetaFamilyGaloisTwist_fixes_integralFamily : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (F₀ : IntFam I D N) (s : Fam D (Kb R) N), F₀.Over s → famTw D N σ s = s := by
  first | exact @GlobalTheory.Mum.Conj.famTw_eq_of_over | exact GlobalTheory.Mum.Conj.famTw_eq_of_over | (intros; apply GlobalTheory.Mum.Conj.famTw_eq_of_over <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

theorem _root_.GlobalTheory.T.pullbackThetaSectionsGaloisTwist_chart_semilinear : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (c : Kb R) (t t' : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N), (∀ j, t'.f j = liftFun A.A _ (fnF (R := R) (Kb R) c) * t.f j) → ∀ j, (secTw A N σ t').f j = liftFun A.A _ (fnF (R := R) (Kb R) (σ c)) * (secTw A N σ t).f j := by
  first | exact @GlobalTheory.Mum.Conj.secTw_chart_smul | exact GlobalTheory.Mum.Conj.secTw_chart_smul | (intros; apply GlobalTheory.Mum.Conj.secTw_chart_smul <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

theorem _root_.GlobalTheory.T.operator_relation_pullback_galois_automorphism : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ) (τ : Kb R →ₐ[FractionRing R] Kb R) (p p₀ : QkPt D (Kb R) N) (h : QkExt τ.toRingHom p p₀) (w : GlobalTheory.UT.Frm D (Kb R) N p.g.b) (s s' : Fam D (Kb R) N), PhiRel D (Kb R) N p w s s' → PhiRel D (Kb R) N p₀ (frTw D τ h w) (famTw D N τ s) (famTw D N τ s') := by
  first | exact @GlobalTheory.Mum.Conj.PhiTw.phiRel_famTw | exact GlobalTheory.Mum.Conj.PhiTw.phiRel_famTw | (intros; apply GlobalTheory.Mum.Conj.PhiTw.phiRel_famTw <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.pulledBack_period_constants_symmetric : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V)) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.toPre.X) (L : LowBase (zetaAway n) n) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (f₁ : V →+* V₁) (κ₁ : L.W →+* V₁) (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β' : B'.left ⟶ D.toPre.P.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 D.toPre.P.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsCN V → IsDiscreteValuationRing V → IsCN V₁ → IsDiscreteValuationRing V₁ → Function.Injective f₁ → f₁.Finite → IsLocalHom f₁ → IsLocalHom κ₁ → IsGrpPullback B' D.toPre.P.A (spMap f₁) β' → IsGrpPullback B' L.T.B (spMap κ₁) β'' → IsSquare β' β₂ → IsSquare β'' β₂' → ∀ (x : (Fin L.T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')), (∀ a, (x a).left ≫ β' = spMap f₁ ≫ (D.toPre.c (e₀ (e a))).left ∧ (x a).left ≫ β'' = spMap κ₁ ≫ (L.T.c₀ ((n : ℤ) • a)).left) → ∀ (w₁ : LB.Iso ((abelian₂ D.toPre.P.A D.toPre.P.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂')) (q : (Fin L.T.r → ℤ) → (Fin L.T.r → ℤ) → (FractionRing V₁)ˣ), w₁.IsGen → PeriodRel D.toPre L.T f₁ κ₁ w₁ (e.trans e₀) x n q → IsNormIso w₁ → ∀ a b, q a b = q b a := by
  first | exact @GlobalTheory.TChart.periodConst_symm | exact GlobalTheory.TChart.periodConst_symm | (intros; apply GlobalTheory.TChart.periodConst_symm <;> assumption)
end
