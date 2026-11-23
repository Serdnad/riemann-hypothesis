module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PowEqOneOfPush
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

@[expose] public section

open AlgebraicGeometry CategoryTheory
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable local instance (priority := high) grpObjPullbackForUniformization081
    {S T : Scheme.{0}} (f : T ⟶ S) (G : Over S) [GrpObj G] : GrpObj ((Over.pullback f).obj G) :=
  letI : (Over.pullback f).Monoidal := (Over.instBraidedPullback (f := f)).toMonoidal
  Functor.grpObjObj (F := Over.pullback f)

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.AddGeneric

theorem exists_additionFactor_generator_value {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (P : CP G) {T : Over S}
    (x y : T ⟶ G) :
    ∃ t : LB.Gen (LB.LinComb P.L.L (K := Fin 4) ![x.left, y.left, (x * y).left, (x * y⁻¹).left] ![2, 2, -1, -1]),
      t.IsGen ∧ ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good P.L.L z J →
        val t ρ.left z J = kap0 P.c P.sym z J (ρ ≫ x) (ρ ≫ y) := by
  let r₀ := LB.pullGen P.L.L (fun _ : PUnit => eSec G) (fun _ => 1) P.L.rig T.hom
  have hr₀ : r₀.IsGen := DVR.pullGen_isGen _ _ _ _ P.L.rigGen _
  obtain ⟨t, ht, hv⟩ := exists_gen P.L.isLB (φ' := ![x.left, y.left, (x * y).left, (x * y⁻¹).left])
    (ε' := ![2, 2, -1, -1]) (fun U _ h => by
      have o : ∏ _k : PUnit, h (T.hom ≫ eSec G) ^ (1 : ℤ) = h (1 : T ⟶ G).left := by
        rw [Fintype.prod_unique, zpow_one, one_left]
      refine (DVR.prod_sum₂ (U := U) (K := thK ⊕ Fin 2) (K' := PUnit ⊕ PUnit) _
        (DVR.prod_sum₂ (U := U) (K := thK) (K' := Fin 2) _ (prod_cub x y y⁻¹ h) (DVR.prod_neg _ _ (prod_sym y h)))
        (DVR.prod_sum₂ (U := U) (K := PUnit) (K' := PUnit) _ o o)).trans ?_
      rw [mul_inv_cancel_right, mul_inv_cancel]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen P.L.L _ _ _ _
      (LB.mulGen P.L.L _ _ _ _ (LB.pullGen P.L.L (thφ G (x3 G)) thε P.c.t (lift x (lift y y⁻¹)).left)
        (LB.invGen P.L.L _ _ (LB.pullGen P.L.L _ _ P.sym y.left)))
      (LB.mulGen P.L.L _ _ _ _ r₀ r₀))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ P.c.isGen _)
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ P.sym_gen _))) (DVR.mulGen_isGen _ _ _ _ _ _ _ hr₀ hr₀))
  refine ⟨t, ht, fun T' ρ z J hJ => ?_⟩
  have e₀ : val r₀ ρ.left z J =
      val (L := P.L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) P.L.rig T'.hom z J :=
    (val_pull hJ _ _ _).trans (by rw [Over.w ρ])
  refine ((hv _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (val_cub P.c ρ hJ _ _ _) ((val_inv _ _).trans (congrArg (·⁻¹) (val_pull hJ _ _ _)))))
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) e₀ e₀))))).trans ?_
  rw [kap0, sq, GrpObj.comp_inv, Over.comp_left]

theorem exists_additionFactor_generator_transported {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] [IsCommMonObj G] (P : CP G)
    {A : Over S'} [GrpObj A] [IsCommMonObj A] {Φ : A.left ⟶ G.left} (hw : Φ ≫ G.hom = A.hom ≫ f)
    (mul : ∀ (T : Over S') (x y : T ⟶ A), toBase hw (x * y) = toBase hw x * toBase hw y)
    {L' : LB A.left} (hL' : L'.IsLB) (u : LB.Iso L' (P.L.L.pull Φ)) (hu : PGen u) {Y : Over S'} (p q s d : Y ⟶ A)
    (hs : s = p * q) (hd : d = p * q⁻¹) :
    ∃ a : LB.Gen (LB.LinComb L' (K := Fin 4) ![p.left, q.left, s.left, d.left] ![2, 2, -1, -1]), a.IsGen ∧
      ∀ (T : Over S') (ρ : T ⟶ Y) (z : T.left) (J J'), Good P.L.L z J → Good L' z J' →
        ∀ W : (T ⟶ A) → (T.left.presheaf.stalk z)ˣ, (∀ x, W x = gw u x.left z (J (x.left ≫ Φ)) (J' x.left)) →
        @id (T.left.presheaf.stalk z)ˣ (kap0 P.c P.sym (T := Over.mk (T.hom ≫ f)) z J (toBase hw (ρ ≫ p)) (toBase hw (ρ ≫ q))) =
          W (ρ ≫ p) ^ 2 * W (ρ ≫ q) ^ 2 * (W ((ρ ≫ p) * (ρ ≫ q)))⁻¹ * (W ((ρ ≫ p) * (ρ ≫ q)⁻¹))⁻¹ *
            val a ρ.left z J' := by
  subst hs hd
  obtain ⟨t, ht, hv⟩ := exists_additionFactor_generator_value P (toBase hw p) (toBase hw q)
  have hψ : ∀ k : Fin 4, ![p.left, q.left, (p * q).left, (p * q⁻¹).left] k ≫ Φ = 𝟙 Y.left ≫
      ![(toBase hw p).left, (toBase hw q).left, (toBase hw p * toBase hw q).left,
        (toBase hw p * (toBase hw q)⁻¹).left] k := by
    intro k
    rw [Category.id_comp]
    have e : toBase hw (p * q⁻¹) = toBase hw p * (toBase hw q)⁻¹ :=
      (mul _ _ _).trans (congrArg _ (map_inv (toBaseHom mul Y) q))
    rw [← e, ← mul]
    fin_cases k <;> rfl
  obtain ⟨a, ha, H⟩ := DegPull.exists_pmaps hu P.L.isLB hL' (𝟙 Y.left) hψ t ht
  refine ⟨a, ha, fun T ρ z J J' hJ hJ' W hW => ?_⟩
  have e₁ := DegPull.pmaps_val hψ H ρ.left z hJ hJ'
  let ρ' : Over.mk (T.hom ≫ f) ⟶ Over.mk (Y.hom ≫ f) := Over.homMk ρ.left (by
    show ρ.left ≫ Y.hom ≫ f = T.hom ≫ f
    rw [← Category.assoc, Over.w ρ])
  have e₂ := hv _ ρ' z J hJ
  have e₃ : ∀ x : Y ⟶ A, ρ' ≫ toBase hw x = toBase hw (ρ ≫ x) := fun x =>
    Over.OverMorphism.ext (Category.assoc _ _ _).symm
  rw [e₃, e₃] at e₂
  rw [Category.comp_id] at e₁
  refine e₂.symm.trans (e₁.trans (congrArg (· * val a ρ.left z J') ?_))
  rw [← GrpObj.comp_inv, ← MonObj.comp_mul, ← MonObj.comp_mul, ← zpow_neg_one (W _), ← zpow_neg_one (W _),
    ← zpow_natCast (W _), ← zpow_natCast (W _), hW, hW, hW, hW, Fin.prod_univ_four]
  rfl

theorem cancel_alg {B : Type} [CommRing B] {n : ℕ} (a b c d k k' : Bˣ) (r s s' : B) (t t' : Fin n → B)
    (hk : k = a ^ 2 * b ^ 2 * c⁻¹ * d⁻¹ * k')
    (h : ∑ i, (a.val ^ 2 * t i) * (b.val ^ 2 * t' i) = r * k.val * ((c.val ^ 1 * s) * (d.val ^ 1 * s'))) :
    ∑ i, t i * t' i = r * k'.val * (s * s') := by
  apply (a ^ 2 * b ^ 2).isUnit.mul_left_cancel
  rw [Finset.mul_sum]
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (h.trans ?_)
  · simp only [Units.val_mul, Units.val_pow_eq_pow_val]; ring
  · have hc := c.inv_mul
    have hd := d.inv_mul
    rw [hk]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    linear_combination (r * a.val ^ 2 * b.val ^ 2 * k'.val * s * s' * (d⁻¹).val * d.val) * hc +
      (r * a.val ^ 2 * b.val ^ 2 * k'.val * s * s') * hd

theorem isUnit_scal {R : Type} [CommRing R] [IsDomain R] {Y : Scheme.{0}}
    (p : Y ⟶ Spec (CommRingCat.of (FractionRing R))) {r : R} (hr : r ≠ 0) : IsUnit (scal (p ≫ jK R) r) := by
  have e : scal (jK R) r = (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (algebraMap R (FractionRing R) r) :=
    (congrArg (fun q => q.hom r)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))).symm
  have h : IsUnit (algebraMap R (FractionRing R) r) :=
    IsUnit.mk0 _ fun h => hr ((IsFractionRing.injective R (FractionRing R)) (h.trans (map_zero _).symm))
  have : IsUnit (scal (jK R) r) := e ▸ h.map _
  exact this.map p.appTop.hom

theorem addA_of_addG : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (I : Ideal R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (θ : U.SecGT (𝟙_ _) 1) (r : R) (n : ℕ) (σ σ' : Fin n → U.SecGT (𝟙_ _) 2) (th : LB.Sec (LPow A.A A.L ((1 : ℕ) : ℤ) (TFK (R := R) F))) (t t' : Fin n → LB.Sec (LPow A.A A.L ((2 : ℕ) : ℤ) (TFK (R := R) F))), r ≠ 0 → U.AddG θ r σ σ' → U.PullG F (toUnit _) 1 θ th → (∀ i, U.PullG F (toUnit _) 2 (σ i) (t i) ∧ U.PullG F (toUnit _) 2 (σ' i) (t' i)) → AddA A (TFK (R := R) F) th t t' := by
  intro R _ _ D I A G _ _ U F _ _ θ r n σ σ' th t t' hr hadd hθ hσ
  have := U.gen_hom
  have hi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := congrArg (fun q => q.left) U.gen.inv_hom_id
  obtain ⟨u, hu, huv⟩ := ThetaBaseChange.exists_unpull U.wA_gen U.gen.inv.left hi rfl
  have hw : (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) ≫ G.hom = A.A.hom ≫ jK R := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ jK R) (Over.w U.gen.inv)
  have tb : ∀ (T : Over (Spec (CommRingCat.of (FractionRing R)))) (x : T ⟶ A.A), toBase hw x =
      toBase (A := G) (A' := (Over.pullback (jK R)).obj G) (g := pullback.fst G.hom (jK R)) pullback.condition
        (x ≫ U.gen.inv) := fun T x => Over.OverMorphism.ext (Category.assoc _ _ _).symm
  have mul : ∀ (T : Over (Spec (CommRingCat.of (FractionRing R)))) (x y : T ⟶ A.A),
      toBase hw (x * y) = toBase hw x * toBase hw y := fun T x y => by
    rw [tb, tb, tb, MonObj.mul_comp, toBase_mul_pullback]
  obtain ⟨a, ha, hv⟩ := exists_additionFactor_generator_transported U.P hw mul A.isLB u hu (Y := TFK (R := R) F ⊗ (A.A ⊗ A.A))
    (snd _ _ ≫ fst A.A A.A) (snd _ _ ≫ snd A.A A.A) (snd _ _ ≫ (fst A.A A.A * snd A.A A.A))
    (snd _ _ ≫ (fst A.A A.A * (snd A.A A.A)⁻¹)) (MonObj.comp_mul _ _ _)
    ((MonObj.comp_mul _ _ _).trans (by rw [GrpObj.comp_inv]))
  have hun := isUnit_scal (TFK (R := R) F ⊗ (A.A ⊗ A.A)).hom hr
  refine ⟨scaleGen hun.unit a, scaleGen_isGen _ ha, fun T ρ x y z J hJ => ?_⟩
  obtain ⟨JG, hJG⟩ := exists_good_pt U.P.L.isLB z
  let W : (T ⟶ A.A) → (T.left.presheaf.stalk z)ˣ := fun p =>
    gw u p.left z (JG (p.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R))) (J p.left)
  have k₀ := hv T (lift ρ (lift x y)) z JG J hJG hJ W (fun _ => rfl)
  have ex : lift ρ (lift x y) ≫ snd _ _ ≫ fst A.A A.A = x := by simp
  have ey : lift ρ (lift x y) ≫ snd _ _ ≫ snd A.A A.A = y := by simp
  rw [ex, ey] at k₀
  have pull : ∀ (k : ℕ) (s : U.SecGT (𝟙_ _) k) (s' : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F))),
      U.PullG F (toUnit _) k s s' → ∀ p : T ⟶ A.A,
      (W p).val ^ k * sval (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => (k : ℤ))
        s' (lift ρ p).left z J =
      @id (T.left.presheaf.stalk z) (sval s (lift (toUnit (Over.mk (T.hom ≫ jK R))) (toBase hw p)).left z JG) := by
    intro k s s' h p
    have e₁ : (p.left ≫ U.gen.inv.left) ≫ U.gen.hom.left = p.left := by rw [Category.assoc, hi, Category.comp_id]
    have e := h T.left (lift ρ p).left (p.left ≫ U.gen.inv.left)
      (lift (toUnit (Over.mk (T.hom ≫ jK R))) (toBase hw p)).left
      ((congrArg (fun q => q.left) (lift_snd ρ p)).trans e₁.symm)
      ((congrArg (fun q => q.left) (lift_snd _ (toBase hw p))).trans (Category.assoc _ _ _).symm)
      (by
        rw [← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst, Rosenlicht.toUnit_left, Rosenlicht.toUnit_left]
        show T.hom ≫ jK R = ρ.left ≫ jFK (R := R) F ≫ jK R
        rw [← Category.assoc]
        exact congrArg (· ≫ jK R) (Over.w ρ).symm) z J JG hJ hJG
    rw [e₁, Category.assoc] at e
    refine Eq.trans (congrArg (fun q : (T.left.presheaf.stalk z)ˣ => q.val ^ k * _) ?_) e
    exact huv _ p.left z _ _ (hJG (p.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R))) (hJ p.left)
  have add := hadd (Over.mk (T.hom ≫ jK R)) (toBase hw x) (toBase hw y) z JG hJG
  have e : toBase hw (x * y⁻¹) = toBase hw x * (toBase hw y)⁻¹ :=
    (mul _ _ _).trans (congrArg _ (map_inv (toBaseHom mul T) y))
  rw [← e, ← mul] at add
  have key := cancel_alg (W x) (W y) (W (x * y)) (W (x * y⁻¹)) _ _ _ _ _ _ _ k₀
    ((Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) (pull 2 _ _ (hσ i).1 x) (pull 2 _ _ (hσ i).2 y)).trans
      (add.trans (congrArg₂ (· * ·) rfl (congrArg₂ (· * ·) (pull 1 _ _ hθ _).symm (pull 1 _ _ hθ _).symm))))
  refine key.trans (congrArg (· * _) ?_)
  rw [val_scaleGen _ _ _ hJ, Units.val_mul]
  refine congrArg (· * _) (Eq.trans ?_ (gs_unit _ z ⊤ trivial _))
  refine Eq.trans ?_ ((gs_pull (𝟙 _) (lift ρ (lift x y)).left z ⊤ trivial _).trans (by rw [Category.id_comp]))
  refine congrArg (gs (𝟙 T.left) z ⊤) ?_
  show scal (T.hom ≫ jK R) r = scal ((lift ρ (lift x y)).left ≫ (TFK (R := R) F ⊗ (A.A ⊗ A.A)).hom ≫ jK R) r
  rw [← Category.assoc, Over.w]

end GlobalTheory.AddGeneric
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.ThetaIrred

theorem irreducible_of_ringEquiv (F : Type) [Field F] [IsAlgClosed F] (R : Type) [CommRing R] (σ : F ≃+* R)
    (A : Type) [CommGroup A] (V : Type) [AddCommGroup V] [Module R V] (E : Type) [AddCommGroup E] [Module F E]
    (j : V ≃+ E) (hj : ∀ (c : F) v, j (σ c • v) = c • j v) (e : A → A → Rˣ) (Φ : A → (V ≃ₗ[R] V))
    (hcard : (Nat.card A : F) ≠ 0) (hdim : Module.finrank R V ^ 2 = Nat.card A)
    (hmul : ∀ a b, ∃ c : Rˣ, ∀ v, Φ (a * b) v = (c : R) • Φ a (Φ b v))
    (hcomm : ∀ a b v, Φ a (Φ b v) = (e a b : R) • Φ b (Φ a v)) (hnd : ∀ a, (∀ b, e a b = 1) → a = 1)
    (U : Submodule F E) (hU : ∀ a v, j v ∈ U → j (Φ a v) ∈ U) : U = ⊥ ∨ U = ⊤ := by
  letI := (MulEquiv.isField (Field.toIsField F) σ.symm.toMulEquiv).toField
  haveI : IsAlgClosed R := IsAlgClosed.of_ringEquiv F R σ
  have h0 : Nat.card A ≠ 0 := fun h => hcard (by rw [h, Nat.cast_zero])
  haveI : Finite A := Nat.finite_of_card_ne_zero h0
  haveI : Module.Finite R V := Module.finite_of_finrank_pos
    (Nat.pos_of_ne_zero fun h => h0 (by rw [← hdim, h]; rfl))
  have hc : (Nat.card A : R) ≠ 0 := fun h => hcard (σ.injective (by rw [map_natCast, h, map_zero]))
  let W : Submodule R V :=
    { carrier := {v | j v ∈ U}
      add_mem' := fun {a b} ha hb => by
        show j (a + b) ∈ U
        rw [map_add (f := _)]; exact U.add_mem ha hb
      zero_mem' := by
        show j 0 ∈ U
        rw [map_zero]; exact U.zero_mem
      smul_mem' := fun c v hv => by
        show j (c • v) ∈ U
        rw [← σ.apply_symm_apply c, hj]; exact U.smul_mem _ hv }
  have hone : ∃ c : Rˣ, ∀ v, (1 : V ≃ₗ[R] V) v = (c : R) • Φ 1 v := by
    obtain ⟨c, hc⟩ := hmul 1 1
    refine ⟨c, fun v => (Φ 1).injective ?_⟩
    rw [map_smul, ← hc, _root_.mul_one]; rfl
  have key := GlobalTheory.heisenberg_weightSpace_irreducible R A V e Φ hc hdim hmul hcomm hnd ⊥ 1
    (fun t => by
      obtain rfl : t = 1 := Subsingleton.elim _ _
      exact hone)
    (fun _ => ⊤)
    (fun χ v => ⟨fun _ t => by
      obtain rfl : t = 1 := Subsingleton.elim _ _
      rw [map_one, map_one, Units.val_one, one_smul]; rfl, fun _ => trivial⟩)
    1 W le_top (fun h _ v hv => hU h v hv)
  refine key.imp (fun h => ?_) (fun h => ?_)
  · refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
    obtain ⟨v, rfl⟩ := j.surjective x
    have hv : v ∈ W := hx
    rw [h, Submodule.mem_bot] at hv
    rw [hv, map_zero]
  · refine Submodule.eq_top_iff'.2 fun x => ?_
    obtain ⟨v, rfl⟩ := j.surjective x
    exact (h ▸ Submodule.mem_top : v ∈ W)

theorem main : Laws → Laws2 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (F : Type) [Field F] [IsAlgClosed F] (p : Spec (CommRingCat.of F) ⟶ S) (N : ℕ), (N : F) ≠ 0 → (∀ x : Over.mk p ⟶ P.A, x ^ N = 1 → ∃ θ : ThetaGrp P.A P.L (N : ℤ) (Over.mk p), θ.pt = x) ∧ ∀ U : Submodule F (EA P p N), (∀ θ : ThetaGrp P.A P.L (N : ℤ) (Over.mk p), θ.pt ^ N = 1 → ∀ v v' : EA P p N, IsActOf P.A P.L (N : ℤ) θ v.sec v'.sec → v ∈ U → v' ∈ U) → U = ⊥ ∨ U = ⊤ := by
  intro hL hL2 S _ P F _ _ p N hN
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 fun e => hN (by rw [e, Nat.cast_zero])
  obtain ⟨Φ, e, hdim, hact, hmul, hcomm, hnd⟩ := GlobalTheory.ThetaRep.exists_projective_rep hL hL2 S P F p N hN
  refine ⟨fun x hx => (hact ⟨x, hx⟩).imp fun θ h => h.1, fun U hU => ?_⟩
  let G : Subgroup (Over.mk p ⟶ P.A) := (powMonoidHom N).ker
  have hcard : Nat.card G = N ^ (2 * P.g) := (hL.mulN _ P N hN1).2.2.2.2 F p hN
  let j : SecM P.A P.L N (Over.mk p) ≃+ EA P p N :=
    { toFun := fun v => SecMod.mk _ (SecM.toSec P.A v)
      invFun := fun v => SecM.ofSec P.A v.sec
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  refine irreducible_of_ringEquiv F Γ((Over.mk p).left, ⊤)
    (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv G _ _ j (fun c v => rfl)
    (fun a b => e ⟨a.1, a.2⟩ ⟨b.1, b.2⟩) (fun a => Φ ⟨a.1, a.2⟩) ?_ ?_ (fun a b => hmul _ _ _ rfl)
    (fun a b => (hcomm _ _).2) (fun a h => Subtype.ext (hnd ⟨a.1, a.2⟩ fun b => h ⟨b.1, b.2⟩)) U fun a v hv => ?_
  · rw [hcard, Nat.cast_pow]; exact pow_ne_zero _ hN
  · rw [hdim, hcard, ← pow_mul, mul_comm]
  · obtain ⟨θ, h₁, h₂⟩ := hact ⟨a.1, a.2⟩
    exact hU θ (by rw [h₁]; exact a.2) (j v) _ (h₂ v) hv

end GlobalTheory.ThetaIrred
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UU.PointImage

def levelHom {R W : Type} [CommRing R] [CommRing W] (f : R →+* W) (I : Ideal R) (n : ℕ) :
    R ⧸ I ^ n →+* W ⧸ (I.map f) ^ n :=
  Ideal.quotientMap _ f (by rw [← Ideal.map_pow]; exact Ideal.le_comap_map)

theorem isPushout_level {R W : Type} [CommRing R] [CommRing W] (f : R →+* W) (I : Ideal R) (n : ℕ) :
    IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)))
      (CommRingCat.ofHom (Ideal.Quotient.mk ((I.map f) ^ n))) (CommRingCat.ofHom (levelHom f I n)) := by
  have w : CommRingCat.ofHom f ≫ CommRingCat.ofHom (Ideal.Quotient.mk ((I.map f) ^ n)) =
      CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)) ≫ CommRingCat.ofHom (levelHom f I n) := rfl
  have hk : ∀ s : PushoutCocone (CommRingCat.ofHom f) (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n))),
      ∀ a ∈ (I.map f) ^ n, s.inl.hom a = 0 := by
    intro s a ha
    rw [← Ideal.map_pow] at ha
    have : (I ^ n).map f ≤ RingHom.ker s.inl.hom := by
      rw [Ideal.map_le_iff_le_comap]
      intro y hy
      have h := congrArg (fun φ => φ.hom y) s.condition
      change s.inl.hom (f y) = s.inr.hom (Ideal.Quotient.mk _ y) at h
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hy, map_zero] at h
      exact h
    exact this ha
  refine ⟨⟨w⟩, ⟨PushoutCocone.IsColimit.mk w
    (fun s => CommRingCat.ofHom (Ideal.Quotient.lift _ s.inl.hom (hk s))) (fun s => rfl)
    (fun s => ?_) (fun s m h _ => ?_)⟩⟩
  · apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    exact congrArg CommRingCat.Hom.hom s.condition
  · apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    exact congrArg CommRingCat.Hom.hom h

theorem isPullback_level {R W : Type} [CommRing R] [CommRing W] (f : R →+* W) (I : Ideal R) (e : ℕ) :
    IsPullback (adicLevelι (I.map f) (e + 1)) (Spec.map (CommRingCat.ofHom (levelHom f I (e + 1))))
      (Spec.map (CommRingCat.ofHom f)) (thick R I e) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_level f I (e + 1))

theorem thick_mono' (R : Type) [CommRing R] (I : Ideal R) (e : ℕ) : Mono (thick R I e) := by
  have : IsClosedImmersion (thick R I e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance

theorem existsUnique_image {R W : Type} [CommRing R] [CommRing W] [IsLocalRing W] (f : R →+* W)
    (I : Ideal R) [IsAdicComplete (I.map f) W] {G B : Scheme.{0}}
    (pG : G ⟶ Spec (CommRingCat.of R)) (pB : B ⟶ Spec (CommRingCat.of R))
    {P : ℕ → Scheme.{0}} (fst : ∀ e, P e ⟶ G)
    (snd : ∀ e, P e ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
    (hP : ∀ e, IsPullback (fst e) (snd e) pG (thick R I e))
    (τ : ∀ e, P e ⟶ P (e + 1)) (hm : ∀ e, τ e ≫ fst (e + 1) = fst e)
    (φ : ∀ e, P e ⟶ B) (hφ : ∀ e, φ e ≫ pB = snd e ≫ thick R I e)
    (hc : ∀ e, τ e ≫ φ (e + 1) = φ e)
    (x : Spec (CommRingCat.of W) ⟶ G) (hx : x ≫ pG = Spec.map (CommRingCat.ofHom f)) :
    ∃! b : Spec (CommRingCat.of W) ⟶ B, b ≫ pB = Spec.map (CommRingCat.ofHom f) ∧
      ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ P e),
        xe ≫ fst e = r ≫ x → xe ≫ φ e = r ≫ b := by
  have hw : ∀ e, (adicLevelι (I.map f) (e + 1) ≫ x) ≫ pG =
      Spec.map (CommRingCat.ofHom (levelHom f I (e + 1))) ≫ thick R I e := fun e => by
    rw [← (isPullback_level f I e).w, Category.assoc, hx]
  choose y hy hy2 using fun e => (hP e).exists_lift _ _ (hw e)
  have hmono : ∀ e, Mono (fst e) := fun e =>
    (MorphismProperty.monomorphisms Scheme).of_isPullback (hP e).flip (thick_mono' R I e)
  have hfam : IsAdicFamily (I.map f) (fun e => y e ≫ φ e) := by
    intro e
    have : adicLevelMap (I.map f) (Nat.le_succ (e + 1)) ≫ y (e + 1) = y e ≫ τ e := by
      rw [← cancel_mono (fst (e + 1)), Category.assoc, hy,
        adicLevelMap_ι_assoc, Category.assoc, hm, hy]
    change _ ≫ y (e + 1) ≫ φ (e + 1) = y e ≫ φ e
    rw [← hc e, ← Category.assoc, this, Category.assoc]
  obtain ⟨g, ⟨hg, hg'⟩, hu⟩ := existsUnique_over_of_isAdicFamily (Spec.map (CommRingCat.ofHom f))
    pB hfam (fun e => by
      rw [(isPullback_level f I e).w, ← hy2, Category.assoc, hφ, Category.assoc])
  refine ⟨g, ⟨hg, fun e Z r xe h => ?_⟩, fun b hb => ?_⟩
  · have hr : r ≫ Spec.map (CommRingCat.ofHom f) = (xe ≫ snd e) ≫ thick R I e := by
      rw [← hx, ← Category.assoc, ← h, Category.assoc, (hP e).w, Category.assoc]
    obtain ⟨l, hl, -⟩ := (isPullback_level f I e).exists_lift _ _ hr
    have hxe : xe = l ≫ y e := by
      rw [← cancel_mono (fst e), h, ← hl, Category.assoc, Category.assoc, hy]
    rw [hxe, ← hl, Category.assoc, Category.assoc, hg']
  · exact hu b ⟨hb.1, fun e => (hb.2 e _ _ (y e) (hy e)).symm⟩

theorem main : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W → IsLocalHom (algebraMap V W) → ∀ x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G, ∃! b : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b).left) := by
  intro V _ _ _ A G _ _ s t a W _ _ _ hW _ x
  obtain ⟨g, ⟨hg, hg'⟩, hu⟩ := existsUnique_image (algebraMap V W) (IsLocalRing.maximalIdeal V)
    G.hom a.B.hom (P := fun e => (thickObj V (IsLocalRing.maximalIdeal V) e G).left)
    (fun e => (fstG _ e G).left) (fun e => (thickObj V (IsLocalRing.maximalIdeal V) e G).hom)
    (fun e => IsPullback.of_hasPullback G.hom (thick V _ e)) (fun e => thickMap V _ e G)
    (fun e => (pullback.lift_fst _ _ _).trans (Category.comp_id _))
    (fun e => (t.l e).Q.q.left ≫ a.b e)
    (fun e => by
      obtain ⟨h, -⟩ := a.b_pb e
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w])
    (fun e => by rw [← a.b_β e, ← Category.assoc, ← t.β_q e, Category.assoc])
    x.left (Over.w x)
  exact ⟨Over.homMk g hg, hg', fun b hb => Over.OverMorphism.ext (hu b.left ⟨Over.w b, hb⟩)⟩

end GlobalTheory.UU.PointImage
end
end
