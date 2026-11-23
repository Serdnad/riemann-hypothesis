module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle007
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle010
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle013
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle027
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.WeightIndep
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.OLinearCompare

open GlobalTheory.TorusCoord

theorem oneGen_isGen {X Y : Scheme.{0}} (L : LB X) : (LB.oneGen L (Y := Y)).IsGen :=
  isGen_of_gm _ fun _ _ _ _ _ =>
    (map_one _).trans (Eq.symm ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans
      (_root_.mul_one _)))

theorem val₂_axis {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}
    (hA : IsAbelianScheme A) (hL : L.IsLB) (f g : A ⟶ A) [IsMonHom f] [IsMonHom g]
    (u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)) (hu : u.IsGen)
    (h₀ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (zero2 A)) (LB.oneGen L))
    {T : Over S} {z : T.left} {J} (hJ : Good L z J) (x : T ⟶ A) : val₂ u z J x 1 = 1 := by
  have key := gen_unique' hL (u := LB.pullGen L _ _ u (lift (𝟙 A) (1 : A ⟶ A)).left)
    (u' := LB.oneGen L) (fun U _ h => by
      refine (Fintype.prod_empty _).trans (Eq.symm ((prod_ros f g (𝟙 A) 1 h).trans ?_))
      rw [MonObj.one_comp, _root_.mul_one, _root_.mul_one]
      simp)
    A.hom η[A].left (Over.w η[A]) (globalFns_holds _ _ hA).2 (DVR.pullGen_isGen _ _ _ _ hu _)
    (oneGen_isGen L) (fun y I hI => by
      have := val_corr hI h₀ (𝟙 _)
      rw [val_pull hI, Category.id_comp, val_one] at this
      rw [val_pull hI, val_one, ← Over.comp_left]
      have e : η[A] ≫ lift (𝟙 A) (1 : A ⟶ A) = lift η[A] η[A] := by simp [Hom.one_def]
      rw [e]; exact this) _ x.left z J hJ
  rw [val_pull hJ, val_one, ← Over.comp_left, comp_lift, Category.comp_id, MonObj.comp_one] at key
  exact key

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem val_pull_lift {b b' : D.P.A ⟶ D.P.A}
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A b' b) rosatiε)) (χ : D.X)
    {T Z : Over (Spec (CommRingCat.of R))} (p : T ⟶ D.P.A) (x : Z ⟶ T) {z : Z.left} {J}
    (hJ : Good D.P.L z J) :
    val (LB.pullGen D.P.L _ _ u (lift (toUnit T ≫ D.c χ) p).left) x.left z J =
      val₂ u z J (toUnit Z ≫ D.c χ) (x ≫ p) := by
  rw [val_pull hJ, ← Over.comp_left, comp_lift, comp_toUnit_assoc]; rfl

end GlobalTheory.OLinearCompare
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefPhi
open GlobalTheory.UT.CoefBasic

theorem cubN_mul {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ) (k n : ℕ) (a m x : A) :
    cubN θ (k * n) a m x = cubN θ n a (m ^ k) x * cubN θ k 1 m x ^ n := by
  induction n with
  | zero => simp [cubN]
  | succ n ih =>
    have e : cubN θ (k * (n + 1)) a m x = cubN θ (k * n) a m x * cubN θ k (a * (m ^ k) ^ n) m x := by
      rw [Nat.mul_succ, cubN, Finset.prod_range_add, cubN, cubN]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [pow_add, pow_mul, _root_.mul_assoc]
    have e' : cubN θ (n + 1) a (m ^ k) x = cubN θ n a (m ^ k) x * θ (a * (m ^ k) ^ n) (m ^ k) x :=
      Finset.prod_range_succ _ _
    rw [e, e', ih, h.N_split k (a * (m ^ k) ^ n), pow_succ (cubN θ k 1 m x)]
    ac_rfl

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem exists_frame {k : ℕ} (p : QkPt D F k) (w : Frm D F k p.g.b) (hw : w.IsGen) (g₀ : GtPtF D F)
    (ω₀ : Frm D F k g₀.b) (h₀ : ω₀.IsGen) (b : TF (R := R) F ⟶ D.P.A) (hb : b = g₀.b * p.g.b) :
    ∃ ω₁ : Frm D F k b, ω₁.IsGen ∧ ∀ z J, Good D.P.L z J → val ω₁ (𝟙 _) z J =
      val ω₀ (𝟙 _) z J * val w (𝟙 _) z J * val (g₀.s p.y) (𝟙 _) z J * cubN (th D z J) k 1 p.g.b g₀.b := by
  obtain ⟨N, hN, vN⟩ := exists_cubN D.cub (1 : TF (R := R) F ⟶ D.P.A) p.g.b g₀.b k
  obtain ⟨u, hu, vu⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F b) (ε' := DegPre.lineε k) (fun U _ h => by
      refine Eq.trans (prod_sum₂ (K := (Fin 2 ⊕ Fin 2) ⊕ Fin 4) (K' := Fin 8) (U := U) _
        (prod_sum₂ (K := Fin 2 ⊕ Fin 2) (K' := Fin 4) (U := U) _
          (prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := U) _ (prod_line k g₀.b h) (prod_line k p.g.b h))
          (prod_gt g₀.b p.y h)) rfl) ?_
      rw [prod_line, cPoint_y, hb, mul_comm g₀.b]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ ω₀ w) (g₀.s p.y)) N)
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ h₀ hw) (g₀.isGen _)) hN)
  refine ⟨u, hu, fun z J hJ => ?_⟩
  have e := vN _ (𝟙 _) z J hJ
  simp only [Category.id_comp, Over.id_left] at e
  exact (vu _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (val_mul hJ _ _ _) rfl)) e))

theorem coef_phi : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (w : Frm D.toPre F k p.g.b), w.IsGen → ∀ (g₀ g₁ : GtPtF D.toPre F), g₀.IsAdd p.g g₁ → ∀ ω₀ : Frm D.toPre F k g₀.b, ω₀.IsGen → ∃ ω₁ : Frm D.toPre F k g₁.b, ω₁.IsGen ∧ (g₀.IsZero → FrmOne ω₀ → ∀ z J, Good D.toPre.P.L z J → val ω₁ (𝟙 _) z J = val w (𝟙 _) z J) ∧ ∀ (n N : ℕ), 1 ≤ n → N = k * n → ∀ (q : QkPt D.toPre F N), q.y = n • p.y → q.g = p.g → ∀ (wN : Frm D.toPre F N q.g.b) (w₀ : Frm D.toPre F N g₀.b) (w₁ : Frm D.toPre F N g₁.b), (wN.IsGen ∧ ∀ z J, Good D.toPre.P.L z J → val wN (𝟙 _) z J = val w (𝟙 _) z J ^ n) → (w₀.IsGen ∧ ∀ z J, Good D.toPre.P.L z J → val w₀ (𝟙 _) z J = val ω₀ (𝟙 _) z J ^ n) → (w₁.IsGen ∧ ∀ z J, Good D.toPre.P.L z J → val w₁ (𝟙 _) z J = val ω₁ (𝟙 _) z J ^ n) → ∀ s s' : Fam D.toPre F N, PhiRel D.toPre F N q wN s s' → ∀ α, coef s' g₀ w₀ (α + q.y) = coef s g₁ w₁ α := by
  intro hL R _ _ _ I _ D F _ _ _ k _ p w hw g₀ g₁ hadd ω₀ h₀
  obtain ⟨hb, hs⟩ := (isAdd_iff _ _ _).1 hadd
  obtain ⟨ω₁, h₁, v₁⟩ := exists_frame p w hw g₀ ω₀ h₀ g₁.b hb
  refine ⟨ω₁, h₁, fun hz ho z J hJ => ?_, ?_⟩
  · have C : IsCub (th D.toPre (T := TF (R := R) F) z J) := isCub_cubV D.toPre.cub hJ
    obtain ⟨z₁, z₂⟩ := (isZero_iff _).1 hz
    have c : cubN (th D.toPre z J) k 1 p.g.b g₀.b = 1 := by rw [z₁, C.N_one]
    rw [v₁ z J hJ, ho.2 z J hJ, z₂ _ z J hJ, c, _root_.one_mul, _root_.mul_one, _root_.mul_one]
  · rintro n _ _ rfl ⟨qy, qg, qe⟩ hy hg wN w₀ w₁ ⟨hN, vN⟩ ⟨-, v₀⟩ ⟨hw₁, vw₁⟩ s s' hΦ α
    dsimp only at hy hg
    subst hy hg
    have H := (phiRel_iff hL.1.globalFns _ wN hN s s').1 hΦ
    refine coef_eq fun z J hJ => ?_
    have C : IsCub (th D.toPre (T := TF (R := R) F) z J) := isCub_cubV D.toPre.cub hJ
    have e₁ := H α _ rfl _ (lift (𝟙 (TF (R := R) F)) g₀.b) z J hJ
    have t : lift (𝟙 (TF (R := R) F)) g₀.b ≫ DegPre.trPt D.toPre F p.g.b = lift (𝟙 (TF (R := R) F)) g₁.b := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, tr_fst, lift_fst, lift_fst]
      · rw [lift_snd, hb, Category.assoc]
        refine (congrArg (_ ≫ ·) (tr_pr D.toPre F p.g.b)).trans ?_
        rw [MonObj.comp_mul, lift_fst_assoc, Category.id_comp, lift_snd]
    dsimp only at e₁ vN
    rw [t, uVal, lift_fst_assoc, lift_fst, lift_snd, Category.id_comp, Over.id_left, val_mul hJ, vN z J hJ,
      cubN_mul C] at e₁
    have e₂ := gt_nsmul (𝟙 (TF (R := R) F)) hJ g₀ α p.y n
    rw [Category.id_comp, Over.id_left, cPoint_y] at e₂
    have e₃ := hs α z J hJ
    rw [isCoef_coef g₁ hw₁ α s z J hJ]
    dsimp only
    rw [e₁, v₀ z J hJ, vw₁ z J hJ, v₁ z J hJ]
    simp only [_root_.mul_assoc, ← Units.val_mul]
    congr 2
    apply Additive.ofMul.injective
    have a₂ := congrArg Additive.ofMul e₂
    have a₃ := congrArg Additive.ofMul e₃
    simp only [ofMul_mul, ofMul_inv, ofMul_pow] at a₂ a₃ ⊢
    linear_combination (norm := module) a₃ - a₂

end GlobalTheory.UT.CoefPhi
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem comb_eq_zero_iff_expansion_comb_eq_zero : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ) (n : ℕ) (c : Fin n → R) (σ : Fin n → LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)))) (f : Fin n → ∀ α, D.toPre.SecB k α), (∀ i e, U.ExpandsAt e k (σ i) (f i)) → ((∀ j, ∑ i, resTop _ (scal G.hom (c i)) * (σ i).f j = 0) → ∀ α j, ∑ i, resTop _ (scal D.toPre.P.A.hom (c i)) * (f i α).f j = 0) ∧ (GeometricallyConnected G.hom → (∀ α j, ∑ i, resTop _ (scal D.toPre.P.A.hom (c i)) * (f i α).f j = 0) → ∀ j, ∑ i, resTop _ (scal G.hom (c i)) * (σ i).f j = 0) := by
  intro R _ _ I hR D A G _ _ U k n c σ f hE
  obtain ⟨hN, -, -, hC⟩ := hR
  have hI : I ≤ Ideal.jacobson ⊥ := IsAdicComplete.le_jacobson_bot I
  let σ₀ := ExpansionLinear.secComb (fun i => scal G.hom (c i)) σ
  let f₀ : ∀ α, D.toPre.SecB k α := fun α =>
    ExpansionLinear.secComb (fun i => scal D.toPre.P.A.hom (c i)) (fun i => f i α)
  have h₀ : ∀ e, U.ExpandsAt e k σ₀ f₀ := fun e =>
    expandsAt_linear R I D A G U k e n c σ f σ₀ f₀ (fun i => hE i e) (fun _ => rfl) (fun _ _ => rfl)
  refine ⟨fun h α => ?_, fun hG h => ?_⟩
  · have := D.toPre.P.isAb.smooth
    have := D.toPre.P.isAb.geomConnected
    refine (sec_eq_zero_and_hom_eq_of_thickenings R I hI D.toPre.P.A).1 _
      (DVR.linComb_isLB _ D.toPre.P.isLB _ _) (f₀ α) fun e j => ?_
    refine (ExtDiv.pG_app_eq_zero_iff (U.gt e) _ _).1
      (WeightPf.weightIndep R I D A G U e k σ₀ f₀ (fun j => ?_) (h₀ e) α j)
    exact (congrArg _ (h j)).trans (map_zero _)
  · have := U.smooth
    refine (sec_eq_zero_and_hom_eq_of_thickenings R I hI G).1 _
      (DVR.linComb_isLB _ U.LG.isLB _ _) σ₀ fun e j => ?_
    exact ClosedFibreTerm.vanish_of_terms_vanish U e k σ₀ f₀ (h₀ e)
      (fun α j => (congrArg _ (h α j)).trans (map_zero _)) j

end GlobalTheory
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PullDegCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification (CarriesAt PullIdent ptK_comp)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(X, U)ˣ) :
    res h₂ (res h₁ s) = res (h₂.trans h₁) s := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem res_self {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U) (s : Γ(X, U)ˣ) : res h s = s := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  have : (homOfLE h).op = 𝟙 _ := rfl
  rw [this, CategoryTheory.Functor.map_id]
  rfl

theorem res_eq_iff {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (h' : U ≤ V) (s t : Γ(X, U)ˣ) :
    res h s = res h t ↔ s = t :=
  ⟨fun e => by
    have := congrArg (res h') e
    rwa [res_res, res_res, res_self, res_self] at this, fun e => e ▸ rfl⟩

section Bundle

variable {X X' Y : Scheme.{0}} (L : LB X) (L' : LB X') (F : X' ⟶ X)

theorem corr_iff_eq (p : Y ⟶ X) (n : ℤ)
    (b c : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n))) :
    LB.Gen.Corr L _ _ _ _ b c ↔ b = c := by
  constructor
  · intro h
    obtain ⟨b⟩ := b
    obtain ⟨c⟩ := c
    congr 1
    funext j
    have := h j j (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    exact (res_eq_iff _ (le_inf le_rfl le_rfl) _ _).1 this
  · rintro rfl j j' _ _ h
    obtain rfl : j = j' := funext fun k => h k k rfl
    rfl

theorem exists_mapsAt_iff (w : LB.Iso L' (L.pull F)) (p' : Y ⟶ X') (p : Y ⟶ X) (hp : p' ≫ F = p) (n : ℤ)
    (a : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => p') (fun _ => n)))
    (c : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n))) :
    (∃ b : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p' ≫ F) (fun _ => n)),
      GeneratorPullback.MapsAt L L' (J := PUnit) (fun _ => F) w p' n a b ∧ LB.Gen.Corr L _ _ _ _ b c) ↔
    CarriesAt L L' F w p' p hp n a c := by
  subst hp
  constructor
  · rintro ⟨b, hb, hc⟩ j j'
    obtain rfl := (corr_iff_eq L _ n b c).1 hc
    exact hb (fun _ => j) j'
  · intro h
    exact ⟨c, fun jN jL => h (jN PUnit.unit) jL, (corr_iff_eq L _ n c c).2 rfl⟩

end Bundle

section Grp

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']

theorem rig_iff [IsCommMonObj G] [IsCommMonObj G'] (F : G'.left ⟶ G.left) (f : S' ⟶ S)
    (he : eSec G' ≫ F = f ≫ eSec G) (L : LB G.left) (L' : LB G'.left) (w : LB.Iso L' (L.pull F))
    (r : LB.Gen (L.pull (eSec G))) (r' : LB.Gen (L'.pull (eSec G'))) :
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G') (fun _ => 1)) r' (rigPullOf F f he L r) ↔
    CarriesAt L L' F w (eSec G') (f ≫ eSec G) he 1 r' (LB.pullGen L _ _ r f) := by
  have key : ∀ (j : L.ι) (j' : L'.ι),
      (res (inf_le_left : _ ⊓ (L'.pull (eSec G')).U (fun _ => j') ≤ _) ((rigPullOf F f he L r).s (fun _ _ => j)) =
        @id (Γ((𝟙_ (Over S')).left, ((L.pull F).pull (eSec G')).U (fun _ _ => j) ⊓ (L'.pull (eSec G')).U (fun _ => j'))ˣ)
          ((LB.linCombIso w (K := PUnit) (fun _ => eSec G') (fun _ => 1)).s (fun _ _ => j, fun _ => j')) *
          res inf_le_right (r'.s (fun _ => j'))) ↔
      res (GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.chart_le_target L L' F (eSec G') (f ≫ eSec G) he j j')
          ((LB.pullGen L _ _ r f).s (fun _ => j)) =
        (pullU (eSec G') _ (w.s (fun _ => j, j'))) ^ (1 : ℤ) *
          res (GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.chart_le_source L L' F (eSec G') j j') (r'.s (fun _ => j')) := by
    intro j j'
    have h₁ : ((L.pull F).pull (eSec G')).U (fun _ _ => j) ⊓ (L'.pull (eSec G')).U (fun _ => j') ≤
        eSec G' ⁻¹ᵁ (LB.div (L.pull F) L').U (fun _ => j, j') :=
      fun y hy => ⟨Set.mem_iInter.1 hy.1 PUnit.unit, Set.mem_iInter.1 hy.2 PUnit.unit⟩
    have h₂ : eSec G' ⁻¹ᵁ (LB.div (L.pull F) L').U (fun _ => j, j') ≤
        ((L.pull F).pull (eSec G')).U (fun _ _ => j) ⊓ (L'.pull (eSec G')).U (fun _ => j') :=
      fun y hy => ⟨Set.mem_iInter.2 fun _ => hy.1, Set.mem_iInter.2 fun _ => hy.2⟩
    rw [← res_eq_iff h₁ h₂, map_mul, map_zpow]
    refine Eq.congr ?_ (congrArg₂ (· * ·) (Fintype.prod_unique fun _ : PUnit =>
      res h₁ (pullU (eSec G') _ (w.s (fun _ => j, j'))) ^ (1 : ℤ)) ?_)
    · exact (res_res _ _ _).trans ((res_res _ _ _).trans (res_res _ _ _)).symm
    · exact (res_res _ _ _).symm
  exact ⟨fun h j j' => (key j j').1 (h (fun _ _ => j, fun _ => j')),
    fun h p => (key (p.1 PUnit.unit PUnit.unit) (p.2 PUnit.unit)).2 (h _ _)⟩

theorem isGrpPullback_iff {f : S' ⟶ S} {F : G'.left ⟶ G.left} (cart : IsPullback F G'.hom G.hom f) :
    IsGrpPullback G' G f F ↔ (μ[G']).left ≫ F =
      pullback.map G'.hom G'.hom G.hom G.hom F F f cart.w.symm cart.w.symm ≫ (μ[G]).left := by
  have m : ∀ (T : Over S') (x y : T ⟶ G') (x₀ y₀ : Over.mk (T.hom ≫ f) ⟶ G),
      x₀.left = x.left ≫ F → y₀.left = y.left ≫ F → (lift x₀ y₀).left = (lift x y).left ≫
        pullback.map G'.hom G'.hom G.hom G.hom F F f cart.w.symm cart.w.symm := by
    intro T x y x₀ y₀ hx hy
    apply pullback.hom_ext
    · have e₁ : (lift x₀ y₀).left ≫ pullback.fst G.hom G.hom = x₀.left := congrArg (·.left) (lift_fst x₀ y₀)
      have e₂ : (lift x y).left ≫ pullback.fst G'.hom G'.hom = x.left := congrArg (·.left) (lift_fst x y)
      refine e₁.trans (hx.trans ?_)
      rw [← e₂, Category.assoc, Category.assoc]
      exact congrArg _ (pullback.lift_fst _ _ _).symm
    · have e₁ : (lift x₀ y₀).left ≫ pullback.snd G.hom G.hom = y₀.left := congrArg (·.left) (lift_snd x₀ y₀)
      have e₂ : (lift x y).left ≫ pullback.snd G'.hom G'.hom = y.left := congrArg (·.left) (lift_snd x y)
      refine e₁.trans (hy.trans ?_)
      rw [← e₂, Category.assoc, Category.assoc]
      exact congrArg _ (pullback.lift_snd _ _ _).symm
  constructor
  · intro h
    have e := h.2 _ (fst G' G') (snd G' G') (pushPt cart.w _) (pushPt cart.w _) rfl rfl
    have e' := m _ (fst G' G') (snd G' G') (pushPt cart.w _) (pushPt cart.w _) rfl rfl
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp, Over.comp_left, e', lift_fst_snd, Over.id_left] at e
    exact e.symm.trans (congrArg (· ≫ _) (Category.id_comp _))
  · intro h
    refine ⟨cart, fun T x y x₀ y₀ hx hy => ?_⟩
    rw [Hom.mul_def, Hom.mul_def, Over.comp_left, Over.comp_left, m T x y x₀ y₀ hx hy, Category.assoc]
    exact (Category.assoc _ _ _).trans (congrArg _ h.symm)

end Grp

section Main

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

abbrev OpenChoice (φ : R →+* R') (D : DegPre R) : Type :=
  Σ W : (Spec (CommRingCat.of R)).Opens,
    PsiOn D W × {g : (TK R').left ⟶ (TW W).left // g ≫ W.ι = jK R' ≫ specOf φ}

def PsiCarried (p : PullIdent φ D D') (o : OpenChoice φ D) : Prop :=
  ∀ χ : D'.X, CarriesAt D.P.L D'.P.L p.F p.w (D'.xK χ) (o.2.2.1 ≫ (toUnit (TW o.1) ≫ D.c (p.xe χ)).left)
    (ptK_comp φ p.F (D.c (p.xe χ)) (D'.c χ) (p.c_eq χ) o.1 o.2.2.1 o.2.2.2) (-1) (D'.psi χ)
    (LB.pullGen D.P.L _ _ (o.2.1.psi (p.xe χ)) o.2.2.1)

def toOpenChoice (h : IsPullDeg φ D D') : OpenChoice φ D := ⟨h.W, h.psiW, h.g, h.g_comm⟩

theorem psi_pr_carries (h : IsPullDeg φ D D') (χ : D'.X) :
    CarriesAt D.P.L D'.P.L (h.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) h.w (D'.xK χ)
      (h.g ≫ (toUnit (TW h.W) ≫ D.c (h.xe χ)).left)
      (ptK_comp φ _ (D.c (h.xe χ)) (D'.c χ) (h.c_pr χ) h.W h.g h.g_comm) (-1) (D'.psi χ)
      (LB.pullGen D.P.L _ _ (h.psiW.psi (h.xe χ)) h.g) :=
  (exists_mapsAt_iff D.P.L D'.P.L _ h.w _ _ _ (-1) _ _).1 (h.psi_pr χ)

def toIdent (h : IsPullDeg φ D D') : PullIdent φ D D' where
  F := h.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)
  cart := (pull_grp h).1
  F_one := h.he
  F_mul := (isGrpPullback_iff (pull_grp h).1).1 (pull_grp h)
  w := h.w
  w_gen := h.w_gen
  w_rig := (rig_iff _ _ h.he _ _ h.w D.rig D'.rig).1 h.w_rig
  xe := h.xe
  c_eq := h.c_pr
  w_psi := ⟨h.W, h.psiW, h.g, h.g_comm, psi_pr_carries h⟩

theorem exists_toIdent_eq (p : PullIdent φ D D') (o : OpenChoice φ D) (H : PsiCarried p o) :
    ∃ h : IsPullDeg φ D D', toIdent h = p ∧ toOpenChoice h = o := by
  obtain ⟨e, me, he⟩ := grpPullback_iso ((isGrpPullback_iff p.cart).2 p.F_mul)
    (isGrpPullback_pullback D.P.A (specOf φ))
  obtain ⟨F, cart, F₁, Fm, w, wg, wr, xe, ce, wp⟩ := p
  dsimp only at he
  subst he
  exact ⟨⟨e, me, w, wg, F₁, (rig_iff _ _ F₁ _ _ w D.rig D'.rig).2 wr, xe, ce, o.1, o.2.1, o.2.2.1, o.2.2.2,
    fun χ => (exists_mapsAt_iff D.P.L D'.P.L _ w _ _ _ (-1) _ _).2 (H χ)⟩, rfl, rfl⟩

theorem toIdent_surjective : Function.Surjective (toIdent : IsPullDeg φ D D' → PullIdent φ D D') := fun p => by
  obtain ⟨W, ψW, g, hg, H⟩ := p.w_psi
  obtain ⟨h, e, -⟩ := exists_toIdent_eq p ⟨W, ψW, g, hg⟩ H
  exact ⟨h, e⟩

theorem nonempty_iff : Nonempty (IsPullDeg φ D D') ↔ Nonempty (PullIdent φ D D') :=
  ⟨fun ⟨h⟩ => ⟨toIdent h⟩, fun ⟨p⟩ => let ⟨h, _⟩ := toIdent_surjective p; ⟨h⟩⟩

end Main

end GlobalTheory.PullDegCompare
end
end
