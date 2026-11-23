module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsCommVOfLe
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1207
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2629
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle010
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1794
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2625
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1955
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2627
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1909
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2630
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ArtinPicGlue

theorem units_lift_of_surjective {R R₀ : Type} [CommRing R] [CommRing R₀] (hR : Nontrivial R₀ → IsLocalRing R) (g : R →+* R₀)
    (hg : Function.Surjective g) (r : R₀ˣ) : ∃ r' : Rˣ, g r' = r := by
  rcases subsingleton_or_nontrivial R₀ with h | h
  · exact ⟨1, Subsingleton.elim _ _⟩
  · haveI := hR h
    haveI : IsLocalHom g := IsLocalHom.of_surjective g hg
    obtain ⟨a, ha⟩ := hg r
    exact ⟨(isUnit_of_map_unit g a (ha ▸ r.isUnit)).unit, ha⟩

theorem units_lift_baseChange (P R₂ R₀ : CommRingCat.{0}) (f₂ : P ⟶ R₂) (g₂ : R₂ ⟶ R₀) (hR : Nontrivial R₀ → IsLocalRing R₂)
    (hg₂ : Function.Surjective g₂) (A : Over (Spec P)) [GrpObj A] (hA : IsAbelianScheme A) :
    Function.Surjective (Units.map (A ◁ (Over.homMk (Spec.map g₂) (by simp [Spec.map_comp]) :
      Over.mk (Spec.map (f₂ ≫ g₂)) ⟶ Over.mk (Spec.map f₂))).left.appTop.hom.toMonoidHom) := by
  have hpb : IsPullback (fst A (Over.mk (Spec.map (f₂ ≫ g₂)))).left (snd A (Over.mk (Spec.map (f₂ ≫ g₂)))).left
      A.hom (Over.mk (Spec.map (f₂ ≫ g₂))).hom := IsPullback.of_hasPullback _ _
  obtain ⟨G, -, hAb, -⟩ := GlobalTheory.AbCoh.exists_grpObj_isGrpPullback_of_isPullback P R₀ (f₂ ≫ g₂).hom A _ _ _ hpb
  letI := G
  have hbij := GlobalTheory.globalFns_holds _ _ (hAb hA)
  let e := RingEquiv.ofBijective _ hbij
  intro u
  let u₀ : Γ((Over.mk (snd A (Over.mk (Spec.map (f₂ ≫ g₂)))).left).left, ⊤) := u.1
  have hu' : IsUnit (e.symm u₀) := by have := u.isUnit.map e.symm; exact this
  have hr : IsUnit ((Scheme.ΓSpecIso R₀).hom.hom (e.symm u₀)) := hu'.map _
  obtain ⟨r₂, hr₂⟩ := units_lift_of_surjective hR g₂.hom hg₂ hr.unit
  have hv : IsUnit ((snd A (Over.mk (Spec.map f₂))).left.appTop.hom ((Scheme.ΓSpecIso R₂).inv.hom r₂)) :=
    (r₂.isUnit.map (Scheme.ΓSpecIso R₂).inv.hom).map _
  refine ⟨hv.unit, Units.ext ?_⟩
  have hw : (A ◁ (Over.homMk (Spec.map g₂) (by simp [Spec.map_comp]) :
      Over.mk (Spec.map (f₂ ≫ g₂)) ⟶ Over.mk (Spec.map f₂))).left ≫ (snd A (Over.mk (Spec.map f₂))).left =
      (snd A (Over.mk (Spec.map (f₂ ≫ g₂)))).left ≫ Spec.map g₂ := by
    rw [← Over.comp_left, whiskerLeft_snd]; rfl
  have hn := Scheme.ΓSpecIso_inv_naturality g₂
  have h1 : (Spec.map g₂).appTop.hom ((Scheme.ΓSpecIso R₂).inv.hom r₂) =
      (Scheme.ΓSpecIso R₀).inv.hom (g₂.hom r₂) := by
    have := congrArg (fun φ => φ.hom (r₂ : R₂)) hn
    exact this.symm
  have key : (Spec.map g₂).appTop.hom ((Scheme.ΓSpecIso R₂).inv.hom r₂) = e.symm u₀ := by
    rw [h1, hr₂, IsUnit.unit_spec]
    exact congrArg (fun φ => φ.hom (e.symm u₀)) (Scheme.ΓSpecIso R₀).hom_inv_id
  have h2 := congrArg (fun φ => φ.appTop.hom ((Scheme.ΓSpecIso R₂).inv.hom r₂)) hw
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h2
  simp only [Units.coe_map, IsUnit.unit_spec, MonoidHom.coe_coe]
  exact h2.trans ((congrArg _ key).trans (e.apply_symm_apply u₀))

theorem surjective_of_isPullback {P R₁ R₂ R₀ : CommRingCat.{0}} {f₁ : P ⟶ R₁} {f₂ : P ⟶ R₂} {g₁ : R₁ ⟶ R₀}
    {g₂ : R₂ ⟶ R₀} (h : IsPullback f₁ f₂ g₁ g₂) (hg₁ : Function.Surjective g₁) : Function.Surjective f₂ := by
  intro y
  obtain ⟨x, hx⟩ := hg₁ (g₂ y)
  have H := (Types.isPullback_iff _ _ _ _).1 (h.map (forget CommRingCat))
  obtain ⟨p, -, hp⟩ := H.2.2 x y hx
  exact ⟨p, hp⟩

theorem pic_eq_zero_of_pull_eq_zero : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (A : Over (Spec P)) [GrpObj A] (A₁ : Over (Spec R₁)) (A₂ : Over (Spec R₂)) (φ₁ : A₁.left ⟶ A.left) (φ₂ : A₂.left ⟶ A.left), IsAbelianScheme A → IsPullback φ₁ A₁.hom A.hom (Spec.map f₁) → IsPullback φ₂ A₂.hom A.hom (Spec.map f₂) → ∀ c : GlobalTheory.CechPic.Pic A.left, GlobalTheory.CechPic.pull φ₁ c = 0 → GlobalTheory.CechPic.pull φ₂ c = 0 → c = 0 := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ h hP _ hg₁ hg₂ A _ A₁ A₂ φ₁ φ₂ hA h₁ h₂ c hc₁ hc₂
  haveI : Flat A.hom := by have := hA.smooth; infer_instance
  have hf₂ := surjective_of_isPullback h hg₁
  have hloc : Nontrivial R₀ → IsLocalRing R₂ := fun _ => by
    haveI : Nontrivial R₂ := g₂.hom.domain_nontrivial
    exact IsLocalRing.of_surjective' f₂.hom hf₂
  let T : Over (Spec P) := Over.mk (𝟙 (Spec P))
  let T₁ : Over (Spec P) := Over.mk (Spec.map f₁)
  let T₂ : Over (Spec P) := Over.mk (Spec.map f₂)
  let T₀ : Over (Spec P) := Over.mk (Spec.map (f₂ ≫ g₂))
  let j₁ : T₁ ⟶ T := Over.homMk (Spec.map f₁) (by simp [T, T₁])
  let j₂ : T₂ ⟶ T := Over.homMk (Spec.map f₂) (by simp [T, T₂])
  let k₁ : T₀ ⟶ T₁ := Over.homMk (Spec.map g₁) (by simp only [T₀, T₁, Over.mk_hom]; rw [← Spec.map_comp, h.w])
  let k₂ : T₀ ⟶ T₂ := Over.homMk (Spec.map g₂) (by simp [T₀, T₂, Spec.map_comp])
  have hM : GlobalTheory.DualOpen.Milnor j₁.left j₂.left k₁.left k₂.left := GlobalTheory.DualOpen.Milnor.of_isPullback h hg₂
  have key := GlobalTheory.DualOpen.pic_eq_zero_of_milnor (Spec P) A T T₁ T₂ T₀ j₁ j₂ k₁ k₂ hM
    (units_lift_baseChange P R₂ R₀ f₂ g₂ hloc hg₂ A hA)
  let s : A ⟶ A ⊗ T := lift (𝟙 A) (Over.homMk A.hom (by simp [T]))
  have hs : s.left ≫ (fst A T).left = 𝟙 _ := by rw [← Over.comp_left, lift_fst]; rfl
  have hc : c = GlobalTheory.CechPic.pull s.left (GlobalTheory.CechPic.pull (fst A T).left c) := by
    rw [← GlobalTheory.CechPic.pull_comp, hs, GlobalTheory.CechPic.pull_id]
  rw [hc, key (GlobalTheory.CechPic.pull (fst A T).left c) ?_ ?_, map_zero]
  · rw [← GlobalTheory.CechPic.pull_comp, ← Over.comp_left, whiskerLeft_fst]
    have hm := h₁.lift_fst (fst A T₁).left (snd A T₁).left ((Over.w (fst A T₁)).trans (Over.w (snd A T₁)).symm)
    rw [← hm, GlobalTheory.CechPic.pull_comp, hc₁, map_zero]
  · rw [← GlobalTheory.CechPic.pull_comp, ← Over.comp_left, whiskerLeft_fst]
    have hm := h₂.lift_fst (fst A T₂).left (snd A T₂).left ((Over.w (fst A T₂)).trans (Over.w (snd A T₂)).symm)
    rw [← hm, GlobalTheory.CechPic.pull_comp, hc₂, map_zero]

end GlobalTheory.ArtinPicGlue
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DiagPairing

open GlobalTheory.CechPic

section Classes

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {P : LB (A ⊗ A).left} (hP : P.IsLB)

def pc {T : Over S} (a b : T ⟶ A) : Pic T.left := pull (lift a b).left (cls P hP)

variable (hB : ∀ (T : Over S) (x x' y : T ⟶ A), pc hP (x * x') y = pc hP x y + pc hP x' y)
  (hB' : ∀ (T : Over S) (x y y' : T ⟶ A), pc hP x (y * y') = pc hP x y + pc hP x y')

include hB in
theorem pc_pow_left {T : Over S} (x y : T ⟶ A) (k : ℕ) : pc hP (x ^ k) y = k • pc hP x y := by
  have one : pc hP (1 : T ⟶ A) y = 0 := by
    have := hB T 1 1 y
    rwa [_root_.mul_one, left_eq_add] at this
  induction k with
  | zero => rw [pow_zero, one, zero_smul]
  | succ k ih => rw [pow_succ, hB, ih, succ_nsmul]

include hB' in
theorem pc_pow_right {T : Over S} (x y : T ⟶ A) (k : ℕ) : pc hP x (y ^ k) = k • pc hP x y := by
  have one : pc hP x (1 : T ⟶ A) = 0 := by
    have := hB' T x 1 1
    rwa [_root_.mul_one, left_eq_add] at this
  induction k with
  | zero => rw [pow_zero, one, zero_smul]
  | succ k ih => rw [pow_succ, hB', ih, succ_nsmul]


include hB hB' in
theorem exists_theta_diag {k : ℕ} {T : Over S} (x : T ⟶ A) (hx : x ^ k = 1) :
    ∃ θ : Out.ThetaGrp A (P.pull (lift (𝟙 A) (𝟙 A)).left) k T, θ.pt = x := by
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have e : ∀ g : T ⊗ A ⟶ A, pull g.left (cls _ hD) = pc hP g g := fun g => by
    rw [cls_pull hP, ← pull_comp, ← Over.comp_left, comp_lift, Category.comp_id]
    rfl
  have ha : (fst T A ≫ x) ^ k = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  have h1 : k • pc hP (fst T A ≫ x) (fst T A ≫ x) = 0 := by
    rw [← pc_pow_left hP hB, ha]
    have := hB (T ⊗ A) 1 1 (fst T A ≫ x)
    rwa [_root_.mul_one, left_eq_add] at this
  have h2 : k • pc hP (fst T A ≫ x) (snd T A) = 0 := by
    rw [← pc_pow_left hP hB, ha]
    have := hB (T ⊗ A) 1 1 (snd T A)
    rwa [_root_.mul_one, left_eq_add] at this
  have h3 : k • pc hP (snd T A) (fst T A ≫ x) = 0 := by
    rw [← pc_pow_right hP hB', ha]
    have := hB' (T ⊗ A) (snd T A) 1 1
    rwa [_root_.mul_one, left_eq_add] at this
  obtain ⟨t, ht⟩ : ∃ t : LB.Gen (Out.thetaLB A (P.pull (lift (𝟙 A) (𝟙 A)).left) k x), t.IsGen := by
    refine (cls_eq_zero_iff (LB.isLB_linComb hD _ _)).1 ?_
    rw [cls_linComb hD, Fin.sum_univ_two]
    show (k : ℤ) • pull (snd T A).left _ + (-(k : ℤ)) • pull ((fst T A ≫ x) * snd T A).left _ = 0
    rw [e, e, hB, hB', hB']
    simp only [natCast_zsmul, neg_smul, smul_add, h1, h2, h3]
    abel
  exact ⟨⟨x, t, ht⟩, rfl⟩

end Classes

section Mul

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]


open WeilMul in
theorem weilIs_mul_left (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB) {k : ℤ}
    {T : Over S} {x x' y : T ⟶ A} {c c' : Γ(T.left, ⊤)ˣ} (h : Out.WeilIs A L k x y c)
    (h' : Out.WeilIs A L k x' y c') : Out.WeilIs A L k (x * x') y (c * c') := by
  intro p
  obtain ⟨V, hV, a₁, a₂⟩ := h p
  obtain ⟨V', hV', b₁, b₂⟩ := h' p
  obtain ⟨θx, θy, px, py, hc⟩ := exists_commV_of_le hL (inf_le_left : V ⊓ V' ≤ V) a₁ a₂
  obtain ⟨θx', θy', px', py', hc'⟩ := exists_commV_of_le hL (inf_le_right : V ⊓ V' ≤ V') b₁ b₂
  obtain ⟨θ, pθ, hθ⟩ := hc.mul hL (hc'.congr hG hA hL rfl (py.trans py'.symm))
  have q : θ.pt = Out.overResι (V ⊓ V') ≫ (x * x') := by rw [pθ, px, px', MonObj.comp_mul]
  refine ⟨V ⊓ V', ⟨hV, hV'⟩, ⟨θ, θy, q, py⟩, fun θ₁ θ₂ p₁ p₂ => ?_⟩
  exact (commIs_iff hL _ _ _ _).2 (hθ.congr hG hA hL (p₁.trans q.symm) (p₂.trans py.symm))

end Mul

end GlobalTheory.DiagPairing

namespace GlobalTheory.DiagPairing

open GlobalTheory.CechPic

theorem exists_weilIs_diag_root : ∀ (h n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) (s : S ⟶ Sp B)
    (c : SiegPre h n ζ s) (N : ℕ) (T : Over S) (x y : T ⟶ c.A), Out.RelAmple c.A c.diag → 0 < N →
    IsUnit (N : Γ(T.left, ⊤)) → x ^ N = 1 → y ^ N = 1 →
    ∃ c₀ : Γ(T.left, ⊤)ˣ, c₀ ^ N = 1 ∧ Out.WeilIs c.A c.diag N x y c₀ := by
  intro h n B _ ζ S s c N T x y hamp hN _ hx hy
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hD : c.diag.IsLB := pull_isLB c.isLB _
  have hB : ∀ (T : Over S) (x x' y : T ⟶ c.A), pc c.isLB (x * x') y = pc c.isLB x y + pc c.isLB x' y :=
    fun T x x' y => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S c.A c.diag c.ab hD hamp c.P c.isLB c.rig₁ c.rig₂
        T x x' y).1
      have e := (cls_eq_zero_iff (LB.isLB_linComb c.isLB _ _)).2 ⟨t, ht⟩
      rw [cls_linComb c.isLB, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hB' : ∀ (T : Over S) (x y y' : T ⟶ c.A), pc c.isLB x (y * y') = pc c.isLB x y + pc c.isLB x y' :=
    fun T x y y' => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S c.A c.diag c.ab hD hamp c.P c.isLB c.rig₁ c.rig₂
        T y y' x).2
      have e := (cls_eq_zero_iff (LB.isLB_linComb c.isLB _ _)).2 ⟨t, ht⟩
      rw [cls_linComb c.isLB, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have lifts : ∀ z : T ⟶ c.A, z ^ N = 1 → ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ θ : Out.ThetaGrp c.A c.diag N (Out.overRes V), θ.pt = Out.overResι V ≫ z := fun z hz p => by
    obtain ⟨θ, hθ⟩ := exists_theta_diag c.isLB hB hB' (k := N) (Out.overResι ⊤ ≫ z)
      (by rw [← MonObj.comp_pow, hz, MonObj.comp_one])
    exact ⟨⊤, trivial, θ, hθ⟩
  obtain ⟨c₀, hc₀⟩ := CommutatorPairing.exists_weilIs hG c.ab hD (lifts x hx) (lifts y hy)
  obtain ⟨c₁, hc₁⟩ := CommutatorPairing.exists_weilIs hG c.ab hD (lifts 1 (one_pow N)) (lifts y hy)
  have h11 := weilIs_mul_left hG c.ab hD hc₁ hc₁
  rw [_root_.mul_one] at h11
  have e₁ : c₁ * c₁ = c₁ := CommutatorPairing.weilIs_unique hG c.ab hD h11 hc₁
  have e₁' : c₁ = 1 := mul_eq_left.1 e₁
  have pw : ∀ m : ℕ, Out.WeilIs c.A c.diag N (x ^ (m + 1)) y (c₀ ^ (m + 1)) := by
    intro m
    induction m with
    | zero => simpa using hc₀
    | succ m ih =>
      rw [pow_succ x (m + 1), pow_succ c₀ (m + 1)]
      exact weilIs_mul_left hG c.ab hD ih hc₀
  have hp := pw (N - 1)
  rw [Nat.sub_add_cancel hN, hx] at hp
  exact ⟨c₀, CommutatorPairing.weilIs_unique hG c.ab hD hp (e₁' ▸ hc₁), hc₀⟩

end GlobalTheory.DiagPairing
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.kodairaSpencerUniqueValue_abelianScheme_field : GlobalTheory.Published.AbelianDeRham → ∀ {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) {g : ℕ}, Semi.IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → KSRegular h := by
  first | exact @GlobalTheory.DeRham.ksRegular_of_isAbelianScheme | exact GlobalTheory.DeRham.ksRegular_of_isAbelianScheme | (intros; apply GlobalTheory.DeRham.ksRegular_of_isAbelianScheme <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

theorem _root_.GlobalTheory.T.closedFibre_isAbelianScheme_relDim_of_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ι : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ι → IsAbelianScheme A ∧ SmoothOfRelativeDimension n A.hom := by
  first | exact @GlobalTheory.FibreAbDim.isAbelianScheme_and_relDim | exact GlobalTheory.FibreAbDim.isAbelianScheme_and_relDim | (intros; apply GlobalTheory.FibreAbDim.isAbelianScheme_and_relDim <;> assumption)
end

section

namespace GlobalTheory

theorem abelianDeRham_of_hodge_dual_poincare :
    GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.DualAbelianScheme →
      GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianDeRham :=
  fun h₁ h₂ h₃ => GlobalTheory.T.abelianSchemeDeRhamStructure_of_cube_dual_poincare h₁ GlobalTheory.T.theoremOfCubeAbelianScheme_over_arbitrary_base h₂ h₃

end GlobalTheory
end

section

theorem GlobalTheory.SqLift.abelianLifting_of_known_theorems :
    GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.CubeTheorem → GlobalTheory.Published.DualAbelianScheme →
      GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianUnobstructed →
      GlobalTheory.Published.AbelianLifting :=
  fun a b c d e =>
    GlobalTheory.SqLift.abelianLifting_of_schemeLifts (GlobalTheory.T.abelianSchemeDeRhamStructure_of_cube_dual_poincare a b c d) (GlobalTheory.T.abelianSchemeSquareZeroLifts_of_deRhamCohomology a) e
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor
open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.AbLaw

namespace GlobalTheory.KerCalc

attribute [local instance] Over.cartesianMonoidalCategory

theorem evc_pow_left {S : Scheme.{0}} {A B Y : Over S} [GrpObj A] [GrpObj B] {P : LB (A ⊗ B).left}
    (hP : P.IsLB) (h : IsAdditive P) (a : Y ⟶ A) (b : Y ⟶ B) (n : ℕ) :
    evc hP (a ^ n) b = n • evc hP a b := by
  induction n with
  | zero => rw [pow_zero, zero_smul, h.evc_one hP]
  | succ n ih => rw [pow_succ, (isAdditive_iff hP).1 h, ih, succ_nsmul]

end GlobalTheory.KerCalc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegelTor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PrinThicken

open GlobalTheory.AbDual GlobalTheory.CechPic

theorem evc_comm {S : Scheme.{0}} {X Y : Over S} {M : LB (X ⊗ X).left} (hM : M.IsLB)
    (hc : cls M hM = CechPic.pull (lift (snd X X) (fst X X)).left (cls M hM)) (a b : Y ⟶ X) :
    evc hM a b = evc hM b a := by
  rw [evc, evc]
  conv_lhs => rw [hc]
  rw [← pull_comp, ← Over.comp_left, comp_lift, lift_snd, lift_fst]

end GlobalTheory.PrinThicken
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor
open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.AbLaw

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CubeAxes

variable {S : Scheme.{0}} {G : Over S} [GrpObj G]

theorem lift_mul_lift {Y : Over S} (a a' b b' : Y ⟶ G) : lift a b * lift a' b' = lift (a * a') (b * b') := by
  ext <;> simp [MonObj.mul_comp]

theorem cube_cls (hG : IsAbelianScheme G) {P : LB (G ⊗ G).left} (hP : P.IsLB) {Y : Over S} (a b c : Y ⟶ G ⊗ G) :
    CechPic.pull (a * b * c).left (cls P hP) - CechPic.pull (a * b).left (cls P hP) - CechPic.pull (a * c).left (cls P hP)
      - CechPic.pull (b * c).left (cls P hP) + CechPic.pull a.left (cls P hP) + CechPic.pull b.left (cls P hP)
      + CechPic.pull c.left (cls P hP) - CechPic.pull (1 : Y ⟶ G ⊗ G).left (cls P hP) = 0 := by
  have hGG := AbelianSchemeGerms.isAbelianScheme_tensor G G hG hG
  have T := GlobalTheory.CubeTop.cubeTheorem S (G ⊗ G) hGG P hP Y a b c
  have z := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 T
  rw [cls_linComb hP] at z
  simp only [Fin.sum_univ_eight, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at z
  rw [← z]
  abel

theorem additive_of_triv_axes : ∀ {S : Scheme.{0}} {G : Over S} [GrpObj G], IsAbelianScheme G →
    ∀ {P : LB (G ⊗ G).left} (hP : P.IsLB), (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → IsAdditive P ∧ IsAdditive (swap P) := by
  intro S G _ hG P hP h₁ h₂
  have l : ∀ {Y : Over S} (a : Y ⟶ G), evc hP 1 a = 0 := fun a ↦ evc_one_left hP h₁ a
  have r : ∀ {Y : Over S} (a : Y ⟶ G), evc hP a 1 = 0 := fun a ↦ evc_one_right hP h₂ a
  have o : ∀ {Y : Over S}, (1 : Y ⟶ G ⊗ G) = lift 1 1 := by
    intro Y
    ext <;> simp
  refine ⟨(isAdditive_iff hP).2 fun Y x x' y ↦ ?_, (GlobalTheory.BirigidLift.isAdditive_swap_iff hP).2 fun Y x y y' ↦ ?_⟩
  · have e := cube_cls hG hP (lift x 1) (lift x' 1) (lift 1 y)
    simp only [lift_mul_lift, _root_.mul_one, _root_.one_mul, o] at e
    change evc hP (x * x') y - evc hP (x * x') 1 - evc hP x y - evc hP x' y + evc hP x 1 + evc hP x' 1
      + evc hP 1 y - evc hP 1 1 = 0 at e
    rw [r, r, r, r, l] at e
    rw [← sub_eq_zero, ← e]
    abel
  · have e := cube_cls hG hP (lift 1 y) (lift 1 y') (lift x 1)
    simp only [lift_mul_lift, _root_.mul_one, _root_.one_mul, o] at e
    change evc hP x (y * y') - evc hP 1 (y * y') - evc hP x y - evc hP x y' + evc hP 1 y + evc hP 1 y'
      + evc hP x 1 - evc hP 1 1 = 0 at e
    rw [l, l, l, l, r] at e
    rw [← sub_eq_zero, ← e]
    abel

end GlobalTheory.CubeAxes
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

theorem _root_.GlobalTheory.T.exists_logCanonicalMultiple_of_globally_klt : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p →
  topologicalKrullDim X = n → ∀ Δ : X → ℚ, IsEffQDiv Δ → (∀ y, KltAt p n Δ y) →
  ∃ (m : ℕ) (G : CartierDiv X), 0 < m ∧ IsLogCanonicalMultiple p n Δ m G := by
  first | exact @GlobalTheory.Discrepancy.exists_isLogCanonicalMultiple_of_kltAt | exact GlobalTheory.Discrepancy.exists_isLogCanonicalMultiple_of_kltAt | (intros; apply GlobalTheory.Discrepancy.exists_isLogCanonicalMultiple_of_kltAt <;> assumption)
end
