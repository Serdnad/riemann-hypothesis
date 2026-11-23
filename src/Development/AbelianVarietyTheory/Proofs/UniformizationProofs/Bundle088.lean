module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle080
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle081
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle078
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle079
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RepSymInv
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle070
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle016
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic

@[expose] public section

open AlgebraicGeometry CategoryTheory in
noncomputable local instance (priority := high) grpObjPullbackForUniformization088
    {S T : Scheme.{0}} (f : T ⟶ S) (G : Over S) [GrpObj G] : GrpObj ((Over.pullback f).obj G) :=
  letI : (Over.pullback f).Monoidal := (Over.instBraidedPullback (f := f)).toMonoidal
  Functor.grpObjObj (F := Over.pullback f)

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.product_support_in_subgroup_theta : (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (Λ : AddSubgroup D.X) (k l : ℕ) (σ : U.SecGT (𝟙_ _) k) (σ' : U.SecGT (𝟙_ _) l) (σ'' : U.SecGT (𝟙_ _) (k + l)) f f' f'', U.ExpT (𝟙_ _) k σ f → U.ExpT (𝟙_ _) l σ' f' → U.ExpT (𝟙_ _) (k + l) σ'' f'' → (∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ _ ⊗ G).left) (z : Z) (J), Good U.P.L.L z J → sval σ'' r z J = sval σ r z J * sval σ' r z J) → (∀ α ∉ Λ, ∀ j, (f α).f j = 0) → (∀ α ∉ Λ, ∀ j, (f' α).f j = 0) → ∀ α ∉ Λ, ∀ j, (f'' α).f j = 0) := by
  first | exact @GlobalTheory.MulSupp.main | exact GlobalTheory.MulSupp.main | (intros; apply GlobalTheory.MulSupp.main <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.AddCoeff
open ReciprocityTheory.ChartRestriction.G.DVR

theorem sum_diff_inj {X : Type} [AddCommGroup X] [Module.Free ℤ X] {a b a' b' : X} (h₁ : a + b = a' + b')
    (h₂ : a - b = a' - b') : a = a' ∧ b = b' := by
  have e : (2 : ℤ) • a = (2 : ℤ) • a' := by
    rw [two_smul, two_smul]
    calc a + a = (a + b) + (a - b) := by abel
      _ = a' + a' := by rw [h₁, h₂]; abel
  have ha : a = a' := smul_right_injective X two_ne_zero e
  subst ha
  exact ⟨rfl, add_left_cancel h₁⟩

theorem reindex {X R : Type} [AddCommGroup X] [Module.Free ℤ X] [CommRing R] (s₀ s : Finset X)
    (hs : ∀ a ∈ s₀, ∀ b ∈ s₀, a + b ∈ s ∧ a - b ∈ s) (F g c : X → X → R)
    (hF : ∀ a b, a ∉ s₀ ∨ b ∉ s₀ → F a b = 0) (g₁ : ∀ a b, g (a + b) (a - b) = F a b)
    (g₀ : ∀ α β, (¬ ∃ a b, α = a + b ∧ β = a - b) → g α β = 0) :
    ∑ α ∈ s, ∑ β ∈ s, g α β * c α β = ∑ a ∈ s₀, ∑ b ∈ s₀, F a b * c (a + b) (a - b) := by
  classical
  rw [← Finset.sum_product', ← Finset.sum_product']
  symm
  refine Finset.sum_of_injOn (fun p : X × X => (p.1 + p.2, p.1 - p.2)) ?_ ?_ ?_ ?_
  · intro p _ q _ h
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
    exact Prod.ext (sum_diff_inj h₁ h₂).1 (sum_diff_inj h₁ h₂).2
  · intro p hp
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.1 hp
    exact Finset.mem_product.2 (hs _ h₁ _ h₂)
  · rintro ⟨α, β⟩ _ hp
    by_cases h : ∃ a b, α = a + b ∧ β = a - b
    · obtain ⟨a, b, rfl, rfl⟩ := h
      have : a ∉ s₀ ∨ b ∉ s₀ := by
        by_contra hc
        push Not at hc
        exact hp ⟨(a, b), Finset.mem_coe.2 (Finset.mem_product.2 hc), rfl⟩
      simp only [g₁, hF a b this, zero_mul]
    · simp only [g₀ α β h, zero_mul]
  · intro p _
    simp only [g₁]

section
variable {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem sval_zero_of (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval s r z J = 0 := by
  refine (congrArg (gs r z (LB.wchart L φ (fun k => J (r ≫ φ k)))) (h _)).trans ((gs_eq r z _ (hJ.mem φ r) _).trans ?_)
  exact (congrArg _ (map_zero _)).trans (map_zero _)

theorem gs_scal {R : Type} [CommRing R] (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z) (c : R) :
    gs r z ⊤ (scal p c) = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := by
  calc gs r z ⊤ (scal p c) = gs (𝟙 _ ≫ r) z ⊤ (scal p c) := by rw [Category.id_comp]
    _ = gs (𝟙 _) z (r ⁻¹ᵁ ⊤) ((r.app ⊤).hom (scal p c)) := (gs_pull (𝟙 _) r z ⊤ (by trivial) _).symm
    _ = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := rfl

theorem exists_sub_scale (s t : LB.Sec (LB.LinComb L φ ε)) (c : Γ(Y, ⊤)) : ∃ d : LB.Sec (LB.LinComb L φ ε),
    ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      sval d r z J = sval s r z J - gs r z ⊤ c * sval t r z J := by
  refine ⟨SecOps.secAdd s (SecOps.secNeg (SecOps.secScale c t)), fun Z r z J hJ => ?_⟩
  have hm := hJ.mem φ r
  have e : sval (SecOps.secScale c t) r z J = gs r z ⊤ c * sval t r z J :=
    (gs_mul r z _ hm _ _).trans (congrArg (· * _) (gs_res r z le_top hm c))
  have e' : ∀ u : LB.Sec (LB.LinComb L φ ε), sval (SecOps.secNeg u) r z J = - sval u r z J := fun u =>
    (gs_eq r z _ hm _).trans (((congrArg _ (map_neg _ _)).trans (map_neg _ _)).trans
      (congrArg Neg.neg (gs_eq r z _ hm _).symm))
  refine (gs_add r z _ hm _ _).trans ?_
  rw [sub_eq_add_neg, ← e, ← e']
  rfl
end

theorem main : GlobalFnsSt → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (θ : U.SecGT (𝟙_ _) 1) (f₀ : ∀ α, SecBT D (𝟙_ _) 1 α) (r : V) (n : ℕ) (σ σ' : Fin n → U.SecGT (𝟙_ _) 2) (f f' : Fin n → ∀ α, SecBT D (𝟙_ _) 2 α), U.AddG θ r σ σ' → U.ExpT (𝟙_ _) 1 θ f₀ → (∀ i, U.ExpT (𝟙_ _) 2 (σ i) (f i) ∧ U.ExpT (𝟙_ _) 2 (σ' i) (f' i)) → AddB D (𝟙_ _) f₀ r f f') := by
  classical
  intro hGF V _ _ _ hV D A G _ _ U θ f₀ r n σ σ' f f' hA hθ hσ
  have hlev := GlobalTheory.addition_formula_expanded_at_level hGF V hV D A G U θ f₀ r n σ σ' f f' hA hθ hσ
  have hbox := GlobalTheory.UU.BoxSec.main V D (𝟙_ _) (toUnit _)
  have hd : ∀ p : D.X × D.X, ∃ d : LB.Sec (LB.LinComb D.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun i => (fst D.P.A D.P.A).left ≫ D.famφB p.1 i) (fun i => (snd D.P.A D.P.A).left ≫ D.famφB p.2 i)) (Sum.elim (DegPre.famε 2) (DegPre.famε 2))),
      ∀ (T : Over (Spec (CommRingCat.of V))) (x y : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J →
        (∀ a b, p.1 = a + b → p.2 = a - b → sval d (lift x y).left z J =
          ∑ i, sval (f i p.1) (lift (toUnit T) x).left z J * sval (f' i p.2) (lift (toUnit T) y).left z J -
          gs (𝟙 _) z ⊤ (scal T.hom r) * (kapV D a b z J x y).val *
            (sval (f₀ a) (lift (toUnit T) (x * y)).left z J * sval (f₀ b) (lift (toUnit T) (x * y⁻¹)).left z J)) ∧
        ((¬ ∃ a b, p.1 = a + b ∧ p.2 = a - b) → sval d (lift x y).left z J =
          ∑ i, sval (f i p.1) (lift (toUnit T) x).left z J * sval (f' i p.2) (lift (toUnit T) y).left z J) := by
    rintro ⟨α, β⟩
    obtain ⟨d₁, h₁⟩ := (hbox α β).1 n (fun i => f i α) (fun i => f' i β)
    simp only [comp_toUnit] at h₁
    by_cases h : ∃ a b, α = a + b ∧ β = a - b
    · obtain ⟨a, b, ha, hb⟩ := h
      obtain ⟨d₂, h₂⟩ := (hbox α β).2 a b (f₀ a) (f₀ b) ha hb
      simp only [comp_toUnit] at h₂
      obtain ⟨d, hd⟩ := exists_sub_scale d₁ d₂ (scal (D.P.A ⊗ D.P.A).hom r)
      refine ⟨d, fun T x y z J hJ => ⟨fun a' b' ha' hb' => ?_, fun h => absurd ⟨a, b, ha, hb⟩ h⟩⟩
      obtain ⟨rfl, rfl⟩ := sum_diff_inj (ha.symm.trans ha') (hb.symm.trans hb')
      rw [hd _ _ z J hJ, h₁ T x y z J hJ, h₂ T x y z J hJ, gs_scal, Over.w, _root_.mul_assoc]
    · exact ⟨d₁, fun T x y z J hJ => ⟨fun a b ha hb => absurd ⟨a, b, ha, hb⟩ h, fun _ => h₁ T x y z J hJ⟩⟩
  choose d hd using hd
  have h0 := GlobalTheory.WeightTwo.main V hV D A G U 2 2 d (fun e => by
    obtain ⟨s₀, H⟩ := hlev e
    refine ⟨s₀ ∪ Finset.image₂ (· + ·) s₀ s₀ ∪ Finset.image₂ (· - ·) s₀ s₀,
      fun s hs T x y xe ye hx hy hxy z J hJ => ?_⟩
    obtain ⟨H₁, H₂⟩ := H T x y xe ye hx hy hxy z J hJ
    have hs₀ : s₀ ⊆ s := (Finset.subset_union_left.trans Finset.subset_union_left).trans hs
    have R := reindex s₀ s (fun a ha b hb =>
        ⟨hs (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image₂_of_mem ha hb))),
          hs (Finset.mem_union_right _ (Finset.mem_image₂_of_mem ha hb))⟩)
      (fun a b => gs (𝟙 _) z ⊤ (scal T.hom r) * (kapV D a b z J x y).val *
        (sval (f₀ a) (lift (toUnit T) (x * y)).left z J * sval (f₀ b) (lift (toUnit T) (x * y⁻¹)).left z J))
      (fun α β => ∑ i, sval (f i α) (lift (toUnit T) x).left z J * sval (f' i β) (lift (toUnit T) y).left z J -
        sval (d (α, β)) (lift x y).left z J)
      (fun α β => (val ((U.gt e).t α) xe z J).val * (val ((U.gt e).t β) ye z J).val)
      (by
        rintro a b (h | h)
        · rw [(H₁ a h).1, zero_mul, mul_zero]
        · rw [(H₁ b h).2, mul_zero, mul_zero])
      (fun a b => by rw [(hd (a + b, a - b) T x y z J hJ).1 a b rfl rfl, sub_sub_cancel])
      (fun α β h => by rw [(hd (α, β) T x y z J hJ).2 h, sub_self])
    rw [← H₂ s hs₀] at R
    simp only [sub_mul, Finset.sum_sub_distrib] at R
    exact sub_eq_self.1 R)
  intro T ρ x y z J hJ
  obtain rfl : ρ = toUnit T := toUnit_unique _ _
  refine ⟨fun a b α β hα hβ => ?_, fun α β h => ?_⟩
  · exact sub_eq_zero.1 (((hd (α, β) T x y z J hJ).1 a b hα hβ).symm.trans (sval_zero_of _ (h0 _) _ z hJ))
  · exact ((hd (α, β) T x y z J hJ).2 h).symm.trans (sval_zero_of _ (h0 _) _ z hJ)

end GlobalTheory.AddCoeff
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.abelianPart_image_one_mul_inv : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (W : Type) [CommRing W] [Algebra V W] (x x' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G) (b b' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ ((1 : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G)).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ ((1 : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B)).left) ∧ ((∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b).left) → (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x').left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b').left) → (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x * x').left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b * b').left) ∧ (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x⁻¹).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b⁻¹).left)) := by
  first | exact @GlobalTheory.UU.image_one_mul_inv | exact GlobalTheory.UU.image_one_mul_inv | (intros; apply GlobalTheory.UU.image_one_mul_inv <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.cubicalWeilPairing_eq_abelianPart_image : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W → IsLocalHom (algebraMap V W) → ∀ (N : ℕ) (x x' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G) (b b' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B) (ζ), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b).left) → (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x').left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b').left) → b ^ N = 1 → b' ^ N = 1 → CubWeil s.P.c N x x' ζ → CubWeil a.M.c N b b' ζ := by
  first | exact @GlobalTheory.UU.ImagePairing.cubWeil_image | exact GlobalTheory.UU.ImagePairing.cubWeil_image | (intros; apply GlobalTheory.UU.ImagePairing.cubWeil_image <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.generic_fibre_card_torsion_cubical_pairing_perfect : Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (N : ℕ), 1 ≤ N → Nat.card {x : TF (R := V) F ⟶ G // x ^ N = 1} = N ^ (2 * A.g) ∧ ∀ x : TF (R := V) F ⟶ G, x ^ N = 1 → (∀ y : TF (R := V) F ⟶ G, y ^ N = 1 → CubWeil s.P.c N x y 1) → x = 1 := by
  first | exact @GlobalTheory.UU.generic_card_and_nondeg | exact GlobalTheory.UU.generic_card_and_nondeg | (intros; apply GlobalTheory.UU.generic_card_and_nondeg <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.existsUnique_abelianPart_image_adicComplete_point : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W → IsLocalHom (algebraMap V W) → ∀ x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G, ∃! b : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b).left) := by
  first | exact @GlobalTheory.UU.PointImage.main | exact GlobalTheory.UU.PointImage.main | (intros; apply GlobalTheory.UU.PointImage.main <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU.ExpLinC

theorem gs_sum' {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (hm : r z ∈ U) {K : Type} (S : Finset K)
    (a : K → Γ(Y, U)) : gs r z U (∑ i ∈ S, a i) = ∑ i ∈ S, gs r z U (a i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have h := gs_add r z U hm 0 0
    rw [add_zero] at h
    simpa using h
  | insert i S hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, gs_add r z U hm, ih]

theorem sval_lincomb {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {n : ℕ}
    {t : Fin n → LB.Sec (LB.LinComb L φ ε)} {t' : LB.Sec (LB.LinComb L φ ε)} (a : Fin n → Γ(Y, ⊤))
    (h : ∀ j, t'.f j = ∑ i, (Y.presheaf.map (homOfLE le_top).op).hom (a i) * (t i).f j)
    (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval t' r z J = ∑ i, gs r z ⊤ (a i) * sval (t i) r z J := by
  have hm := hJ.mem φ r
  refine (congrArg (gs r z _) (h _)).trans ?_
  refine (gs_sum' _ _ _ hm _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
  exact (gs_mul _ _ _ hm _ _).trans (congrArg (· * _) (gs_res r z le_top hm (a i)))

theorem expF_lincomb : (AllPre fun {V} _ _ _ {D} {A} {_} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k n : ℕ) (c : Fin n → F) (t : Fin n → LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := V) F))) (s : Fin n → Raw D F k) (t' : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := V) F))) (s' : Raw D F k), (∀ i, U.ExpF F k (t i) (s i)) → (∀ j, t'.f j = ∑ i, liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i)) * (t i).f j) → (∀ α j, (s' α).f j = ∑ i, DegPre.constBF D F (c i) _ * (s i α).f j) → U.ExpF F k t' s') := by
  intro V _ _ _ _ D A G _ _ U F _ _ k n c t s t' s' H ht hs
  choose m a σ f h1 h2 h3 using H
  let e : Fin (Fintype.card (Σ i, Fin (m i))) ≃ (Σ i, Fin (m i)) := (Fintype.equivFin _).symm
  refine ⟨_, fun p => c (e p).1 * a (e p).1 (e p).2, fun p => σ (e p).1 (e p).2, fun p => f (e p).1 (e p).2,
    fun p => h1 _ _, fun Z rA y rG e1 e2 z JA JG hA hG => ?_, fun α Z rF rB e0 z J hJ => ?_⟩
  · rw [e.sum_comp (fun q => gs rA z ⊤ (scal (fst (TFK (R := V) F) A.A).left (c q.1 * a q.1 q.2)) *
      sval (σ q.1 q.2) rG z JG), Fintype.sum_sigma,
      sval_lincomb (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := V) F) A.A).left) (ε := fun _ => (k : ℤ))
        (fun i => scal (fst (TFK (R := V) F) A.A).left (c i)) ht rA z hA, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ExpLin.gs_scal_mul, _root_.mul_assoc]
    rw [← Finset.mul_sum, ← h2 i Z rA y rG e1 e2 z JA JG hA hG]
    ring
  · rw [e.sum_comp (fun q => gs rF z ⊤ (scal (fst (TF (R := V) F) D.P.A).left (c q.1 * a q.1 q.2)) *
      sval (f q.1 q.2 α) rB z J), Fintype.sum_sigma]
    refine (sval_lincomb (fun i => scal (fst (TF (R := V) F) D.P.A).left (c i)) (hs α) rF z hJ).trans ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ExpLin.gs_scal_mul, _root_.mul_assoc]
    rw [← Finset.mul_sum, ← h3 i α Z rF rB e0 z J hJ]

end GlobalTheory.UU.ExpLinC
end
end

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.BaseExpansionExists

section General
variable {X X₁ X₂ Y Y' Z : Scheme.{0}} {L : LB X} {L₁ : LB X₁} {L₂ : LB X₂} {K : Type} [Fintype K]

theorem exists_pull {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)} {ε : K → ℤ} (h : Y' ⟶ Y) (e : ∀ i, φ' i = h ≫ φ i)
    (s : LB.Sec (LB.LinComb L φ ε)) : ∃ s' : LB.Sec (LB.LinComb L φ' ε),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) J, Good L z J → sval s' r z J = sval s (r ≫ h) z J := by
  obtain rfl : φ' = fun i => h ≫ φ i := funext e
  exact ⟨_, fun Z r z J hJ => H1.SectionArithmetic.sval_pullSec s h r z hJ⟩

theorem exists_carry (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (hw : w.IsGen) (k : ℕ)
    (s : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => f₁) (fun _ => (k : ℤ)))) :
    ∃ τ : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ))),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J₁ J₂, Good L₁ z J₁ → Good L₂ z J₂ →
        sval τ r z J₂ = (gw w r z (J₂ (r ≫ f₂)) (fun _ => J₁ (r ≫ f₁))).val ^ k * sval s r z J₁ := by
  obtain ⟨τ, hτ⟩ := GenericFibreSections.exists_transfer hL₁ hL₂ f₁ f₂ k
    (fun i j => (L₂.pull f₂).U (fun _ => j) ⊓ (L₁.pull f₁).U (fun _ => i))
    (fun i j y hi hj => ⟨mem_pull.2 hj, mem_pull.2 hi⟩)
    (fun i j => (show Γ(Y, (L₂.pull f₂).U (fun _ => j) ⊓ (L₁.pull f₁).U (fun _ => i))ˣ from
      w.s (fun _ => j, fun _ => i)) ^ k) (fun y i i' j j' hi hi' hj hj' => by
      have e := GenericFibreSections.gw_trans hw y hi hi' hj hj'
      rw [map_pow, map_pow, zpow_natCast, zpow_natCast, ← mul_pow, ← mul_pow]
      exact congrArg (· ^ k) e) s
  refine ⟨τ, fun Z r z J₁ J₂ h₁ h₂ => ?_⟩
  rw [hτ Z r z J₁ J₂ h₁ h₂, map_pow, Units.val_pow_eq_pow_val]
  rfl

theorem sval_zero {φ : K → (Y ⟶ X)} {ε : K → ℤ} {s : LB.Sec (LB.LinComb L φ ε)} (h : ∀ j, s.f j = 0)
    (r : Z ⟶ Y) {z : Z} {J} (hJ : Good L z J) : sval s r z J = 0 :=
  (congrArg (gs r z _) (h _)).trans ((gs_eq r z _ (hJ.mem φ r) _).trans
    ((congrArg _ (map_zero _)).trans (map_zero _)))

theorem zero_of_sval (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {s : LB.Sec (LB.LinComb L φ ε)}
    (h : ∀ y J, Good L y J → sval s (𝟙 Y) y J = 0) (j) : s.f j = 0 := by
  refine fn_ext fun y hy => ?_
  obtain ⟨J, hJ, e⟩ := sval_trans hL s y j hy
  rw [h y J hJ, mul_zero] at e
  exact e.trans ((gs_eq (𝟙 Y) y _ hy _).trans ((congrArg _ (map_zero _)).trans (map_zero _))).symm

theorem sval_eq_of_id {Y₁ : Scheme.{0}} {K' : Type} [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {φ' : K' → (Y₁ ⟶ X)} {ε' : K' → ℤ} {s : LB.Sec (LB.LinComb L φ ε)} {s' : LB.Sec (LB.LinComb L φ' ε')}
    {p : Y' ⟶ Y} {p' : Y' ⟶ Y₁} (h : ∀ y J, Good L y J → sval s p y J = sval s' p' y J)
    (r : Z ⟶ Y') (z : Z) {J} (hJ : Good L z J) : sval s (r ≫ p) z J = sval s' (r ≫ p') z J := by
  obtain ⟨h₀, h₁, -⟩ := values_natural X Y Y' Z L K φ ε p r z J hJ
  obtain ⟨-, h₂, -⟩ := values_natural X Y₁ Y' Z L K' φ' ε' p' r z J hJ
  rw [h₁, h₂, h _ _ h₀]

theorem sum_of_id {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] {N : Type} {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {φ₁ : N → K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {φ₂ : N → K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ}
    {τ : LB.Sec (LB.LinComb L φ ε)} {f : ∀ α, LB.Sec (LB.LinComb L (φ₁ α) ε₁)}
    {t : ∀ α, LB.Gen (LB.LinComb L (φ₂ α) ε₂)} {q : Y ⟶ Y'} {S : Finset N}
    (h : ∀ y J, Good L y J → sval τ (𝟙 Y) y J = ∑ α ∈ S, sval (f α) q y J * (val (t α) (𝟙 Y) y J).val)
    (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval τ r z J = ∑ α ∈ S, sval (f α) (r ≫ q) z J * (val (t α) r z J).val := by
  obtain ⟨h₀, h₁, -⟩ := values_natural X Y Y Z L K φ ε (𝟙 Y) r z J hJ
  have a := h₁ τ

  rw [Category.comp_id, h _ _ h₀, map_sum] at a
  refine a.trans (Finset.sum_congr rfl fun α _ => ?_)
  have b := (values_natural X Y' Y Z L K₁ (φ₁ α) ε₁ q r z J hJ).2.1 (f α)
  have c := (values_natural X Y Y Z L K₂ (φ₂ α) ε₂ (𝟙 Y) r z J hJ).2.2.1 (t α)
  rw [Category.comp_id] at c
  rw [map_mul, b, c]

end General

section Levels
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

omit [GrpObj G] [IsCommMonObj G] in
theorem thickMap_fst (e : ℕ) : thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem thickMap_prBe (e : ℕ) : thickMap R I e D.P.A ≫ (D.prBe I (e + 1)).left = (D.prBe I e).left :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem q_thickMap (U : PreU I D A G) (e : ℕ) :
    (U.gt e).q.left ≫ thickMap R I e D.P.A = thickMap R I e G ≫ (U.gt (e + 1)).q.left := by
  refine pullback.hom_ext ?_ ?_
  · exact (Category.assoc _ _ _).trans ((congrArg ((U.gt e).q.left ≫ ·) (thickMap_prBe e)).trans
      ((U.gt_q e).symm.trans (Category.assoc _ _ _).symm))
  · have a : (U.gt e).q.left ≫ pullback.snd D.P.A.hom (thick R I e) = pullback.snd G.hom (thick R I e) :=
      Over.w (U.gt e).q
    have b : (U.gt (e + 1)).q.left ≫ pullback.snd D.P.A.hom (thick R I (e + 1)) =
      pullback.snd G.hom (thick R I (e + 1)) := Over.w (U.gt (e + 1)).q
    have c : ∀ H : Over (Spec (CommRingCat.of R)), thickMap R I e H ≫ pullback.snd H.hom (thick R I (e + 1)) =
      pullback.snd H.hom (thick R I e) ≫ thickTrans R I e := fun H => pullback.lift_snd _ _ _
    exact (Category.assoc _ _ _).trans ((congrArg ((U.gt e).q.left ≫ ·) (c _)).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ thickTrans R I e) a).trans ((c G).symm.trans
        ((congrArg (thickMap R I e G ≫ ·) b.symm).trans (Category.assoc _ _ _).symm)))))

theorem famφT_eq (T : Over (Spec (CommRingCat.of R))) (α : D.X) (i : Fin 4) :
    famφT D T α i = (snd T D.P.A).left ≫ D.famφB α i := by
  fin_cases i
  · exact (Category.comp_id _).symm
  · show (padd D.P.A (snd T D.P.A) (toUnit _ ≫ D.c α)).left =
      (snd T D.P.A ≫ padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left
    congr 1
    rw [padd, padd, ← Category.assoc, comp_lift, Category.comp_id, ← Category.assoc, comp_toUnit]
  · show (toUnit (T ⊗ D.P.A) ≫ D.c α).left = (snd T D.P.A ≫ toUnit D.P.A ≫ D.c α).left
    congr 1
    simp
  · show (toUnit (T ⊗ D.P.A) ≫ η[D.P.A]).left = (snd T D.P.A ≫ toUnit D.P.A ≫ η[D.P.A]).left
    congr 1
    simp

end Levels

theorem main : Laws → Laws2 → (AllPre fun U => ∀ k, 1 ≤ k → ∀ σ, ∃ f, U.ExpT (𝟙_ _) k σ f) := by
  intro h1 h2 V _ _ _ hV D A G _ _ U k hk σ
  have hB := D.P.isLB
  have hG := U.P.L.isLB
  have lam : (snd (𝟙_ _) G).left ≫ (λ_ G).inv.left = 𝟙 _ := by
    rw [← Over.comp_left, ← leftUnitor_hom, Iso.hom_inv_id, Over.id_left]
  have lam' : (λ_ G).inv.left ≫ (snd (𝟙_ _) G).left = 𝟙 _ := by
    rw [← Over.comp_left, ← leftUnitor_hom, Iso.inv_hom_id, Over.id_left]

  have lev : ∀ e : ℕ, ∃ τ : LB.Sec (LB.LinComb D.P.L (K := Fin 1) (fun _ => (U.gt e).pG.left) (fun _ => (k : ℤ))),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left) (z : Z) JG J,
        Good U.P.L.L z JG → Good D.P.L z J →
        sval τ r z J = (gw (U.w e) r z (J (r ≫ (U.gt e).pG.left))
          (fun _ => JG (r ≫ (fstG (IsLocalRing.maximalIdeal V) e G).left))).val ^ k *
          sval σ ((r ≫ (fstG (IsLocalRing.maximalIdeal V) e G).left) ≫ (λ_ G).inv.left) z JG := fun e => by
    obtain ⟨s, hs⟩ := exists_pull (φ' := fun _ : Fin 1 => (fstG (IsLocalRing.maximalIdeal V) e G).left)
      ((fstG (IsLocalRing.maximalIdeal V) e G).left ≫ (λ_ G).inv.left)
      (fun _ => by rw [Category.assoc, lam', Category.comp_id]) σ
    obtain ⟨τ, hτ⟩ := exists_carry hG hB (U.w e) (U.w_gen e) k s
    refine ⟨τ, fun Z r z JG J hJG hJ => (hτ Z r z JG J hJG hJ).trans (congrArg _ ((hs Z r z JG hJG).trans ?_))⟩
    exact congrArg (fun p => sval σ p z JG) (Category.assoc _ _ _).symm
  choose τ hτ using lev
  have ex := fun e => GlobalTheory.T.existsUnique_thickTorus_level_weight_expansion V _ D e G (U.gt e) k (τ e)
  choose f hf hu using ex
  choose S hS hsum using hf

  have compat : ∀ α e z J, Good D.P.L z J →
      sval (f (e + 1) α) (thickMap V _ e D.P.A) z J = sval (f e α) (𝟙 _) z J := by
    intro α e
    choose f' hf' using fun β => exists_pull
      (φ' := fun i => (D.prBe (IsLocalRing.maximalIdeal V) e).left ≫ D.famφB β i) (thickMap V _ e D.P.A)
      (fun i => ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ D.famφB β i) (thickMap_prBe e))).symm) (f (e + 1) β)
    have E : f' = f e := by
      refine hu e f' ⟨S (e + 1), fun β hβ => zero_of_sval hB fun y J hJ =>
        (hf' β _ _ y J hJ).trans (sval_zero (hS _ β hβ) _ hJ), fun z J hJ => ?_⟩
      obtain ⟨JG, hJG⟩ := exists_good_pt hG z
      have a := sum_of_id (hsum (e + 1)) (thickMap V _ e G) z hJ
      have b : sval (τ e) (𝟙 (thickObj V (IsLocalRing.maximalIdeal V) e G).left) z J =
          sval (τ (e + 1)) (thickMap V _ e G) z J := by
        refine (hτ e _ _ z JG J hJG hJ).trans (Eq.trans ?_ (hτ (e + 1) _ _ z JG J hJG hJ).symm)
        have c := U.w_compat e _ (𝟙 _) z _ _ (hJ (U.gt e).pG.left) (hJG (fstG (IsLocalRing.maximalIdeal V) e G).left)
        rw [Category.id_comp] at c
        rw [U.gt_q, thickMap_fst, c]
        simp only [Category.id_comp]
      refine b.trans (a.trans (Finset.sum_congr rfl fun β _ => congrArg₂ (· * ·) ?_ (congrArg Units.val ?_)))
      · exact (congrArg (fun p => sval (f (e + 1) β) p z J) (q_thickMap U e).symm).trans (hf' β _ _ z J hJ).symm
      · exact ((congrArg (fun p => val ((U.gt (e + 1)).t β) p z J) (Category.id_comp _).symm).trans
          (val_pull hJ _ _ _).symm).trans (val_corr hJ (U.gt_t e β) _)
    intro z J hJ
    rw [← E]
    exact ((hf' α _ _ z J hJ).trans (congrArg (fun p => sval (f (e + 1) α) p z J) (Category.id_comp _))).symm
  choose s hs _ using fun α => GlobalTheory.T.existsUnique_twistedSection_of_compatible_levels h1 h2 V hV D k hk α (fun e => f e α) (compat α)
  choose F hF using fun α => exists_pull (snd (𝟙_ _) D.P.A).left (famφT_eq (𝟙_ _) α) (s α)
  refine ⟨F, fun e => ⟨S e, fun Z x rG rB hrG hrB _ z JG J hJG hJ => ?_⟩⟩
  have v : ∀ α, sval (F α) rB z J = sval (f e α) (x ≫ (U.gt e).q.left) z J := fun α => by
    refine (hF α _ _ z J hJ).trans ?_
    have a := sval_eq_of_id (hs α e) (x ≫ (U.gt e).q.left) z hJ
    refine Eq.trans (congrArg (fun p => sval (s α) p z J) (hrB.trans (Category.assoc _ _ _).symm)) (a.trans ?_)
    exact congrArg (fun p => sval (f e α) p z J) (Category.comp_id _)
  refine ⟨fun α hα => (v α).trans (sval_zero (hS e α hα) _ hJ), ?_⟩
  have r : rG = (x ≫ (fstG (IsLocalRing.maximalIdeal V) e G).left) ≫ (λ_ G).inv.left := by
    rw [← hrG, Category.assoc, lam, Category.comp_id]
  rw [r]
  refine (hτ e _ x z JG J hJG hJ).symm.trans ((sum_of_id (hsum e) x z hJ).trans ?_)
  exact Finset.sum_congr rfl fun α _ => congrArg (· * _) (v α).symm

end GlobalTheory.BaseExpansionExists
end
end
