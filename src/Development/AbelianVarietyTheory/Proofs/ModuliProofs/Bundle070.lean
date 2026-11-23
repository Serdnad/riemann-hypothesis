module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle065
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle064
public import Mathlib.NumberTheory.Padics.Complex
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle067
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenMove
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilIsogeny

open CommutatorPairing

section Gen

variable {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε ε' : K → ℤ}

theorem wchart_le_pow (d : ℕ) (j : K → L.ι) : LB.wchart L φ j ≤ LB.wchart (lbPow L d) φ (fun k _ => j k) :=
  fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy k

theorem exists_gen_of_lbPow (d : ℕ) (hε : ∀ k, ε' k = ε k * d) (a : LB.Gen (LB.LinComb (lbPow L d) φ ε))
    (ha : a.IsGen) : ∃ u : LB.Gen (LB.LinComb L φ ε'), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι), r z ∈ LB.wchart L φ j →
        gm r z (LB.wchart L φ j) (u.s j) = gm r z (LB.wchart (lbPow L d) φ (fun k _ => j k)) (a.s fun k _ => j k) := by
  refine ⟨⟨fun j => res (wchart_le_pow d j) (a.s fun k _ => j k)⟩, fun j j' => unit_ext fun y hy => ?_,
    fun Z r z j hj => gm_res r z _ hj _⟩
  refine (gm_res _ y _ hy _).trans ((gm_res _ y _ hy.1 _).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_linComb L φ ε' (𝟙 Y) y j j' hy.1 hy.2)
      ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.2 _)))).symm))
  refine (gen_trans ha (𝟙 Y) y (wchart_le_pow d j hy.1) (wchart_le_pow d j' hy.2)).trans (congrArg (· * _) ?_)
  refine Finset.prod_congr rfl fun k _ => ?_
  have e := gm_linComb L (fun _ : PUnit => 𝟙 X) (fun _ => (d : ℤ)) (𝟙 Y ≫ φ k) y (fun _ => j k) (fun _ => j' k)
    (Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy.1 k) (Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy.2 k)
  rw [Fintype.prod_unique, Category.comp_id] at e
  refine (congrArg (· ^ ε k) e).trans ?_
  rw [hε, mul_comm (ε k), zpow_mul]

theorem exists_gen_pow (d : ℕ) (hε : ∀ k, ε' k = ε k * d) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L φ ε'), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), val u r z J = val t r z J ^ d := by
  refine ⟨⟨fun j => t.s j ^ d⟩, fun i j => ?_, fun Z r z J => map_pow _ _ _⟩
  have h := congrArg (· ^ d) (ht i j)
  simp only [mul_pow, ← map_pow] at h
  refine h.trans (congrArg₂ (· * ·) ?_ rfl)
  refine (Finset.prod_pow _ _ _).symm.trans (Finset.prod_congr rfl fun a _ => ?_)
  exact ((zpow_natCast _ _).symm.trans (zpow_mul _ _ _).symm).trans (congrArg _ (hε a).symm)

theorem exists_gen_move_pow {X₀ Y₀ : Scheme.{0}} {M : LB X₀} {F : X ⟶ X₀} (hL : L.IsLB) (hM : M.IsLB) {d : ℕ}
    (w : LB.Iso (lbPow L d) (M.pull F)) (hw : w.IsGen) (hε : ∀ k, ε' k = ε k * d) {φ₀ : K → (Y₀ ⟶ X₀)} (h : Y ⟶ Y₀)
    (hc : ∀ k, φ k ≫ F = h ≫ φ₀ k) (t : LB.Gen (LB.LinComb M φ₀ ε)) (ht : t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L φ ε'), u.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J J₀),
      Good L z J → Good M z J₀ → val t (r ≫ h) z J₀ =
        (∏ k, (fun χ : Z ⟶ X => gw w χ z (J₀ (χ ≫ F)) (fun _ => J χ)) (r ≫ φ k) ^ ε k) * val u r z J := by
  obtain ⟨b, hb, hm⟩ := H1.exists_gen_move hM (DVR.linComb_isLB L hL _ _) w ((isGen_iff w).1 hw) φ₀ φ ε h hc t ht
  obtain ⟨u, hu, hv⟩ := exists_gen_of_lbPow d hε b hb
  refine ⟨u, hu, fun Z r z J J₀ hJ hJ₀ => ?_⟩
  have m := hm _ r z (fun i => J₀ ((r ≫ φ i) ≫ F)) (fun i _ => J (r ≫ φ i))
    (fun i => hJ₀ ((r ≫ φ i) ≫ F)) (fun i => Set.mem_iInter.2 fun _ => hJ (r ≫ φ i))
  exact (val_of t _ z J₀ _ (fun i => congrArg J₀ (by rw [Category.assoc, Category.assoc, hc]))).trans
    (m.trans (congrArg (_ * ·) (hv _ r z _ (hJ.mem φ r)).symm))

end Gen

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}

theorem weilIs_of_local (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {k : ℤ} {T : Over S}
    {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ}
    (h : ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ θx θy : ThetaGrp A L k (overRes V),
      θx.pt = overResι V ≫ x ∧ θy.pt = overResι V ≫ y ∧ CommIsOf A L k θx θy (unitRes V c)) :
    WeilIs A L k x y c := by
  intro p
  obtain ⟨V, hV, θx, θy, ex, ey, H⟩ := h p
  refine ⟨V, hV, ⟨θx, θy, ex, ey⟩, fun θ θ' e e' => (commIsOf_iff hL _ _ _).2 fun Z t b z J hJ => ?_⟩
  exact (commVal_indep hG hA hL θ θ' θx θy t t (by rw [e, ex]) (by rw [e', ey]) b z J hJ).trans
    ((commIsOf_iff hL _ _ _).1 H _ t b z J hJ)

theorem exists_theta_pow (d : ℕ) {n : ℤ} {T : Over S} (θ : ThetaGrp A L n T) :
    ∃ θ' : ThetaGrp A L (n * d) T, θ'.pt = θ.pt ∧ ∀ (Z : Over S) (t : Z ⟶ T) (a : Z ⟶ A) (z : Z.left) (J),
      thetaVal θ' t a z J = thetaVal θ t a z J ^ d := by
  obtain ⟨u, hu, hv⟩ := exists_gen_pow (L := L) (K := Fin 2) (φ := ![(snd T A).left, (translPt A θ.pt).left])
    (ε := ![n, -n]) (ε' := ![n * d, -(n * d)]) d (fun k => by fin_cases k <;> simp) θ.φ θ.isGen
  exact ⟨⟨θ.pt, u, hu⟩, rfl, fun Z t a z J => hv _ _ z J⟩

theorem weilIs_pow (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) (d : ℕ) {n : ℤ} {T : Over S}
    {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ} (h : WeilIs A L n x y c) : WeilIs A L (n * d) x y (c ^ d) := by
  refine weilIs_of_local hG hA hL fun p => ?_
  obtain ⟨V, hV, ⟨θx, θy, ex, ey⟩, H⟩ := h p
  obtain ⟨θx', fx, vx⟩ := exists_theta_pow d θx
  obtain ⟨θy', fy, vy⟩ := exists_theta_pow d θy
  refine ⟨V, hV, θx', θy', fx.trans ex, fy.trans ey, (commIsOf_iff hL _ _ _).2 fun Z t a z J hJ => ?_⟩
  have e := (commIsOf_iff hL _ _ _).1 (H θx θy ex ey) Z t a z J hJ
  have e' : unitRes V (c ^ d) = unitRes V c ^ d := map_pow _ _ _
  rw [e', map_pow, ← e, commVal, commVal, vx, vx, vy, vy, fx, fy]
  simp only [mul_pow, inv_pow]

theorem exists_theta_pull (hL : L.IsLB) (hM : M.IsLB) (ψ : A ⟶ B) [IsMonHom ψ] {d : ℕ}
    (w : LB.Iso (lbPow L d) (M.pull ψ.left)) (hw : w.IsGen) {n : ℤ} {T : Over S} (x : T ⟶ A)
    (θ₀ : ThetaGrp B M n T) (hx : θ₀.pt = x ≫ ψ) :
    ∃ θ : ThetaGrp A L (n * d) T, θ.pt = x ∧ ∀ (Z : Over S) (t : Z ⟶ T) (a : Z ⟶ A) (z : Z.left) (J J₀),
      Good L z J → Good M z J₀ → thetaVal θ₀ t (a ≫ ψ) z J₀ =
        gw w a.left z (J₀ (a ≫ ψ).left) (fun _ => J a.left) ^ n *
          gw w ((t ≫ x) * a).left z (J₀ (((t ≫ x) * a) ≫ ψ).left) (fun _ => J ((t ≫ x) * a).left) ^ (-n) *
          thetaVal θ t a z J := by
  have hl : ∀ {Z : Over S} (t : Z ⟶ T) (a : Z ⟶ A), lift t a ≫ (T ◁ ψ) = lift t (a ≫ ψ) := fun t a => by simp
  have h₀ : snd T A ≫ ψ = (T ◁ ψ) ≫ snd T B := by simp
  have h₁ : translPt A x ≫ ψ = (T ◁ ψ) ≫ translPt B θ₀.pt := by
    show ((fst T A ≫ x) * snd T A) ≫ ψ = (T ◁ ψ) ≫ ((fst T B ≫ θ₀.pt) * snd T B)
    rw [MonObj.comp_mul, MonObj.mul_comp, hx]
    simp
  have hc : ∀ i : Fin 2, ![(snd T A).left, (translPt A x).left] i ≫ ψ.left =
      (T ◁ ψ).left ≫ ![(snd T B).left, (translPt B θ₀.pt).left] i := fun i => by
    fin_cases i
    · exact congrArg CommaMorphism.left h₀
    · exact congrArg CommaMorphism.left h₁
  obtain ⟨u, hu, hv⟩ := exists_gen_move_pow (ε := ![n, -n]) (ε' := ![n * d, -(n * d)]) hL hM w hw
    (fun k => by fin_cases k <;> simp) (T ◁ ψ).left hc θ₀.φ θ₀.isGen
  refine ⟨⟨x, u, hu⟩, rfl, fun Z t a z J J₀ hJ hJ₀ => ?_⟩
  have m := hv _ (lift t a).left z J J₀ hJ hJ₀
  rw [← Over.comp_left, hl, prod_theta x t a
    (fun χ : Z.left ⟶ A.left => gw w χ z (J₀ (χ ≫ ψ.left)) (fun _ => J χ))] at m
  exact m

theorem weilIs_pull_hom (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) (hM : M.IsLB) (ψ : A ⟶ B)
    [IsMonHom ψ] {d : ℕ} (hw : LBIso (lbPow L d) (M.pull ψ.left)) {n : ℤ} {T : Over S} {x y : T ⟶ A}
    {c : Γ(T.left, ⊤)ˣ} (h : WeilIs B M n (x ≫ ψ) (y ≫ ψ) c) : WeilIs A L (n * d) x y c := by
  obtain ⟨w, hw⟩ := hw
  have := hA.comm
  refine weilIs_of_local hG hA hL fun p => ?_
  obtain ⟨V, hV, ⟨θx₀, θy₀, ex, ey⟩, H⟩ := h p
  obtain ⟨θx, fx, vx⟩ := exists_theta_pull hL hM ψ w hw (overResι V ≫ x) θx₀ (by rw [ex, Category.assoc])
  obtain ⟨θy, fy, vy⟩ := exists_theta_pull hL hM ψ w hw (overResι V ≫ y) θy₀ (by rw [ey, Category.assoc])
  refine ⟨V, hV, θx, θy, fx, fy, (commIsOf_iff hL _ _ _).2 fun Z t a z J hJ => ?_⟩
  choose J₀ hJ₀ using fun χ : Z.left ⟶ B.left => exists_chart hM (χ z)
  have e := (commIsOf_iff hM _ _ _).1 (H θx₀ θy₀ ex ey) Z t (a ≫ ψ) z J₀ hJ₀
  have gx : (t ≫ θx₀.pt) * (a ≫ ψ) = ((t ≫ overResι V ≫ x) * a) ≫ ψ := by
    rw [MonObj.mul_comp, ex]; simp only [Category.assoc]
  have gy : (t ≫ θy₀.pt) * (a ≫ ψ) = ((t ≫ overResι V ≫ y) * a) ≫ ψ := by
    rw [MonObj.mul_comp, ey]; simp only [Category.assoc]
  rw [← e, commVal, commVal, gx, gy, vx _ _ _ _ _ _ hJ hJ₀, vx _ _ _ _ _ _ hJ hJ₀, vy _ _ _ _ _ _ hJ hJ₀,
    vy _ _ _ _ _ _ hJ hJ₀, fx, fy, mul_left_comm (t ≫ overResι V ≫ y) (t ≫ overResι V ≫ x) a]
  simp only [zpow_neg]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.WeilIsogeny

namespace GlobalTheory

theorem weilIs_along_hom : Out.GlobalFnsSt → ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (ψ : A ⟶ B)
    (L : LB A.left) (M : LB B.left) (d : ℕ) (n : ℤ) (T : Over S) (x y : T ⟶ A) (c c' : Γ(T.left, ⊤)ˣ),
    IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → IsMonHom ψ → LBIso (lbPow L d) (M.pull ψ.left) →
    Out.WeilIs B M n (x ≫ ψ) (y ≫ ψ) c' →
      Out.WeilIs A L (n * d) x y c' ∧ (Out.WeilIs A L n x y c → c' = c ^ d) := by
  intro hG S A B _ _ ψ L M d n T x y c c' hA _ hL hM hψ hw h
  have h' := WeilIsogeny.weilIs_pull_hom hG hA hL hM ψ hw h
  exact ⟨h', fun hc => CommutatorPairing.weilIs_unique hG hA hL h' (WeilIsogeny.weilIs_pow hG hA hL d hc)⟩

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_descends_etale_cover : ∀ (K : Type) [Field K] (X Y : Scheme.{0}) (π : X ⟶ Y) (s : Y ⟶ Sp K) (d : ℕ), Etale π → Surjective π → LocallyOfFiniteType s → SmoothOfRelativeDimension d (π ≫ s) → SmoothOfRelativeDimension d s := by
  first | exact @GlobalTheory.SmoothDescent.smoothOfRelativeDimension_of_etale_cover | exact GlobalTheory.SmoothDescent.smoothOfRelativeDimension_of_etale_cover | (intros; apply GlobalTheory.SmoothDescent.smoothOfRelativeDimension_of_etale_cover <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.SmoothNearFibre

open GlobalTheory.VeryDenseFibres

private lemma smoothOfRelativeDimension_pullback_snd_restrict {Z S T : Scheme.{0}} (s : Z ⟶ S) (t : T ⟶ S) (W : Z.Opens)
    (g : ℕ) (h : SmoothOfRelativeDimension g (pullback.snd s t)) :
    SmoothOfRelativeDimension g (pullback.snd (W.ι ≫ s) t) := by
  rw [← pullbackRightPullbackFstIso_inv_snd_snd s t W.ι,
    MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension g)]
  exact IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension g) h _

private lemma smoothOfRelativeDimension_opensRange_ι_comp' {U Z S : Scheme.{0}} (i : U ⟶ Z) [IsOpenImmersion i] (s : Z ⟶ S)
    (g : ℕ) (h : SmoothOfRelativeDimension g (i ≫ s)) :
    SmoothOfRelativeDimension g (i.opensRange.ι ≫ s) := by
  rw [← i.isoOpensRange_inv_comp, Category.assoc,
    MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension g)]
  exact h

theorem exists_opens_of_flat {R : CommRingCat.{0}} {Z T : Scheme.{0}} (s : Z ⟶ Spec R)
    [LocallyOfFinitePresentation s] [Flat s] (t : T ⟶ Spec R) (g : ℕ)
    (h : SmoothOfRelativeDimension g (pullback.snd s t)) (z : Z) (w : T) (hw : s z = t w) :
    ∃ W : Z.Opens, z ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ s) := by
  have : Smooth (pullback.snd s t) := SmoothOfRelativeDimension.smooth g _
  have hF : Smooth ((pullback.snd s t).fiberToSpecResidueField w) := by
    unfold Scheme.Hom.fiberToSpecResidueField
    infer_instance
  have hF' : Smooth (s.fiberToSpecResidueField (s z)) := by
    rw [hw]
    exact smooth_fiber_of_smooth_fiber s t w hF
  have hz : z ∈ s.smoothLocus := mem_smoothLocus_of_smooth_fiber s z hF'
  have : Smooth (s.smoothLocus.ι ≫ s) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    ext a
    simp
  have h' : SmoothOfRelativeDimension g (pullback.snd (s.smoothLocus.ι ≫ s) t) :=
    smoothOfRelativeDimension_pullback_snd_restrict s t _ g h
  obtain ⟨V, hV, hVg⟩ :=
    exists_opens_smoothOfRelativeDimension (s.smoothLocus.ι ≫ s) t g h' ⟨z, hz⟩ w (by simpa using hw)
  refine ⟨(V.ι ≫ s.smoothLocus.ι).opensRange, ⟨⟨⟨z, hz⟩, hV⟩, by simp⟩, ?_⟩
  apply smoothOfRelativeDimension_opensRange_ι_comp'
  simpa using hVg

theorem smoothOfRelativeDimension_pullback_snd {Z S T : Scheme.{0}} (s : Z ⟶ S) (t : T ⟶ S) (g : ℕ)
    (h : ∀ (z : Z) (w : T), s z = t w →
      ∃ W : Z.Opens, z ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ s)) :
    SmoothOfRelativeDimension g (pullback.snd s t) := by
  have hb := smoothOfRelativeDimension_isStableUnderBaseChange (n := g)
  have key : ∀ p : ↥(pullback s t), ∃ U : (pullback s t).Opens,
      p ∈ U ∧ SmoothOfRelativeDimension g (U.ι ≫ pullback.snd s t) := by
    intro p
    have hc : s (pullback.fst s t p) = t (pullback.snd s t p) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    obtain ⟨W, hzW, hW⟩ := h _ _ hc
    let e := pullbackRightPullbackFstIso s t W.ι
    let j := e.inv ≫ pullback.snd W.ι (pullback.fst s t)
    have hj : j ≫ pullback.snd s t = pullback.snd (W.ι ≫ s) t := by
      simp [j, e]
    refine ⟨j.opensRange, ?_, ?_⟩
    · obtain ⟨q, -, hq2⟩ := Scheme.Pullback.exists_preimage_pullback
        (f := W.ι) (g := pullback.fst s t) ⟨_, hzW⟩ p (by simp)
      refine ⟨e.hom q, ?_⟩
      rw [← Scheme.Hom.comp_apply]
      simpa [j] using hq2
    · rw [← j.isoOpensRange_inv_comp, Category.assoc, hj,
        MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension g)]
      exact MorphismProperty.pullback_snd _ _ hW
  choose U hU hP using key
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) U ?_ hP
  rw [eq_top_iff]
  intro p _
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨p, hU p⟩

theorem exists_smoothOfRelativeDimension_of_isUnit :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (g : ℕ) (K : Type) [Field K] (x : R →+* K), IsProper s → Flat s → SmoothOfRelativeDimension g (pullback.snd s (spMap x)) → ∃ f : R, x f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) → SmoothOfRelativeDimension g (pullback.snd s (spMap φ)) := by
  intro R _ _ Z s g K _ x hprop hflat hsm
  have : LocallyOfFinitePresentation s := inferInstance
  let U : Z.Opens := sSup {W : Z.Opens | SmoothOfRelativeDimension g (W.ι ≫ s)}
  have hpt : ∀ w : Sp K, ∀ z : Z, (s z).asIdeal = RingHom.ker x → z ∈ U := by
    intro w z hz
    have hzw : s z = spMap x w := PrimeSpectrum.ext (by rw [hz, spMap_apply_asIdeal])
    obtain ⟨W, hzW, hW⟩ :=
      exists_opens_of_flat (R := CommRingCat.of R) s (spMap x) g hsm z w hzw
    exact TopologicalSpace.Opens.mem_sSup.mpr ⟨W, hW, hzW⟩
  let w₀ : Sp K := IsLocalRing.closedPoint K
  let C : Set (Sp R) := s '' (U : Set Z)ᶜ
  have hC : IsClosed C := s.isClosedMap _ U.isOpen.isClosed_compl
  have hp : spMap x w₀ ∈ Cᶜ := by
    rintro ⟨z, hzU, hzp⟩
    apply hzU
    apply hpt w₀ z
    rw [hzp, spMap_apply_asIdeal]
  obtain ⟨_, ⟨f, rfl⟩, hpf, hfC⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp hC.isOpen_compl
  refine ⟨f, ?_, ?_⟩
  · intro hf0
    apply hpf
    show f ∈ (spMap x w₀).asIdeal
    rw [spMap_apply_asIdeal]
    exact hf0
  · intro R' _ φ hφ
    apply smoothOfRelativeDimension_pullback_snd
    intro z w hzw
    have hzU : z ∈ U := by
      by_contra hzU
      have hmem : s z ∈ C := ⟨z, hzU, rfl⟩
      apply hfC (PrimeSpectrum.mem_basicOpen _ _ |>.mpr ?_) hmem
      rw [hzw]
      show f ∉ (PrimeSpectrum.comap (CommRingCat.ofHom φ).hom w).asIdeal
      intro hfw
      exact w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hfw hφ)
    obtain ⟨W, hW, hzW⟩ := TopologicalSpace.Opens.mem_sSup.mp hzU
    exact ⟨W, hzW, hW⟩

end GlobalTheory.SmoothNearFibre
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.PsiNormPull

theorem valF_eq_valR' {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (f : Γ(X, U)) :
    valF x U f = valR x U f := by
  rfl

theorem toStk_map_valR {A F : Type} [CommRing A] [Field F] (ψ : A →+* F) {X : Scheme.{0}} (x : Sp A ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (z : Sp F) (a : Γ(X, U)ˣ) :
    toStk z (ψ (valR x U a.val)) = (gm (spMap ψ ≫ x) z U a).val := by
  obtain ⟨h', e⟩ := CrdCalc.valR_spMap ψ x U h
  rw [← e, ← valF_eq_valR']
  exact toStk_valF _ U z (h' trivial) a

theorem norm_eq_one_of_isUnit {A F : Type} [CommRing A] [NormedField F] (ψ : A →+* F) (hψ : ∀ a, ‖ψ a‖ ≤ 1)
    {a : A} (ha : IsUnit a) : ‖ψ a‖ = 1 := by
  obtain ⟨u, rfl⟩ := ha
  have e : ‖ψ u.val‖ * ‖ψ (u⁻¹).val‖ = 1 := by rw [← norm_mul, ← map_mul, u.mul_inv, map_one, norm_one]
  refine le_antisymm (hψ _) ?_
  calc (1 : ℝ) = ‖ψ u.val‖ * ‖ψ (u⁻¹).val‖ := e.symm
    _ ≤ ‖ψ u.val‖ * 1 := mul_le_mul_of_nonneg_left (hψ _) (norm_nonneg _)
    _ = _ := _root_.mul_one _

theorem norm_psi_pull : ∀ (p : ℕ) [Fact p.Prime] (V V' : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing V'] [IsDomain V'] [IsLocalRing V'] [Algebra (FractionRing V) (PadicAlgCl p)] [Algebra (FractionRing V') (PadicAlgCl p)] (φ : V →+* V'), (∀ v : V, algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V _ v) = algebraMap (FractionRing V') (PadicAlgCl p) (algebraMap V' _ (φ v))) → (∀ v : V', ‖algebraMap (FractionRing V') (PadicAlgCl p) (algebraMap V' _ v)‖ ≤ 1) → ∀ (D : DegPre V) (D' : DegPre V') (hD : IsPullDeg φ D D') (χ : D'.X) (j : D.P.L.ι) (j' : D'.P.L.ι), ⊤ ≤ (D.c (hD.xe χ)).left ⁻¹ᵁ D.P.L.U j → ⊤ ≤ (D'.c χ).left ⁻¹ᵁ D'.P.L.U j' → ‖algebraMap (FractionRing V') (PadicAlgCl p) (valF (𝟙 (Sp (FractionRing V'))) _ ((D'.psi χ).s fun _ => j').val)‖ = ‖algebraMap (FractionRing V) (PadicAlgCl p) (valF (𝟙 (Sp (FractionRing V))) _ ((D.psi (hD.xe χ)).s fun _ => j).val)‖ := by
  intro p _ V V' _ _ _ _ _ _ _ _ φ hφ hn D D' hD χ j j' hj hj'
  let F := PadicAlgCl p
  let ψ' : V' →+* F := (algebraMap (FractionRing V') F).comp (algebraMap V' (FractionRing V'))
  have hsq : jFK (R := V') F ≫ jK V' ≫ spMap φ = jFK (R := V) F ≫ jK V := by
    refine ((congrArg (jFK (R := V') F ≫ ·) (spMap_comp φ _).symm).trans (spMap_comp _ _).symm).trans
      ((congrArg spMap ?_).trans (spMap_comp _ _))
    exact RingHom.ext fun v => (hφ v).symm
  have z : Sp F := (default : PrimeSpectrum F)
  let Φ := hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)
  have hΦ : ⊤ ≤ ((D'.c χ).left ≫ Φ) ⁻¹ᵁ D.P.L.U j := by
    rw [show (D'.c χ).left ≫ Φ = _ from hD.c_pr χ]
    exact fun y _ => hj (Set.mem_univ ((specOf φ) y))
  let U := (D.P.L.pull Φ).U (fun _ => j) ⊓ D'.P.L.U j'
  have hU : ⊤ ≤ (D'.c χ).left ⁻¹ᵁ U := fun y _ => ⟨mem_pull.2 (hΦ (Set.mem_univ y)), hj' (Set.mem_univ y)⟩
  have m' : ∀ y, D'.xK χ y ∈ D'.P.L.U j' := fun y => hj' (Set.mem_univ (jK V' y))
  have m : ∀ y, D.xK (hD.xe χ) y ∈ D.P.L.U j := fun y => hj (Set.mem_univ (jK V y))
  have e := pmaps_psi hD F hsq χ _ (𝟙 _) z (fun _ => j) (fun _ => j')
    (fun _ => hΦ (Set.mem_univ (jK V' (jFK (R := V') F z)))) (fun _ => m' _)
  have g₁ := gm_pullGen D.P.L (fun _ : PUnit => D.xK (hD.xe χ)) (fun _ => -1) (D.psi (hD.xe χ)) (jFK (R := V) F)
    (𝟙 _ ≫ 𝟙 _) z (fun _ => j) (Set.mem_iInter.2 fun _ => m _)
  have g₂ := gm_pullGen D'.P.L (fun _ : PUnit => D'.xK χ) (fun _ => -1) (D'.psi χ) (jFK (R := V') F)
    (𝟙 _) z (fun _ => j') (Set.mem_iInter.2 fun _ => m' _)
  rw [Fintype.prod_unique] at e
  replace e := g₁.symm.trans (e.trans (congrArg₂ (· * ·) (zpow_neg_one _) g₂))
  rw [eq_inv_mul_iff_mul_eq] at e
  simp only [Category.id_comp] at e
  have a := toStk_map_valR (algebraMap (FractionRing V) F) (𝟙 _)
    (LB.wchart D.P.L (fun _ : PUnit => D.xK (hD.xe χ)) fun _ => j) (fun y _ => Set.mem_iInter.2 fun _ => m y) z
    ((D.psi (hD.xe χ)).s fun _ => j)
  have a' := toStk_map_valR (algebraMap (FractionRing V') F) (𝟙 _)
    (LB.wchart D'.P.L (fun _ : PUnit => D'.xK χ) fun _ => j') (fun y _ => Set.mem_iInter.2 fun _ => m' y) z
    ((D'.psi χ).s fun _ => j')
  rw [Category.comp_id, ← valF_eq_valR'] at a a'
  have b := toStk_map_valR ψ' (D'.c χ).left U hU z (hD.w.s (fun _ => j, j'))
  have hpt : spMap ψ' ≫ (D'.c χ).left = jFK (R := V') F ≫ D'.xK χ :=
    (congrArg (· ≫ (D'.c χ).left) (spMap_comp _ _)).trans (Category.assoc _ _ _)
  have b' : toStk z (ψ' (valR (D'.c χ).left U (hD.w.s (fun _ => j, j')).val)) =
      (gw hD.w (jFK (R := V') F ≫ D'.xK χ) z j j').val := by
    rw [← hpt]; exact b
  have hu : IsUnit (valR (D'.c χ).left U (hD.w.s (fun _ => j, j')).val) := by
    exact (congrArg IsUnit (CrdCalc.valR_eq (R := V') (D'.c χ).left U hU _)).mpr ((Units.isUnit _).map _)
  have key := (toStk z).injective (a'.trans ((congrArg Units.val e).symm.trans
    ((Units.val_mul _ _).trans ((congrArg₂ (· * ·) b' a).symm.trans (map_mul _ _ _).symm))))
  refine (congrArg norm key).trans ?_
  rw [norm_mul, norm_eq_one_of_isUnit ψ' hn hu, _root_.one_mul]
  rfl

end GlobalTheory.ZH.PsiNormPull
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.generator_iso_extend_from_open_containing_charts : ∀ (X Y : Scheme.{0}) (c : Y ⟶ X) [IsOpenImmersion c], (∀ N : LB X, (∀ a, N.U a ≤ c.opensRange) → (∃ t : (N.pull c).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen) ∧ ∀ M M' : LB X, (∀ a b, M.U a ⊓ M'.U b ≤ c.opensRange) → LBIso (M.pull c) (M'.pull c) → LBIso M M' := by
  first | exact @GlobalTheory.GenPush.gen_iso_of_charts_le_range | exact GlobalTheory.GenPush.gen_iso_of_charts_le_range | (intros; apply GlobalTheory.GenPush.gen_iso_of_charts_le_range <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem torsionSection_eq_labelled_of_isDomain : ∀ (R : Type) [CommRing R] [IsDomain R] (P : PolAV (Sp R)) (M : ℕ) (I : Type) (pt : I → (baseOver (Sp R) ⟶ P.A)), (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (z : Over.mk x ⟶ P.A), z ^ M = 1 → ∃ a, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp R)) ≫ pt a = z) → ∀ y : baseOver (Sp R) ⟶ P.A, y ^ M = 1 → ∃ a, pt a = y := by
  intro R _ _ P M I pt h y hy
  let K := AlgebraicClosure (FractionRing R)
  let j : R →+* K := (algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R))
  have hj : Function.Injective j :=
    (algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective R (FractionRing R))
  have hdom : IsDominant (Geo.Tor.spMap j) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical j).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot j).1 hj]; exact bot_le)⟩
  have hprop : IsProper P.A.hom := P.isAb.proper
  obtain ⟨a, ha⟩ := h K (Geo.Tor.spMap j)
    ((Over.homMk (Geo.Tor.spMap j) (by simp) : Over.mk (Geo.Tor.spMap j) ⟶ baseOver (Sp R)) ≫ y)
    (by rw [← MonObj.comp_pow, hy, MonObj.comp_one])
  exact ⟨a, Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Sp R) P.A.hom
    ((Over.w (pt a)).trans (Over.w y).symm) (Geo.Tor.spMap j) (congrArg Over.Hom.left ha))⟩

end GlobalTheory
end
