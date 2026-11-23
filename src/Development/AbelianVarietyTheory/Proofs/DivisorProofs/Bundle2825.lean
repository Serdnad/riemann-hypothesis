module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubTrivDeltaAndEvenUnique
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle023
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2339
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsLinearOfIsPullUniformisation
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformizationEndomorphismCalculus
public import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle037
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.TranslateEvenTriv
open GlobalTheory.UU

theorem exists_gen_pull {X X' Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {F : X' ⟶ X} {L' : LB X'} (e : L' = L.pull F)
    {K : Type} [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε))
    (ht : t.IsGen) : ∃ a : LB.Gen (LB.LinComb L' φ ε), a.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι), Good L z J →
        (∀ q, HEq (J' q) (fun _ : PUnit.{1} => J (q ≫ F))) → val a r z J' = val t r z J := by
  subst e
  have h := pull_isLB hL F
  have hc : ∀ k, φ k ≫ F = 𝟙 Y ≫ (fun k => φ k ≫ F) k := fun k => (Category.id_comp _).symm
  obtain ⟨a, ha, Ha⟩ := CubTransport.exists_pmaps ((isGen_iff _).1 (pullIso_isGen hL F)) hL h (𝟙 Y) hc t ht
  refine ⟨a, ha, fun Z r z J J' hJ hJ' => ?_⟩
  obtain rfl : J' = fun q _ => J (q ≫ F) := funext fun q => eq_of_heq (hJ' q)
  have hg : Good (L.pull F) z (fun q _ => J (q ≫ F)) := fun q => mem_pull.2 (hJ (q ≫ F))
  have := CubTransport.val_pmaps hc Ha r hJ hg
  rw [Category.comp_id, Finset.prod_eq_one, _root_.one_mul] at this
  · exact this.symm
  · intro k _
    have : gw (pullIso L F) (r ≫ φ k) z (J ((r ≫ φ k) ≫ F)) (fun _ => J ((r ≫ φ k) ≫ F)) = 1 :=
      gm_self h (r ≫ φ k) z (hg (r ≫ φ k))
    rw [this, one_zpow]

theorem exists_good_of_pull {X Z : Scheme.{0}} {L L' : LB X} {F : X ⟶ X} (hF : F ≫ F = 𝟙 X) (e : L' = L.pull F)
    {z : Z} {J' : (Z ⟶ X) → L'.ι} (hJ' : Good L' z J') :
    ∃ J : (Z ⟶ X) → L.ι, Good L z J ∧ ∀ q, HEq (J' q) (fun _ : PUnit.{1} => J (q ≫ F)) := by
  subst e
  refine ⟨fun q => J' (q ≫ F) PUnit.unit, fun q => ?_, fun q => heq_of_eq ?_⟩
  · have : ((q ≫ F) ≫ F) z ∈ L.U (J' (q ≫ F) PUnit.unit) := (mem_pull (F := F)).1 (hJ' (q ≫ F))
    rwa [Category.assoc, hF, Category.comp_id] at this
  · show J' q = J' ((q ≫ F) ≫ F)
    rw [Category.assoc, hF, Category.comp_id]

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]


omit [IsCommMonObj G] in
theorem comp_translate (a : 𝟙_ (Over S) ⟶ G) {T : Over S} (g : T ⟶ G) :
    g ≫ ((toUnit G ≫ a) * 𝟙 G) = (toUnit T ≫ a) * g := by
  rw [MonObj.comp_mul, comp_toUnit_assoc, Category.comp_id]

variable {X : Type} [AddCommGroup X] (Q : TQ G X)


omit [IsCommMonObj G] in
theorem mul_torus_comp {T : Over S} (g : T ⟶ G) (x : T ⟶ splitTorus S X) : (g * (x ≫ Q.i)) ≫ Q.q = g ≫ Q.q := by
  have := Q.q_hom
  have e : Q.i ≫ Q.q = 1 := Q.isKernel.w
  rw [MonObj.mul_comp, Category.assoc, e, MonObj.comp_one, _root_.mul_one]

theorem exists_gen_torus {P₁ : CP G} (D : Q.Desc P₁) (a : 𝟙_ (Over S) ⟶ G) :
    ∃ s : LB.Gen (LB.LinComb P₁.L.L (K := Fin 2) (fun k => ![Q.i.left, (1 : splitTorus S X ⟶ G).left] k ≫
      ((toUnit G ≫ a) * 𝟙 G).left) ![1, -1]), s.IsGen ∧
      ∀ (T : Over S) (x : T ⟶ splitTorus S X) (z : T.left) (N) (J), Good D.M.L.L z N → Good P₁.L.L z J →
        ∀ W : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ,
          (∀ g, W g = gw D.w g.left z (N (g.left ≫ Q.q.left)) (J g.left)) →
          val s x.left z J = W (toUnit T ≫ a) * (W ((toUnit T ≫ a) * (x ≫ Q.i)))⁻¹ := by
  obtain ⟨t, ht, v⟩ := exists_gen D.M.L.isLB (φ := (PEmpty.elim : PEmpty → ((splitTorus S X).left ⟶ Q.B.left)))
    (ε := PEmpty.elim) (K' := Fin 2) (φ' := fun _ => ((toUnit (splitTorus S X) ≫ a) ≫ Q.q).left)
    (ε' := ![1, -1]) (fun U _ h => by simp [Fin.prod_univ_two]) (LB.oneGen D.M.L.L)
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
  have hc : ∀ k : Fin 2, (![Q.i.left, (1 : splitTorus S X ⟶ G).left] k ≫ ((toUnit G ≫ a) * 𝟙 G).left) ≫ Q.q.left =
      𝟙 _ ≫ ((toUnit (splitTorus S X) ≫ a) ≫ Q.q).left := fun k => by
    rw [Category.id_comp]
    fin_cases k
    · refine congrArg (fun q => q.left) (show (Q.i ≫ ((toUnit G ≫ a) * 𝟙 G)) ≫ Q.q = _ from ?_)
      have := mul_torus_comp Q (toUnit (splitTorus S X) ≫ a) (𝟙 _)
      rw [Category.id_comp] at this
      rw [comp_translate, this]
    · refine congrArg (fun q => q.left) (show ((1 : splitTorus S X ⟶ G) ≫ ((toUnit G ≫ a) * 𝟙 G)) ≫ Q.q = _ from ?_)
      rw [comp_translate, _root_.mul_one]
  obtain ⟨s, hs, Hs⟩ := CubTransport.exists_pmaps ((isGen_iff _).1 D.map.gen) D.M.L.isLB P₁.L.isLB (𝟙 _) hc t ht
  refine ⟨s, hs, fun T x z N J hN hJ W hW => ?_⟩
  have e := CubTransport.val_pmaps hc Hs x.left hN hJ
  rw [v _ _ z N hN, val_one] at e
  have hτ : ∀ g : T ⟶ G, g.left ≫ ((toUnit G ≫ a) * 𝟙 G).left = ((toUnit T ≫ a) * g).left := fun g =>
    congrArg (fun q => q.left) (comp_translate a g)
  have e₂ := CubTrivTorus.prod_cubTriv Q.i x (fun q => gw D.w (q ≫ ((toUnit G ≫ a) * 𝟙 G).left) z
    (N ((q ≫ ((toUnit G ≫ a) * 𝟙 G).left) ≫ Q.q.left)) (J (q ≫ ((toUnit G ≫ a) * 𝟙 G).left)))
  rw [hτ, hτ, _root_.mul_one, ← hW, ← hW] at e₂
  simp only [← Category.assoc x.left] at e
  have e₃ := e.trans (congrArg₂ (· * ·) e₂ rfl)
  apply Additive.ofMul.injective
  have e₄ := congrArg Additive.ofMul e₃
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at e₄ ⊢
  linear_combination (norm := abel) -e₄

theorem exists_even_cubTriv : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (X : Type) [AddCommGroup X]
    (Q : GlobalTheory.UU.TQ G X) (P₁ : GlobalTheory.UU.CP G), Nonempty (Q.Desc P₁) → ∀ a : 𝟙_ (Over S) ⟶ G, a ^ 2 = 1 →
    ∀ P : GlobalTheory.UU.CP G, P.L.L = P₁.L.L.pull ((toUnit G ≫ a) * 𝟙 G).left →
    (∀ (T : Over S) (x : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → P₁.L.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good P₁.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        val P.sym x.left z J' =
          val P₁.sym ((toUnit T ≫ a) * x).left z J * (val P₁.sym (toUnit T ≫ a).left z J)⁻¹) →
    (∀ (T : Over S) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → P₁.L.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good P₁.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        cubV P.c z J' x y u = cubV P₁.c z J x y ((toUnit T ≫ a) * u) * (cubV P₁.c z J x y (toUnit T ≫ a))⁻¹) →
    ∃ σ : GlobalTheory.UU.CubTriv P.c Q.i, σ.Even := by
  rintro S G _ _ X _ Q P₁ ⟨D⟩ a ha P hP hsym hcub
  have := Q.i_hom
  have hinv : ∀ T : Over S, (toUnit T ≫ a)⁻¹ = toUnit T ≫ a := fun T => by
    rw [inv_eq_iff_mul_eq_one, ← MonObj.comp_mul, ← pow_two, ha, MonObj.comp_one]
  have hF : ((toUnit G ≫ a) * 𝟙 G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left = 𝟙 G.left := by
    refine congrArg (fun q => q.left) (show ((toUnit G ≫ a) * 𝟙 G) ≫ ((toUnit G ≫ a) * 𝟙 G) = 𝟙 G from ?_)
    rw [comp_translate, ← _root_.mul_assoc, (inv_eq_iff_mul_eq_one.1 (hinv G)), _root_.one_mul]
  obtain ⟨s, hs, vs⟩ := exists_gen_torus Q D a
  obtain ⟨σ, hσ, vσ⟩ := exists_gen_pull P₁.L.isLB hP _ _ s hs
  have hq : ∀ {T : Over S} (g : T ⟶ G) (x : T ⟶ splitTorus S X), (g * (x ≫ Q.i)).left ≫ Q.q.left = g.left ≫ Q.q.left :=
    fun g x => congrArg (fun q => q.left) (mul_torus_comp Q g x)
  refine ⟨⟨σ, hσ, fun T x y u z J' hJ' => ?_⟩, fun T x z J' hJ' => ?_⟩
  all_goals
    obtain ⟨J, hJ, hJJ⟩ := exists_good_of_pull hF hP hJ'
    obtain ⟨N, hN⟩ := exists_good_pt D.M.L.isLB z
    obtain ⟨W, hW⟩ : ∃ W : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ,
      ∀ g, W g = gw D.w g.left z (N (g.left ≫ Q.q.left)) (J g.left) := ⟨_, fun _ => rfl⟩
    have v : ∀ t : T ⟶ splitTorus S X, val σ t.left z J' = W (toUnit T ≫ a) * (W ((toUnit T ≫ a) * (t ≫ Q.i)))⁻¹ :=
      fun t => (vσ _ t.left z J J' hJ hJJ).trans (vs T t z N J hN hJ W hW)
    obtain ⟨-, a₂, a₃⟩ := D.map.vals T z J N hJ hN W hW
  · have b₁ := a₃ (x ≫ Q.i) (y ≫ Q.i) ((toUnit T ≫ a) * (u ≫ Q.i))
    have b₂ := a₃ (x ≫ Q.i) (y ≫ Q.i) (toUnit T ≫ a)
    have e : toBase (f := 𝟙 S) (g := Q.q.left) (by simp) ((toUnit T ≫ a) * (u ≫ Q.i)) =
        toBase (f := 𝟙 S) (g := Q.q.left) (by simp) (toUnit T ≫ a) := Over.OverMorphism.ext (hq _ u)
    rw [e] at b₁
    rw [hcub T _ _ _ z J J' hJ hJJ]
    simp only [v, MonObj.mul_comp]
    generalize x ≫ Q.i = x' at *
    generalize y ≫ Q.i = y' at *
    generalize u ≫ Q.i = u' at *
    generalize toUnit T ≫ a = A at *
    rw [mul_left_comm x' A, mul_left_comm y' A, mul_left_comm (x' * y') A] at b₁
    rw [mul_comm x' A, mul_comm y' A, mul_comm (x' * y') A] at b₂
    apply Additive.ofMul.injective
    have c₁ := congrArg Additive.ofMul b₁
    have c₂ := congrArg Additive.ofMul b₂
    simp only [ofMul_mul, ofMul_inv] at c₁ c₂ ⊢
    linear_combination (norm := abel) c₁ - c₂
  · have b₁ := a₂ ((toUnit T ≫ a) * (x ≫ Q.i))
    have b₂ := a₂ (toUnit T ≫ a)
    rw [hq, mul_inv, hinv] at b₁
    rw [hinv] at b₂
    show val σ _ z J' = _ * val σ _ z J'
    rw [hsym T _ z J J' hJ hJJ, v, v, GrpObj.inv_comp]
    apply Additive.ofMul.injective
    have c₁ := congrArg Additive.ofMul b₁
    have c₂ := congrArg Additive.ofMul b₂
    simp only [ofMul_mul, ofMul_inv] at c₁ c₂ ⊢
    linear_combination (norm := abel) c₁ - c₂

end GlobalTheory.TranslateEvenTriv
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange

noncomputable section
namespace GlobalTheory.SecAdicSumAny

open GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw GlobalTheory.SecAdicSum

theorem sumF_of_sum_on_thickenings_any : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (X : Scheme.{0}) (N : LB X), N.IsLB → ∀ (K : Type) [Fintype K] (φ : K → (D.toPre.P.A.left ⟶ X)) (ε : K → ℤ) (Ix : Type) (n : Ix → LB.Sec (LB.LinComb N φ ε)) (n₀ : LB.Sec (LB.LinComb N φ ε)), (∀ e : ℕ, ∃ S : Finset Ix, ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e D.toPre.P.A).left) (z : Z) (J), Good N z J → (∀ i ∉ S, sval (n i) (r ≫ (D.toPre.prBe I e).left) z J = 0) ∧ sval n₀ (r ≫ (D.toPre.prBe I e).left) z J = ∑ i ∈ S, sval (n i) (r ≫ (D.toPre.prBe I e).left) z J) → ∀ (b : TF (R := R) F ⟶ D.toPre.P.A) (τ : LB.Gen (LB.LinComb N (fun i => b.left ≫ φ i) ε)), τ.IsGen → ∀ (x : Ix → F) (x₀ : F), (∀ z J, Good N z J → (∀ i, sval (n i) b.left z J = cst F z (x i) * (val τ (𝟙 _) z J).val) ∧ sval n₀ b.left z J = cst F z x₀ * (val τ (𝟙 _) z J).val) → SumF I F x x₀ := by
  intro R _ _ _ I hR D F _ _ _ X N hL K _ φ ε Ix n n₀ hS b τ _ x x₀ hx
  have := hR.1
  have := D.toPre.P.isAb.smooth
  obtain ⟨P⟩ := GlobalTheory.T.nonempty_perfectSectionsComplex_of_noetherian R _ D.toPre.P.A.hom inferInstance
    (GlobalTheory.AbProj.isProjBy_of_isPullback D.toPre.P (IsPullback.id_horiz _)) _ (LB.isLB_linComb hL φ ε)
  choose v hv hv' using fun i => exists_vec P (n i)
  obtain ⟨v₀, hv₀, hv₀'⟩ := exists_vec P n₀
  obtain ⟨z⟩ := CoefBasic.exists_pt (R := R) (F := F)
  obtain ⟨J, hJ⟩ := CoefBasic.exists_good' hL z
  obtain ⟨i₀, hi₀⟩ := exists_mem P (b.left z)
  let t := trF φ ε b.left z (P.ch i₀) (fun k => J (b.left ≫ φ k)) * val τ (𝟙 _) z J
  choose y hy using fun k => CoefBasic.cstH_surj z (gs b.left z _ (P.u k i₀) * (t⁻¹).val)
  letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))
  let ev : (Fin P.a → R) →ₗ[R] F := Fintype.linearCombination R y
  have key : ∀ (s : LB.Sec (LB.LinComb N φ ε)) (w : Fin P.a → R) (c : F),
      (∀ i, AbLaw.rs _ (P.le i) (s.f (P.ch i)) = loc₀ P w i) →
      sval s b.left z J = UT.cst F z c * (val τ (𝟙 _) z J).val → c = ev w := fun s w c h₁ h₂ => by
    have e := gs_loc₀ P h₁ b.left z hi₀ hJ
    rw [h₂, mul_left_comm, ← Units.val_mul, CoefBasic.cst_eq] at e
    refine CoefBasic.cstH_inj (R := R) z ?_
    have e' : CoefBasic.cstH z c = gs b.left z _ (loc₀ P w i₀) * (t⁻¹).val :=
      (Units.eq_mul_inv_iff_mul_eq t).2 e.symm
    have hs : ∀ a : Fin P.a → Γ(D.toPre.P.A.left, P.W i₀), gs b.left z _ (∑ k, a k) = ∑ k, gs b.left z _ (a k) :=
      fun a => by simp only [gs_eq b.left z _ hi₀, map_sum]
    rw [e', loc₀, hs, Finset.sum_mul]
    refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) (map_sum _ (fun k => w k • y k) _).symm
    rw [gs_mul b.left z _ hi₀, gs_cst_point b z _ hi₀, _root_.mul_assoc, ← hy, ← map_mul, ← Algebra.smul_def]
    rfl
  obtain rfl : x = fun i => ev (v i) := funext fun i => key _ _ _ (hv' i) ((hx z J hJ).1 i)
  obtain rfl : x₀ = ev v₀ := key _ _ _ hv₀' (hx z J hJ).2
  refine sumI_of_ker I P.D₀ ev v v₀ hv hv₀ fun e => ?_
  obtain ⟨S, hS⟩ := hS e
  refine ⟨S, fun T hT k => Ideal.Quotient.eq_zero_iff_mem.1 (congrFun (comp_eq_zero P
    (IsPullback.of_hasPullback D.toPre.P.A.hom (thick R I e)) (v₀ - ∑ i ∈ T, v i) ?_ fun i p hp => ?_) k)⟩
  · simp only [Matrix.mulVec_sub, Matrix.mulVec_sum, hv, hv₀, Finset.sum_const_zero, sub_zero]
  · obtain ⟨J', hJ'⟩ := CoefBasic.exists_good' hL p
    obtain ⟨h₁, h₂⟩ := hS _ (𝟙 _) p J' hJ'
    rw [Category.id_comp] at h₁ h₂
    have h₃ := h₂.trans (Finset.sum_subset hT fun j _ hj => h₁ j hj)
    have e₀ := gs_loc₀ P hv₀' _ p hp hJ'
    have e₁ := fun j => gs_loc₀ P (hv' j) _ p hp hJ'
    rw [gs_eq _ p _ hp] at e₀
    simp only [gs_eq _ p _ hp] at e₁

    rw [loc₀_sub_sum, gs_eq _ p _ hp, map_sub, map_sub, map_sum, map_sum, e₀, Finset.sum_congr rfl fun j _ => e₁ j,
    ← Finset.mul_sum]
    exact sub_eq_zero.2 (congrArg _ h₃)

end GlobalTheory.SecAdicSumAny
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section

namespace GlobalTheory.Poinc.IntTerm

theorem psi_zero_rig_const : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V), ∃ c₀ : FractionRing V, c₀ ≠ 0 ∧ ∀ (z : (TF (R := V) (FractionRing V)).left) (J : ((TF (R := V) (FractionRing V)).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi 0) (jFK (R := V) (FractionRing V)) z J)).val * (rigV D (TF (R := V) (FractionRing V)).hom z J).val = GlobalTheory.UT.cst (FractionRing V) z c₀ := by
  intro V _ _ D
  obtain ⟨z⟩ := GlobalTheory.UT.CoefBasic.exists_pt (R := V) (F := FractionRing V)
  obtain ⟨J', hJ'⟩ := GlobalTheory.UT.CoefBasic.exists_good' D.P.isLB z
  obtain ⟨c, hc⟩ := GlobalTheory.UT.CoefBasic.cstH_surj z
    ((@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi 0) (jFK (R := V) (FractionRing V)) z J')).val * (rigV D (TF (R := V) (FractionRing V)).hom z J').val)
  refine ⟨c, fun h => ?_, fun z' J hJ => ?_⟩
  · rw [h, map_zero] at hc
    rw [← Units.val_mul] at hc
    exact Units.ne_zero _ hc.symm
  · obtain rfl := GlobalTheory.UT.CoefBasic.pt_eq z z'
    have a₁ := GlobalTheory.UT.CoefBasic.val_tr (D.psi_gen 0) (jFK (R := V) (FractionRing V)) hJ hJ'
    have a₂ : rigV D (TF (R := V) (FractionRing V)).hom z J =
        GlobalTheory.UT.CoefBasic.trU D.P.L z J J' ((TF (R := V) (FractionRing V)).hom ≫ eSec D.P.A) *
        rigV D (TF (R := V) (FractionRing V)).hom z J' := by
      refine (GlobalTheory.UT.CoefBasic.val_tr (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig_gen
        (TF (R := V) (FractionRing V)).hom hJ hJ').trans ?_
      rw [Fintype.prod_unique, zpow_one]; rfl
    have e : jFK (R := V) (FractionRing V) ≫ ptK (D.c 0) = (TF (R := V) (FractionRing V)).hom ≫ eSec D.P.A := by
      rw [GlobalTheory.Poinc.ThetaOne.c_zero]
      rfl
    simp only [e] at a₁
    rw [GlobalTheory.UT.CoefBasic.cst_eq, hc]
    show (Geo.Tor.val (D.psi 0) (jFK (R := V) (FractionRing V)) z J).val * _ = _
    rw [a₁, a₂, ← Units.val_mul, ← Units.val_mul]
    congr 1
    simp only [Fintype.prod_unique, Finset.prod_const, Finset.card_univ, Fintype.card_unique, pow_one, zpow_neg,
      zpow_one, id]
    rw [_root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul]

end GlobalTheory.Poinc.IntTerm

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.ArcPull

namespace GlobalTheory.Poinc.AComm

theorem pulled_end_comm : ∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R} {I' : Ideal R'} (g : R →+* R') (hg : Function.Injective g) {D : DegData R I} {D' : DegData R' I'} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {A' : PolAV (Spec (CommRingCat.of (FractionRing R')))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (U' : UnifPre I' D' A' ((Over.pullback (specOf g)).obj G)) (gA : A'.A.left ⟶ A.A.left), IsGrpPullback A'.A A.A (spMap (fracMap hg)) gA → gA ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = U'.gen.inv.left ≫ pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫ pullback.fst G.hom (specOf g) → ∀ (E : EndU U) (E' : EndU U'), E'.aG = (Over.pullback (specOf g)).map E.aG → E'.aA.left ≫ gA = gA ≫ E.aA.left := by
  intro R R' _ _ _ _ I I' g hg D D' A A' G _ _ U U' gA hgA hfst E E' hE
  have key : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
      {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
      (U : UnifPre I D A G) (E : EndU U) {Z : Scheme.{0}} (h : pullback G.hom (jK R) ⟶ Z),
      E.aA.left ≫ U.gen.inv.left ≫ h = U.gen.inv.left ≫ ((Over.pullback (jK R)).map E.aG).left ≫ h := by
    intro R _ _ I D A G _ _ U E Z h
    have k : E.aA ≫ U.gen.inv = U.gen.inv ≫ (Over.pullback (jK R)).map E.aG := by
      rw [Iso.comp_inv_eq, Category.assoc, E.ext, Iso.inv_hom_id_assoc]
    have k' := congrArg CommaMorphism.left k
    simp only [Over.comp_left] at k'
    rw [← Category.assoc, k', Category.assoc]
  have pf : ∀ {Y S : Scheme.{0}} (f : Y ⟶ S) {H H' : Over S} (a : H ⟶ H') {Z : Scheme.{0}} (h : H'.left ⟶ Z),
      ((Over.pullback f).map a).left ≫ pullback.fst H'.hom f ≫ h = pullback.fst H.hom f ≫ a.left ≫ h := by
    intro Y S f H H' a Z h
    have e : ((Over.pullback f).map a).left ≫ pullback.fst H'.hom f = pullback.fst H.hom f ≫ a.left :=
      pullback.lift_fst _ _ _
    rw [← Category.assoc, e, Category.assoc]
  have pf0 : ∀ {Y S : Scheme.{0}} (f : Y ⟶ S) {H H' : Over S} (a : H ⟶ H'),
      ((Over.pullback f).map a).left ≫ pullback.fst H'.hom f = pullback.fst H.hom f ≫ a.left :=
    by intro Y S f H H' a; exact pullback.lift_fst _ _ _
  have ws : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
      {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
      (U : UnifPre I D A G), U.gen.inv.left ≫ pullback.snd G.hom (jK R) = A.A.hom := by
    intro R _ _ I D A G _ _ U
    simpa using Over.w U.gen.inv
  have hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have inj : ∀ a b : A'.A.left ⟶ A.A.left, a ≫ U.gen.inv.left = b ≫ U.gen.inv.left → a = b := by
    intro a b h
    have := congrArg (· ≫ U.gen.hom.left) h
    simpa only [Category.assoc, hgi, Category.comp_id] using this
  apply inj
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [hfst, key U' E', pf, hE, pf0, key U E, pf0]
    rw [reassoc_of% hfst]
  · simp only [Category.assoc]
    rw [ws U, Over.w E.aA, hgA.1.w, ← Category.assoc, Over.w E'.aA]

end GlobalTheory.Poinc.AComm
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.EndPullChar

theorem pull_char_eq : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R'), AdmBase R I → AdmBase R' I' → ∀ (φ : R →+* R'), Function.Injective φ → I.map φ ≤ I' → ∀ (D : DegData R I) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (A : PolAV (Sp (FractionRing R))) (A' : PolAV (Sp (FractionRing R'))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I' D' A' G') (bc : G' ≅ (Over.pullback (spMap φ)).obj G), IsMonHom bc.hom → IsPullUnif φ hD bc U U' → ∀ (E : EndU U.toUnifPre) (E' : EndU U'.toUnifPre), E'.aG.left ≫ bc.hom.left ≫ pullback.fst G.hom (spMap φ) = bc.hom.left ≫ pullback.fst G.hom (spMap φ) ≫ E.aG.left → ∀ χ, hD.xe (E'.h χ) = E.h (hD.xe χ) := by
  intro R R' _ _ _ _ I I' hR hR' φ _hφ _hI D D' hD A A' G _ _ G' _ _ _hG _hG' U U' bc _hbc hU E E' hE
  have hG : E'.aG ≫ bc.hom = bc.hom ≫ (Over.pullback (spMap φ)).map E.aG := by
    refine GlobalTheory.PullLinear.ext_of_pullback (spMap φ) ?_
    rw [Over.comp_left, Over.comp_left, Category.assoc, hE, Category.assoc,
      GlobalTheory.PullLinear.map_left_fst]
  have := E'.homG
  obtain ⟨E'', h₁, h₂, -⟩ := GlobalTheory.UT.EndBaseChange.exists_end hD hU E E'.aG hG
  have h₃ := (GlobalTheory.EndCalc.congr_data hR' E'' E' h₁).2
  intro χ
  rw [← h₂ χ, h₃]

end GlobalTheory.EndPullChar
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.PsiIntGen

theorem gs_specMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (z : Spec (CommRingCat.of B)) (a : A) :
    gs (Spec.map (CommRingCat.ofHom f)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) =
      gs (𝟙 (Spec (CommRingCat.of B))) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (f a)) := by
  have e := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  have e' : (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (f a) =
      ((Spec.map (CommRingCat.ofHom f)).app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) := e
  rw [e']
  have := gs_pull (𝟙 (Spec (CommRingCat.of B))) (Spec.map (CommRingCat.ofHom f)) z ⊤ trivial
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)
  rw [Category.id_comp] at this
  exact this.symm

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (mu : D.X) (r : V), Formalism.L2.Pj.PsiCoord D mu r → ∃ gam : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c mu).left) (fun _ => -1)), gam.IsGen ∧ ∀ (z : (TF (R := V) (FractionRing V)).left) (J : ((TF (R := V) (FractionRing V)).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi mu) (jFK (R := V) (FractionRing V)) z J)).val = GlobalTheory.UT.cst (FractionRing V) z (algebraMap V (FractionRing V) r) * (Geo.Tor.val gam (toUnit (TF (R := V) (FractionRing V))).left z J).val := by
  intro V _ _ D mu r hr
  obtain ⟨j, hj, h, e⟩ := hr
  obtain ⟨t, ht, vt⟩ := PsiSpread.exists_gen_of_chart D.P.isLB (K := PUnit) (fun _ => (D.c mu).left) (fun _ => -1)
    j (fun y => Set.mem_iInter.2 fun _ => hj trivial) ⊤ (fun _ => trivial) 1
  refine ⟨t, ht, fun z J hJ => ?_⟩
  have q : jFK (R := V) (FractionRing V) ≫ ptK (D.c mu) =
      (toUnit (TF (R := V) (FractionRing V))).left ≫ (D.c mu).left := (Category.assoc _ _ _).symm
  have a := gen_trans (D.psi_gen mu) (jFK (R := V) (FractionRing V)) z (j' := j) (hJ.mem _ _) (h trivial)
  have b := vt _ (toUnit (TF (R := V) (FractionRing V))).left z _ (hJ.mem _ _)
  rw [map_one, _root_.mul_one] at b
  have c : (gm (jFK (R := V) (FractionRing V)) z (LB.wchart D.P.L (K := PUnit) (fun _ => ptK (D.c mu)) j)
      ((D.psi mu).s j)).val = GlobalTheory.UT.cst (FractionRing V) z (algebraMap V (FractionRing V) r) := by
    refine (gs_unit _ _ _ (h trivial) _).symm.trans ?_
    refine (gs_res (jFK (R := V) (FractionRing V)) z h trivial ((D.psi mu).s j).val).symm.trans ?_
    refine (congrArg (gs (jFK (R := V) (FractionRing V)) z _) e.symm).trans ?_
    refine (gs_pull (jFK (R := V) (FractionRing V)) (jK V) z ⊤ trivial _).trans ?_
    refine (gs_res _ z (le_top : (⊤ : (Spec (CommRingCat.of V)).Opens) ≤ ⊤) trivial _).trans ?_
    have s : jFK (R := V) (FractionRing V) ≫ jK V = Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) := by
      rw [← Spec.map_comp]; rfl
    rw [s]
    exact gs_specMap _ z r
  have d : trF (L := D.P.L) (K := PUnit) (fun _ => ptK (D.c mu)) (fun _ => -1) (jFK (R := V) (FractionRing V)) z
      (fun _ => J (jFK (R := V) (FractionRing V) ≫ ptK (D.c mu))) j =
      trF (L := D.P.L) (K := PUnit) (fun _ => (D.c mu).left) (fun _ => -1) (toUnit (TF (R := V) (FractionRing V))).left z
      (fun _ => J ((toUnit (TF (R := V) (FractionRing V))).left ≫ (D.c mu).left)) j :=
    congrArg (fun ψ => ∏ k : PUnit.{1}, gm ψ z (D.P.L.U (J ψ) ⊓ D.P.L.U (j k)) (D.P.L.g (J ψ) (j k)) ^ (-1 : ℤ)) q
  refine (congrArg Units.val a).trans ((Units.val_mul _ _).trans ((_root_.mul_comm _ _).trans ?_))
  exact congrArg₂ (· * ·) c (congrArg Units.val (d.trans b.symm))

end GlobalTheory.Poinc.PsiIntGen
end
end
