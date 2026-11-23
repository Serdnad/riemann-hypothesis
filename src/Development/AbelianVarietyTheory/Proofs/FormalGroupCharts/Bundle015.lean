module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsChartOfMemRedKer
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle014
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open SqZero

section Pairs

variable (R : Type) [CommRing R] {A : Type} [CommRing A] [Algebra R A]

def congrPairs (J : Ideal A) : Subalgebra R (A × A) :=
  AlgHom.equalizer ((Ideal.Quotient.mkₐ R J).comp (AlgHom.snd R A A))
    ((Ideal.Quotient.mkₐ R J).comp (AlgHom.fst R A A))

variable {R}

theorem mem_congrPairs {J : Ideal A} {b : A × A} : b ∈ congrPairs R J ↔ b.2 - b.1 ∈ J :=
  Ideal.Quotient.eq

theorem mul_eq_aug_mul (aug : A →ₐ[R] R) {J : Ideal A} (hJ : J * RingHom.ker aug = ⊥) {δ : A}
    (hδ : δ ∈ J) (a : A) : δ * (a - algebraMap R A (aug a)) = 0 := by
  have : δ * (a - algebraMap R A (aug a)) ∈ J * RingHom.ker aug :=
    Ideal.mul_mem_mul hδ (by simp [RingHom.mem_ker])
  rwa [hJ] at this

def pairDiff (aug : A →ₐ[R] R) {J : Ideal A} (hJ : J * RingHom.ker aug = ⊥) :
    congrPairs R J →ₐ[R] A where
  toFun b := algebraMap R A (aug b.1.1) + (b.1.2 - b.1.1)
  map_one' := by simp
  map_mul' b c := by
    have hb := mem_congrPairs.1 b.2
    have hc := mem_congrPairs.1 c.2
    have h₁ := mul_eq_aug_mul aug hJ hb c.1.1
    have h₂ := mul_eq_aug_mul aug hJ hc b.1.1
    simp only [MulMemClass.coe_mul, Prod.fst_mul, Prod.snd_mul, map_mul]
    linear_combination h₁ + h₂
  map_zero' := by simp
  map_add' b c := by
    simp only [AddMemClass.coe_add, Prod.fst_add, Prod.snd_add, map_add (f := _)]
    ring
  commutes' r := by simp

end Pairs

theorem jet_sqZero_eq_lieExp {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))}
    [GrpObj G] [IsCommMonObj G] (hG : Smooth G.hom) {d : ℕ} {v : Fin d → (epsR R ⟶ G)}
    (hv : IsLieBasis v) (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G)
    (hxt : ∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m)
    (hx0 : ∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1)
    (hx1 : ∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j)
    {A : Type} [CommRing A] [Algebra R A] {J : Ideal A} (hJ : J ^ 2 = ⊥) (δ : Fin d → A)
    (hδ : ∀ j, δ j ∈ J) (hδ' : ∀ j, δ j * δ j = 0) (m : ℕ) (φ : JetR R (Fin d) m →ₐ[R] A)
    (hφ : ∀ j, φ (zR m j) = δ j) : spMap φ ≫ x m = lieExp v δ hδ' := by
  have key : ∀ (k : ℕ) (φ : JetR R (Fin d) (k + 1) →ₐ[R] A), (∀ j, φ (zR (k + 1) j) = δ j) →
      spMap φ ≫ x (k + 1) = lieExp v δ hδ' := by
    intro k
    induction k with
    | zero =>
      intro φ hφ
      exact firstJet_eq_prod_tangent R G hG d v hv x hx0 hx1 A φ _
        fun j => (epsTo_eps _ _).trans (hφ j).symm
    | succ k ih =>
      intro φ hφ
      have hk : J ^ (k + 1 + 1) = ⊥ :=
        le_bot_iff.1 ((Ideal.pow_le_pow_right (by omega)).trans hJ.le)
      have e : φ = (jetLift (R := R) J hk δ hδ).comp (jetTruncR R (Fin d) (k + 1)) :=
        jet_ext fun j => (hφ j).trans (jetLift_zR J hk δ hδ j).symm
      rw [e, ← spMap_comp, Category.assoc, hxt]
      exact ih _ (jetLift_zR J hk δ hδ)
  rw [← hxt m, ← Category.assoc, spMap_comp]
  exact key m _ hφ

theorem jet_add_sqZero_eq_prod_mul : ∀ (R : Type) [CommRing R]
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], Smooth G.hom →
    ∀ (d : ℕ) (v : Fin d → (epsR R ⟶ G)), IsLieBasis v →
    ∀ (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G),
    (∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m) →
    (∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1) →
    (∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j) →
    ∀ (A : Type) [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (J : Ideal A),
    J * RingHom.ker aug = ⊥ → J ≤ RingHom.ker aug →
    ∀ (m : ℕ) (ψ ψ' : JetR R (Fin d) m →ₐ[R] A), aug.comp ψ = jetAug R (Fin d) m →
    aug.comp ψ' = jetAug R (Fin d) m → ∀ e : Fin d → (DualNumber R →ₐ[R] A),
    (∀ j, e j (TrivSqZeroExt.inr 1) ∈ J) →
    (∀ j, ψ' (zR m j) = ψ (zR m j) + e j (TrivSqZeroExt.inr 1)) →
    spMap ψ' ≫ x m = (∏ j, (spMap (e j) ≫ v j : sp (R₀ := R) A ⟶ G)) * (spMap ψ ≫ x m) := by
  intro R _ G _ _ hG d v hv x hxt hx0 hx1 A _ _ aug J hJ hle m ψ ψ' hψ _ e he hz
  have hJJ : ∀ a ∈ J, ∀ b ∈ J, a * b = 0 := fun a ha b hb => by
    have : a * b ∈ J * RingHom.ker aug := Ideal.mul_mem_mul ha (hle hb)
    rwa [hJ] at this
  have hJ2 : J ^ 2 = ⊥ := by
    rw [pow_two]
    exact le_bot_iff.1 ((Ideal.mul_mono_right hle).trans hJ.le)
  let p₁ : congrPairs R J →ₐ[R] A := (AlgHom.fst R A A).comp (congrPairs R J).val
  let p₂ : congrPairs R J →ₐ[R] A := (AlgHom.snd R A A).comp (congrPairs R J).val
  let s : A →ₐ[R] congrPairs R J := ((AlgHom.id R A).prod (AlgHom.id R A)).codRestrict _
    fun a => mem_congrPairs.2 (by simp)
  have hq : (Ideal.Quotient.mkₐ R J).comp ψ' = (Ideal.Quotient.mkₐ R J).comp ψ :=
    jet_ext fun j => Ideal.Quotient.eq.2 (by
      change ψ' (zR m j) - ψ (zR m j) ∈ J
      rw [hz, add_sub_cancel_left]
      exact he j)
  let Ψ : JetR R (Fin d) m →ₐ[R] congrPairs R J := (ψ.prod ψ').codRestrict _
    fun a => AlgHom.congr_fun hq a
  let c : Fin d → congrPairs R J := fun j =>
    ⟨(0, e j (TrivSqZeroExt.inr 1)), mem_congrPairs.2 (by simpa using he j)⟩
  have hc : ∀ j, c j * c j = 0 := fun j =>
    Subtype.ext (Prod.ext (mul_zero _) (hJJ _ (he j) _ (he j)))
  have hK : RingHom.ker p₁ ^ 2 = ⊥ := by
    rw [pow_two, ← le_bot_iff, Ideal.mul_le]
    intro a ha b hb
    have ha1 : a.1.1 = 0 := ha
    have hb1 : b.1.1 = 0 := hb
    have ha2 := mem_congrPairs.1 a.2
    have hb2 := mem_congrPairs.1 b.2
    rw [ha1, sub_zero] at ha2
    rw [hb1, sub_zero] at hb2
    exact Subtype.ext (Prod.ext (show a.1.1 * b.1.1 = 0 by rw [ha1, zero_mul]) (hJJ _ ha2 _ hb2))
  have m₁ : (spMap Ψ ≫ x m) * (spMap (s.comp ψ) ≫ x m)⁻¹ ∈ redKer G (RingHom.ker p₁) := by
    refine mem_redKer_of_section p₁ s (fun _ => rfl) ?_
    rw [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc, spMap_comp,
      spMap_comp]
    exact mul_inv_cancel _
  have m₂ : lieExp v c hc ∈ redKer G (RingHom.ker p₁) :=
    lieExp_mem_redKer hv.1 c (fun _ => rfl) hc
  have main := redKer_ext hK m₁ m₂ p₁ (pairDiff aug hJ)
    (fun a h₁ h₂ => by
      have h₁' : a.1.1 = 0 := h₁
      have h₂' : algebraMap R A (aug a.1.1) + (a.1.2 - a.1.1) = 0 := h₂
      rw [h₁', map_zero, map_zero, zero_add, sub_zero] at h₂'
      exact Subtype.ext (Prod.ext h₁' h₂'))
    (by rw [comp_eq_one_of_mem_redKer m₁ p₁ fun _ h => h,
      comp_eq_one_of_mem_redKer m₂ p₁ fun _ h => h])
    (by
      have hψz : ∀ j, aug (ψ (zR m j)) = 0 := fun j =>
        (AlgHom.congr_fun hψ _).trans (jetAug_zR m j)
      rw [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc, spMap_comp,
        spMap_comp, comp_lieExp,
        jet_sqZero_eq_lieExp hG hv x hxt hx0 hx1 hJ2 (fun j => e j (TrivSqZeroExt.inr 1)) he
          (fun j => hJJ _ (he j) _ (he j)) m _ (fun j => by
            change algebraMap R A (aug (ψ (zR m j))) + (ψ' (zR m j) - ψ (zR m j)) = _
            rw [hψz, hz, map_zero, zero_add, add_sub_cancel_left]),
        jet_sqZero_eq_lieExp hG hv x hxt hx0 hx1 hJ2 (fun _ => 0) (fun _ => J.zero_mem)
          (fun _ => mul_zero _) m _ (fun j => by
            change algebraMap R A (aug (ψ (zR m j))) + (ψ (zR m j) - ψ (zR m j)) = _
            rw [hψz, map_zero, zero_add, sub_self])]
      have h1 : lieExp v (fun _ => (0 : A)) (fun _ => mul_zero _) = 1 :=
        Finset.prod_eq_one fun i _ => epsTo_zero_comp ((isTan_iff _).2 (hv.1 i)) _ rfl _
      rw [h1, inv_one, _root_.mul_one]
      refine lieExp_congr _ (fun j => ?_) _ _
      change _ = algebraMap R A (aug 0) + (e j (TrivSqZeroExt.inr 1) - 0)
      rw [map_zero, map_zero, zero_add, sub_zero])
  have fin := congrArg (spMap p₂ ≫ ·) (mul_inv_eq_iff_eq_mul.1 main)
  simp only [MonObj.comp_mul, ← Category.assoc, spMap_comp, comp_lieExp] at fin
  refine fin.trans ?_
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  congr 2
  exact DualNumber.algHom_ext (epsTo_eps _ _)

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

noncomputable section

namespace GlobalTheory

theorem linComb_gen_eq_of_eSec (hGF : GlobalFnsSt) {S X : Scheme.{0}} (A : Over S) [GrpObj A]
    (hA : IsAbelianScheme A) {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (A.left ⟶ X)} {ε : K → ℤ} {φ' : K' → ((𝟙_ (Over S)).left ⟶ X)} {ε' : K' → ℤ}
    {a b : LB.Gen (LB.LinComb L φ ε)} (ha : a.IsGen) (hb : b.IsGen) {r : LB.Gen (LB.LinComb L φ' ε')}
    (har : LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε a (eSec A)) r)
    (hbr : LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε b (eSec A)) r) : a = b := by
  have hcov : ∀ x : A.left, ∃ i, x ∈ (LB.LinComb L φ ε).U i := fun x => by
    choose I hI using fun k => exists_chart hL (φ k x)
    exact ⟨I, Set.mem_iInter.2 hI⟩
  obtain ⟨u, hu⟩ := ChartFrameTrA.exists_ratio_gen hcov ha hb
  suffices hu1 : u = 1 by
    cases a
    cases b
    congr 1
    funext p
    exact (hu p).trans (by rw [hu1, map_one, _root_.one_mul])
  apply ChartFrameTrA.unit_eq_one_of_eSec hGF A hA u
  have key : pullU (eSec A) ⊤ u = 1 := by
    refine unit_ext fun z hz => ?_
    choose J hJ using fun χ : (𝟙_ (Over S)).left ⟶ X => exists_chart hL (χ z)
    have hJ' : Good L z J := hJ
    have e1 := (val_pull hJ' a (eSec A) (𝟙 _)).symm.trans ((val_corr hJ' har (𝟙 _)).trans
      ((val_corr hJ' hbr (𝟙 _)).symm.trans (val_pull hJ' b (eSec A) (𝟙 _))))
    have hm := hJ'.mem φ (𝟙 _ ≫ eSec A)
    have e2 : val a (𝟙 _ ≫ eSec A) z J = gm (𝟙 _ ≫ eSec A) z ⊤ u * val b (𝟙 _ ≫ eSec A) z J :=
      (congrArg (gm _ z _) (hu _)).trans ((map_mul _ _ _).trans
        (congrArg₂ (· * ·) (gm_res _ z _ hm _) rfl))
    have e3 : gm (𝟙 _ ≫ eSec A) z ⊤ u = 1 := mul_eq_right.1 (e2.symm.trans e1)
    exact (gm_pull (𝟙 _) (eSec A) z ⊤ trivial u).trans (e3.trans (map_one _).symm)
  exact congrArg Units.val key

theorem isPrimG_unique : GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (X0 : Scheme.{0}) (t : SAB H X0), IsAbelianScheme t.G → ∀ wP wP' : PrimTyG t,
    IsPrimG t wP → IsPrimG t wP' → wP = wP' :=
  fun hGF _ _ _ _ _ _ t hA _ _ h h' =>
    linComb_gen_eq_of_eSec hGF t.G hA t.PP.isLB h.1 h'.1 h.2 h'.2

end GlobalTheory
end
end

section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RosatiCube

open ReciprocityTheory.ChartRestriction.G.DVR

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

def IsNormGen (L : LB A.left) (f g : A ⟶ A) (u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)) : Prop :=
  u.IsGen ∧ LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (zero2 A)) (LB.oneGen L)

variable {L : LB A.left}

theorem IsNormGen.val_origin {f g : A ⟶ A} {u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)} (hu : IsNormGen L f g u)
    {y : (𝟙_ (Over S)).left} {J} (hJ : Good L y J) : val₂ u y J (1 : 𝟙_ (Over S) ⟶ A) 1 = 1 := by
  have e : lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A) = lift η[A] η[A] := by simp [Hom.one_def]
  have := val_corr hJ hu.2 (𝟙 _)
  rw [val_pull hJ, Category.id_comp, val_one] at this
  rw [val₂, e]; exact this

omit [IsCommMonObj A] in
theorem val_pull_pair {K : Type} [Fintype K] {φ : K → ((A ⊗ A).left ⟶ A.left)} {ε : K → ℤ}
    (u : LB.Gen (LB.LinComb L φ ε)) {T T' : Over S} (ρ : T' ⟶ T) {z : T'.left} {J} (hJ : Good L z J) (a b : T ⟶ A) :
    val (LB.pullGen L _ _ u (lift a b).left) ρ.left z J = val₂ u z J (ρ ≫ a) (ρ ≫ b) := by
  rw [val_pull hJ, ← Over.comp_left, comp_lift]; rfl

theorem pair_unique_of_surj (sj : Function.Surjective (A ⊗ A).hom.appTop.hom) (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → ((A ⊗ A).left ⟶ A.left)} {ε : K → ℤ} {φ' : K' → ((A ⊗ A).left ⟶ A.left)} {ε' : K' → ℤ}
    (hF : FormEq φ' ε' φ ε) {u : LB.Gen (LB.LinComb L φ ε)} {u' : LB.Gen (LB.LinComb L φ' ε')} (hu : u.IsGen)
    (hu' : u'.IsGen) (h : ∀ y J, Good L y J → val u (lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A)).left y J =
      val u' (lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A)).left y J)
    {Z : Scheme.{0}} (r : Z ⟶ (A ⊗ A).left) {z : Z} {J} (hJ : Good L z J) : val u r z J = val u' r z J :=
  gen_unique' hL hF (A ⊗ A).hom _
    (Over.w (lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A)))
    sj hu hu' h Z r z J hJ

variable {Lr : RigLB A} (c : CubicalStr A Lr)

theorem ros_add_of_surj (sj : Function.Surjective (A ⊗ A ⊗ A).hom.appTop.hom) (f g : A ⟶ A) [IsMonHom f] [IsMonHom g]
    (u : LB.Gen (LB.LinComb Lr.L (rosatiφ A f g) rosatiε)) (hu : u.IsGen)
    (h₀ : LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (zero2 A)) (LB.oneGen Lr.L)) {T : Over S} {z : T.left} {J}
    (hJ : Good Lr.L z J) (x x' y : T ⟶ A) :
    val₂ u z J (x * x') y * cubV c z J x x' (y ≫ g) =
        cubV c z J (x ≫ f) (x' ≫ f) y * (val₂ u z J x y * val₂ u z J x' y) ∧
      val₂ u z J y (x * x') * cubV c z J y (x ≫ g) (x' ≫ g) =
        cubV c z J (y ≫ f) x x' * (val₂ u z J y x * val₂ u z J y x') := by
  let p₀ := x3 A 0
  let p₁ := x3 A 1
  let p₂ := x3 A 2
  have mf : ∀ {T : Over S} (a b : T ⟶ A), (a * b) ≫ f = (a ≫ f) * (b ≫ f) := fun a b => MonObj.mul_comp a b f
  have mg : ∀ {T : Over S} (a b : T ⟶ A), (a * b) ≫ g = (a ≫ g) * (b ≫ g) := fun a b => MonObj.mul_comp a b g
  have vp : ∀ {T T' : Over S} (ρ : T' ⟶ T) {z : T'.left} {J}, Good Lr.L z J → ∀ a b : T ⟶ A,
      val (LB.pullGen Lr.L _ _ u (lift a b).left) ρ.left z J = val₂ u z J (ρ ≫ a) (ρ ≫ b) := fun ρ z J hJ a b => by
    rw [val_pull hJ, ← Over.comp_left, comp_lift]; rfl
  have v1 : ∀ {y : (𝟙_ (Over S)).left} {J}, Good Lr.L y J → val₂ u y J (1 : 𝟙_ (Over S) ⟶ A) 1 = 1 := fun {y J} hJ => by
    have e : lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A) = lift η[A] η[A] := by simp [Hom.one_def]
    have := val_corr hJ h₀ (𝟙 _)
    rw [val_pull hJ, Category.id_comp, val_one] at this
    rw [val₂, e]; exact this
  let e : 𝟙_ (Over S) ⟶ G3 A := lift 1 (lift 1 1)
  have e₀ : e ≫ p₀ = 1 := by simp [e, p₀, x3]
  have e₁ : e ≫ p₁ = 1 := by simp [e, p₁, x3]
  have e₂ : e ≫ p₂ = 1 := by simp [e, p₂, x3]
  have he : e.left ≫ (A ⊗ A ⊗ A).hom = 𝟙 _ := Over.w e
  let ρ : T ⟶ G3 A := lift x (lift x' y)
  have r₀ : ρ ≫ p₀ = x := by simp [ρ, p₀, x3]
  have r₁ : ρ ≫ p₁ = x' := by simp [ρ, p₁, x3]
  have r₂ : ρ ≫ p₂ = y := by simp [ρ, p₂, x3]
  have gen : ∀ (a b a₁ b₁ a₂ b₂ k₁ k₂ k₃ l₁ l₂ l₃ : G3 A ⟶ A),
      (∀ (V : Type) [CommGroup V] (k : (G3 A ⟶ A) → V),
        (k (l₁ * l₂ * l₃) * (k (l₁ * l₂))⁻¹ * (k (l₁ * l₃))⁻¹ * (k (l₂ * l₃))⁻¹ * k l₁ * k l₂ * k l₃ * (k 1)⁻¹) *
          ((k ((a₁ ≫ f) * b₁) * (k (a₁ ≫ f))⁻¹ * (k b₁)⁻¹ * (k (a₁ * (b₁ ≫ g)))⁻¹ * k a₁ * k (b₁ ≫ g)) *
            (k ((a₂ ≫ f) * b₂) * (k (a₂ ≫ f))⁻¹ * (k b₂)⁻¹ * (k (a₂ * (b₂ ≫ g)))⁻¹ * k a₂ * k (b₂ ≫ g))) =
        (k ((a ≫ f) * b) * (k (a ≫ f))⁻¹ * (k b)⁻¹ * (k (a * (b ≫ g)))⁻¹ * k a * k (b ≫ g)) *
          (k (k₁ * k₂ * k₃) * (k (k₁ * k₂))⁻¹ * (k (k₁ * k₃))⁻¹ * (k (k₂ * k₃))⁻¹ * k k₁ * k k₂ * k k₃ * (k 1)⁻¹)) →
      e ≫ a = 1 → e ≫ b = 1 → e ≫ a₁ = 1 → e ≫ b₁ = 1 → e ≫ a₂ = 1 → e ≫ b₂ = 1 → e ≫ k₁ = 1 → e ≫ l₁ = 1 ∨ e ≫ l₂ = 1 →
      val₂ u z J (ρ ≫ a) (ρ ≫ b) * cubV c z J (ρ ≫ k₁) (ρ ≫ k₂) (ρ ≫ k₃) =
        cubV c z J (ρ ≫ l₁) (ρ ≫ l₂) (ρ ≫ l₃) * (val₂ u z J (ρ ≫ a₁) (ρ ≫ b₁) * val₂ u z J (ρ ≫ a₂) (ρ ≫ b₂)) := by
    intro a b a₁ b₁ a₂ b₂ k₁ k₂ k₃ l₁ l₂ l₃ hF ha hb ha₁ hb₁ ha₂ hb₂ hk hl
    have ev : ∀ {T' : Over S} (σ : T' ⟶ G3 A) {z : T'.left} {J}, Good Lr.L z J →
        val (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (lift a b).left)
          (LB.pullGen Lr.L (thφ A (x3 A)) thε c.t (lift k₁ (lift k₂ k₃)).left)) σ.left z J =
          val₂ u z J (σ ≫ a) (σ ≫ b) * cubV c z J (σ ≫ k₁) (σ ≫ k₂) (σ ≫ k₃) ∧
        val (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L (thφ A (x3 A)) thε c.t (lift l₁ (lift l₂ l₃)).left)
          (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (lift a₁ b₁).left) (LB.pullGen Lr.L _ _ u (lift a₂ b₂).left)))
          σ.left z J = cubV c z J (σ ≫ l₁) (σ ≫ l₂) (σ ≫ l₃) *
            (val₂ u z J (σ ≫ a₁) (σ ≫ b₁) * val₂ u z J (σ ≫ a₂) (σ ≫ b₂)) := fun σ z J hJ =>
      ⟨(val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vp σ hJ _ _) (val_cub c σ hJ _ _ _)),
        (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_cub c σ hJ _ _ _)
          ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vp σ hJ _ _) (vp σ hJ _ _))))⟩
    refine (ev ρ hJ).1.symm.trans (Eq.trans (gen_unique' Lr.isLB (fun V _ k => ?_) _ e.left he sj
      (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hu _) (pullGen_isGen _ _ _ _ c.isGen _))
      (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ c.isGen _) (mulGen_isGen _ _ _ _ _ _ _
        (pullGen_isGen _ _ _ _ hu _) (pullGen_isGen _ _ _ _ hu _))) (fun y I hI => ?_) _ ρ.left z J hJ) (ev ρ hJ).2)
    · exact (prod_sum₂ (K := thK) (K' := Fin 6 ⊕ Fin 6) (U := V) _ (prod_cub l₁ l₂ l₃ k)
        (prod_sum₂ (K := Fin 6) (K' := Fin 6) (U := V) _ (prod_ros f g a₁ b₁ k) (prod_ros f g a₂ b₂ k))).trans
        ((hF V fun q => k q.left).trans (prod_sum₂ (K := Fin 6) (K' := thK) (U := V) _ (prod_ros f g a b k)
          (prod_cub k₁ k₂ k₃ k)).symm)
    · have C : IsCub (cubV c y I) := isCub_cubV c hI
      refine (ev e hI).1.trans (Eq.trans ?_ (ev e hI).2.symm)
      rw [ha, hb, ha₁, hb₁, ha₂, hb₂, hk, v1 hI, C.face]
      rcases hl with hl | hl
      · rw [hl, C.face]; simp
      · rw [hl, C.face₂]; simp
  have o₁ : e ≫ (p₀ * p₁) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [e₀, e₁, _root_.mul_one])
  have s₁ : ρ ≫ (p₀ * p₁) = x * x' := (MonObj.comp_mul _ _ _).trans (by rw [r₀, r₁])
  constructor
  · have := gen (p₀ * p₁) p₂ p₀ p₂ p₁ p₂ p₀ p₁ (p₂ ≫ g) (p₀ ≫ f) (p₁ ≫ f) p₂ (fun V _ k => by
      rw [mf]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) o₁ e₂ e₀ e₂ e₁ e₂ e₀ (Or.inl (by rw [← Category.assoc, e₀, MonObj.one_comp]))
    rwa [s₁, ← Category.assoc ρ p₂, ← Category.assoc ρ p₀, ← Category.assoc ρ p₁, r₀, r₁, r₂] at this
  · have := gen p₂ (p₀ * p₁) p₂ p₀ p₂ p₁ p₂ (p₀ ≫ g) (p₁ ≫ g) (p₂ ≫ f) p₀ p₁ (fun V _ k => by
      rw [mg, _root_.mul_assoc p₂, _root_.mul_assoc (p₂ ≫ f)]
      have : (p₀ * p₁) ≫ g = (p₀ ≫ g) * (p₁ ≫ g) := mg _ _
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) e₂ o₁ e₂ e₀ e₂ e₁ e₂ (Or.inr e₀)
    rwa [s₁, ← Category.assoc ρ p₂, ← Category.assoc ρ p₀, ← Category.assoc ρ p₁, r₀, r₁, r₂] at this

theorem ros_sum_of_surj (sj : Function.Surjective (A ⊗ A).hom.appTop.hom) {f g f₁ g₁ f₂ g₂ : A ⟶ A}
    (hf : f = f₁ * f₂) (hg : g = g₁ * g₂) {u : LB.Gen (LB.LinComb Lr.L (rosatiφ A f g) rosatiε)}
    {u₁ : LB.Gen (LB.LinComb Lr.L (rosatiφ A f₁ g₁) rosatiε)} {u₂ : LB.Gen (LB.LinComb Lr.L (rosatiφ A f₂ g₂) rosatiε)}
    (hu : IsNormGen Lr.L f g u) (hu₁ : IsNormGen Lr.L f₁ g₁ u₁) (hu₂ : IsNormGen Lr.L f₂ g₂ u₂) {T : Over S} {z : T.left} {J}
    (hJ : Good Lr.L z J) (x w : T ⟶ A) :
    val₂ u z J x w * cubV c z J x (w ≫ g₁) (w ≫ g₂) =
      cubV c z J (x ≫ f₁) (x ≫ f₂) w * (val₂ u₁ z J x w * val₂ u₂ z J x w) := by
  subst hf hg
  have ev : ∀ {T : Over S} {z : T.left} {J}, Good Lr.L z J → ∀ x w : T ⟶ A,
      val (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (lift (fst A A) (snd A A)).left)
        (LB.pullGen Lr.L (thφ A (x3 A)) thε c.t (lift (fst A A) (lift (snd A A ≫ g₁) (snd A A ≫ g₂))).left))
        (lift x w).left z J = val₂ u z J x w * cubV c z J x (w ≫ g₁) (w ≫ g₂) ∧
      val (LB.mulGen Lr.L _ _ _ _
        (LB.pullGen Lr.L (thφ A (x3 A)) thε c.t (lift (fst A A ≫ f₁) (lift (fst A A ≫ f₂) (snd A A))).left)
        (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u₁ (lift (fst A A) (snd A A)).left)
          (LB.pullGen Lr.L _ _ u₂ (lift (fst A A) (snd A A)).left))) (lift x w).left z J =
        cubV c z J (x ≫ f₁) (x ≫ f₂) w * (val₂ u₁ z J x w * val₂ u₂ z J x w) := fun hJ x w =>
    ⟨((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull_pair u _ hJ _ _) (val_cub c _ hJ _ _ _))).trans (by
      rw [lift_snd_assoc, lift_snd_assoc, lift_fst, lift_snd]),
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_cub c _ hJ _ _ _) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (val_pull_pair u₁ _ hJ _ _) (val_pull_pair u₂ _ hJ _ _))))).trans (by
      rw [lift_fst_assoc, lift_fst_assoc, lift_fst, lift_snd])⟩
  refine (ev hJ x w).1.symm.trans (Eq.trans (pair_unique_of_surj sj Lr.isLB (fun U _ h => ?_)
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hu.1 _) (pullGen_isGen _ _ _ _ c.isGen _))
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ c.isGen _)
      (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hu₁.1 _) (pullGen_isGen _ _ _ _ hu₂.1 _)))
    (fun y I hI => ?_) _ hJ) (ev hJ x w).2)
  · refine (prod_sum₂ (K := thK) (K' := Fin 6 ⊕ Fin 6) (U := U) _ (prod_cub _ _ _ h)
      (prod_sum₂ (K := Fin 6) (K' := Fin 6) (U := U) _ (prod_ros _ _ _ _ h) (prod_ros _ _ _ _ h))).trans
      (Eq.trans ?_ (prod_sum₂ (K := Fin 6) (K' := thK) (U := U) _ (prod_ros _ _ _ _ h) (prod_cub _ _ _ h)).symm)
    rw [MonObj.comp_mul, MonObj.comp_mul, _root_.mul_assoc (fst A A)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have C : IsCub (cubV c y I) := isCub_cubV c hI
    refine (ev hI 1 1).1.trans (Eq.trans ?_ (ev hI 1 1).2.symm)
    rw [hu.val_origin hI, hu₁.val_origin hI, hu₂.val_origin hI, C.face, C.face₃, _root_.mul_one, _root_.mul_one]

theorem rosati_cubical_additive : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], Function.Surjective (G ⊗ G).hom.appTop.hom → Function.Surjective (G ⊗ G ⊗ G).hom.appTop.hom → ∀ (Lr : RigLB G) (c : CubicalStr G Lr) (O : Type) [CommRing O] [StarRing O] (act : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G) (u : ∀ a : O, LB.Gen (LB.LinComb Lr.L (rosatiφ G (act.act a) (act.act (star a))) rosatiε)), (∀ a, (u a).IsGen ∧ LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ (u a) (zero2 G)) (LB.oneGen Lr.L)) → ∀ (T : Over S) (z : T.left) (J), Good Lr.L z J → (∀ (a : O) (x x' y : T ⟶ G), val₂ (u a) z J (x * x') y * cubV c z J x x' (y ≫ act.act (star a)) = cubV c z J (x ≫ act.act a) (x' ≫ act.act a) y * (val₂ (u a) z J x y * val₂ (u a) z J x' y)) ∧ (∀ (a : O) (x y y' : T ⟶ G), val₂ (u a) z J x (y * y') * cubV c z J x (y ≫ act.act (star a)) (y' ≫ act.act (star a)) = cubV c z J (x ≫ act.act a) y y' * (val₂ (u a) z J x y * val₂ (u a) z J x y')) ∧ (∀ (a b : O) (x y : T ⟶ G), val₂ (u (a + b)) z J x y * cubV c z J x (y ≫ act.act (star a)) (y ≫ act.act (star b)) = cubV c z J (x ≫ act.act a) (x ≫ act.act b) y * (val₂ (u a) z J x y * val₂ (u b) z J x y)) := by
  intro S G _ _ s₂ s₃ Lr c O _ _ act u hu T z J hJ
  refine ⟨fun a x x' y => ?_, fun a x y y' => ?_, fun a b x y => ?_⟩
  · have := act.hom a
    have := act.hom (star a)
    exact (ros_add_of_surj c s₃ _ _ (u a) (hu a).1 (hu a).2 hJ x x' y).1
  · have := act.hom a
    have := act.hom (star a)
    exact (ros_add_of_surj c s₃ _ _ (u a) (hu a).1 (hu a).2 hJ y y' x).2
  · exact ros_sum_of_surj c s₂ (act.add a b) (by rw [star_add, act.add]) (hu (a + b)) (hu a) (hu b) hJ x y

end GlobalTheory.RosatiCube
end
end
