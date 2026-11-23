module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeCocycleClassIndependent
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle005
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle171
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle161
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle169
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle173
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle162
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle170
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle002
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.IsIntegralOfSmoothPf
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.LX

variable {K : Type} [Field K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {C : Type 1} [Category.{0} C]
  {g : C ⥤ Thick (smFun X q)} {D : E.LineData X}

def epsE (Λ : CLiftK g D) (v : ∀ c, (g.obj c).Bˣ) (e : ℕ) {c c' : C} (φ : c ⟶ c') : (g.obj c').Bˣ :=
  Λ.w φ ^ e * v c' * (Units.map (g.map φ).φ.toMonoidHom (v c))⁻¹

def bE (Λ : CLiftK g D) (v : ∀ c, (g.obj c).Bˣ) (e s : ℕ) : CH.Cn (g ⋙ O (smFun X q)) 1 :=
  fun τ => (show (g.obj (τ.obj (Fin.last 1))).B from
    plogK (g.obj (τ.obj (Fin.last 1))).δ s (((epsE Λ v e (τ.map' 0 1) : (g.obj (τ.obj (Fin.last 1))).Bˣ) :
      (g.obj (τ.obj (Fin.last 1))).B) - 1))

theorem grpE_add {G : Type} [AddCommGroup G] (a b c x y z : G) (e : ℕ) :
    e • a + y + -z + (e • b + x + -y) + -(e • c + x + -z) = e • (a + b + -c) := by
  simp only [smul_add, smul_neg]; abel

theorem grpE {G : Type} [CommGroup G] (a b c x y z : G) (e : ℕ) :
    a ^ e * y * z⁻¹ * (b ^ e * x * y⁻¹) * (c ^ e * x * z⁻¹)⁻¹ = (a * b * c⁻¹) ^ e :=
  @grpE_add (Additive G) _ a b c x y z e

theorem grpS_add {G : Type} [AddCommGroup G] (a x x' y y' : G) :
    (a + x + -y) + -(a + x' + -y') = (x + -x') + -(y + -y') := by abel

theorem grpS {G : Type} [CommGroup G] (a x x' y y' : G) :
    (a * x * y⁻¹) * (a * x' * y'⁻¹)⁻¹ = (x * x'⁻¹) * (y * y'⁻¹)⁻¹ :=
  @grpS_add (Additive G) _ a x x' y y'

theorem plog_pow [CharZero K] (T : Thick (smFun X q)) (s : ℕ) (hs : T.pdPow s = ⊥) (a : T.Bˣ)
    (ha : (a : T.B) - 1 ∈ T.J) (n : ℕ) :
    ((a ^ n : T.Bˣ) : T.B) - 1 ∈ T.J ∧
      plogK T.δ s (((a ^ n : T.Bˣ) : T.B) - 1) = n • plogK T.δ s ((a : T.B) - 1) := by
  induction n with
  | zero => simp [GlobalTheory.CompanionTheory.ConeZcls.plogK_zero, T.J.zero_mem]
  | succ n ih =>
    rw [pow_succ]
    refine ⟨GlobalTheory.CompanionTheory.ConeZcls.mul_sub_mem T _ _ ih.1 ha, ?_⟩
    rw [GlobalTheory.CompanionTheory.ConeZcls.plog_mul T s hs _ _ ih.1 ha, ih.2, succ_nsmul]

theorem epsE_rr (Λ : CLiftK g D) (v : ∀ c, (g.obj c).Bˣ) (e : ℕ) {c₀ c₁ c₂ : C} (φ : c₀ ⟶ c₁) (ψ : c₁ ⟶ c₂)
    (χ : c₀ ⟶ c₂) (hχ : χ = φ ≫ ψ) :
    Units.map (g.map ψ).φ.toMonoidHom (epsE Λ v e φ) * epsE Λ v e ψ * (epsE Λ v e χ)⁻¹ =
      GlobalTheory.CompanionTheory.ConeZcls.rr Λ φ ψ χ ^ e := by
  subst hχ
  have h : Units.map (g.map (φ ≫ ψ)).φ.toMonoidHom (v c₀) =
      Units.map (g.map ψ).φ.toMonoidHom (Units.map (g.map φ).φ.toMonoidHom (v c₀)) := by
    rw [g.map_comp]; rfl
  unfold epsE GlobalTheory.CompanionTheory.ConeZcls.rr
  rw [h]
  simp only [map_mul, map_inv, map_pow]
  exact grpE _ _ _ _ _ _ e

def lE (Λ : CLiftK g D) (v : ∀ c, (g.obj c).Bˣ) (e s : ℕ) {c c' : C} (φ : c ⟶ c') : (g.obj c').B :=
  plogK (g.obj c').δ s (((epsE Λ v e φ : (g.obj c').Bˣ) : (g.obj c').B) - 1)

theorem log_rr [CharZero K] (Λ : CLiftK g D) (v : ∀ c, (g.obj c).Bˣ) (e s : ℕ) (hs : ∀ c, (g.obj c).pdPow s = ⊥)
    (hε : ∀ {c c' : C} (φ : c ⟶ c'), ((epsE Λ v e φ : (g.obj c').Bˣ) : (g.obj c').B) - 1 ∈ (g.obj c').J)
    {c₀ c₁ c₂ : C} (φ : c₀ ⟶ c₁) (ψ : c₁ ⟶ c₂) (χ : c₀ ⟶ c₂) (hχ : χ = φ ≫ ψ)
    (hr : ((GlobalTheory.CompanionTheory.ConeZcls.rr Λ φ ψ χ : (g.obj c₂).Bˣ) : (g.obj c₂).B) - 1 ∈ (g.obj c₂).J) :
    e • plogK (g.obj c₂).δ s (((GlobalTheory.CompanionTheory.ConeZcls.rr Λ φ ψ χ : (g.obj c₂).Bˣ) : (g.obj c₂).B) - 1) =
      (g.map ψ).φ (lE Λ v e s φ) + lE Λ v e s ψ - lE Λ v e s χ := by
  have e0 := hε φ
  have e1 := hε ψ
  have e2 := hε χ
  have e0' : ((Units.map (g.map ψ).φ.toMonoidHom (epsE Λ v e φ) : (g.obj c₂).Bˣ) : (g.obj c₂).B) - 1 ∈ (g.obj c₂).J := by
    have := (g.map ψ).hle e0
    simpa using this
  have hm : plogK (g.obj c₂).δ s (((Units.map (g.map ψ).φ.toMonoidHom (epsE Λ v e φ) : (g.obj c₂).Bˣ) :
      (g.obj c₂).B) - 1) = (g.map ψ).φ (lE Λ v e s φ) := by
    unfold lE
    rw [GlobalTheory.CompanionTheory.ConeZcls.plogK_map (g.map ψ) s e0]
    simp
  rw [← (plog_pow (g.obj c₂) s (hs _) _ hr e).2, ← epsE_rr Λ v e φ ψ χ hχ,
    GlobalTheory.CompanionTheory.ConeZcls.plog_mul _ s (hs _) _ _ (GlobalTheory.CompanionTheory.ConeZcls.mul_sub_mem _ _ _ e0' e1)
      (GlobalTheory.CompanionTheory.ConeZcls.inv_sub _ _ e2),
    GlobalTheory.CompanionTheory.ConeZcls.plog_mul _ s (hs _) _ _ e0' e1, GlobalTheory.CompanionTheory.ConeZcls.plog_inv _ s (hs _) _ e2, hm]
  unfold lE
  ring

theorem epsE_div (Λ : CLiftK g D) (v v' : ∀ c, (g.obj c).Bˣ) (e : ℕ) {c c' : C} (φ : c ⟶ c') :
    epsE Λ v e φ * (epsE Λ v' e φ)⁻¹ =
      (v c' * (v' c')⁻¹) * (Units.map (g.map φ).φ.toMonoidHom (v c * (v' c)⁻¹))⁻¹ := by
  unfold epsE
  simp only [map_mul, map_inv]
  exact grpS _ _ _ _ _

theorem lE_sub [CharZero K] (Λ : CLiftK g D) (v v' : ∀ c, (g.obj c).Bˣ) (e s : ℕ) (hs : ∀ c, (g.obj c).pdPow s = ⊥)
    {c c' : C} (φ : c ⟶ c')
    (e1 : ((epsE Λ v e φ : (g.obj c').Bˣ) : (g.obj c').B) - 1 ∈ (g.obj c').J)
    (e2 : ((epsE Λ v' e φ : (g.obj c').Bˣ) : (g.obj c').B) - 1 ∈ (g.obj c').J) :
    lE Λ v e s φ - lE Λ v' e s φ =
      plogK (g.obj c').δ s (((v c' * (v' c')⁻¹ : (g.obj c').Bˣ) : (g.obj c').B) *
        Ring.inverse ((g.map φ).φ (((v c * (v' c)⁻¹ : (g.obj c).Bˣ) : (g.obj c).B))) - 1) := by
  have hR : Ring.inverse ((g.map φ).φ (((v c * (v' c)⁻¹ : (g.obj c).Bˣ) : (g.obj c).B))) =
      (((Units.map (g.map φ).φ.toMonoidHom (v c * (v' c)⁻¹))⁻¹ : (g.obj c').Bˣ) : (g.obj c').B) := by
    rw [← Ring.inverse_unit]; rfl
  unfold lE
  rw [hR, ← Units.val_mul, ← epsE_div Λ v v' e φ,
    GlobalTheory.CompanionTheory.ConeZcls.plog_mul _ s (hs _) _ _ e1 (GlobalTheory.CompanionTheory.ConeZcls.inv_sub _ _ e2),
    GlobalTheory.CompanionTheory.ConeZcls.plog_inv _ s (hs _) _ e2, sub_eq_add_neg]

theorem zK_smul_eq_d [CharZero K] (Λ : CLiftK g D) (v : ∀ c, (g.obj c).Bˣ) (e s : ℕ) (hs : ∀ c, (g.obj c).pdPow s = ⊥)
    (hε : ∀ {c c' : C} (φ : c ⟶ c'), ((epsE Λ v e φ : (g.obj c').Bˣ) : (g.obj c').B) - 1 ∈ (g.obj c').J) :
    e • zK Λ s = CH.d _ 1 (bE Λ v e s) := by
  funext σ
  have hr : ((GlobalTheory.CompanionTheory.ConeZcls.rr Λ (σ.map' 0 1) (σ.map' 1 2) (σ.map' 0 2) : (g.obj (σ.obj (Fin.last 2))).Bˣ) :
      (g.obj (σ.obj (Fin.last 2))).B) - 1 ∈ (g.obj (σ.obj (Fin.last 2))).J := GlobalTheory.T.cone_lift_ratio_mem_ideal Λ σ
  have key := log_rr Λ v e s hs hε (σ.map' 0 1) (σ.map' 1 2) (σ.map' 0 2) (GlobalTheory.CompanionTheory.ConeZcls.composable_arrows_map_zero_two σ) hr
  have h0 : ((g ⋙ O (smFun X q)).map (GlobalTheory.CatH.toLast 0 σ)).hom (bE Λ v e s (GlobalTheory.CatH.face 0 σ)) =
      (show (g.obj (σ.obj (Fin.last 2))).B from lE Λ v e s (σ.map' 1 2)) :=
    GlobalTheory.CompanionTheory.ConeZcls.map_self (g ⋙ O (smFun X q)) σ (Fin.last 2) _ _
  have h1 : ((g ⋙ O (smFun X q)).map (GlobalTheory.CatH.toLast 1 σ)).hom (bE Λ v e s (GlobalTheory.CatH.face 1 σ)) =
      (show (g.obj (σ.obj (Fin.last 2))).B from lE Λ v e s (σ.map' 0 2)) :=
    GlobalTheory.CompanionTheory.ConeZcls.map_self (g ⋙ O (smFun X q)) σ (Fin.last 2) _ _
  have h2 : ((g ⋙ O (smFun X q)).map (GlobalTheory.CatH.toLast 2 σ)).hom (bE Λ v e s (GlobalTheory.CatH.face 2 σ)) =
      (show (g.obj (σ.obj (Fin.last 2))).B from (g.map (σ.map' 1 2)).φ (lE Λ v e s (σ.map' 0 1))) := rfl
  have hd : CH.d (g ⋙ O (smFun X q)) 1 (bE Λ v e s) σ =
      ∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) • ((g ⋙ O (smFun X q)).map (GlobalTheory.CatH.toLast i σ)).hom
        (bE Λ v e s (GlobalTheory.CatH.face i σ)) := rfl
  rw [Pi.smul_apply, hd, Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_smul, neg_smul, even_two, Even.neg_pow, one_pow]
  rw [h0, h1, h2]
  refine key.trans ?_
  have fin : ∀ a b c : (g.obj (σ.obj (Fin.last 2))).B, a + b - c = b + -c + a := fun a b c => by abel
  exact fin _ _ _

theorem bE_mem (Λ : CLiftK g D) (v : ∀ c, (g.obj c).Bˣ) (e s : ℕ)
    (hε : ∀ {c c' : C} (φ : c ⟶ c'), ((epsE Λ v e φ : (g.obj c').Bˣ) : (g.obj c').B) - 1 ∈ (g.obj c').J)
    (τ : ComposableArrows C 1) : (show (g.obj (τ.obj (Fin.last 1))).B from bE Λ v e s τ) ∈ (g.obj (τ.obj (Fin.last 1))).J := by
  change plogK (g.obj (τ.obj (Fin.last 1))).δ s (((epsE Λ v e (τ.map' 0 1) : (g.obj (τ.obj (Fin.last 1))).Bˣ) :
    (g.obj (τ.obj (Fin.last 1))).B) - 1) ∈ _
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ ((g.obj (τ.obj (Fin.last 1))).δ.dpow_mem (Nat.succ_ne_zero k)
    (hε (τ.map' 0 1)))

theorem bE_sub [CharZero K] (Λ : CLiftK g D) (v v' : ∀ c, (g.obj c).Bˣ) (e s : ℕ) (hs : ∀ c, (g.obj c).pdPow s = ⊥)
    (hε : ∀ {c c' : C} (φ : c ⟶ c'), ((epsE Λ v e φ : (g.obj c').Bˣ) : (g.obj c').B) - 1 ∈ (g.obj c').J)
    (hε' : ∀ {c c' : C} (φ : c ⟶ c'), ((epsE Λ v' e φ : (g.obj c').Bˣ) : (g.obj c').B) - 1 ∈ (g.obj c').J)
    (τ : ComposableArrows C 1) :
    (show (g.obj (τ.obj (Fin.last 1))).B from bE Λ v e s τ - bE Λ v' e s τ) =
      plogK (g.obj (τ.obj (Fin.last 1))).δ s
        (((v (τ.obj (Fin.last 1)) * (v' (τ.obj (Fin.last 1)))⁻¹ : (g.obj (τ.obj (Fin.last 1))).Bˣ) :
            (g.obj (τ.obj (Fin.last 1))).B) *
          Ring.inverse (show (g.obj (τ.obj (Fin.last 1))).B from (g.map (τ.map' 0 1)).φ
            (((v (τ.obj 0) * (v' (τ.obj 0))⁻¹ : (g.obj (τ.obj 0)).Bˣ) : (g.obj (τ.obj 0)).B))) - 1) :=
  lE_sub Λ v v' e s hs (τ.map' 0 1) (hε (τ.map' 0 1)) (hε' (τ.map' 0 1))

end CrystallineSemistableComparison.Pb.LX
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N)

theorem biInf_preimage {m : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K) (S : Finset (Fin m)) :
    ⨅ k ∈ S, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k) = i ⁻¹ᵁ Proj.basicOpen (grK K N) (yS y S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    ext x
    simp [yS, Proj.basicOpen]
  | insert a S ha ih =>
    rw [Finset.iInf_insert, ih]
    simp only [yS]
    rw [Finset.prod_insert ha, Proj.basicOpen_mul]
    rfl

theorem isAffineOpen_preimage (hci : IsClosedImmersion i) {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ}
    (hg : g ∈ grK K N e) (he : 0 < e) : IsAffineOpen (i ⁻¹ᵁ Proj.basicOpen (grK K N) g) := by
  haveI := hci
  exact (Proj.isAffineOpen_basicOpen (grK K N) g hg he).preimage i

theorem evV_surjective (hci : IsClosedImmersion i) {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ}
    (hg : g ∈ grK K N e) (he : 0 < e) :
    Function.Surjective (evV i g (i ⁻¹ᵁ Proj.basicOpen (grK K N) g) le_rfl) := by
  first
    | exact GlobalTheory.T.basic_open_eval_surjective ..
    | (intros; apply GlobalTheory.T.basic_open_eval_surjective <;> assumption)

theorem range_resO_eq (hci : IsClosedImmersion i) {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ}
    (hg : g ∈ grK K N e) (he : 0 < e) {V W : X.Opens} (hW : W = i ⁻¹ᵁ Proj.basicOpen (grK K N) g) (h : V ≤ W)
    (h' : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) g) : Set.range (resO h) = Set.range (evV i g V h') := by
  subst hW
  have e0 : i.appLE _ (i ⁻¹ᵁ Proj.basicOpen (grK K N) g) le_rfl ≫ X.presheaf.map (homOfLE h).op = i.appLE _ V h' :=
    Scheme.Hom.appLE_map i _ _
  have hcomp : evV i g V h' = (resO h).comp (evV i g _ le_rfl) := by
    refine RingHom.ext fun a => ?_
    simp only [evV, resO, RingHom.comp_apply, ← e0]
    rfl
  rw [hcomp, RingHom.coe_comp, Set.range_comp, (evV_surjective i hci hg he).range_eq, Set.image_univ]

theorem iSup_preimage_eq_top {m e : ℕ} (he : 0 < e) (y : Fin m → MvPolynomial (Fin (N + 1)) K)
    (hy : ∀ k, (y k).IsHomogeneous e)
    (hfin : Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk (homIdeal i) (y k)))
      (MvPolynomial (Fin (N + 1)) K ⧸ homIdeal i)) :
    ⨆ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k) = ⊤ := by
  first
    | exact GlobalTheory.T.basic_opens_cover_of_finite ..
    | (intros; apply GlobalTheory.T.basic_opens_cover_of_finite <;> assumption)

theorem finiteType_affine (q : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType q] {W : X.Opens}
    (hW : IsAffineOpen W) : letI := (strV q W).toAlgebra; Algebra.FiniteType K Γ(X, W) := by
  first
    | exact GlobalTheory.T.affine_open_finiteType ..
    | (intros; apply GlobalTheory.T.affine_open_finiteType <;> assumption)

end CrystallineSemistableComparison.Pb
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

theorem isIntegral_of_smooth {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    [ConnectedSpace X] (n : ℕ) [SmoothOfRelativeDimension n q] : IsIntegral X :=
  isIntegral_of_smooth_pf q n

theorem exists_etale_away {K A : Type} [Field K] [CharZero K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.FiniteType K A] {d : ℕ} (s : Fin d → A) (hs : AlgebraicIndependent K s)
    (halg : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range s)) A) :
    ∃ g : A, g ≠ 0 ∧ (MvPolynomial.eval₂Hom (algebraMap K (Localization.Away g))
      (fun k => algebraMap A (Localization.Away g) (s k)) : MvPolynomial (Fin d) K →+* Localization.Away g).Etale :=
  exists_etale_away_pf s hs halg

theorem exists_coord_basicOpen {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    {W : X.Opens} (hW : IsAffineOpen W) (g : Γ(X, W)) {d : ℕ} (s : Fin d → Γ(X, W)) :
    letI := (strV q W).toAlgebra
    (MvPolynomial.eval₂Hom (algebraMap K (Localization.Away g))
      (fun k => algebraMap Γ(X, W) (Localization.Away g) (s k)) : MvPolynomial (Fin d) K →+* Localization.Away g).Etale →
    ∃ c : Coord q (X.basicOpen g) d, ∀ k, c.t k = resO (X.basicOpen_le g) (s k) :=
  GlobalTheory.T.coords_of_etale_basic_open q hW g s

theorem coord_card_eq {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)
    [SmoothOfRelativeDimension n q] {V : X.Opens} (hne : (V : Set X).Nonempty) {m : ℕ} (c : Coord q V m) : m = n :=
  GlobalTheory.T.coord_dim_eq_relative_dim q n hne c

theorem exists_frac_basicOpen {X : Scheme.{0}} {W : X.Opens} (hW : IsAffineOpen W) (g : Γ(X, W))
    (hne : (X.basicOpen g : Set X).Nonempty) :
    ∀ r : Γ(X, X.basicOpen g), ∃ b ∈ Set.range (resO (X.basicOpen_le g)), ∃ b' ∈ Set.range (resO (X.basicOpen_le g)),
      b' ≠ 0 ∧ r * b' = b := by
  intro r
  letI := (resO (X.basicOpen_le g)).toAlgebra
  haveI := hW.isLocalization_basicOpen g
  haveI : Nonempty (X.basicOpen g) := hne.to_subtype
  obtain ⟨k, a, hk⟩ := IsLocalization.Away.surj g r
  refine ⟨resO (X.basicOpen_le g) a, ⟨a, rfl⟩, resO (X.basicOpen_le g) (g ^ k), ⟨g ^ k, rfl⟩, ?_, ?_⟩
  · rw [map_pow]
    exact ((IsLocalization.Away.algebraMap_isUnit (S := Γ(X, X.basicOpen g)) g).pow k).ne_zero
  · rw [map_pow]
    exact hk

end CrystallineSemistableComparison.Pb
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N)

theorem homIdeal_homog : ∀ f ∈ homIdeal i, ∀ n : ℕ, MvPolynomial.homogeneousComponent n f ∈ homIdeal i := by
  first
    | exact GlobalTheory.T.homogeneous_ideal_component_mem ..
    | (intros; apply GlobalTheory.T.homogeneous_ideal_component_mem <;> assumption)

theorem homIdeal_ne_top [Nonempty X] : homIdeal i ≠ ⊤ := by
  first
    | exact GlobalTheory.T.homogeneous_ideal_ne_top ..
    | (intros; apply GlobalTheory.T.homogeneous_ideal_ne_top <;> assumption)

theorem preimage_basicOpen_nonempty [IsIntegral X] {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ} (he : 0 < e)
    (hg : g ∈ grK K N e) (hg0 : Ideal.Quotient.mk (homIdeal i) g ≠ 0) :
    ((i ⁻¹ᵁ Proj.basicOpen (grK K N) g : X.Opens) : Set X).Nonempty := by
  first
    | exact GlobalTheory.T.basic_open_nonempty_of_ne_zero ..
    | (intros; apply GlobalTheory.T.basic_open_nonempty_of_ne_zero <;> assumption)

end CrystallineSemistableComparison.Pb
end
end
