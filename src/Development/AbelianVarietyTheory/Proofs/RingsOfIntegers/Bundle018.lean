module

public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle003
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.BoxProductLinearIndependent
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxSec
import Mathlib.Algebra.Module.StablyFree.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle013
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.TauBalBox

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily

variable {R : Type} [CommRing R] [IsDomain R] {j : ℕ} {D D' : DegPre R}

theorem tau_val (D : DegPre R) {Z : Scheme.{0}} {y : Z} {J} (hJ : Good D.P.L y J) (p q : D.X) (r : Z ⟶ (TK R).left) :
    val (D.tau p q) r y J = val (D.psi (p + q)) r y J * (val (D.psi p) r y J)⁻¹ * (val (D.psi q) r y J)⁻¹ *
      (val D.rigK r y J)⁻¹ := by
  unfold DegPre.tau
  rw [val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv, val_inv]

private theorem inv_mul_mul_mul_inv_mul_eq_commGroup {G : Type*} [CommGroup G] (A B C E a b c e : G) :
    A⁻¹ * B * C * E⁻¹ * (a * b⁻¹ * c⁻¹ * e⁻¹) = A⁻¹ * a * (B⁻¹ * b)⁻¹ * (C⁻¹ * c)⁻¹ * (E * e)⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem tau_box (pD : IsPowDeg D' D j) {y : (TK R).left} {J J'} (hJ : Good D.P.L y J) (hJ' : Good D'.P.L y J')
    (p q : D'.X) :
    ((om pD.w y J J' (cP D' (TK R) p * cP D' (TK R) q).left)⁻¹ * om pD.w y J J' (cP D' (TK R) p).left *
      om pD.w y J J' (cP D' (TK R) q).left *
      (om pD.w y J J' (𝟙 _ ≫ (toUnit (TK R)).left ≫ eSec D'.P.A))⁻¹) * val (D'.tau p q) (𝟙 _) y J' =
      ∏ i, val (D.tau (pD.xe p i) (pD.xe q i)) (𝟙 _) y J := by
  have hc : ∀ x : D'.X, 𝟙 _ ≫ D'.xK x = (cP D' (TK R) x).left := fun x => by
    simp only [Category.id_comp, DegPre.xK, ptK, cP]
  have hpq : cP D' (TK R) (p + q) = cP D' (TK R) p * cP D' (TK R) q := by
    unfold cP
    rw [D'.c_add, padd, comp_lift_assoc]
    rfl
  have h1 := psi_val pD hJ hJ' (p + q) (𝟙 _)
  have h2 := psi_val pD hJ hJ' p (𝟙 _)
  have h3 := psi_val pD hJ hJ' q (𝟙 _)
  have h4 := rig_val pD hJ hJ' (𝟙 _)
  rw [hc, hpq] at h1
  rw [hc] at h2 h3
  have e : ∀ i, val (D.tau (pD.xe p i) (pD.xe q i)) (𝟙 _) y J =
      val (D.psi (pD.xe (p + q) i)) (𝟙 _) y J * (val (D.psi (pD.xe p i)) (𝟙 _) y J)⁻¹ *
        (val (D.psi (pD.xe q i)) (𝟙 _) y J)⁻¹ * (val D.rigK (𝟙 _) y J)⁻¹ := fun i => by
    rw [tau_val D hJ, map_add (f := _), Pi.add_apply]
  rw [Finset.prod_congr rfl (fun i _ => e i), Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_inv_distrib, Finset.prod_inv_distrib, ← h1, ← h2,
    ← h3, ← h4, tau_val D' hJ' p q (𝟙 _)]
  exact inv_mul_mul_mul_inv_mul_eq_commGroup _ _ _ _ _ _ _ _

theorem rosatiφ_pr {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
    (π : A' ⟶ A) [IsMonHom π] {f g : A ⟶ A} {f' g' : A' ⟶ A'} (hf : f' ≫ π = π ≫ f) (hg : g' ≫ π = π ≫ g)
    (a : Fin 6) : rosatiφ A' f' g' a ≫ π.left = (π ⊗ₘ π).left ≫ rosatiφ A f g a := by
  fin_cases a <;>
    simp [rosatiφ, padd, ← Over.comp_left, comp_lift_assoc, IsMonHom.mul_hom, lift_map_assoc, hf, hg,
      tensorHom_fst_assoc, tensorHom_snd_assoc, tensorHom_fst, tensorHom_snd]

private theorem mul_eq_of_four_relations_commGroup {G : Type*} [CommGroup G] (X1 X2 X3 X4 LinearSubstitution X6 Eo t1 t2 U P1 P2 PU : G)
    (hT1 : X1⁻¹ * X2 * X3 * Eo⁻¹ * t1 = P1) (hT2 : X4⁻¹ * LinearSubstitution * X6 * Eo⁻¹ * t2 = P2)
    (hBU : X1 * X2⁻¹ * X3⁻¹ * X4⁻¹ * LinearSubstitution * X6 * U = PU) (hB : P1 * PU = P2) : t1 * U = t2 := by
  subst hT1 hBU hB
  apply mul_left_cancel (a := X4⁻¹ * LinearSubstitution * X6 * Eo⁻¹)
  rw [hT2]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

private theorem mul_inv_inv_inv_mul_mul_eq_one {G : Type*} [CommGroup G] (x : G) : x * x⁻¹ * x⁻¹ * x⁻¹ * x * x = 1 := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel

theorem tauBal_pow : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j) (f g : D.P.A ⟶ D.P.A) (f' g' : D'.P.A ⟶ D'.P.A), IsMonHom f → IsMonHom g → IsMonHom f' → IsMonHom g' → (∀ i, f' ≫ pD.pw.pr i = pD.pw.pr i ≫ f) → (∀ i, g' ≫ pD.pw.pr i = pD.pw.pr i ≫ g) → RosatiAdj D.P.A D.P.L f g → ∀ (a a' : D.X → D.X) (b b' : D'.X → D'.X), (∀ x i, pD.xe (b x) i = a (pD.xe x i)) → (∀ x i, pD.xe (b' x) i = a' (pD.xe x i)) → (∀ y, D.c (a y) = D.c y ≫ f) → (∀ y, D.c (a' y) = D.c y ≫ g) → D.TauBal f g a a' → D'.TauBal f' g' b b' := by
  intro hG R _ _ j D D' pD f g f' g' hfm hgm hfm' hgm' hf hg hr a a' b b' hb hb' ca ca' hB
  have hcb : ∀ x, cP D' (TK R) x ≫ f' = cP D' (TK R) (b x) := fun x => by
    unfold cP
    rw [Category.assoc]
    congr 1
    refine pD.pw.lim.hom_ext (fun k => ?_)
    rcases k with ⟨i⟩
    simp only [Fan.mk_π_app, Category.assoc, hf i, pD.c_pr, ← reassoc_of% (pD.c_pr x i), hb, ca]
  have hcb' : ∀ x, cP D' (TK R) x ≫ g' = cP D' (TK R) (b' x) := fun x => by
    unfold cP
    rw [Category.assoc]
    congr 1
    refine pD.pw.lim.hom_ext (fun k => ?_)
    rcases k with ⟨i⟩
    simp only [Fan.mk_π_app, Category.assoc, hg i, pD.c_pr, ← reassoc_of% (pD.c_pr x i), hb', ca']
  unfold DegPre.TauBal
  intro u' hu' h0' y y'
  obtain ⟨u, hu, h0⟩ := exists_ros hG D.P.isAb D.P.isLB f g hr
  apply corr_of_val D'.P.isLB
  intro z J' hJ'
  obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB z
  rw [val_mul hJ', val_pull hJ', Category.id_comp]
  have T1 := tau_box pD hJ hJ' (b y) y'
  have T2 := tau_box pD hJ hJ' y (b' y')
  have HB : ∀ i, val (D.tau (pD.xe (b y) i) (pD.xe y' i)) (𝟙 _) z J *
      val u (D.pt2 (pD.xe y i) (pD.xe y' i)) z J = val (D.tau (pD.xe y i) (pD.xe (b' y') i)) (𝟙 _) z J := fun i => by
    rw [hb, hb']
    have := val_corr hJ (hB u hu h0 (pD.xe y i) (pD.xe y' i)) (𝟙 _)
    rwa [val_mul hJ, val_pull hJ, Category.id_comp] at this
  have hpt : ∀ i, D'.pt2 y y' ≫ (pD.pw.pr i ⊗ₘ pD.pw.pr i).left = D.pt2 (pD.xe y i) (pD.xe y' i) := fun i => by
    show (lift (cP D' (TK R) y) (cP D' (TK R) y')).left ≫ _ = (lift (cP D (TK R) _) (cP D (TK R) _)).left
    rw [← Over.comp_left, lift_map, cPoint_pr pD, cPoint_pr pD]
  have hψ : ∀ i k, rosatiφ D'.P.A f' g' k ≫ (pD.pw.pr i).left =
      (pD.pw.pr i ⊗ₘ pD.pw.pr i).left ≫ rosatiφ D.P.A f g k := fun i k => by
    have := pD.pw.hom i
    exact rosatiφ_pr (pD.pw.pr i) (hf i) (hg i) k
  have hp : Function.Surjective (D'.P.A ⊗ D'.P.A).hom.appTop.hom := by
    have h1 := surj_comp (surj_snd hG D'.P.isAb D'.P.A) (hG _ D'.P.A D'.P.isAb).2
    rwa [Over.w] at h1
  have hone : ∀ {Z : Scheme.{0}} (z₀ : Z) (J₀ : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z₀ J₀ → ∀ (r : Z ⟶ (𝟙_ (Over (Spec (CommRingCat.of R)))).left), val u' (r ≫ zero2 D'.P.A) z₀ J₀ = 1 := by
    intro Z z₀ J₀ hJ₀ r
    have := val_corr hJ₀ h0' r
    rwa [val_pull hJ₀, val_one] at this
  have hcond : ∀ (y₀ : (𝟙_ (Over (Spec (CommRingCat.of R)))).left) J₀ J₀', Good D.P.L y₀ J₀ → Good D'.P.L y₀ J₀' →
      (∏ k, bw pD.w (zero2 D'.P.A ≫ rosatiφ D'.P.A f' g' k) y₀
        (fun i => J₀ ((zero2 D'.P.A ≫ rosatiφ D'.P.A f' g' k) ≫ (pD.pw.pr i).left))
        (J₀' (zero2 D'.P.A ≫ rosatiφ D'.P.A f' g' k)) ^ rosatiε k) * val u' (zero2 D'.P.A) y₀ J₀' =
      ∏ i, val u (zero2 D'.P.A ≫ (pD.pw.pr i ⊗ₘ pD.pw.pr i).left) y₀ J₀ := by
    intro y₀ J₀ J₀' hJ₀ hJ₀'
    have hz : ∀ i, zero2 D'.P.A ≫ (pD.pw.pr i ⊗ₘ pD.pw.pr i).left = 𝟙 _ ≫ zero2 D.P.A := fun i => by
      have := pD.pw.hom i
      rw [Category.id_comp]
      unfold zero2
      rw [← Over.comp_left, lift_map, IsMonHom.one_hom]
    have hz' := hone y₀ J₀' hJ₀' (𝟙 _)
    rw [Category.id_comp] at hz'
    have hu0 : val u (𝟙 _ ≫ zero2 D.P.A) y₀ J₀ = 1 := by
      have := val_corr hJ₀ h0 (𝟙 _)
      rwa [val_pull hJ₀, val_one] at this
    simp only [hz, hu0, Finset.prod_const_one, hz', _root_.mul_one]
    have PR0 := prod_ros f' g' (η[D'.P.A]) (η[D'.P.A]) (fun ψ => om pD.w y₀ J₀ J₀' ψ)
    beta_reduce at PR0
    have e1 : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A) = η[D'.P.A] := by
      show toUnit _ ≫ η[D'.P.A] = η[D'.P.A]
      rw [toUnit_unit, Category.id_comp]
    have e2 : η[D'.P.A] * η[D'.P.A] = η[D'.P.A] := by rw [← e1, _root_.mul_one]
    rw [IsMonHom.one_hom, IsMonHom.one_hom, e2] at PR0
    exact PR0.trans (mul_inv_inv_inv_mul_mul_eq_one _)
  have BU := CubBox.box_unique D.P.isLB D'.P.isLB pD.w pD.w_gen hψ hu' hu ((D'.P.A ⊗ D'.P.A).hom) (zero2 D'.P.A)
    (by unfold zero2; exact Over.w (lift η[D'.P.A] η[D'.P.A])) hp hcond (TK R).left (D'.pt2 y y') z J J' hJ hJ'
  simp only [hpt] at BU
  have BU2 : (∏ k, om pD.w z J J' ((lift (cP D' (TK R) y) (cP D' (TK R) y')).left ≫ rosatiφ D'.P.A f' g' k) ^
      rosatiε k) * val u' (D'.pt2 y y') z J' = ∏ i, val u (D.pt2 (pD.xe y i) (pD.xe y' i)) z J := BU
  have PR := prod_ros f' g' (cP D' (TK R) y) (cP D' (TK R) y') (fun ψ => om pD.w z J J' ψ)
  beta_reduce at PR
  rw [hcb, hcb'] at PR
  rw [PR] at BU2
  exact mul_eq_of_four_relations_commGroup _ _ _ _ _ _ _ _ _ _ _ _ _ T1 T2 BU2
    (by rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl (fun i _ => HB i))

end GlobalTheory.TauBalBox
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem expBijF_of_admissible_base : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I →
    ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R)))
      [GrpObj G] [IsCommMonObj G] (U : Unif I D A G), Geo.Tor.ExpBijF U.toUnifPre :=
  fun hL _ R _ _ I _ D A G _ _ U => expansion_bijective_over_fields hL.globalFns R I D A G U

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace BoxFamIndep

open ReciprocityTheory.ChartRestriction.G.Geo.Tor BoxIndep

theorem exists_tensor_pow (F O : Type) [Field F] [CommRing O] [Algebra F O] {A : Type} {m : ℕ} (β : A → Fin m → O)
    (hβ : ∀ c : Fin m → F, (∀ α, ∑ l, c l • β α l = 0) → c = 0) (j : ℕ) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra F B) (em : Fin j → (O →ₐ[F] B)),
      ∀ c : (Fin j → Fin m) → F,
        (∀ α : Fin j → A, ∑ a, c a • ∏ i, em i (β (α i) (a i)) = 0) → c = 0 := by
  induction j with
  | zero =>
    refine ⟨F, inferInstance, inferInstance, fun i => i.elim0, fun c hc => ?_⟩
    have := hc (fun i => i.elim0)
    funext a
    rw [Fintype.sum_unique] at this
    rw [Subsingleton.elim a default]
    simpa using this
  | succ j ih =>
    obtain ⟨B, _, _, em, h⟩ := ih
    refine ⟨TensorProduct F O B, inferInstance, inferInstance,
      Fin.cons Algebra.TensorProduct.includeLeft
        (fun i => (Algebra.TensorProduct.includeRight).comp (em i)), fun c hc => ?_⟩
    have key : ∀ (α₀ : A) (α : Fin j → A), ∑ l : Fin m, β α₀ l ⊗ₜ[F]
        (∑ a : Fin j → Fin m, c (Fin.cons l a) • ∏ i, em i (β (α i) (a i))) = 0 := by
      intro α₀ α
      rw [← hc (Fin.cons α₀ α), ← (Fin.consEquiv (fun _ : Fin (j+1) => Fin m)).sum_comp, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, AlgHom.comp_apply]
      rw [← map_prod, Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul, TensorProduct.tmul_smul]
    have key2 : ∀ l, (fun a : Fin j → Fin m => c (Fin.cons l a)) = 0 := fun l => h _ fun α => by
      refine (Module.forall_dual_apply_eq_zero_iff F _).1 fun φ => ?_
      refine congrFun (hβ (fun l => φ (∑ a : Fin j → Fin m, c (Fin.cons l a) • ∏ i, em i (β (α i) (a i))))
        fun α₀ => ?_) l
      have := congrArg (fun t => TensorProduct.rid F O (LinearMap.lTensor O φ t)) (key α₀ α)

      simpa only [map_sum (LinearMap.lTensor O φ), map_sum (TensorProduct.rid F O), LinearMap.lTensor_tmul,
      TensorProduct.rid_tmul, map_zero] using this
    funext a
    have := congrFun (key2 (a 0)) (Fin.tail a)
    simp only [Fin.cons_self_tail] at this
    exact this

variable {X Z : Scheme.{0}}

theorem exists_test {F : Type} [Field F] (p : X ⟶ Spec (CommRingCat.of F)) (x : X) {A : Type} {U : A → X.Opens}
    (hx : ∀ α, x ∈ U α) {m : ℕ} (s : ∀ α, Fin m → Γ(X, U α))
    (hs : ∀ c : Fin m → F, (∀ α, ∑ l, germOf p x (c l) * gs (𝟙 X) x (U α) (s α l) = 0) → c = 0) (j : ℕ) :
    ∃ (Z : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of F)) (r : Fin j → (Z ⟶ X)), (∀ i, r i ≫ p = q) ∧
      (∀ i z α, r i z ∈ U α) ∧ ∀ c : (Fin j → Fin m) → F,
        (∀ (α : Fin j → A) z, ∑ a, germOf q z (c a) * ∏ i, gs (r i) z (U (α i)) (s (α i) (a i)) = 0) → c = 0 := by
  let : Algebra F (X.presheaf.stalk x) := (germOf p x).toAlgebra
  obtain ⟨B, _, _, em, h⟩ := exists_tensor_pow F _ (fun α l => gs (𝟙 X) x (U α) (s α l))
    (fun c hc => hs c fun α => by
      have := hc α
      simp only [Algebra.smul_def] at this
      exact this) j
  refine ⟨Spec (CommRingCat.of B), Spec.map (CommRingCat.ofHom (algebraMap F B)),
    fun i => (Spec.map (CommRingCat.ofHom (em i).toRingHom) : _ ⟶ Spec (X.presheaf.stalk x)) ≫ X.fromSpecStalk x,
    fun i => ?_, fun i z α => fromSpecStalk_mem x (hx α) _, fun c hc => ?_⟩
  · rw [Category.assoc, fromSpecStalk_comp]
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a
    exact (em i).commutes a
  · refine h c fun α => eq_zero_of_germOf (B := CommRingCat.of B) _ fun z => ?_

    rw [← hc α z, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Algebra.smul_def, map_mul, map_prod]
    congr 1
    · rw [← Category.id_comp (Spec.map _), germOf_map]; rfl
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [gs_fromSpecStalk x (hx _)]
      exact (germOf_map (B := X.presheaf.stalk x) (𝟙 _) (CommRingCat.ofHom (em i).toRingHom) z _).symm

variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

theorem sum_f {D : DegPre R} {K : Type} (S : Finset K) (b : K → Fam D F k) (α : D.X) (jj) :
    ((∑ l ∈ S, b l).s α).f jj = ∑ l ∈ S, ((b l).s α).f jj := by
  classical
  induction S using Finset.induction_on with
  | empty => rfl
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_f, ih]

theorem gs_comb {D : DegPre R} {K : Type} [Fintype K] (c : K → F) (b : K → Fam D F k) (α : D.X) (jj)
    (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (hz : r z ∈ LB.wchart D.P.L (DegPre.famφ D F α) jj) :
    gs r z (LB.wchart D.P.L (DegPre.famφ D F α) jj) (((∑ l, c l • b l).s α).f jj) =
      ∑ l, germOf (B := CommRingCat.of F) (r ≫ (fst (TF (R := R) F) D.P.A).left) z (c l) *
        gs r z (LB.wchart D.P.L (DegPre.famφ D F α) jj) (((b l).s α).f jj) := by
  refine (congrArg _ (sum_f _ _ α jj)).trans ?_
  refine (gs_fsum r z _ hz _ _).trans (Finset.sum_congr rfl fun l _ => ?_)
  refine (gs_mul r z _ hz _ _).trans (congrArg (· * _) ?_)
  exact (gs_res r z le_top hz _).trans
    ((gs_pull r (fst (TF (R := R) F) D.P.A).left z ⊤ trivial _).trans (germOf_apply _ _ _).symm)

theorem main {j : ℕ} {D D' : DegPre R} (pD : IsPowDeg D' D j) {m : ℕ} (b : Fin m → Fam D F k)
    (hb : LinearIndependent F b) (b' : (Fin j → Fin m) → Fam D' F k)
    (hb' : ∀ a, IsBoxFam pD F k (b' a) (fun i => b (a i))) : LinearIndependent F b' := by
  refine Fintype.linearIndependent_iff.2 fun c hc => congrFun (?_ : c = 0)
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have hg := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres D.P.A.hom
  have hint : IsIntegral (DegPre.BF D F).left :=
    hg.geometrically_isIntegral (TF (R := R) F).hom _ _ (IsPullback.of_hasPullback (TF (R := R) F).hom D.P.A.hom).flip
  choose J₀ hJ₀ using fun χ : (DegPre.BF D F).left ⟶ D.P.A.left =>
    exists_chart D.P.isLB (χ (genericPoint (DegPre.BF D F).left))
  have hx : ∀ α, genericPoint (DegPre.BF D F).left ∈
      LB.wchart D.P.L (DegPre.famφ D F α) (fun a => J₀ (DegPre.famφ D F α a)) :=
    fun α => Set.mem_iInter.2 fun a => hJ₀ _
  obtain ⟨Z, q, r, hq, hr, H⟩ := exists_test (F := F) (fst (TF (R := R) F) D.P.A).left _ hx
    (fun α l => ((b l).s α).f (fun a => J₀ (DegPre.famφ D F α a)))
    (fun c hc => funext <| Fintype.linearIndependent_iff.1 hb c <| fam_ext fun α jj => by
      refine fn_ext fun y hy => congrArg _ ?_
      have hy' : genericPoint (DegPre.BF D F).left ∈ LB.wchart D.P.L (DegPre.famφ D F α) jj :=
        ((genericPoint_spec _).mem_open_set_iff (TopologicalSpace.Opens.isOpen _)).mpr ⟨y, trivial, hy⟩
      apply germ_injective_of_isIntegral _ _ hy'
      refine (gs_eq (𝟙 _) _ _ hy' _).symm.trans (Eq.trans ?_ (map_zero _).symm)
      refine (sec_trans _ (𝟙 _) _ hy' (hx α)).trans ?_
      refine (congrArg _ ((gs_comb c b α _ (𝟙 _) _ (hx α)).trans ?_)).trans (mul_zero _)
      rw [Category.id_comp]
      exact hc α) j
  let T : Over (Spec (CommRingCat.of R)) := Over.mk (q ≫ (TF (R := R) F).hom)
  let q' : T ⟶ TF (R := R) F := Over.homMk q rfl
  let r' : Fin j → (T ⟶ DegPre.BF D F) := fun i => Over.homMk (r i) (by
    rw [← Over.w (fst (TF (R := R) F) D.P.A), ← Category.assoc, hq]; rfl)
  let ρ : T ⟶ DegPre.BF D' F := lift q' (Fan.IsLimit.lift pD.pw.lim fun i => r' i ≫ snd _ _)
  have hρ : ∀ i, ρ ≫ TF (R := R) F ◁ pD.pw.pr i = r' i := fun i => by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, whiskerLeft_fst, lift_fst]
      exact Over.OverMorphism.ext (hq i).symm
    · rw [Category.assoc, whiskerLeft_snd, ← Category.assoc, lift_snd]
      exact Fan.IsLimit.fac pD.pw.lim _ i
  have hρ' : ∀ i, (ρ.left : Z ⟶ _) ≫ prB pD F i = r i := fun i => congrArg (fun g => g.left) (hρ i)
  have hρq : (ρ.left : Z ⟶ _) ≫ (fst (TF (R := R) F) D'.P.A).left = q :=
    congrArg (fun g => g.left) (lift_fst q' (Fan.IsLimit.lift pD.pw.lim fun i => r' i ≫ snd _ _))
  refine H c fun α z => ?_
  obtain ⟨α', rfl⟩ := pD.xe.surjective α
  choose J hJ using fun ψ : Z ⟶ D.P.A.left => exists_chart D.P.isLB (ψ z)
  have hJ : Good D.P.L z J := hJ
  choose J' hJ' using fun ψ : Z ⟶ D'.P.A.left => exists_chart D'.P.isLB (ψ z)
  have hJ' : Good D'.P.L z J' := hJ'
  have hm := hJ'.mem (DegPre.famφ D' F α') (ρ.left : Z ⟶ _)
  have E := (gs_comb c b' α' _ (ρ.left : Z ⟶ _) z hm).symm.trans
    ((congrArg (fun s : Fam D' F k => gs (Y := Z) ρ.left z _ ((s.s α').f _)) hc).trans (gs_zero _ _ _ hm))
  rw [hρq] at E
  have E' := fun a => BoxPhi.fam_val pD (hb' a) α' (Z := Z) ρ.left z hJ hJ'
  simp only [hρ'] at E'
  obtain ⟨u, hu⟩ : ∃ u : Z.presheaf.stalk z, ∀ a, u * sval (Z := Z) ((b' a).s α') ρ.left z J' =
      ∏ i, sval ((b (a i)).s (pD.xe α' i)) (r i) z J := ⟨_, E'⟩
  obtain ⟨v, hv⟩ : ∃ v : Fin j → Z.presheaf.stalk z, ∀ i l,
      gs (r i) z (LB.wchart D.P.L (DegPre.famφ D F (pD.xe α' i)) (fun a => J₀ (DegPre.famφ D F (pD.xe α' i) a)))
        (((b l).s (pD.xe α' i)).f (fun a => J₀ (DegPre.famφ D F (pD.xe α' i) a))) =
      v i * sval ((b l).s (pD.xe α' i)) (r i) z J :=
    ⟨_, fun i l => sec_trans _ (r i) z (hr i z _) (hJ.mem _ (r i))⟩
  refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_) ((Finset.mul_sum _ _ ((∏ i, v i) * u)).symm.trans
    ((congrArg _ E).trans (mul_zero _)))
  refine Eq.trans (congrArg _ (((Finset.prod_congr rfl fun i _ => hv i (a i)).trans Finset.prod_mul_distrib).trans
    (congrArg _ (hu a).symm))) ?_
  exact (congrArg _ (_root_.mul_assoc _ _ _).symm).trans (mul_left_comm _ _ _)

end BoxFamIndep

theorem boxFam_linearIndependent : ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j) (F : Type) [Field F] [Algebra (FractionRing R) F] (k m : ℕ) (b : Fin m → Fam D F k), LinearIndependent F b → ∀ b' : (Fin j → Fin m) → Fam D' F k, (∀ a, IsBoxFam pD F k (b' a) (fun i => b (a i))) → LinearIndependent F b' :=
  fun _ _ _ _ _ _ pD _ _ _ _ _ b hb b' hb' => BoxFamIndep.main pD b hb b' hb'

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
theorem _root_.GlobalTheory.T.pullAl_extension_field_of_fraction : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (E : Fam D.toPre (FractionRing V) k) (E' : Fam D.toPre (FractionRing V) (k * N)) (g : ∀ α, D.toPre.SecB k α) (g' : ∀ α, D.toPre.SecB (k * N) α) (θ : Fam D.toPre F k) (θ' : Fam D.toPre F (k * N)), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k) (E.s α) (D.toPre.famφB α) (DegPre.famε k) (g α) (DegPre.prB D.toPre (FractionRing V)).left 1) → (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε (k * N)) (E'.s α) (D.toPre.famφB α) (DegPre.famε (k * N)) (g' α) (DegPre.prB D.toPre (FractionRing V)).left 1) → (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (θ.s α) (D.toPre.famφB α) (DegPre.famε k) (g α) (DegPre.prB D.toPre F).left 1) → (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε (k * N)) (θ'.s α) (D.toPre.famφB α) (DegPre.famε (k * N)) (g' α) (DegPre.prB D.toPre F).left 1) → PullAl D (FractionRing V) oa a k N E E' → PullAl D F oa a k N θ θ' := by
  first | exact @GlobalTheory.PullBaseChange.main | exact GlobalTheory.PullBaseChange.main | (intros; apply GlobalTheory.PullBaseChange.main <;> assumption)
end
