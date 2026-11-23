module

public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.UniformityLowerBounds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle080
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPtEqUnitMulTh
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle081
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle082
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
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.padicIntermediateFieldIntRing_complete_dvr : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K → IsDiscreteValuationRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) ∧ IsAdicComplete (IsLocalRing.maximalIdeal (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K)) (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) ∧ ∀ x : FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K), ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) (FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K))) := by
  first | exact @GlobalTheory.intRing_complete_dvr | exact GlobalTheory.intRing_complete_dvr | (intros; apply GlobalTheory.intRing_complete_dvr <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaCompare

private theorem pow_eq_one_of_three_pow_relations {G : Type*} [CommGroup G] (M : ℕ) (U0 Ax Ap A0 F R : G)
    (h1 : U0 ^ M * (Ax ^ M * Ap) = A0 ^ M * A0) (h2 : F ^ M * A0 = Ap * R ^ M) (h3 : A0 = R ^ M * R⁻¹) :
    (U0 * Ax * F * (R ^ M)⁻¹) ^ M = 1 := by
  rw [mul_pow, mul_pow, mul_pow, inv_pow, mul_inv_eq_one]
  apply mul_right_cancel (b := Ap * A0)
  calc U0 ^ M * Ax ^ M * F ^ M * (Ap * A0) = (U0 ^ M * (Ax ^ M * Ap)) * (F ^ M * A0) := by ac_rfl
    _ = (A0 ^ M * A0) * (Ap * R ^ M) := by rw [h1, h2]
    _ = (A0 ^ M * R ^ M) * (Ap * A0) := by ac_rfl
    _ = (R ^ M) ^ M * (Ap * A0) := by
      congr 1
      rw [h3, mul_pow, inv_pow, _root_.mul_assoc, inv_mul_cancel, _root_.mul_one]


open CommPairing in
theorem normalised_root_stalk {S : Scheme.{0}} (hG : GlobalFnsSt) (P : PolAV S) {T : Over S} {m : ℕ} (hm : Odd m)
    {rig : LB.Gen (P.L.pull (eSec P.A))} {th : LB.Sec (LPow P.A P.L 1 T)} {x p : T ⟶ P.A} (hx : x ^ m = p)
    {fr : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => p.left) (fun _ => 1))}
    (hfr : IsTorsFrame P rig m p fr) {t v : Γ(T.left, ⊤)} (ht : IsValueAt P.A P.L 1 th p fr t)
    (a : ℤ) (ha : a = (m : ℤ) ^ 2) {s₁ s₂ : LB.Sec (LPow P.A P.L a T)}
    (h₁ : GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.IsMulPull P rig m a th s₁) {U : ThetaGrp P.A P.L a T}
    (hU : SymLift P.A P.L a (m ^ 2) x U) (hs₂ : IsActOf P.A P.L a U s₁ s₂)
    (h₃ : GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.IsValueZero P rig a s₂ v) (y : T.left) :
    ∃ ξ : (T.left.presheaf.stalk y)ˣ, ξ ^ (m ^ 2) = 1 ∧ gs (𝟙 _) y ⊤ v = ξ.val * gs (𝟙 _) y ⊤ t := by
  subst ha
  unfold IsActOf at hs₂
  obtain ⟨α, hα, hαn, htw⟩ := h₁
  obtain ⟨τ₀, -, hτ₀, hval⟩ := h₃
  obtain ⟨J, hJ, -⟩ := exists_good (L := P.L) P.isLB y (Empty.elim : Empty → (T.left ⟶ P.A.left)) Empty.elim
    (fun a => a.elim) (fun a => a.elim)
  have hxM : x ^ (m ^ 2) = 1 := by rw [sq, pow_mul, hx, hfr.1]
  have hR : ∀ k : ℕ, val rig T.hom y J ^ (k : ℤ) = val rig T.hom y J ^ k := fun k => zpow_natCast _ _
  have e1 := sval_valueAt hval hJ
  have e2 := sval_twist hs₂ (ptSecT P.A 1).left hJ
  have hpt : (ptSecT P.A (U.pt * 1)).left = (ptSecT P.A x).left := by rw [_root_.mul_one, hU.pt_eq]
  rw [pt_translT, hpt] at e2
  have e3 := sval_twist htw (ptSecT P.A x).left hJ
  rw [pt_mulT, hx] at e3
  have e4 := sval_valueAt ht hJ
  have e5 : val τ₀ (𝟙 _) y J = val rig T.hom y J ^ (m ^ 2) := by
    rw [val_corr hJ hτ₀, val_rigT rig _ hJ, ← Nat.cast_pow, hR]
  have F1 := frame_pow hG P hm hα hxM hU hJ
  rw [hx] at F1
  have F2 := torsFrame_pow hG P hα hfr hJ
  have F3 := val_corr hJ hαn (𝟙 _)
  rw [val_pull hJ, val_mul hJ, val_inv, val_rigT rig _ hJ, val_rigT rig _ hJ, Category.id_comp] at F3
  have F3' : val α (ptSecT P.A 1).left y J = val rig T.hom y J ^ (m ^ 2) * (val rig T.hom y J)⁻¹ := by
    rw [F3, zpow_one, ← hR, Nat.cast_pow]
  refine ⟨tval U (ptSecT P.A 1).left y J * val α (ptSecT P.A x).left y J * val fr (𝟙 _) y J *
    (val rig T.hom y J ^ (m ^ 2))⁻¹, pow_eq_one_of_three_pow_relations _ _ _ _ _ _ _ F1 F2 F3', ?_⟩
  calc gs (𝟙 _) y ⊤ v = gs (𝟙 _) y ⊤ v * (val τ₀ (𝟙 _) y J).val * (val τ₀ (𝟙 _) y J)⁻¹.val := by
        rw [_root_.mul_assoc, Units.mul_inv, _root_.mul_one]
    _ = _ := by
        rw [← e1, e2, e3, e4, e5, show tval U (ptSecT P.A 1).left y J = val U.φ (ptSecT P.A 1).left y J from rfl]
        simp only [Units.val_mul]
        ring

end GlobalTheory.ThetaCompare

namespace GlobalTheory

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
theorem _root_.GlobalTheory.T.invariantVectorFields_along_groupHom : ∀ (K : Type) [Field K] (A₁ A₀ : Over (Sp K)) [GrpObj A₁] [GrpObj A₀] (f : A₁ ⟶ A₀) (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)) (w : epsR K ⟶ A₁) (dw : ∀ O : A₁.left.Opens, Γ(A₁.left, O) → Γ(A₁.left, O)) (c : Fin g → K), IsMonHom f → (∀ a, IsTangent (v a)) → IsTangent w → (∀ a, IsInvDer (v a) (dd a)) → IsInvDer w dw → IsLieComb c v (w ≫ f) → ∀ (W : A₀.left.Opens) (h : Γ(A₀.left, W)), dw (f.left ⁻¹ᵁ W) ((f.left.app W).hom h) = ∑ a, constFn A₁.hom _ (c a) * (f.left.app W).hom (dd a W h) := by
  first | exact @GlobalTheory.KS.InvHom.invDer_along_hom | exact GlobalTheory.KS.InvHom.invDer_along_hom | (intros; apply GlobalTheory.KS.InvHom.invDer_along_hom <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.InvField

theorem pbT_pbT {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) {O₀ : X.Opens} {O₁ : Y.Opens} {O₂ : Z.Opens}
    (h₁ : O₁ ≤ g ⁻¹ᵁ O₀) (h₂ : O₂ ≤ f ⁻¹ᵁ O₁) (s : Γ(X, O₀)) :
    pbT f (pbT g s O₁) O₂ = pbT (f ≫ g) s O₂ := by
  rw [pbT_of_le g h₁, pbT_of_le f h₂, pbT_of_le (f ≫ g) (h₂.trans (f.preimage_mono h₁))]
  exact congrArg (fun φ => φ.hom s) (Scheme.Hom.appLE_comp_appLE f g O₀ O₁ O₂ h₁ h₂)

theorem pbT_id {Y : Scheme.{0}} {O : Y.Opens} (s : Γ(Y, O)) : pbT (𝟙 Y) s O = s := by
  rw [pbT_of_le (𝟙 Y) (O := O) (O₀ := O) le_rfl]
  exact (congrArg (fun φ => φ.hom s) (Scheme.Hom.appLE_eq_app (𝟙 Y) (U := O))).trans rfl

theorem pbT_eq_app {Y Z : Scheme.{0}} (f : Z ⟶ Y) {O : Y.Opens} (s : Γ(Y, O)) :
    pbT f s (f ⁻¹ᵁ O) = (f.app O).hom s := by
  rw [pbT_of_le f le_rfl, Scheme.Hom.appLE_eq_app]

theorem constFn_spMap {R S : Type} [CommRing R] [CommRing S] {Y : Scheme.{0}} (q : Y ⟶ Sp S) (φ : R →+* S)
    (O : Y.Opens) (a : R) : constFn (q ≫ spMap φ) O a = constFn q O (φ a) := by
  have h : (spMap φ).appLE ⊤ ⊤ (fun _ _ => trivial) = (spMap φ).appTop := by
    rw [Scheme.Hom.appTop, ← Scheme.Hom.appLE_eq_app]; rfl
  have h2 := congrArg (fun ψ => ψ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  have h3 := congrArg (fun ψ => ψ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_comp_appLE q (spMap φ) ⊤ ⊤ O (fun _ _ => trivial) (fun _ _ => trivial))
  rw [h] at h3
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2 h3
  unfold constFn
  rw [← h3, h2]

theorem constFn_mul {R : Type} [CommRing R] {Y : Scheme.{0}} (q : Y ⟶ Sp R)
    (O : Y.Opens) (a b : R) : constFn q O (a * b) = constFn q O a * constFn q O b := by
  simp [constFn]

theorem constFn_zero {R : Type} [CommRing R] {Y : Scheme.{0}} (q : Y ⟶ Sp R)
    (O : Y.Opens) : constFn q O 0 = 0 := by
  simp [constFn]

theorem aux {K : Type} [Field K] {Y Y' : Scheme.{0}} (q : Y ⟶ Sp K) (π : Y' ⟶ Sp (DualNumber K)) (ρ T : Y' ⟶ Y)
    (j : Y ⟶ Y') (hp : IsPullback ρ π q (spMap (algebraMap K (DualNumber K)))) (hρ : j ≫ ρ = 𝟙 Y)
    (hπ : j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom K K K).toRingHom)) (hT : j ≫ T = 𝟙 Y) (hq : T ≫ q = ρ ≫ q)
    (P : (∀ W : Y.Opens, Γ(Y, W) → Γ(Y, W)) → Prop)
    (hP : ∀ dd, P dd ↔ ∀ (W : Y.Opens) (f : Γ(Y, W)), pbT T f (ρ ⁻¹ᵁ W) =
      pbT ρ f (ρ ⁻¹ᵁ W) + constFn π _ DualNumber.eps * pbT ρ (dd W f) (ρ ⁻¹ᵁ W)) :
    (∃ dd, P dd) ∧ ∀ dd, P dd → (∀ W f f', dd W (f + f') = dd W f + dd W f') ∧ (∀ W f f', dd W (f * f') = f * dd W f' + f' * dd W f) ∧ (∀ W W' (f : Γ(Y, W)), W' ≤ W → dd W' (rsT f W') = rsT (dd W f) W') ∧ (∀ W a, dd W (constFn q W a) = 0) ∧ ∀ dd', P dd' → dd' = dd := by
  obtain ⟨hO, -, hex⟩ := GlobalTheory.T.const_thickening_field_structure K Y Y' q π ρ j hp hρ hπ
  have hTW : ∀ W : Y.Opens, ρ ⁻¹ᵁ W ≤ T ⁻¹ᵁ W := fun W => by
    have := hO (T ⁻¹ᵁ W)
    rw [← Scheme.Hom.comp_preimage j T, hT, Scheme.Hom.id_preimage] at this
    exact this.le
  have hjW : ∀ W : Y.Opens, W ≤ j ⁻¹ᵁ (ρ ⁻¹ᵁ W) := fun W => by
    rw [← Scheme.Hom.comp_preimage, hρ, Scheme.Hom.id_preimage]
  have uniq : ∀ (W : Y.Opens) (a b b' : Γ(Y, W)),
      pbT ρ a (ρ ⁻¹ᵁ W) + constFn π _ DualNumber.eps * pbT ρ b (ρ ⁻¹ᵁ W) =
      pbT ρ a (ρ ⁻¹ᵁ W) + constFn π _ DualNumber.eps * pbT ρ b' (ρ ⁻¹ᵁ W) → b = b' := by
    intro W a b b' h
    simp only [pbT_eq_app] at h
    have := (hex W _).unique (y₁ := (a, b)) (y₂ := (a, b')) rfl h
    exact congrArg Prod.snd this
  have hee : ∀ O, constFn π O DualNumber.eps * constFn π O DualNumber.eps = 0 := fun O => by
    rw [← constFn_mul, DualNumber.eps_mul_eps, constFn_zero]
  refine ⟨?_, fun dd hd => ?_⟩
  · choose ab hab using fun W (f : Γ(Y, W)) => (hex W (pbT T f (ρ ⁻¹ᵁ W))).exists
    refine ⟨fun W f => (ab W f).2, (hP _).2 fun W f => ?_⟩
    have h := hab W f
    rw [← pbT_eq_app, ← pbT_eq_app] at h
    have h' := congrArg (fun s => pbT j s W) h
    simp only [pbT_add, pbT_mul] at h'
    rw [pbT_pbT j T (hTW W) (hjW W), pbT_pbT j ρ le_rfl (hjW W), hT, hρ, pbT_id, pbT_id,
      pbT_constFn π j (hjW W), hπ, constFn_spMap] at h'
    have e : (TrivSqZeroExt.fstHom K K K).toRingHom DualNumber.eps = 0 := by simp
    rw [e, constFn_zero, zero_mul, add_zero] at h'
    rw [h, ← h']
  · have hd' := (hP _).1 hd
    refine ⟨fun W f f' => uniq W (f + f') _ _ ?_, fun W f f' => uniq W (f * f') _ _ ?_,
      fun W W' f h => uniq W' (rsT f W') _ _ ?_, fun W a => uniq W (constFn q W a) _ _ ?_, fun dd' hd₁ => ?_⟩
    · rw [← hd', pbT_add, hd', hd', pbT_add, pbT_add]; ring
    · rw [← hd', pbT_mul, hd', hd', pbT_add, pbT_mul, pbT_mul, pbT_mul]
      linear_combination (pbT ρ (dd W f) (ρ ⁻¹ᵁ W) * pbT ρ (dd W f') (ρ ⁻¹ᵁ W)) * hee (ρ ⁻¹ᵁ W)
    · have h1 : ρ ⁻¹ᵁ W' ≤ ρ ⁻¹ᵁ W := ρ.preimage_mono h
      rw [← hd', pbT_rsT T h (hTW W'), pbT_rsT ρ h le_rfl, pbT_rsT ρ h le_rfl, ← rsT_pbT T (hTW W) h1, hd',
        rsT_add, rsT_mul, rsT_pbT ρ le_rfl h1, rsT_pbT ρ le_rfl h1, rsT_constFn π h1]
    · rw [← hd', pbT_constFn q T (hTW W), pbT_constFn q ρ le_rfl, hq, pbT_zero, mul_zero, add_zero]
    · funext W f
      exact uniq W f _ _ (((hP _).1 hd₁ W f).symm.trans (hd' W f))

theorem main : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (v : epsR K ⟶ A₀), IsTangent v → (∃ dd, IsInvDer v dd) ∧ ∀ dd, IsInvDer v dd → (∀ W f f', dd W (f + f') = dd W f + dd W f') ∧ (∀ W f f', dd W (f * f') = f * dd W f' + f' * dd W f) ∧ (∀ W W' (f : Γ(A₀.left, W)), W' ≤ W → dd W' (rsT f W') = rsT (dd W f) W') ∧ (∀ W a, dd W (constFn A₀.hom W a) = 0) ∧ ∀ dd', IsInvDer v dd' → dd' = dd := by
  intro K _ A₀ _ v hv
  let s : 𝟙_ (Over (Sp K)) ⟶ epsR K := Over.homMk (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) (by
    change spMap _ ≫ spMap _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1)
  have hs : s ≫ v = η[A₀] := Over.OverMorphism.ext hv
  let j : A₀ ⟶ epsR K ⊗ A₀ := lift (toUnit A₀ ≫ s) (𝟙 A₀)
  have hT : j ≫ ((fst (epsR K) A₀ ≫ v) * snd (epsR K) A₀) = 𝟙 A₀ := by
    rw [MonObj.comp_mul, lift_fst_assoc, lift_snd, Category.assoc, hs, ← Hom.one_def, _root_.one_mul]
  refine aux A₀.hom (fst (epsR K) A₀).left (snd (epsR K) A₀).left
    ((fst (epsR K) A₀ ≫ v) * snd (epsR K) A₀).left j.left ?_ ?_ ?_ ?_ ?_ (IsInvDer v) (fun _ => Iff.rfl)
  · exact (IsPullback.of_hasPullback (epsR K).hom A₀.hom).flip
  · rw [← Over.comp_left, lift_snd]; rfl
  · rw [← Over.comp_left, lift_fst, Over.comp_left, Over.toUnit_left]; rfl
  · rw [← Over.comp_left, hT]; rfl
  · rw [Over.w, Over.w]

end GlobalTheory.KS.InvField
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PELPull

theorem lbIso_pull {X Y Y' : Scheme.{0}} {A : LB Y} {L : LB X} {φ : Y ⟶ X} (H : LBIso A (L.pull φ)) (h : Y' ⟶ Y)
    {F : Y' ⟶ X} (e : F = h ≫ φ) : LBIso (A.pull h) (L.pull F) :=
  H.chartPull (chartPullPull A h h rfl)
    (chartPullSame L (fun _ : PUnit => F) (fun _ : PUnit => φ) (fun _ => 1) h fun _ => e)

theorem isPEL_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g k : ℕ) (J : Type) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (o : Type) [CommRing o] (b : TBase o k) (ρ : o) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (f : S' ⟶ S) (t : TObj g k J b s) (t' : TObj g k J b s') (τ : SAB H S), f ≫ s = s' → TMap t' t f → IsPEL D a bas ρ t τ → ∃ τ' : SAB H S', IsPEL D a bas ρ t' τ' := by
  intro E _ _ _ H D g k J a bas o _ b ρ S S' s s' f t t' τ hs ⟨ψ, hψ, hψL, hpt, hact⟩ ⟨φ, hφ, hφL, hφa, hgeom⟩
  obtain ⟨τ', ⟨m⟩⟩ : ∃ τ' : SAB H S', Nonempty (SABMap τ' τ f) := by
    have hC := Out.CubePf.cubePull
    have hsemi : IsSemiAbelian ((Over.pullback f).obj τ.G) := by
      refine { comm := ?_, smooth := ?_, separated := ?_, quasiCompact := ?_, geomConnected := ?_, fibres := ?_ }
      · have := τ.semi.comm
        infer_instance
      · have := τ.semi.smooth
        change Smooth (pullback.snd τ.G.hom f)
        infer_instance
      · have := τ.semi.separated
        change IsSeparated (pullback.snd τ.G.hom f)
        infer_instance
      · have := τ.semi.quasiCompact
        change QuasiCompact (pullback.snd τ.G.hom f)
        infer_instance
      · have := τ.semi.geomConnected
        change GeometricallyConnected (pullback.snd τ.G.hom f)
        infer_instance
      · intro Ω _ _ q
        obtain ⟨A⟩ := τ.semi.fibres Ω (q ≫ f)
        exact ⟨torusExtOfIso (pullCompIso q f τ.G) A⟩
    have hp : ∃ (PP' : RigLB ((Over.pullback f).obj τ.G)) (cub : CubicalStr _ PP') (sym : PP'.IsSymmetric) (adj : _) (prim : _)
        (m : SABMap ⟨(Over.pullback f).obj τ.G, hsemi, OAct.pullback f τ.G τ.act, PP', cub,
          sym, adj, prim⟩ τ f), m.φ = pullback.fst τ.G.hom f := by
      have h := isGrpPullback_pullback τ.G f
      obtain ⟨hL, hr, ⟨c', hc'⟩, hs⟩ := hC S S' τ.G _ (cubeMapOf h) τ.PP τ.cub
      have hact : ∀ a, ((OAct.pullback f τ.G τ.act).act a).left ≫ pullback.fst τ.G.hom f =
          pullback.fst τ.G.hom f ≫ (τ.act.act a).left := fun a => pullback.lift_fst _ _ _
      have pa : ∀ {T : Over S'} (x : T ⟶ (Over.pullback f).obj τ.G) a,
          pushPt h.1.w (x ≫ (OAct.pullback f τ.G τ.act).act a) = pushPt h.1.w x ≫ τ.act.act a := fun x a =>
        Over.OverMorphism.ext (by
          show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
          rw [Category.assoc, hact, Category.assoc])
      refine ⟨(cubeMapOf h).rigLB τ.PP hL hr, c', hs τ.sym, fun a => ?_, ?_, ⟨cubeMapOf h, h, rfl, hact, hc'⟩, rfl⟩
      · let U := lift (pushPt h.1.w (fst ((Over.pullback f).obj τ.G) ((Over.pullback f).obj τ.G)))
          (pushPt h.1.w (snd ((Over.pullback f).obj τ.G) ((Over.pullback f).obj τ.G)))
        refine LBIso.chartPull (chartPullLinComb τ.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
          (chartPullLinComb τ.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) (τ.adj a)
        · fin_cases i
          · exact (pa _ a).trans (by simp [U])
          · simp [U]
        · fin_cases i
          · simp [U]
          · exact (pa _ _).trans (by simp [U])
      · let U := pushPt h.1.w (𝟙 ((Over.pullback f).obj τ.G))
        refine LBIso.chartPull (chartPullPull τ.PP.L _ U.left (Category.id_comp _))
          (chartPullLinComb τ.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) τ.prim
        fin_cases i
        · simp [U]
        · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)
    obtain ⟨_, _, _, _, _, m, -⟩ := hp
    exact ⟨_, ⟨m⟩⟩
  have pull_isLB : ∀ {X Y : Scheme.{0}} {L : LB X}, L.IsLB → (F : Y ⟶ X) → (L.pull F).IsLB :=
    fun hL F => ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB hL F
  have hL : LBIso τ'.PP.L (τ.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  have hc : IsGrpPullback τ'.G t.A f (m.cm.F ≫ φ.hom.left) :=
    (IsGrpPullback.comp m.cart (isGrpPullback_of_iso φ)).congr (Category.comp_id f) rfl
  obtain ⟨e, he, heF⟩ := grpPullback_iso hc hψ
  refine ⟨τ', e, he, ?_, fun j => ?_, fun K _ _ _ x β hx => ?_⟩
  · exact (hL.trans τ'.PP.isLB (pull_isLB τ.PP.isLB _) (pull_isLB t.isLB _) (lbIso_pull hφL m.cm.F rfl)).trans
      τ'.PP.isLB (pull_isLB t.isLB _) (pull_isLB t'.isLB _) (lbIso_pull hψL e.hom.left heF.symm).symm
  · apply Over.OverMorphism.ext
    apply hψ.1.hom_ext
    · have h₁ : (τ.act.act (a j)).left ≫ φ.hom.left = φ.hom.left ≫ (t.act j).left :=
        congrArg (fun z => z.left) (hφa j)
      have h₂ : (τ'.act.act (a j)).left ≫ m.cm.F = m.cm.F ≫ (τ.act.act (a j)).left := m.act _
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, heF, hact, ← Category.assoc, h₂,
        Category.assoc, h₁, ← Category.assoc, ← heF, Category.assoc]
    · rw [Over.w, Over.w]
  · obtain ⟨hdet, I, hI, hA⟩ := hgeom K (x ≫ f) β (by rw [Category.assoc, hs, hx])
    refine ⟨fun σ => ?_, GlobalTheory.ObjPull.tateMove (GlobalTheory.ObjPull.pushEquiv m.cart (Over.mk x)) (fun c y => ?_)
      (fun n y y' c hc => ?_) I, hI, fun i => ?_⟩
    · rw [GlobalTheory.LiePull.lieMult_pull _ S S' τ.G τ'.G f m.cm.F τ.act τ'.act m.cart m.act K x σ,
        GlobalTheory.LiePull.lieMult_pull _ S S' τ.G τ'.G f m.cm.F τ.act τ'.act m.cart m.act K x σ]
      exact hdet σ
    · apply Over.OverMorphism.ext
      show (y.left ≫ _) ≫ _ = (y.left ≫ _) ≫ _
      rw [Category.assoc, m.act, Category.assoc]
    · exact (GlobalTheory.weilIs_grpPullback_of_comm S S' τ.G τ'.G f m.cm.F τ.PP.L τ'.PP.L τ.PP.isLB τ'.PP.isLB m.cart hL
        (Over.mk x) n y y' _ _ _ rfl rfl).2 hc
    · apply Over.OverMorphism.ext
      apply hψ.1.hom_ext
      · have h₁ : (I.ev k (bas (Pi.single i 1))).left ≫ φ.hom.left = (x ≫ f) ≫ (t.pt i).left :=
          congrArg (fun z => z.left) (hA i)
        have h₂ := GlobalTheory.ObjPull.pushEquiv_symm_left m.cart (Over.mk x) (I.ev k (bas (Pi.single i 1)))
        show (((GlobalTheory.ObjPull.pushEquiv m.cart (Over.mk x)).symm (I.ev k (bas (Pi.single i 1)))).left ≫ e.hom.left) ≫ ψ =
          (x ≫ (t'.pt i).left) ≫ ψ
        rw [Category.assoc, heF, Category.assoc, hpt]
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ.hom.left) h₂).trans (h₁.trans (Category.assoc _ _ _)))
      · rw [Over.w, Over.w]

end GlobalTheory.PELPull
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

theorem _root_.GlobalTheory.T.exists_differentiableOn_verticalVectorField : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ (n : ℕ) (B : Set (Fin n → ℂ)) (G : (Fin n → ℂ) → (Fin P₀.g → ℂ)) (s : (Fin n → ℂ) → ∀ W : X.Opens, Γ(X, W) → ℂ), IsOpen B → Differentiable ℂ G → (∀ z ∈ B, PtDer ((u.ex (G z)).left ≫ m) (s z) ∧ ∀ r, s z ⊤ (constFn p ⊤ r) = 0) → (∀ W f, DifferentiableOn ℂ (fun z => s z W f) {z ∈ B | G z ∈ dom u m W}) → ∃ w : (Fin n → ℂ) → (Fin P₀.g → ℂ), DifferentiableOn ℂ w B ∧ ∀ z ∈ B, ∀ W f, G z ∈ dom u m W → s z W f = fderiv ℂ (fn u m W f) (G z) (w z) := by
  first | exact @GlobalTheory.KS.VertField.exists_differentiableOn_vertical | exact GlobalTheory.KS.VertField.exists_differentiableOn_vertical | (intros; apply GlobalTheory.KS.VertField.exists_differentiableOn_vertical <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem lbPow_descends_of_isotropic_of_laws : Out.Laws → ∀ (k : Type) [Field k] [IsAlgClosed k] (P : Out.PolAV (Sp k)) (n : ℕ) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ P.A)) (B : Over (Sp k)) [GrpObj B] (ψ : P.A ⟶ B), 0 < n → (n : k) ≠ 0 → (∀ x ∈ C, x ^ n = 1) → (∀ x ∈ C, ∀ y ∈ C, Out.WeilIs P.A P.L n x y 1) → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ x : 𝟙_ (Over (Sp k)) ⟶ P.A, x ≫ ψ = 1 ↔ x ∈ C) → ∃ M : LB B.left, M.IsLB ∧ LBIso (lbPow P.L n) (M.pull ψ.left) :=
  LinDescent.lbPow_descends

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.exists_diagonal_coordinates_of_determinantCondition : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (act : OAct (𝓞 E) P.A) (ty : Fin P.g → (E →+* ℂ)), u.IsAH Hm χ → IsTypeFn H D.p D.q ty → DetCond D act (𝟙 (Sp ℂ)) H.rt0 → ∃ h : (Fin P.g → ℂ) ≃ₗ[ℂ] (Fin P.g → ℂ), ∀ (a : 𝓞 E) z, u.ex (h (fun i => ty i (a : E) * z i)) = u.ex (h z) ≫ act.act a := by
  first | exact @GlobalTheory.exists_diagonal_coordinates_of_detCond | exact GlobalTheory.exists_diagonal_coordinates_of_detCond | (intros; apply GlobalTheory.exists_diagonal_coordinates_of_detCond <;> assumption)
end
