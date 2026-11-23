module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Smooth.Basic
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle042
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle043
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle040
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_binary_op_glued_along_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) (G : ∀ i, Over (U i).toScheme) (ψ : ∀ i, (G i).left ⟶ A.left) (o : ∀ i, G i ⊗ G i ⟶ G i), iSup U = ⊤ → (∀ i, IsPullback (ψ i) (G i).hom A.hom (U i).ι) → (∀ i j (T : Scheme.{0}) (r : T ⟶ (U i).toScheme) (r' : T ⟶ (U j).toScheme) (x y : Over.mk r ⟶ G i) (x' y' : Over.mk r' ⟶ G j), x.left ≫ ψ i = x'.left ≫ ψ j → y.left ≫ ψ i = y'.left ≫ ψ j → (lift x y ≫ o i).left ≫ ψ i = (lift x' y' ≫ o j).left ≫ ψ j) → ∃ m : A ⊗ A ⟶ A, ∀ i (T : Over (U i).toScheme) (x y : T ⟶ G i) (x₀ y₀ : Over.mk (T.hom ≫ (U i).ι) ⟶ A), x₀.left = x.left ≫ ψ i → y₀.left = y.left ≫ ψ i → (lift x₀ y₀ ≫ m).left = (lift x y ≫ o i).left ≫ ψ i := by
  first | exact @GlobalTheory.CoverGlue.exists_binary_op | exact GlobalTheory.CoverGlue.exists_binary_op | (intros; apply GlobalTheory.CoverGlue.exists_binary_op <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.glue_schemes_over_opens_along_cocycle : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (G : ∀ i, Over (U i).toScheme) (B : ∀ i j, Over (U i ⊓ U j).toScheme) (a : ∀ i j, (B i j).left ⟶ (G i).left) (b : ∀ i j, (B i j).left ⟶ (G j).left), (∀ i j, IsPullback (a i j) (B i j).hom (G i).hom (S.homOfLE inf_le_left)) → (∀ i j, IsPullback (b i j) (B i j).hom (G j).hom (S.homOfLE inf_le_right)) → (∀ i j k (T : Scheme.{0}) (x : T ⟶ (B i j).left) (y : T ⟶ (B j k).left) (z : T ⟶ (B i k).left), x ≫ b i j = y ≫ a j k → x ≫ a i j = z ≫ a i k → y ≫ b j k = z ≫ b i k) → ∃ (A : Over S) (ψ : ∀ i, (G i).left ⟶ A.left), (∀ i, IsPullback (ψ i) (G i).hom A.hom (U i).ι) ∧ ∀ i j, IsPullback (a i j) (b i j) (ψ i) (ψ j) := by
  first | exact @GlobalTheory.CocycleGlue.glue_over_opens | exact GlobalTheory.CocycleGlue.glue_over_opens | (intros; apply GlobalTheory.CocycleGlue.glue_over_opens <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

theorem _root_.GlobalTheory.T.exists_derivation_extend' : ∀ (R B C : Type) [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra.FormallySmooth R B] (φ : B →+* C) (D : R → C), (∀ a b, D (a + b) = D a + D b) → (∀ a b, D (a * b) = φ (algebraMap R B a) * D b + φ (algebraMap R B b) * D a) → ∃ d : B → C, (∀ a b, d (a + b) = d a + d b) ∧ (∀ a b, d (a * b) = φ a * d b + φ b * d a) ∧ ∀ r, d (algebraMap R B r) = D r := by
  first | exact @GlobalTheory.KS.exists_derivation_extend_of_formallySmooth | exact GlobalTheory.KS.exists_derivation_extend_of_formallySmooth | (intros; apply GlobalTheory.KS.exists_derivation_extend_of_formallySmooth <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.EpsCocycle

noncomputable section

lemma res_res {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (x : Γ(X, U)ˣ) :
    res h' (res h x) = res (h'.trans h) x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

lemma cocycle_on {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (i j k : L.ι) {W : X.Opens}
    (h₁ : W ≤ L.U i ⊓ L.U j) (h₂ : W ≤ L.U j ⊓ L.U k) (h₃ : W ≤ L.U i ⊓ L.U k) :
    res h₁ (L.g i j) * res h₂ (L.g j k) = res h₃ (L.g i k) := by
  have := congrArg (res (le_inf h₁ (h₂.trans inf_le_right) : W ≤ L.U i ⊓ L.U j ⊓ L.U k))
    (hL.cocycle i j k)
  simpa only [map_mul, res_res] using this

def regauge {X : Scheme.{0}} (L : LB X) (u : ∀ i, Γ(X, L.U i)ˣ) : LB X :=
  ⟨L.ι, L.U, fun i i' => (res inf_le_left (u i))⁻¹ * L.g i i' * res inf_le_right (u i')⟩

lemma regauge_isLB {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (u : ∀ i, Γ(X, L.U i)ˣ) :
    (regauge L u).IsLB := {
  cover := hL.cover
  g_self := fun i => by
    have := hL.g_self i
    change res (le_inf le_rfl le_rfl : L.U i ≤ L.U i ⊓ L.U i)
      ((res inf_le_left (u i))⁻¹ * L.g i i * res inf_le_right (u i)) = 1
    simp only [map_mul, map_inv, res_res, this, _root_.mul_one, inv_mul_cancel]
  cocycle := fun i j k => by
    have := hL.cocycle i j k
    change res (inf_le_left : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U j)
        ((res inf_le_left (u i))⁻¹ * L.g i j * res inf_le_right (u j)) *
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        L.U i ⊓ L.U j ⊓ L.U k ≤ L.U j ⊓ L.U k)
        ((res inf_le_left (u j))⁻¹ * L.g j k * res inf_le_right (u k)) =
      res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U k)
        ((res inf_le_left (u i))⁻¹ * L.g i k * res inf_le_right (u k))
    simp only [map_mul, map_inv, res_res, ← this]
    group }

lemma regauge_iso {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (u : ∀ i, Γ(X, L.U i)ˣ) :
    LBIso L (regauge L u) := by
  refine ⟨⟨fun p : L.ι × L.ι => ((res inf_le_left (u p.1))⁻¹ * L.g p.1 p.2 :
    Γ(X, L.U p.1 ⊓ L.U p.2)ˣ)⟩, ?_⟩
  rintro ⟨a, b⟩ ⟨a', b'⟩
  let W : X.Opens := L.U a ⊓ L.U b ⊓ (L.U a' ⊓ L.U b')
  have ha : W ≤ L.U a := inf_le_left.trans inf_le_left
  have hb : W ≤ L.U b := inf_le_left.trans inf_le_right
  have ha' : W ≤ L.U a' := inf_le_right.trans inf_le_left
  have hb' : W ≤ L.U b' := inf_le_right.trans inf_le_right
  change res (le_inf ha hb) ((res inf_le_left (u a))⁻¹ * L.g a b) =
    (res (le_inf ha ha') ((res inf_le_left (u a))⁻¹ * L.g a a' * res inf_le_right (u a')) *
      (res (le_inf hb hb') (L.g b b'))⁻¹) *
      res (le_inf ha' hb') ((res inf_le_left (u a'))⁻¹ * L.g a' b')
  have e₁ := cocycle_on hL a a' b' (le_inf ha ha') (le_inf ha' hb') (le_inf ha hb')
  have e₂ := cocycle_on hL a b b' (le_inf ha hb) (le_inf hb hb') (le_inf ha hb')
  have e₃ : res (le_inf ha hb) (L.g a b) = res (le_inf ha ha') (L.g a a') *
      res (le_inf ha' hb') (L.g a' b') * (res (le_inf hb hb') (L.g b b'))⁻¹ := by
    rw [e₁, ← e₂, mul_inv_cancel_right]
  simp only [map_mul, map_inv, res_res, e₃]
  generalize res ha (u a) = x
  generalize res ha' (u a') = y
  generalize res (le_inf ha ha') (L.g a a') = z
  generalize res (le_inf ha' hb') (L.g a' b') = w
  generalize res (le_inf hb hb') (L.g b b') = v
  rw [mul_mul_mul_comm _ v⁻¹, mul_inv_cancel_right]
  ac_rfl

lemma appLE_section {Y Y' : Scheme.{0}} {ρ : Y' ⟶ Y} {j : Y ⟶ Y'} (hj : j ≫ ρ = 𝟙 Y)
    {O O₂ : Y.Opens} {O' : Y'.Opens} (h : O' ≤ ρ ⁻¹ᵁ O) (h' : O₂ ≤ j ⁻¹ᵁ O') (h'' : O₂ ≤ O)
    (a : Γ(Y, O)) :
    (j.appLE O' O₂ h').hom ((ρ.appLE O O' h).hom a) = resG Y h'' a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  have key : ∀ (f : Y ⟶ Y) (_ : f = 𝟙 Y) (e : O₂ ≤ f ⁻¹ᵁ O), (f.appLE O O₂ e).hom a = resG Y h'' a := by
    intro f hf e
    subst hf
    simp [Scheme.Hom.appLE]
    rfl
  exact key _ hj _

lemma appLE_constFn_eps {Y Y' : Scheme.{0}} {q : Y ⟶ Sp ℂ} {π : Y' ⟶ Sp (DualNumber ℂ)}
    {j : Y ⟶ Y'} (hq : j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom))
    {O : Y.Opens} {O' : Y'.Opens} (h : O ≤ j ⁻¹ᵁ O') :
    (j.appLE O' O h).hom (constFn π O' DualNumber.eps) = 0 := by
  have h0 : O' ≤ π ⁻¹ᵁ ⊤ := fun _ _ => trivial
  change (j.appLE O' O h).hom ((π.appLE ⊤ O' h0).hom
    ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).inv.hom DualNumber.eps)) = 0
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  have key : ∀ (f : Y ⟶ Sp (DualNumber ℂ))
      (_ : f = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)) (e : O ≤ f ⁻¹ᵁ ⊤),
      (f.appLE ⊤ O e).hom ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).inv.hom DualNumber.eps) = 0 := by
    intro f hf e
    subst hf
    rw [Scheme.Hom.comp_appLE, CommRingCat.comp_apply]
    have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)
    have e2 := congrArg (fun φ => φ.hom DualNumber.eps) this
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
    have e3 : (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).hom DualNumber.eps = 0 := by
      simp
    rw [e3, map_zero] at e2
    exact (congrArg _ e2.symm).trans (map_zero _)
  exact key _ hq _

lemma eq_one_add_eps {Y Y' : Scheme.{0}} {q : Y ⟶ Sp ℂ} {π : Y' ⟶ Sp (DualNumber ℂ)} {ρ : Y' ⟶ Y}
    {j : Y ⟶ Y'} (hp : IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ)))) (hj : j ≫ ρ = 𝟙 Y)
    (hq : j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)) (O' : Y'.Opens)
    (F : Γ(Y', O')) (hF : (j.appLE O' _ le_rfl).hom F = 1) :
    ∃ k : Γ(Y, j ⁻¹ᵁ O'), ∀ h : O' ≤ ρ ⁻¹ᵁ (j ⁻¹ᵁ O'),
      F = 1 + constFn π _ DualNumber.eps * (ρ.appLE _ _ h).hom k := by
  obtain ⟨h₁, -, h₃⟩ := GlobalTheory.EpsThick.thickening_functions Y Y' q π ρ j hp hj hq
  have key : ∀ (O : Y.Opens) (O' : Y'.Opens) (_ : ρ ⁻¹ᵁ O = O') (F : Γ(Y', O')), ∃ a b : Γ(Y, O),
      ∀ h : O' ≤ ρ ⁻¹ᵁ O,
        F = (ρ.appLE _ _ h).hom a + constFn π _ DualNumber.eps * (ρ.appLE _ _ h).hom b := by
    intro O O' e F
    subst e
    obtain ⟨ab, hab, -⟩ := h₃ O F
    refine ⟨ab.1, ab.2, fun h => ?_⟩
    rw [Scheme.Hom.appLE_eq_app]
    exact hab
  obtain ⟨a, b, hab⟩ := key _ O' (h₁ O') F
  refine ⟨b, fun h => ?_⟩
  have ha : a = 1 := by
    rw [hab h, map_add (f := _), map_mul, appLE_constFn_eps hq, zero_mul, add_zero,
      appLE_section hj h le_rfl le_rfl] at hF
    have e : resG Y (le_refl (j ⁻¹ᵁ O')) a = a := by
      change (Y.presheaf.map (𝟙 _)).hom a = a
      rw [Y.presheaf.map_id]
      rfl
    exact e.symm.trans hF
  rw [hab h, ha, map_one]

def pullLE {X Y : Scheme.{0}} (f : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U) :
    Γ(X, U)ˣ →* Γ(Y, V)ˣ := Units.map (f.appLE U V h).hom

lemma pullLE_eq {X Y : Scheme.{0}} (f : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U)
    (x : Γ(X, U)ˣ) : pullLE f h x = res h (pullU f U x) := by
  ext
  rfl

lemma pullLE_res {X Y : Scheme.{0}} (f : Y ⟶ X) {U U' : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U')
    (h' : U' ≤ U) (h'' : V ≤ f ⁻¹ᵁ U) (x : Γ(X, U)ˣ) : pullLE f h (res h' x) = pullLE f h'' x := by
  ext
  simp only [pullLE, res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

lemma pullLE_section {Y Y' : Scheme.{0}} {ρ : Y' ⟶ Y} {j : Y ⟶ Y'} (hj : j ≫ ρ = 𝟙 Y)
    {O O₂ : Y.Opens} {O' : Y'.Opens} (h : O' ≤ ρ ⁻¹ᵁ O) (h' : O₂ ≤ j ⁻¹ᵁ O') (h'' : O₂ ≤ O)
    (a : Γ(Y, O)ˣ) : pullLE j h' (pullLE ρ h a) = res h'' a := by
  ext
  exact appLE_section hj h h' h'' a.val

theorem exists_cocycle_one_add_eps : ∀ (Y Y' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → ∀ Q : LB Y', Q.IsLB → (∃ t : (Q.pull j).Gen, t.IsGen) → ∃ (Q' : LB Y') (k : ∀ i i', Γ(Y, j ⁻¹ᵁ (Q'.U i ⊓ Q'.U i'))), Q'.IsLB ∧ LBIso Q Q' ∧ (∀ i i' (h : Q'.U i ⊓ Q'.U i' ≤ ρ ⁻¹ᵁ (j ⁻¹ᵁ (Q'.U i ⊓ Q'.U i'))), (Q'.g i i').val = 1 + constFn π _ DualNumber.eps * (ρ.appLE _ _ h).hom (k i i')) := by
  intro Y Y' q π ρ j hp hj hq Q hQ ⟨t, ht⟩
  obtain ⟨h₁, -, -⟩ := GlobalTheory.EpsThick.thickening_functions Y Y' q π ρ j hp hj hq
  have hw : ∀ i : Q.ι, j ⁻¹ᵁ Q.U i ≤ (Q.pull j).U (fun _ => i) :=
    fun i _ hy => Set.mem_iInter.2 fun _ => hy
  let s : ∀ i : Q.ι, Γ(Y, j ⁻¹ᵁ Q.U i)ˣ := fun i => res (hw i) (t.s fun _ => i)
  let u : ∀ i, Γ(Y', Q.U i)ˣ := fun i => pullLE ρ (h₁ (Q.U i)).ge (s i)
  have main : ∀ i i' : Q.ι, (j.appLE (Q.U i ⊓ Q.U i') _ le_rfl).hom ((regauge Q u).g i i').val = 1 := by
    intro i i'
    have hl : j ⁻¹ᵁ (Q.U i ⊓ Q.U i') ≤ j ⁻¹ᵁ Q.U i := fun _ hy => hy.1
    have hr : j ⁻¹ᵁ (Q.U i ⊓ Q.U i') ≤ j ⁻¹ᵁ Q.U i' := fun _ hy => hy.2
    have e := congrArg (res (le_inf (hl.trans (hw i)) (hr.trans (hw i'))))
      (ht (fun _ => i) (fun _ => i'))
    have eg : res (le_inf (hl.trans (hw i)) (hr.trans (hw i')))
        ((Q.pull j).g (fun _ => i) (fun _ => i')) =
        pullLE j (le_refl (j ⁻¹ᵁ (Q.U i ⊓ Q.U i'))) (Q.g i i') := by
      rw [pullLE_eq]
      change res _ (∏ _k : PUnit.{1}, (res _ (pullU j _ (Q.g i i'))) ^ (1 : ℤ)) = _
      rw [Fintype.prod_unique, zpow_one]
      exact res_res _ _ _
    rw [map_mul, res_res, res_res, eg] at e
    have : pullLE j (le_refl (j ⁻¹ᵁ (Q.U i ⊓ Q.U i')))
        ((res inf_le_left (u i))⁻¹ * Q.g i i' * res inf_le_right (u i')) = 1 := by
      rw [map_mul, map_mul, map_inv, pullLE_res j _ _ hl, pullLE_res j _ _ hr,
        pullLE_section hj _ _ hl, pullLE_section hj _ _ hr, res_res, res_res, _root_.mul_assoc, ← e,
        inv_mul_cancel]
    exact congrArg Units.val this
  choose k hk using fun i i' : Q.ι => eq_one_add_eps hp hj hq _ _ (main i i')
  exact ⟨regauge Q u, k, regauge_isLB hQ u, regauge_iso hQ u, hk⟩

end

end GlobalTheory.EpsCocycle
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.EpsAct

theorem subsingleton_sp_dualNumber (k : Type) [Field k] : Subsingleton (Sp (DualNumber k)) := by
  change Subsingleton (PrimeSpectrum (DualNumber k))
  have key : ∀ (p : PrimeSpectrum (DualNumber k)) (x : DualNumber k), x ∈ p.asIdeal ↔ x.fst = 0 := by
    intro p x
    constructor
    · intro hx
      by_contra h
      exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx
        (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (isUnit_iff_ne_zero.2 h)))
    · intro h
      apply p.isPrime.mem_of_pow_mem 2
      have hx : x = TrivSqZeroExt.inr x.snd := TrivSqZeroExt.ext (by simp [h]) (by simp)
      rw [hx, pow_two]
      simp
  exact ⟨fun p q => PrimeSpectrum.ext (Ideal.ext fun x => (key p x).trans (key q x).symm)⟩

theorem rigidity (hL : Out.Laws) (k : Type) [Field k] {Z : Scheme.{0}} (c₀ : Z ⟶ Sp k)
    (A' G' : Over (Sp (DualNumber k))) [GrpObj A'] [GrpObj G'] (j : Z ⟶ A'.left) (a b : A' ⟶ G')
    (hA : IsAbelianScheme A')
    (hj : IsPullback j c₀ A'.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom))
    (hab : j ≫ a.left = j ≫ b.left) (hη : η[A'] ≫ a = η[A'] ≫ b) : a = b := by
  classical
  have hsurj : Function.Surjective A'.hom.appTop.hom := (hL.globalFns _ A' hA).2
  set d : A' ⟶ G' := a * b⁻¹ with hd
  have hsub : Subsingleton (Sp (DualNumber k)) := subsingleton_sp_dualNumber k
  have hjs : Function.Surjective j.base := by
    have hs0 : Surjective (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) := by
      constructor
      intro y
      obtain ⟨q⟩ : Nonempty (Sp k) := by
        change Nonempty (PrimeSpectrum k)
        infer_instance
      exact ⟨q, Subsingleton.elim _ _⟩
    exact (MorphismProperty.of_isPullback (P := @Surjective) hj.flip hs0).surj
  have key : ∀ {W : Over (Sp (DualNumber k))} (u : W ⟶ A'), u ≫ a = u ≫ b → u ≫ d = 1 := by
    intro W u h
    rw [MonObj.comp_mul, GrpObj.comp_inv, h, mul_inv_cancel]
  have hjd : j ≫ d.left = (toUnit (Over.mk (j ≫ A'.hom))).left ≫ η[G'].left := by
    have h1 := congrArg (fun f => Over.Hom.left f)
      (key (Over.homMk j rfl : Over.mk (j ≫ A'.hom) ⟶ A') (by ext; exact hab))
    simpa [Hom.one_def] using h1
  obtain ⟨pt⟩ : Nonempty ((𝟙_ (Over (Sp (DualNumber k)))).left) := by
    obtain ⟨q⟩ : Nonempty (Sp k) := by
      change Nonempty (PrimeSpectrum k)
      infer_instance
    exact ⟨(spMap (TrivSqZeroExt.fstHom k k k).toRingHom).base q⟩
  have hsub1 : Subsingleton ((𝟙_ (Over (Sp (DualNumber k)))).left) := hsub
  have hy : ∀ x, d.left x = η[G'].left pt := by
    intro x
    obtain ⟨z, rfl⟩ := hjs x
    have h2 := congrArg (fun f : Z ⟶ G'.left => f z) hjd
    simp only [Scheme.Hom.comp_apply] at h2
    rw [h2]
    exact congrArg _ (Subsingleton.elim _ _)
  have hfac := GlobalTheory.DualRigidity.eq_comp_section_of_const A'.hom η[A'].left d.left
    (by simp) hsurj _ hy
  have hη' : η[A'] ≫ d = 1 := key _ hη
  have hd2 : d = toUnit A' ≫ η[A'] ≫ d := by
    ext
    exact hfac
  have hd1 : d = 1 := by
    rw [hd2, hη']
    simp
  exact mul_inv_eq_one.1 hd1

theorem main : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] (T : Scheme.{0}) (t : SAB H T) (x : Sp (DualNumber k) ⟶ T) (t' : SAB H (Sp (DualNumber k))) (ν : SABMap t' t x) (φ : t'.G.left ⟶ t.G.left), IsProper t.G.hom → IsGrpPullback t'.G t.G (constPt x) φ → (∀ (Z : Scheme.{0}) (j : Z ⟶ t'.G.left) (c : Z ⟶ Sp k), j ≫ t'.G.hom = c ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → j ≫ φ = j ≫ ν.φ) → ∀ a, (t'.act.act a).left ≫ φ = φ ≫ (t.act.act a).left := by
  intro hL E _ _ _ H k _ T t x t' ν φ hP hpb hag a
  have hsq := hpb.1
  have hprop : IsProper t'.G.hom := MorphismProperty.of_isPullback (P := @IsProper) hsq hP
  have hs := t'.semi
  have hA : IsAbelianScheme t'.G :=
    { comm := hs.comm, smooth := hs.smooth, proper := hprop, geomConnected := hs.geomConnected }
  have hα : ((t'.act.act a).left ≫ φ) ≫ t.G.hom = t'.G.hom ≫ constPt x := by
    rw [Category.assoc, hsq.w, ← Category.assoc, Over.w]
  have hβ : (φ ≫ (t.act.act a).left) ≫ t.G.hom = t'.G.hom ≫ constPt x := by
    rw [Category.assoc, Over.w, hsq.w]
  let A : t'.G ⟶ t'.G := Over.homMk (hsq.lift _ _ hα) (hsq.lift_snd _ _ _)
  let B : t'.G ⟶ t'.G := Over.homMk (hsq.lift _ _ hβ) (hsq.lift_snd _ _ _)
  have e3 : (t'.act.act a).left ≫ ν.φ = ν.φ ≫ (t.act.act a).left := ν.act a
  have hj := IsPullback.of_hasPullback t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)
  have hab : pullback.fst t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ A.left = pullback.fst t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ B.left := by
    apply hsq.hom_ext
    · simp only [A, B, Over.homMk_left, Category.assoc, IsPullback.lift_fst]
      have e1 := hag _ (pullback.fst t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (pullback.snd t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) hj.w
      have e2 := hag _ (pullback.fst t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ (t'.act.act a).left) (pullback.snd t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom))
        (by rw [Category.assoc, Over.w]; exact hj.w)
      rw [← Category.assoc, e2, Category.assoc, e3, ← Category.assoc, ← e1, Category.assoc]
    · simp only [A, B, Over.homMk_left, Category.assoc, IsPullback.lift_snd]
  let e : Over.mk ((𝟙_ (Over (Sp (DualNumber k)))).hom ≫ constPt x) ⟶ t.G :=
    Over.homMk (η[t'.G].left ≫ φ) (by rw [Category.assoc, hsq.w, ← Category.assoc, Over.w]; rfl)
  have hη1 : (η[t'.G] : 𝟙_ _ ⟶ t'.G) = 1 := by simp [Hom.one_def]
  have he1 : e = 1 := by
    have hm := hpb.2 _ η[t'.G] η[t'.G] e e rfl rfl
    rw [hη1, _root_.mul_one] at hm
    have hee : e * e = e := by
      ext
      rw [hm, ← hη1]
      rfl
    exact _root_.mul_eq_left.1 hee
  have he2 : e ≫ t.act.act a = e := by
    have := t.act.hom a
    rw [he1, Hom.one_def, Category.assoc, IsMonHom.one_hom]
  have he3 := congrArg Over.Hom.left he2
  have hm1 : η[t'.G] ≫ t'.act.act a = η[t'.G] := by
    have := t'.act.hom a
    exact IsMonHom.one_hom _
  have hm2 := congrArg Over.Hom.left hm1
  have hη : η[t'.G] ≫ A = η[t'.G] ≫ B := by
    ext
    simp only [Over.comp_left]
    apply hsq.hom_ext
    · simp only [A, B, Over.homMk_left, Category.assoc, IsPullback.lift_fst]
      simp only [e, Over.comp_left, Over.homMk_left, Category.assoc] at he3 hm2
      rw [← Category.assoc, hm2, he3]
    · simp only [A, B, Over.homMk_left, Category.assoc, IsPullback.lift_snd]
  have hAB := rigidity hL k (pullback.snd t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) t'.G t'.G (pullback.fst t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) A B hA hj hab hη
  have hL' := congrArg Over.Hom.left hAB
  simp only [A, B, Over.homMk_left] at hL'
  calc (t'.act.act a).left ≫ φ = hsq.lift _ _ hα ≫ φ := (hsq.lift_fst _ _ _).symm
    _ = hsq.lift _ _ hβ ≫ φ := by rw [hL']
    _ = φ ≫ (t.act.act a).left := hsq.lift_fst _ _ _

end GlobalTheory.EpsAct
end
