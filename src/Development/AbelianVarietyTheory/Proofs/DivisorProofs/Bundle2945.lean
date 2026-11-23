module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2883
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2861
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2729
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoEqUnitMulOneAddEpsPotential
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2765
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2817
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2755
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2816
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2878
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2818
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2819
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralSeparatedProjModelGradedFunctions
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1543
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2820
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2654
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.TotallySplit
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2641
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.KS.TwoPull

variable {X Y Z : Scheme.{0}}

theorem pull_pull (f : Z ⟶ Y) (g : Y ⟶ X) (h : Z ⟶ X) (e : f ≫ g = h) {U : X.Opens} {V : Y.Opens} {W : Z.Opens}
    (e₁ : V ≤ g ⁻¹ᵁ U) (e₂ : W ≤ f ⁻¹ᵁ V) (e₃ : W ≤ h ⁻¹ᵁ U) (a : Γ(X, U)) :
    (f.appLE V W e₂).hom ((g.appLE U V e₁).hom a) = (h.appLE U W e₃).hom a := by
  subst e
  exact congrArg (fun φ => φ.hom a) (Scheme.Hom.appLE_comp_appLE f g U V W e₁ e₂)

theorem res_pull (φ : Y ⟶ X) {U : X.Opens} {V W : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U) (h' : W ≤ V) (a : Γ(X, U)) :
    resG Y h' ((φ.appLE U V h).hom a) = (φ.appLE U W (h'.trans h)).hom a :=
  congrArg (fun q => q.hom a) (φ.appLE_map h (homOfLE h').op)

theorem pull_res (φ : Y ⟶ X) {U U' : X.Opens} {V : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U') (h' : U' ≤ U) (a : Γ(X, U)) :
    (φ.appLE U' V h).hom (resG X h' a) = (φ.appLE U V (h.trans fun _ hy => h' hy)).hom a :=
  congrArg (fun q => q.hom a) (φ.map_appLE h (homOfLE h').op)

theorem app_res (φ : Y ⟶ X) {U U' : X.Opens} (h' : U' ≤ U) (a : Γ(X, U)) :
    (φ.app U').hom (resG X h' a) = resG Y (fun _ hy => h' hy) ((φ.app U).hom a) := by
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE]
  exact (pull_res φ _ _ _).trans (res_pull φ _ _ _).symm

theorem id_pull {U : X.Opens} (h : U ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ U) (a : Γ(X, U)) :
    ((𝟙 X : X ⟶ X).appLE U U h).hom a = a := by
  have : (𝟙 X : X ⟶ X).appLE U U h = 𝟙 _ := by
    rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
    exact (Category.id_comp _).trans (X.presheaf.map_id _)
  rw [this]
  rfl

theorem spec_pull_inv {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (e : ⊤ ≤ spMap f ⁻¹ᵁ ⊤)
    (r : R) :
    ((spMap f).appLE ⊤ ⊤ e).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) =
      (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom (f r) := by
  have h := congrArg (fun q => q.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  have h2 : (spMap f).appLE ⊤ ⊤ e = (spMap f).appTop := (Scheme.Hom.app_eq_appLE (spMap f) (U := ⊤)).symm
  rw [h2]
  exact h.symm

theorem pull_const {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (φ : Y ⟶ X) (p : X ⟶ Sp R)
    (p' : Y ⟶ Sp R') (hφ : φ ≫ p = p' ≫ spMap f) {U : X.Opens} {V : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U) (r : R) :
    (φ.appLE U V h).hom (constFn p U r) = constFn p' V (f r) := by
  unfold constFn
  rw [← spec_pull_inv f le_top r]
  exact (pull_pull φ p _ hφ _ _ le_top _).trans (pull_pull p' (spMap f) _ rfl _ _ _ _).symm

theorem res_const {R : Type} [CommRing R] (q : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (a : R) :
    resG X h (constFn q U a) = constFn q V a :=
  res_pull q _ h _

def twoPullConstantsRingHom {R : Type} [CommRing R] (q : X ⟶ Sp R) (U : X.Opens) : R →+* Γ(X, U) :=
  (q.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem const_eq {R : Type} [CommRing R] (q : X ⟶ Sp R) (U : X.Opens) (a : R) :
    constFn q U a = twoPullConstantsRingHom q U a := rfl

theorem dual_decomp {k : Type} [Field k] (x : DualNumber k) :
    x = algebraMap k (DualNumber k) x.fst + DualNumber.eps * algebraMap k (DualNumber k) x.snd := by
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

end GlobalTheory.KS.TwoPull


open GlobalTheory.KS.TwoPull in
theorem GlobalTheory.KS.TwoPull.exists_locDerK_of_two_pullbacks : ∀ (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R)) (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.A.left), IsGrpPullback B' P.A (spMap ρ) π₁ → IsGrpPullback B' P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ P.A.left), IsGrpPullback A₀ P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ pr : B'.left ⟶ A₀.left, pr ≫ m₀ = π₂ → pr ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) → ∃ d : ∀ W : P.A.left.Opens, Γ(P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W), GlobalTheory.KS.LocDerK A₀.hom P.A.hom m₀ (fun r => (ρ r).snd) ⊤ d ∧ (∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), pbT π₁ f (π₂ ⁻¹ᵁ W) = pbT π₂ f (π₂ ⁻¹ᵁ W) + constFn B'.hom (π₂ ⁻¹ᵁ W) DualNumber.eps * pbT pr (d W f) (π₂ ⁻¹ᵁ W)) := by
  intro k _ R _ P ρ B' _ π₁ π₂ hπ₁ hπ₂ hagr A₀ _ m₀ hm₀ pr hpr hprA
  subst hpr
  have hsp : spMap (constHom ρ) =
      spMap (algebraMap k (DualNumber k)) ≫ spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ) := by
    rw [← spMap_comp]; rfl
  have hpb : IsPullback pr B'.hom A₀.hom (spMap (algebraMap k (DualNumber k))) := by
    refine IsPullback.of_right ?_ hprA hm₀.1
    rw [← hsp]; exact hπ₂.1
  have hid : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (algebraMap k (DualNumber k)) = 𝟙 _ := by
    rw [← spMap_comp]
    have : ((TrivSqZeroExt.fstHom k k k).toRingHom.comp (algebraMap k (DualNumber k))) = RingHom.id k := by
      ext x; simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [this]; simp [spMap]
  have hcomp : 𝟙 A₀.left ≫ A₀.hom =
      (A₀.hom ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ spMap (algebraMap k (DualNumber k)) := by
    rw [Category.assoc, hid, Category.id_comp, Category.comp_id]
  set j := hpb.lift (𝟙 _) (A₀.hom ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom) hcomp with hjdef
  have hjρ : j ≫ pr = 𝟙 _ := hpb.lift_fst _ _ _
  have hjπ : j ≫ B'.hom = A₀.hom ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom := hpb.lift_snd _ _ _
  have hm : j ≫ π₁ = m₀ := by
    rw [hagr _ j A₀.hom hjπ, ← Category.assoc, hjρ, Category.id_comp]
  have hp : π₁ ≫ P.A.hom = B'.hom ≫ spMap ρ := hπ₁.1.w
  have hW : ∀ W : P.A.left.Opens, pr ⁻¹ᵁ (m₀ ⁻¹ᵁ W) = π₁ ⁻¹ᵁ W := fun W =>
    (GlobalTheory.T.preimage_eq_of_agree_on_closedFibre_dualNumbers k _ _ B'.hom π₁ (pr ≫ m₀) hagr W).symm
  have hdec := GlobalTheory.T.existsUnique_add_eps_mul_on_dualNumber_thickening k A₀.left B'.left A₀.hom B'.hom pr hpb
  have uniq : ∀ (O : A₀.left.Opens) (a b a' b' : Γ(A₀.left, O)),
      (pr.app O).hom a + constFn B'.hom _ DualNumber.eps * (pr.app O).hom b =
        (pr.app O).hom a' + constFn B'.hom _ DualNumber.eps * (pr.app O).hom b' → b = b' := fun O a b a' b' h =>
    congrArg Prod.snd ((hdec O ((pr.app O).hom a + constFn B'.hom _ DualNumber.eps * (pr.app O).hom b)).unique
      (y₁ := (a, b)) (y₂ := (a', b')) rfl h)
  have ex : ∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), ∃ b : Γ(A₀.left, m₀ ⁻¹ᵁ W),
      (π₁.appLE W _ (hW W).le).hom f = (pr.app _).hom ((m₀.app W).hom f) +
        constFn B'.hom _ DualNumber.eps * (pr.app _).hom b := by
    intro W f
    obtain ⟨⟨a, b⟩, hab, -⟩ := hdec (m₀ ⁻¹ᵁ W) ((π₁.appLE W _ (hW W).le).hom f)
    refine ⟨b, ?_⟩
    have hle : m₀ ⁻¹ᵁ W ≤ j ⁻¹ᵁ (pr ⁻¹ᵁ (m₀ ⁻¹ᵁ W)) := by
      rw [← Scheme.Hom.comp_preimage, hjρ]; exact le_rfl
    have h1 := congrArg (j.appLE _ _ hle).hom hab
    rw [map_add (f := _), map_mul, pull_const _ j B'.hom A₀.hom hjπ, pull_pull j π₁ m₀ hm _ _ le_rfl] at h1
    have h2 : (j.appLE _ _ hle).hom ((pr.app (m₀ ⁻¹ᵁ W)).hom a) = a := by
      rw [Scheme.Hom.app_eq_appLE]
      exact (pull_pull j pr (𝟙 _) hjρ (U := m₀ ⁻¹ᵁ W) (W := m₀ ⁻¹ᵁ W) le_rfl hle le_rfl a).trans (id_pull _ a)
    have h3 : constFn A₀.hom (m₀ ⁻¹ᵁ W) ((TrivSqZeroExt.fstHom k k k).toRingHom DualNumber.eps) = 0 := by
      have : (TrivSqZeroExt.fstHom k k k).toRingHom DualNumber.eps = 0 := by simp
      rw [this, const_eq, map_zero]
    have h4 : (m₀.app W).hom f = a := by
      rw [Scheme.Hom.app_eq_appLE]
      refine h1.trans ?_
      rw [h3, zero_mul, add_zero]
      exact h2
    rw [h4]
    exact hab
  choose d hd using ex
  have hee : ∀ O : B'.left.Opens, constFn B'.hom O DualNumber.eps * constFn B'.hom O DualNumber.eps = 0 := fun O => by
    rw [const_eq, ← map_mul, DualNumber.eps_mul_eps, map_zero]
  refine ⟨d, ⟨fun W _ f f' => ?_, fun W _ f f' => ?_, fun W W' h _ f => ?_, fun W _ r => ?_⟩, ?_⟩
  · refine uniq _ ((m₀.app W).hom (f + f')) _ ((m₀.app W).hom (f + f')) _ ?_
    rw [← hd, map_add (f := _), hd, hd]
    simp only [map_add (f := _)]
    ring
  · refine uniq _ ((m₀.app W).hom (f * f')) _ ((m₀.app W).hom (f * f')) _ ?_
    rw [← hd, map_mul, hd, hd]
    simp only [map_add (f := _), map_mul]
    linear_combination (pr.app _).hom (d W f) * (pr.app _).hom (d W f') * hee _
  · have h0 : m₀ ⁻¹ᵁ W' ≤ m₀ ⁻¹ᵁ W := fun _ hy => h hy
    rw [show rsT (d W f) (m₀ ⁻¹ᵁ W') = resG _ h0 (d W f) from dif_pos h0]
    refine uniq _ ((m₀.app W').hom (resG _ h f)) _ ((m₀.app W').hom (resG _ h f)) _ ?_
    have h0' : pr ⁻¹ᵁ (m₀ ⁻¹ᵁ W') ≤ pr ⁻¹ᵁ (m₀ ⁻¹ᵁ W) := fun _ hy => h hy
    have h1 := congrArg (resG _ h0') (hd W f)
    rw [res_pull, map_add (f := _), map_mul, res_const] at h1
    rw [← hd, pull_res]
    refine h1.trans ?_
    rw [app_res m₀ h f]
    exact congrArg₂ (· + ·) (app_res pr h0 _).symm (congrArg (_ * ·) (app_res pr h0 _).symm)
  · refine uniq _ ((m₀.app W).hom (constFn P.A.hom W r)) _ (constFn A₀.hom _ (ρ r).fst) _ ?_
    rw [← hd, pull_const ρ π₁ P.A.hom B'.hom hp, Scheme.Hom.app_eq_appLE, pull_const _ pr A₀.hom B'.hom hpb.w,
      pull_const _ pr A₀.hom B'.hom hpb.w]
    simp only [const_eq]
    rw [← map_mul, ← map_add (f := _)]
    exact congrArg _ (dual_decomp _)
  · intro W f
    show pbT π₁ f (pr ⁻¹ᵁ (m₀ ⁻¹ᵁ W)) = pbT (pr ≫ m₀) f (pr ⁻¹ᵁ (m₀ ⁻¹ᵁ W)) +
      constFn B'.hom (pr ⁻¹ᵁ (m₀ ⁻¹ᵁ W)) DualNumber.eps * pbT pr (d W f) (pr ⁻¹ᵁ (m₀ ⁻¹ᵁ W))
    unfold pbT
    rw [dif_pos (hW W).le, dif_pos le_rfl, dif_pos (show pr ⁻¹ᵁ (m₀ ⁻¹ᵁ W) ≤ (pr ≫ m₀) ⁻¹ᵁ W from le_rfl), hd W f, Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE,
      pull_pull pr m₀ (pr ≫ m₀) rfl]

end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lineBundleIso_eq_unit_mul_one_add_eps_potential : ∀ (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R)) (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.A.left), IsGrpPullback B' P.A (spMap ρ) π₁ → IsGrpPullback B' P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ P.A.left), IsGrpPullback A₀ P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ pr : B'.left ⟶ A₀.left, pr ≫ m₀ = π₂ → pr ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) → ∀ {J : Type} (V : J → P.A.left.Opens) (jj : J → P.L.ι) (ed : ∀ W : P.A.left.Opens, Γ(P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), GlobalTheory.HeatConn.IsConnK P.A P.L A₀ m₀ (fun r => (ρ r).snd) V jj ed pb → (∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), pbT π₁ f (π₂ ⁻¹ᵁ W) = pbT π₂ f (π₂ ⁻¹ᵁ W) + constFn B'.hom (π₂ ⁻¹ᵁ W) DualNumber.eps * pbT pr (ed W f) (π₂ ⁻¹ᵁ W)) → ∀ w : LB.Iso (P.L.pull π₁) (P.L.pull π₂), w.IsGen → ∃ κ : (DualNumber k)ˣ, ∀ i, rsT (w.s (fun _ => jj i, fun _ => jj i)).val (π₂ ⁻¹ᵁ V i) = constFn B'.hom (π₂ ⁻¹ᵁ V i) κ.val * (1 + constFn B'.hom (π₂ ⁻¹ᵁ V i) DualNumber.eps * pbT pr (pb i) (π₂ ⁻¹ᵁ V i)) := by
  first | exact @GlobalTheory.ConnUnit.unit_mul_one_add_eps | exact GlobalTheory.ConnUnit.unit_mul_one_add_eps | (intros; apply GlobalTheory.ConnUnit.unit_mul_one_add_eps <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConstPointCone

theorem unitOn_one {A : Type} [CommRing A] : unitOn (1 : Aˣ) = 1 :=
  map_one (Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.toMonoidHom)

theorem dir_eq_zero_of_const : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : DegPre R) (m : ℕ) (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Q.X), IsMonomial Q t gam → LinearIndependent ℤ gam → (∀ i, t i ∈ maximalIdeal R) → (∀ i y z, gam i y z = gam i z y) → ∀ (k : Type) [Field k] [CharZero k] (ρ : R →+* DualNumber k) (a : Fin m → k), (∀ r, (ρ r).snd = 0) → IsConstAlong Q t gam ρ a → a = 0 := by
  intro R _ _ _ Q m t gam hmon hli _ hs k _ _ ρ a hρ hc
  have hρc : constHom ρ = ρ := by
    ext r
    · simp [constHom, TrivSqZeroExt.algebraMap_eq_inl]
    · simp [constHom, TrivSqZeroExt.algebraMap_eq_inl, hρ]
  obtain ⟨B', _, π₁, π₂, w, c', h1, h2, h3, hw, hc', hrel⟩ := hc
  rw [hρc] at h2 hc' hrel
  have hπ : π₁ = π₂ := GlobalTheory.T.groupPullback_abelianScheme_dualNumber_eq k Q.P.A Q.P.g B' ρ π₁ π₂ Q.P.isAb Q.P.smoothDim h1 h2 h3
  subst hπ
  have hab : IsAbelianScheme B' :=
    (GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback ρ Q.P.A B' π₁ Q.P.g h1 Q.P.isAb Q.P.smoothDim).1
  obtain ⟨lam, hlam⟩ := GlobalTheory.T.pulledBackLineBundle_automorphism_eq_const B' Q.P.L π₁ hab Q.P.isLB w hw
  obtain ⟨zz⟩ : Nonempty (Sp (DualNumber k)) := inferInstance
  obtain ⟨J, hJ⟩ : ∃ J, Good Q.P.L zz J := by
    obtain ⟨J, hJ, -⟩ := exists_good Q.P.L Q.P.isLB zz (K := PEmpty) PEmpty.elim PEmpty.elim
      (fun a => a.elim) (fun a => a.elim)
    exact ⟨J, hJ⟩
  have hW : ∀ x, gm (c' x) zz _ (w.s (fun _ => J (c' x ≫ π₁), fun _ => J (c' x ≫ π₁))) =
      gm (𝟙 (Sp (DualNumber k))) zz ⊤ (unitOn lam) := by
    intro x
    have hmem : π₁ (c' x zz) ∈ Q.P.L.U (J (c' x ≫ π₁)) := by
      have := hJ (c' x ≫ π₁)
      simpa using this
    rw [hlam _ (c' x) zz _ hmem, (hc' x).1]
  have htne := GlobalTheory.T.monomialBoundaryFamily_param_ne_zero Q t gam hmon hli hs
  have key : ∀ y z, ∑ i, a i * (gam i y z : k) = 0 := by
    intro y z
    obtain ⟨τ₀, hτ⟩ := GlobalTheory.T.exists_unitPartOfPeriodTau_monomial Q t gam hmon hs htne y z
    let e : (DualNumber k)ˣ := ⟨1 + TrivSqZeroExt.inr (∑ i, a i * (gam i y z : k)),
      1 - TrivSqZeroExt.inr (∑ i, a i * (gam i y z : k)), by ext <;> simp, by ext <;> simp⟩
    have h := hrel y z τ₀ hτ e rfl zz J hJ
    rw [hW (y + z), hW y, hW z, hW 0] at h
    have h' : gm (𝟙 (Sp (DualNumber k))) zz ⊤ (unitOn e) = gm (𝟙 (Sp (DualNumber k))) zz ⊤ (unitOn 1) := by
      rw [unitOn_one, map_one]
      have hG : ∀ G : ((Sp (DualNumber k)).presheaf.stalk zz)ˣ, G * G⁻¹ * G⁻¹ * G = 1 := fun G => by group
      rw [hG, _root_.one_mul] at h
      exact mul_right_cancel (h.symm.trans (_root_.one_mul _).symm)
    have he := GlobalTheory.T.dualNumber_unit_eq_of_germ_eq k zz _ _ h'
    have := congrArg (fun u : (DualNumber k)ˣ => TrivSqZeroExt.snd (u : DualNumber k)) he
    simpa [e] using this
  exact GlobalTheory.T.linIndep_intBilinForm_charZero_combination_eq_zero gam k a hli key

end GlobalTheory.ConstPointCone
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.BaseInj

theorem fnOf_appLE_top {Y S : Scheme.{0}} [IsIntegral Y] (q : Y ⟶ S) (U : Y.Opens) (e : U ≤ q ⁻¹ᵁ ⊤)
    (h : genericPoint Y ∈ U) (x : Γ(S, ⊤)) :
    fnOf U h ((q.appLE ⊤ U e).hom x) = fnOf ⊤ trivial (q.appTop.hom x) :=
  fnOf_resG (X := Y) (U := ⊤) (V := U) le_top h (q.appTop.hom x)

theorem app_appLE_top {Y Z S : Scheme.{0}} (f : Y ⟶ Z) (s : Z ⟶ S) (U : Z.Opens) (x : Γ(S, ⊤)) :
    (f.app U).hom ((s.appLE ⊤ U le_top).hom x) = ((f ≫ s).appLE ⊤ (f ⁻¹ᵁ U) le_top).hom x := by
  rw [Scheme.Hom.app_eq_appLE]
  exact congrArg (fun t => t.hom x) (Scheme.Hom.appLE_comp_appLE f s ⊤ U (f ⁻¹ᵁ U) le_top le_rfl)

theorem fnOf_app_appLE_top {Y Z S : Scheme.{0}} [IsIntegral Y] (f : Y ⟶ Z) (s : Z ⟶ S) (U : Z.Opens)
    (h : genericPoint Y ∈ f ⁻¹ᵁ U) (x : Γ(S, ⊤)) :
    fnOf (f ⁻¹ᵁ U) h ((f.app U).hom ((s.appLE ⊤ U le_top).hom x)) = fnOf ⊤ trivial ((f ≫ s).appTop.hom x) :=
  (congrArg _ (app_appLE_top f s U x)).trans (fnOf_appLE_top (f ≫ s) (f ⁻¹ᵁ U) le_top h x)

theorem const_agree {R R₁ : Type} [CommRing R] [CommRing R₁] (ρ : R →+* R₁) {P Z : Scheme.{0}} (p : P ⟶ Sp R)
    (g : Z ⟶ P) (s : Z ⟶ Sp R₁) (w : g ≫ p = s ≫ spMap ρ) (V : P.Opens) (r : R) :
    (g.app V).hom ((p.appLE ⊤ V le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) =
      (s.appLE ⊤ (g ⁻¹ᵁ V) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (ρ r)) := by
  have h1 : (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (ρ r) =
      (spMap ρ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) :=
    congrArg (fun t => t.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ρ))
  rw [h1, app_appLE_top, w]
  rfl

theorem app_injective : ∀ (R F : Type) [CommRing R] [IsDomain R] [Field F] (c₀ : R →+* F) (N : ℕ → Set F), GradedFam c₀ N → ∀ (P : Scheme.{0}) [IsIntegral P] (p : P ⟶ Sp R) (ψ : P.functionField →+* F) (Dp : ℕ → F → P.Opens), IsModel c₀ N p ψ Dp → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (ρ : R →+* R₁), ρ.Flat → Function.Injective c₀ → ∀ (Y : Scheme.{0}) [IsIntegral Y] [CompactSpace Y] [QuasiSeparatedSpace Y] (q : Y ⟶ Sp R₁) (θ : F →+* Y.functionField) (D₁ : CartierDiv Y), θ.comp c₀ = (GlobalTheory.Desc.cst q).comp ρ → LinDisj c₀ (GlobalTheory.Desc.cst q) θ → AmpleDiv D₁ → (∀ k, Sec D₁ k = spanBy (GlobalTheory.Desc.cst q) (θ '' N k)) → ∀ m : Y ⟶ P, PFF (𝟙 _) m (θ.comp ψ) → (∀ k, 1 ≤ k → ∀ b ∈ N k, ∀ y, m y ∈ Dp k b ↔ y ∈ locus D₁ k (θ b)) → ∀ (hm : m ≫ p = q ≫ spMap ρ) (k : ℕ), 1 ≤ k → ∀ b ∈ N k, Function.Injective ((pullback.lift m q hm).app ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b)) := by
  intro R F _ _ _ c₀ N hN P _ p ψ Dp hM R₁ _ _ ρ hρ hc Y _ _ _ q θ D₁ hθ hld _ _ m hff hloc hm k hk b hb
  by_cases hb0 : b = 0
  · have hV : Dp k b = ⊥ :=
      eq_bot_iff.2 fun x hx => ((hM.gen k hk b hb).1 (gen_mem hx) hb0).elim
    rw [hV]
    have : Subsingleton Γ(pullback p (spMap ρ), (pullback.fst p (spMap ρ)) ⁻¹ᵁ (⊥ : P.Opens)) :=
      inferInstanceAs (Subsingleton Γ(pullback p (spMap ρ), ⊥))
    exact fun _ _ _ => Subsingleton.elim _ _
  have hV : genericPoint P ∈ Dp k b := (hM.gen k hk b hb).2 hb0
  have hY : genericPoint Y ∈ m ⁻¹ᵁ Dp k b :=
    (hloc k hk b hb _).2 (CartierDiv.generatesAt_genericPoint _ ((map_ne_zero θ).2 hb0))
  generalize hf : pullback.lift m q hm = f
  have hf1 : f ≫ pullback.fst p (spMap ρ) = m := by rw [← hf, pullback.lift_fst]
  have hf2 : f ≫ pullback.snd p (spMap ρ) = q := by rw [← hf, pullback.lift_snd]
  clear hf hm hloc
  subst hf1 hf2
  refine (injective_iff_map_eq_zero (f.app _).hom).2 fun x hx => ?_
  obtain ⟨n, a, r, rfl⟩ := GlobalTheory.T.sections_preimage_affine_baseChange_eq_sum_products R R₁ ρ P p (Dp k b) (hM.affine k hk b hb) x
  letI : Algebra R R₁ := ρ.toAlgebra
  letI : Algebra R Γ(P, Dp k b) :=
    ((p.appLE ⊤ (Dp k b) le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).toAlgebra
  have hsum : ∑ i, θ ((ψ.comp (fnOf (Dp k b) hV)) (a i)) * GlobalTheory.Desc.cst (f ≫ pullback.snd p (spMap ρ)) (r i) = 0 := by
    have := congrArg (fnOf (f ⁻¹ᵁ (pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b) hY) hx

    rw [map_zero, map_sum, map_sum] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul]
    congr 1
    · exact (GlobalTheory.T.rationalFunction_app_of_preservesGenericPoint P Y _ _ hff (Dp k b) hV hY (a i)).symm
    · exact (fnOf_app_appLE_top f _ ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b) hY _).symm
  have hz := GlobalTheory.T.sum_tmul_eq_zero_of_flat_linearlyDisjoint_subring R R₁ Γ(P, Dp k b) F Y.functionField hρ c₀ (ψ.comp (fnOf (Dp k b) hV)) _ θ hc
    (ψ.injective.comp (fnOf_injective _ hV))
    (by
      rw [← hM.const]
      ext t
      exact congrArg ψ (fnOf_appLE_top p _ le_top hV _)) hθ hld n a r hsum
  let g := (pullback.fst p (spMap ρ)).app (Dp k b)
  let s : R₁ →+* Γ(pullback p (spMap ρ), (pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b) :=
    ((pullback.snd p (spMap ρ)).appLE ⊤ ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b) le_top).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom
  letI : Algebra R Γ(pullback p (spMap ρ), (pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b) := (s.comp ρ).toAlgebra
  let gA : Γ(P, Dp k b) →ₐ[R] Γ(pullback p (spMap ρ), (pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b) :=
    ⟨g.hom, fun t => const_agree ρ p _ _ pullback.condition _ t⟩
  let sA : R₁ →ₐ[R] Γ(pullback p (spMap ρ), (pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b) := ⟨s, fun _ => rfl⟩
  have := congrArg (Algebra.TensorProduct.lift gA sA fun _ _ => Commute.all _ _) hz

  rw [map_zero, map_sum] at this
  simp only [Algebra.TensorProduct.lift_tmul] at this
  exact this

end GlobalTheory.Desc.BaseInj
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SqDecFinite

theorem exists_algHom_finite (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) (hR : R.FG) :
    ∃ (k₁ : Type) (_ : Field k₁) (_ : Algebra k k₁) (_ : FiniteDimensional k k₁), Nonempty (R →ₐ[k] k₁) := by
  have : Algebra.FiniteType k R := (Subalgebra.fg_iff_finiteType _).1 hR
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  have : Algebra.FiniteType k (R ⧸ m) := Algebra.FiniteType.trans (S := R) inferInstance inferInstance
  have : Module.Finite k (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (R ⧸ m)
  exact ⟨R ⧸ m, inferInstance, inferInstance, inferInstance, ⟨Ideal.Quotient.mkₐ k m⟩⟩

theorem main : ∀ (k Ω : Type) [Field k] [Field Ω] (σ : k →+* Ω) (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ → ∀ (L M : LB A₀.left), L.IsLB → M.IsLB → SqDec ((Over.pullback (spMap σ)).obj A₀) (L.pull (pullback.fst A₀.hom (spMap σ))) (M.pull (pullback.fst A₀.hom (spMap σ))) → ∃ (k₁ : Type) (_ : Field k₁) (_ : Algebra k k₁) (_ : FiniteDimensional k k₁), SqDec ((Over.pullback (spMap (algebraMap k k₁))).obj A₀) (L.pull (pullback.fst A₀.hom (spMap (algebraMap k k₁)))) (M.pull (pullback.fst A₀.hom (spMap (algebraMap k k₁)))) := by
  intro k Ω _ _ σ A₀ _ hA L M hL hM h
  letI := σ.toAlgebra
  obtain ⟨R, hR, hRd⟩ := GlobalTheory.T.squareDecomposition_descends_to_finitelyGenerated k Ω A₀ hA L M hL hM h
  obtain ⟨k₁, _, _, _, ⟨ρ⟩⟩ := exists_algHom_finite k Ω R hR
  exact ⟨k₁, inferInstance, inferInstance, inferInstance, GlobalTheory.T.squareDecomposition_baseChange_algebraMap k R k₁ ρ A₀ L M hL hM hRd⟩

end GlobalTheory.SqDecFinite
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.exists_integral_separated_projModel_gradedFunctions : ∀ (R F : Type) [CommRing R] [IsDomain R] [Field F] (c₀ : R →+* F) (N : ℕ → Set F), GradedFam c₀ N → (∃ k, 1 ≤ k ∧ ∃ b ∈ N k, b ≠ 0) → ∃ (P : Scheme.{0}) (_ : IsIntegral P) (p : P ⟶ Sp R) (ψ : P.functionField →+* F) (Dp : ℕ → F → P.Opens), IsModel c₀ N p ψ Dp := by
  first | exact @GlobalTheory.Desc.exists_model | exact GlobalTheory.Desc.exists_model | (intros; apply GlobalTheory.Desc.exists_model <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneMapCore

theorem oneMapRowR_of_core_of_size :
    ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → IoExt R → ∀ i, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → OneMapRowR T R κ v₀ O ph i := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hn hC hoff hused hT hI i hP hph
  have hci : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 := GlobalTheory.chartIndependence_unconditional
  have h0 : OneMapRow0 T R κ v₀ O i :=
    GlobalTheory.T.thetaOneMap_baseTuple_of_characterisation_extremal hci D G Pl0 T0 A T R F κ v₀ hC (GlobalTheory.T.cuspFormsAgreement_contains_formIndependentFields D G Pl0 T0 A T R κ v₀ hT) hI O i hP
  exact GlobalTheory.T.oneMapRow_all_tuples_of_core_clauses hci D G Pl0 T0 A T R F κ v₀ O ph hC hoff hused hT hI i hP hph
    (GlobalTheory.T.classSums_span_cuspForms_baseTuple_second_field D G Pl0 T0 A T R F κ v₀ O hn hC hT hI i hP h0)

end GlobalTheory.OneMapCore
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.SiegLev GlobalTheory.SiegLevCalc GlobalTheory.SiegelPullComp GlobalTheory.SiegelPull

theorem _root_.GlobalTheory.T.thetaConstants_finite_of_polarisedAVIso_algClosed : ∀ (G N' : ℕ) (J : Type) (K : Type) [Field K] [IsAlgClosed K] (b : TBase K (N' ^ 2)) (Q : PolAV (Sp K)), Odd N' → 3 ≤ N' → ∃ V : Set (Ix G (N' ^ 2) → K), V.Finite ∧ ∀ t : TObj G (N' ^ 2) J b (𝟙 (Sp K)), (∃ φ : t.A ≅ Q.A, IsMonHom φ.hom ∧ LBIso t.L (Q.L.pull φ.hom.left)) → ∃ v ∈ V, t.HasTh (𝟙 _) v := by
  first | exact @GlobalTheory.ThetaFiniteIso.thetaPts_finite | exact GlobalTheory.ThetaFiniteIso.thetaPts_finite | (intros; apply GlobalTheory.ThetaFiniteIso.thetaPts_finite <;> assumption)
end
