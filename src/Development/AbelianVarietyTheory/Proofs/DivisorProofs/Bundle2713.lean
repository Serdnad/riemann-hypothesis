module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2652
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2647
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan

@[expose] public section

section

set_option autoImplicit false

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.FracPt

theorem stalkIso_gs {K : Type} [CommRing K] [IsLocalRing K] {X : Scheme.{0}} (f : Sp K ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ f ⁻¹ᵁ U) (a : Γ(X, U)) :
    (stalkClosedPointIso (CommRingCat.of K)).hom.hom (gs f (closedPoint K) U a) = valR f U a := by
  have e1 : gs f (closedPoint K) U a = (Sp K).presheaf.germ ⊤ (closedPoint K) trivial ((f.appLE U ⊤ h).hom a) := by
    erw [gs_eq f _ U (h trivial)]
    rw [← TopCat.Presheaf.germ_res_apply (Sp K).presheaf (homOfLE h) (closedPoint K) trivial]
    rfl
  erw [e1]
  rw [valR, dite_eq_left h]
  rw [← ΓSpecIso_hom_stalkClosedPointIso_inv (CommRingCat.of K)]
  simp only [CommRingCat.comp_apply]
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

end GlobalTheory.FracPt

namespace GlobalTheory.FracPt

theorem valR_spMap_const {Ω K : Type} [CommRing Ω] [CommRing K] (f : Ω →+* K) (ω : Ω) :
    valR (spMap f) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom ω) = f ω := by
  have h : ⊤ ≤ spMap f ⁻¹ᵁ ⊤ := le_rfl
  rw [valR, dite_eq_left h]
  calc _ = ((Scheme.ΓSpecIso (CommRingCat.of Ω)).hom ≫ CommRingCat.ofHom f).hom
        ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom ω) := by
          rw [← Scheme.ΓSpecIso_naturality]; rfl
    _ = f ω := by
          have e : (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom ω) = ω := by
            rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
          rw [CommRingCat.hom_comp, RingHom.comp_apply, e, CommRingCat.hom_ofHom]

theorem chart_eq_value_mul_pow : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω]
    (x : Sp Ω ⟶ X) (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 X)) (j : L.ι) (O : X.Opens), O ≤ L.U j →
    ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) ⁻¹ᵁ O → ∃ e₀ : (FractionRing Ω)ˣ,
      ∀ (k : ℕ) (σ : SecM (𝟙 X) L k) (ω : Ω), IsValue (𝟙 _) L x g k σ ω →
        valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) O (rsT (σ.f fun _ => j) O) =
          algebraMap Ω (FractionRing Ω) ω * (e₀ : FractionRing Ω) ^ k := by
  intro X L hL Ω _ _ x g j O hO hxO
  let ηF := spMap (algebraMap Ω (FractionRing Ω))
  let z : Sp (FractionRing Ω) := closedPoint (FractionRing Ω)
  have hz : ((ηF ≫ x) ≫ 𝟙 X) z ∈ L.U j := by
    rw [Category.comp_id]; exact hO (hxO trivial)
  obtain ⟨J, hJ, hJj⟩ := exists_good L hL z (K := PUnit) (fun _ => (ηF ≫ x) ≫ 𝟙 X) (fun _ => j)
    (fun _ _ _ => rfl) (fun _ => hz)
  let φ := (stalkClosedPointIso (CommRingCat.of (FractionRing Ω))).hom.hom
  refine ⟨Units.map φ.toMonoidHom (val g ηF z J), fun k σ ω hv => ?_⟩
  have e := congrArg φ (hv _ ηF z J hJ)
  have hOW : O ≤ (LB.LinComb L (fun _ : Fin 1 => 𝟙 X) (fun _ => (k : ℤ))).U (fun _ => j) :=
    fun y hy => Set.mem_iInter.2 fun _ => hO hy
  rw [sval_of σ (ηF ≫ x) z J (fun _ => j) (fun _ => hJj PUnit.unit)] at e
  erw [← gs_res (ηF ≫ x) z hOW (hxO trivial) (σ.f fun _ => j)] at e
  rw [map_mul, Units.val_pow_eq_pow_val, map_pow] at e
  have e1 := stalkIso_gs (ηF ≫ x) O hxO ((X.presheaf.map (homOfLE hOW).op).hom (σ.f fun _ => j))
  have e2 := stalkIso_gs ηF ⊤ le_rfl ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom ω)
  rw [valR_spMap_const] at e2
  erw [e1, e2] at e
  rw [GlobalTheory.KS.rsT, dite_eq_left hOW]
  exact e

end GlobalTheory.FracPt
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SecSmul

theorem map_resTop {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (c : Γ(X, ⊤)) :
    (X.presheaf.map (homOfLE h).op).hom (resTop U c) = resTop V c := by
  simp only [resTop]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem exists_smul : ∀ (X : Scheme.{0}) (L : LB X) (k : ℕ) (σ : SecM (𝟙 X) L k) (c : Γ(X, ⊤)),
    ∃ σ'' : SecM (𝟙 X) L k, ∀ j, σ''.f j = resTop _ c * σ.f j := by
  intro X L k σ c
  refine ⟨⟨fun j => resTop _ c * σ.f j, fun i j => ?_⟩, fun j => rfl⟩
  rw [map_mul, map_mul, σ.compat i j, map_resTop, map_resTop]
  ring

end GlobalTheory.SecSmul
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatV

theorem val_pow_mul_eq {R : Type} [CommRing R] (t b : Rˣ) (a : R) (k : ℕ) :
    ((t ^ k : Rˣ) : R) * a = a * ((b⁻¹ ^ k : Rˣ) : R) * (((t * b) ^ k : Rˣ) : R) := by
  have e : ((b⁻¹ ^ k : Rˣ) : R) * ((b ^ k : Rˣ) : R) = 1 := by
    rw [← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one]
  rw [mul_pow, Units.val_mul]
  linear_combination (-(((t ^ k : Rˣ) : R) * a)) * e

theorem exists_isValue : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (Ω : Type) [CommRing Ω] [IsLocalRing Ω] (x : Sp Ω ⟶ X) (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 X)), g.IsGen → ∀ (k : ℕ) (σ : SecM (𝟙 X) L k), ∃ ω : Ω, IsValue (𝟙 _) L x g k σ ω := by
  intro X L hL Ω _ _ x g hg k σ
  obtain ⟨j₀, hj₀⟩ : ∃ i, ∀ p : Sp Ω, x.base p ∈ L.U i := by
    have hc : x.base (IsLocalRing.closedPoint Ω) ∈ (⨆ i, L.U i : X.Opens) := by rw [hL.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hc
    exact ⟨i, fun p => ((IsLocalRing.specializes_closedPoint p).map x.continuous).mem_open (L.U i).isOpen hi⟩
  have hW : (⊤ : (Sp Ω).Opens) ≤ x ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j₀) :=
    fun p _ => Set.mem_iInter.2 fun _ => hj₀ p
  have hG : (⊤ : (Sp Ω).Opens) ≤ LB.wchart L (fun _ : PUnit => x ≫ 𝟙 X) (fun _ => j₀) :=
    fun p _ => Set.mem_iInter.2 fun _ => hj₀ p
  let ωs : Γ(Sp Ω, ⊤) := ((Sp Ω).presheaf.map (homOfLE hW).op).hom
      ((x.app (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j₀))).hom (σ.f fun _ => j₀)) *
    ((ReciprocityTheory.ChartRestriction.G.Semi.res hG (g.s fun _ => j₀))⁻¹ ^ k).val
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ωs, ?_⟩
  intro Z r z J hJ
  have hinv : (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ωs) = ωs := by
    simp
  rw [hinv]
  have hj : (r ≫ x) z ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => J ((r ≫ x) ≫ 𝟙 X)) := hJ.mem _ (r ≫ x)
  have hj0 : (r ≫ x) z ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j₀) := hW (show r z ∈ (⊤ : (Sp Ω).Opens) from trivial)
  have hgj : r z ∈ LB.wchart L (fun _ : PUnit => x ≫ 𝟙 X) (fun _ => J (r ≫ x ≫ 𝟙 X)) := hJ.mem _ r
  have hg0 : r z ∈ LB.wchart L (fun _ : PUnit => x ≫ 𝟙 X) (fun _ => j₀) := hG (show r z ∈ (⊤ : (Sp Ω).Opens) from trivial)
  rw [sval_of σ (r ≫ x) z J _ (fun _ => rfl), sec_trans σ (r ≫ x) z hj hj0, val_of g r z J _ (fun _ => rfl),
    gen_trans hg r z hgj hg0]
  have hT : trF (L := L) (fun _ : Fin 1 => 𝟙 X) (fun _ => (k : ℤ)) (r ≫ x) z (fun _ => J ((r ≫ x) ≫ 𝟙 X)) (fun _ => j₀) =
      trF (L := L) (fun _ : PUnit => x ≫ 𝟙 X) (fun _ => 1) r z (fun _ => J (r ≫ x ≫ 𝟙 X)) (fun _ => j₀) ^ k := by
    simp only [trF]
    rw [Category.assoc]
    simp
  have hp := (gs_pull r x z (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j₀)) hj0 (σ.f fun _ => j₀)).symm
  have hm : r z ∈ (⊤ : (Sp Ω).Opens) := trivial
  have h1 := gs_mul r z ⊤ hm (((Sp Ω).presheaf.map (homOfLE hW).op).hom
      ((x.app (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j₀))).hom (σ.f fun _ => j₀)))
    ((ReciprocityTheory.ChartRestriction.G.Semi.res hG (g.s fun _ => j₀))⁻¹ ^ k).val
  have h2 := gm_res r z hG hm (g.s fun _ => j₀)
  rw [gs_res r z hW hm, gs_unit r z ⊤ hm, map_pow, map_inv] at h1
  erw [h2] at h1
  rw [hT, hp, h1]
  exact val_pow_mul_eq _ _ _ _

end GlobalTheory.HeatV
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

noncomputable section

namespace GlobalTheory.HeatPointValue

section Val

variable {A : Type} [CommRing A] {Y : Scheme.{0}}

def evalAt (x : Sp A ⟶ Y) (V : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V) : Γ(Y, V) →+* A :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp (x.appLE V ⊤ h).hom

theorem valR_eq_evalAt (x : Sp A ⟶ Y) (V : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(Y, V)) :
    valR x V f = evalAt x V h f := by
  unfold valR
  rw [dif_pos h]
  rfl

theorem evalAt_constFn {B : Type} [CommRing B] (x : Sp A ⟶ Y) (p : Y ⟶ Sp B) (ψ : B →+* A) (hx : x ≫ p = spMap ψ)
    (V : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V) (a : B) : evalAt x V h (constFn p V a) = ψ a := by
  have e₁ : p.appLE ⊤ V (fun _ _ => trivial) ≫ x.appLE V ⊤ h = (x ≫ p).appLE ⊤ ⊤ le_rfl :=
    Scheme.Hom.appLE_comp_appLE x p ⊤ V ⊤ _ h
  have e₂ : ∀ q : Sp A ⟶ Sp B, q.appLE ⊤ ⊤ le_rfl = q.appTop := fun q => (Scheme.Hom.app_eq_appLE _).symm
  rw [e₂, hx] at e₁
  have n := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ))
  change (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (ψ a) =
    (spMap ψ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom a) at n
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
    ((p.appLE ⊤ V (fun _ _ => trivial) ≫ x.appLE V ⊤ h).hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom a)) = ψ a
  rw [e₁, ← n]
  exact (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id_apply _

theorem rsT_same {O₀ : Y.Opens} (s : Γ(Y, O₀)) : rsT s O₀ = s := by
  have e : rsT s O₀ = resG Y le_rfl s := dif_pos le_rfl
  rw [e]
  change (Y.presheaf.map (𝟙 _)).hom s = s
  rw [Y.presheaf.map_id]; rfl

end Val

theorem value_acts : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (X : Scheme.{0}) (m : G.left ⟶ X) (L : LB X) (n : ℕ) (dd : Fin n → Fld G.left) (D : R → R) (h : Heat G m L dd D) (i0 : h.J) (Ω : Type) [CommRing Ω] (φ : R →+* Ω) (x : Sp Ω ⟶ G.left), x ≫ G.hom = spMap φ → ∀ (δ : Fin n → Derivation ℤ Ω Ω), (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) → ∀ (dΩ : Derivation ℤ Ω Ω), ⊤ ≤ x ⁻¹ᵁ h.W i0 → (∀ O f, O ≤ h.W i0 → ⊤ ≤ x ⁻¹ᵁ O → valR x O (h.d i0 O f) = dΩ (valR x O f)) → (∀ r, dΩ (φ r) = φ (D r)) ∧ ∀ (k : ℕ) (τ τ' : SecM m L k), h.Acts k τ τ' → valR x (h.W i0) (rsT (τ'.f fun _ => h.j i0) (h.W i0)) = ringOp ⇑dΩ (fun a => ⇑(δ a)) (φ.mapMatrix h.Θ) (fun a => φ (h.u a)) (valR x _ (h.p i0)) (valR x _ (h.p' i0)) k (valR x (h.W i0) (rsT (τ.f fun _ => h.j i0) (h.W i0))) := by
  intro R _ G _ _ X m L n dd D h i0 Ω _ φ x hx δ hδ dΩ hW hd
  have hδ' : ∀ a f, evalAt x _ hW (dd a (h.W i0) f) = δ a (evalAt x _ hW f) := fun a f => by
    rw [← valR_eq_evalAt, ← valR_eq_evalAt]; exact hδ a _ f hW
  have hd' : ∀ f, evalAt x _ hW (h.d i0 (h.W i0) f) = dΩ (evalAt x _ hW f) := fun f => by
    rw [← valR_eq_evalAt, ← valR_eq_evalAt]; exact hd _ f le_rfl hW
  have hc := evalAt_constFn x G.hom φ hx _ hW
  refine ⟨fun r => ?_, fun k τ τ' ha => ?_⟩
  · rw [← hc, ← hc, ← hd', (h.lift i0).2 _ le_rfl]
  · rw [ha i0]
    simp only [valR_eq_evalAt x _ hW]
    unfold GlobalTheory.Heat.op ringOp

    simp only [map_add (f := _), map_sub, map_mul, map_sum, map_pow, map_natCast, map_ofNat, hδ', hd', hc, rsT_same,
    RingHom.mapMatrix_apply, Matrix.map_apply]

end GlobalTheory.HeatPointValue
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeatV

abbrev bo (R : Type) [CommRing R] (f : R) : (Sp R).affineOpens :=
  (Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens))
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom f)

abbrev resV (R : Type) [CommRing R] (f : R) : R →+* Γ(Sp R, (bo R f).1) :=
  ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤)
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom f))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

abbrev cst {Y X : Scheme.{0}} (π : Y ⟶ X) (V : X.Opens) {O : Y.Opens} (h : O ≤ π ⁻¹ᵁ V) : Γ(X, V) →+* Γ(Y, O) :=
  (π.appLE V O h).hom

def opV {Y X : Scheme.{0}} (π : Y ⟶ X) (V : X.Opens) {n : ℕ} (dd : Fin n → Fld Y) (Θ : Matrix (Fin n) (Fin n) Γ(X, V))
    (u : Fin n → Γ(X, V)) (d : Fld Y) {W : Y.Opens} (p p' : Γ(Y, W)) (k : ℕ) (O : Y.Opens) (h : O ≤ π ⁻¹ᵁ V)
    (f : Γ(Y, O)) : Γ(Y, O) :=
  2 * (k : Γ(Y, O)) * d O f - ∑ a, ∑ b, cst π V h (Θ a b) * dd a O (dd b O f) +
    2 * ∑ a, cst π V h (u a) * dd a O f + (2 * (k : Γ(Y, O)) ^ 2 * rsT p O + 2 * (k : Γ(Y, O)) * rsT p' O) * f

end GlobalTheory.HeatV
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
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocVal

theorem valR_eq {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)) : valR x U f = (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((x.appLE U ⊤ h).hom f) := dif_pos h

theorem valR_mul {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f g : Γ(X, U)) : valR x U (f * g) = valR x U f * valR x U g := by
  simp only [valR_eq x U h, map_mul]

theorem valR_add {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f g : Γ(X, U)) : valR x U (f + g) = valR x U f + valR x U g := by
  simp only [valR_eq x U h, map_add (f := _)]

theorem valR_pow {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)) (n : ℕ) : valR x U (f ^ n) = valR x U f ^ n := by
  simp only [valR_eq x U h, map_pow]

theorem valR_one {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    valR x U (1 : Γ(X, U)) = 1 := by
  simp only [valR_eq x U h, map_one]

theorem valR_res {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) {U V : X.Opens} (e : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) : valR x V (resG X e f) = valR x U f := by
  rw [valR_eq x V h, valR_eq x U (h.trans (x.preimage_mono e))]
  congr 1
  rw [resG, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem valR_field_of_le : ∀ (Z : Scheme.{0}) (U : Z.Opens), IsAffineOpen U → ∀ (F : Type) [Field F] (ξ : Sp F ⟶ Z),
    ⊤ ≤ ξ ⁻¹ᵁ U → ∀ (d : Fld Z), IsField U d → ∀ (D : F → F), (∀ x y, D (x + y) = D x + D y) →
    (∀ x y, D (x * y) = x * D y + y * D x) → (∀ f : Γ(Z, U), valR ξ U (d U f) = D (valR ξ U f)) →
    ∀ O : Z.Opens, O ≤ U → ⊤ ≤ ξ ⁻¹ᵁ O → ∀ h : Γ(Z, O), valR ξ O (d O h) = D (valR ξ O h) := by
  intro Z U hU F _ ξ _ d hd D _ hDm hDU O hOU hξO h
  obtain ⟨p₀⟩ : Nonempty (Sp F) := inferInstance
  have hp₀ : ξ.base p₀ ∈ O := hξO (Set.mem_univ p₀)
  obtain ⟨g, hgO, hg⟩ := hU.exists_basicOpen_le (V := O) ⟨_, hp₀⟩ (hOU hp₀)
  set B := Z.basicOpen g
  have hBU : B ≤ U := hgO.trans hOU
  have hξB : ⊤ ≤ ξ ⁻¹ᵁ B := by
    intro p _
    have : p = p₀ := Subsingleton.elim _ _
    subst this
    exact hg
  have := hU.isLocalization_basicOpen g
  obtain ⟨m, f, hf⟩ := IsLocalization.Away.surj g (resG Z hgO h)
  have hf' : resG Z hgO h * resG Z hBU g ^ m = resG Z hBU f := hf

  have hgu : IsUnit (resG Z hBU g) := Z.toRingedSpace.isUnit_res_basicOpen g
  have hg0 : valR ξ U g ≠ 0 := by
    obtain ⟨u, hu⟩ := hgu
    intro h0
    have e1 := congrArg (valR ξ B) u.mul_inv
    rw [valR_mul ξ B hξB, valR_one ξ B hξB, hu, valR_res ξ hBU hξB, h0, zero_mul] at e1
    exact zero_ne_one e1

  have hL := congrArg (d B) hf'
  rw [hd.2.1 B hBU, ← map_pow, hd.2.2 U B hBU le_rfl, hd.2.2 U B hBU le_rfl, hd.2.2 O B hgO hOU] at hL
  have hV := congrArg (valR ξ B) hL
  rw [valR_add ξ B hξB, valR_mul ξ B hξB, valR_mul ξ B hξB, valR_res ξ hgO hξB, valR_res ξ hBU hξB,
    valR_res ξ hBU hξB, valR_res ξ hBU hξB, hDU, hDU] at hV
  have hfv : valR ξ U f = valR ξ O h * valR ξ U g ^ m := by
    have := congrArg (valR ξ B) hf'
    rw [valR_mul ξ B hξB, valR_res ξ hgO hξB, valR_res ξ hBU hξB, valR_pow ξ B hξB, valR_res ξ hBU hξB] at this
    exact this.symm
  rw [hfv, hDm, valR_pow ξ U (hξB.trans (ξ.preimage_mono hBU))] at hV
  have key : valR ξ U g ^ m * (valR ξ B (resG Z hgO (d O h)) - D (valR ξ O h)) = 0 := by
    linear_combination hV
  rcases mul_eq_zero.1 key with h1 | h1
  · exact absurd (pow_eq_zero_iff'.1 h1).1 hg0
  · rw [← valR_res ξ hgO hξB]
    exact sub_eq_zero.1 h1

end GlobalTheory.LocVal
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SecRestr

theorem exists_restr : ∀ (X₂ Y : Scheme.{0}) (L₂ : LB X₂) (f₂ : Y ⟶ X₂) (k : ℕ) (σ : SecM (𝟙 X₂) L₂ k), ∃ s : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ))), GeneratorPullback.SecScal L₂ (fun _ : Fin 1 => f₂) (fun _ => (k : ℤ)) s (fun _ : Fin 1 => 𝟙 X₂) (fun _ => (k : ℤ)) σ f₂ 1 := by
  intro X₂ Y L₂ f₂ k σ
  refine ⟨ReciprocityTheory.ChartRestriction.G.DVR.TG.pullSec' L₂ _ _ σ f₂ (fun _ => f₂) (fun _ => (Category.comp_id _).symm), ?_⟩
  intro j₁ j₂ hc
  have hj : j₁ = j₂ := funext fun i => by
    rw [Subsingleton.elim i 0]
    exact hc (Sum.inl 0) (Sum.inr 0) (Category.comp_id _).symm
  subst hj
  rw [ReciprocityTheory.ChartRestriction.G.DVR.TG.pullSec'_f]
  have h1 : ReciprocityTheory.ChartRestriction.G.Out.resTop (LB.wchart L₂ (fun _ : Fin 1 => f₂) j₁ ⊓
      LB.wchart L₂ (fun _ : Fin 1 => f₂ ≫ 𝟙 X₂) j₁) (1 : Γ(Y, ⊤)) = 1 := map_one _
  rw [h1, _root_.one_mul, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

end GlobalTheory.SecRestr
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
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.thetaShiftFunctionalEq_sub_constFn_smul : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (k : ℕ) (mu α : Q.X) (σ σ' : Q.SecB k α) (σ₁ σ₁' : Q.SecB k (α + k • mu)) (c e e₁ : R), ShiftEq Q k mu α σ σ₁ 0 σ₁ → ShiftEq Q k mu α (σ' - constFn Q.P.A.hom ⊤ e • σ) (σ₁' - constFn Q.P.A.hom ⊤ e₁ • σ₁) c σ₁ → ShiftEq Q k mu α σ' σ₁' (c + e₁ - e) σ₁ := by
  first | exact @GlobalTheory.HeatMod.shiftEq_of_sub_constFn_smul | exact GlobalTheory.HeatMod.shiftEq_of_sub_constFn_smul | (intros; apply GlobalTheory.HeatMod.shiftEq_of_sub_constFn_smul <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.isRaynaudTorusWeightFunction_sub_const_mul : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (Ω : Type) [CommRing Ω] [StarRing Ω] [Module Ω Q.X] (oa : Q.OAct Ω) (Y : Ray oa), ∀ (α : Q.X) (W : Y.H.left.Opens) (f g : Γ(Y.H.left, W)) (r : R), IsWt Y α W f → IsWt Y α W g → IsWt Y α W (f - constFn Y.H.hom W r * g) := by
  first | exact @GlobalTheory.HeatMod.isWt_sub_const_mul | exact GlobalTheory.HeatMod.isWt_sub_const_mul | (intros; apply GlobalTheory.HeatMod.isWt_sub_const_mul <;> assumption)
end
