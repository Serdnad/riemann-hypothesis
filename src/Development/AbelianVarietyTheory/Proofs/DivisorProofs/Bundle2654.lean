module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CohomologyLogDerivativeAdjointEndomorphisms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle022
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle010
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2617
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2621
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem

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
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat.Glue

open GlobalTheory.KS

variable {X Y : Scheme.{0}}

theorem map_eq_rsT {O₀ O : Y.Opens} (h : O ≤ O₀) (s : Γ(Y, O₀)) :
    (Y.presheaf.map (homOfLE h).op).hom s = rsT s O := (rsT_of_le h s).symm

theorem rsT_pow' {O₀ O : Y.Opens} (h : O ≤ O₀) (s : Γ(Y, O₀)) (k : ℕ) : rsT (s ^ k) O = rsT s O ^ k := by
  rw [rsT_of_le h, rsT_of_le h, map_pow]

theorem le_wchart {m : Y ⟶ X} {L : LB X} (c : Fin 1 → L.ι) {O : Y.Opens} (h : O ≤ m ⁻¹ᵁ L.U (c 0)) :
    O ≤ LB.wchart L (fun _ : Fin 1 => m) c := fun y hy =>
  Set.mem_iInter.2 fun x => by rw [Subsingleton.elim x 0]; exact h hy

theorem pullbackBundleChart_le_preimage {m : Y ⟶ X} {L : LB X} (c : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => m) c ≤ m ⁻¹ᵁ L.U (c 0) := LB.wchart_le L _ c 0

theorem pbT_cocycle {L : LB X} (hL : L.IsLB) (m : Y ⟶ X) (a b c : L.ι) {O : Y.Opens}
    (h : O ≤ m ⁻¹ᵁ (L.U a ⊓ L.U b ⊓ L.U c)) :
    pbT m (L.g a b).val O * pbT m (L.g b c).val O = pbT m (L.g a c).val O := by
  have e := congrArg (fun u => pbT m u.val O) (hL.cocycle a b c)
  simp only [Units.val_mul, GlobalTheory.KS.AdjDlog.val_res, pbT_mul] at e
  rwa [pbT_rsT m inf_le_left h, pbT_rsT m (le_inf (inf_le_left.trans inf_le_right) inf_le_right) h,
    pbT_rsT m (le_inf (inf_le_left.trans inf_le_left) inf_le_right) h] at e

theorem linComb_g {L : LB X} (m : Y ⟶ X) (k : ℕ) (c c' : Fin 1 → L.ι) {O : Y.Opens}
    (h : O ≤ LB.wchart L (fun _ : Fin 1 => m) c ⊓ LB.wchart L (fun _ : Fin 1 => m) c') :
    rsT ((LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).g c c').val O =
      pbT m (L.g (c 0) (c' 0)).val O ^ k := by
  have hle : LB.wchart L (fun _ : Fin 1 => m) c ⊓ LB.wchart L (fun _ : Fin 1 => m) c' ≤ m ⁻¹ᵁ (L.U (c 0) ⊓ L.U (c' 0)) :=
    fun y hy => ⟨pullbackBundleChart_le_preimage c hy.1, pullbackBundleChart_le_preimage c' hy.2⟩
  simp only [LB.LinComb, Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val]
  rw [rsT_pow' h]
  exact congrArg (· ^ k) ((congrArg (fun s => rsT s O) (GlobalTheory.KS.AdjDlog.val_res_pullU m hle (L.g (c 0) (c' 0)))).trans
    (rsT_pbT m hle h _))

theorem sec_rel {L : LB X} (m : Y ⟶ X) (k : ℕ) (τ : SecM m L k) (c c' : Fin 1 → L.ι) {O : Y.Opens}
    (h : O ≤ LB.wchart L (fun _ : Fin 1 => m) c ⊓ LB.wchart L (fun _ : Fin 1 => m) c') :
    rsT (τ.f c) O = pbT m (L.g (c 0) (c' 0)).val O ^ k * rsT (τ.f c') O := by
  have e := congrArg (fun s => rsT s O) (τ.compat c c')
  simp only [map_eq_rsT] at e
  have h' : O ≤ (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c ⊓
      (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c' := h
  rwa [rsT_rsT inf_le_left h', rsT_mul, linComb_g m k c c' h, rsT_rsT inf_le_right h'] at e

theorem exists_acts : ∀ {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ} {X : Scheme.{0}}
    (m : G.left ⟶ X) (L : LB X), L.IsLB → ∀ (dd : Fin n → Fld G.left), (∀ a, IsField ⊤ (dd a)) →
    ∀ (D : R → R) (h : Heat G m L dd D) (k : ℕ) (τ : SecM m L k), ∃ τ' : SecM m L k, h.Acts k τ τ' := by
  intro R _ G _ _ n X m L hL dd hdd D h k τ

  have loc : ∀ i O (hO : O ≤ h.W i) (f : Γ(G.left, h.W i)),
      rsT (op G dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (h.W i) f) O =
        op G dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k O (rsT f O) := by
    intro i O hO f
    have hd : ∀ g, resG G.left hO (h.d i (h.W i) g) = h.d i O (resG G.left hO g) :=
      fun g => ((h.lift i).1.2.2 (h.W i) O hO le_rfl g).symm
    have hdd' : ∀ a g, resG G.left hO (dd a (h.W i) g) = dd a O (resG G.left hO g) :=
      fun a g => ((hdd a).2.2 (h.W i) O hO le_top g).symm
    have hc : ∀ r, resG G.left hO (constFn G.hom (h.W i) r) = constFn G.hom O r :=
      fun r => (rsT_of_le hO _).symm.trans (rsT_constFn G.hom hO r)
    have hp : ∀ q : Γ(G.left, h.W i), resG G.left hO (rsT q (h.W i)) = rsT q O := fun q => by
      rw [← rsT_of_le hO, rsT_rsT le_rfl hO]
    rw [rsT_of_le hO, rsT_of_le hO]

    simp only [op, map_add (f := _), map_sub, map_mul, map_sum, map_pow, map_natCast, map_ofNat, hd, hdd', hc, hp]
  obtain ⟨F, hF⟩ : ∃ F : ∀ i, Γ(G.left, h.W i), ∀ i,
      F i = op G dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (h.W i) (rsT (τ.f fun _ => h.j i) (h.W i)) :=
    ⟨_, fun _ => rfl⟩
  have hWc : ∀ i, h.W i ≤ LB.wchart L (fun _ : Fin 1 => m) (fun _ => h.j i) := fun i => le_wchart _ (h.le i)

  have Fc : ∀ i i', rsT (F i) (h.W i ⊓ h.W i') =
      pbT m (L.g (h.j i) (h.j i')).val (h.W i ⊓ h.W i') ^ k * rsT (F i') (h.W i ⊓ h.W i') := by
    intro i i'
    have hWc' : ∀ i, h.W i ≤ (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U (fun _ => h.j i) := hWc
    rw [hF, hF, loc i _ inf_le_left, loc i' _ inf_le_right, rsT_rsT (hWc' i) inf_le_left,
      rsT_rsT (hWc' i') inf_le_right,
      sec_rel m k τ (fun _ => h.j i) (fun _ => h.j i') (inf_le_inf (hWc i) (hWc i'))]
    exact h.glue k i i' _ le_rfl _
  have cov : ∀ V : G.left.Opens, V ≤ ⨆ i, V ⊓ h.W i := by
    intro V y hy
    have : y ∈ ⨆ i, h.W i := by rw [h.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hy, hi⟩

  have glue : ∀ c : Fin 1 → L.ι, ∃ t : Γ(G.left, LB.wchart L (fun _ : Fin 1 => m) c), ∀ i,
      rsT t (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i) =
        pbT m (L.g (c 0) (h.j i)).val (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i) ^ k *
          rsT (F i) (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i) := by
    intro c
    refine exists_rsT_eq (fun i => LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i) (fun i => inf_le_left) (cov _) _
      fun i i' => ?_
    have hN1 : (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i) ⊓ (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i') ≤
        LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i := inf_le_left
    have hN2 : (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i) ⊓ (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i') ≤
        LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i' := inf_le_right
    have hNW : (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i) ⊓ (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i') ≤
        h.W i ⊓ h.W i' := fun y hy => ⟨hy.1.2, hy.2.2⟩
    have hV : ∀ i, LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i ≤ m ⁻¹ᵁ (L.U (c 0) ⊓ L.U (h.j i)) :=
      fun i y hy => ⟨pullbackBundleChart_le_preimage c hy.1, h.le i hy.2⟩
    have h3 : (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i) ⊓ (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i') ≤
        m ⁻¹ᵁ (L.U (c 0) ⊓ L.U (h.j i) ⊓ L.U (h.j i')) :=
      fun y hy => ⟨⟨pullbackBundleChart_le_preimage c hy.1.1, h.le i hy.1.2⟩, h.le i' hy.2.2⟩
    rw [rsT_mul, rsT_mul, rsT_pow' hN1, rsT_pow' hN2, rsT_pbT m (hV i) hN1, rsT_pbT m (hV i') hN2,
      rsT_rsT inf_le_right hN1, rsT_rsT inf_le_right hN2, ← rsT_rsT inf_le_left hNW (F i), Fc, rsT_mul,
      rsT_pow' hNW, rsT_pbT m (show h.W i ⊓ h.W i' ≤ m ⁻¹ᵁ (L.U (h.j i) ⊓ L.U (h.j i')) from fun y hy => ⟨h.le i hy.1, h.le i' hy.2⟩) hNW, rsT_rsT inf_le_right hNW,
      ← _root_.mul_assoc, ← _root_.mul_pow, pbT_cocycle hL m _ _ _ h3]
  choose t ht using glue

  refine ⟨⟨t, fun c c' => ?_⟩, fun i => ?_⟩
  · have goal : rsT (t c) ((LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c ⊓
          (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c') =
        ((LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).g c c').val *
          rsT (t c') ((LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c ⊓
            (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c') := ?_
    · exact (rsT_of_le inf_le_left (t c)).symm.trans (goal.trans (congrArg _ (rsT_of_le inf_le_right (t c'))))
    refine eq_of_rsT_eq (fun i => LB.wchart L (fun _ : Fin 1 => m) c ⊓ LB.wchart L (fun _ : Fin 1 => m) c' ⊓ h.W i)
      (fun i => inf_le_left) (cov _) _ _ fun i => ?_
    have a1 : LB.wchart L (fun _ : Fin 1 => m) c ⊓ LB.wchart L (fun _ : Fin 1 => m) c' ⊓ h.W i ≤
        LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i := fun y hy => ⟨hy.1.1, hy.2⟩
    have a2 : LB.wchart L (fun _ : Fin 1 => m) c ⊓ LB.wchart L (fun _ : Fin 1 => m) c' ⊓ h.W i ≤
        LB.wchart L (fun _ : Fin 1 => m) c' ⊓ h.W i := fun y hy => ⟨hy.1.2, hy.2⟩
    have hV : ∀ c : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i ≤ m ⁻¹ᵁ (L.U (c 0) ⊓ L.U (h.j i)) :=
      fun c y hy => ⟨pullbackBundleChart_le_preimage c hy.1, h.le i hy.2⟩
    have h3 : LB.wchart L (fun _ : Fin 1 => m) c ⊓ LB.wchart L (fun _ : Fin 1 => m) c' ⊓ h.W i ≤
        m ⁻¹ᵁ (L.U (c 0) ⊓ L.U (c' 0) ⊓ L.U (h.j i)) :=
      fun y hy => ⟨⟨pullbackBundleChart_le_preimage c hy.1.1, pullbackBundleChart_le_preimage c' hy.1.2⟩, h.le i hy.2⟩
    have e' : LB.wchart L (fun _ : Fin 1 => m) c ⊓ LB.wchart L (fun _ : Fin 1 => m) c' ⊓ h.W i ≤
        (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c ⊓
          (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c' := inf_le_left
    have eL : (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c ⊓
        (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c' ≤ LB.wchart L (fun _ : Fin 1 => m) c := inf_le_left
    have eR : (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c ⊓
        (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c' ≤ LB.wchart L (fun _ : Fin 1 => m) c' := inf_le_right
    erw [rsT_rsT eL e', rsT_mul, rsT_rsT eR e', linComb_g m k c c' e',
      ← rsT_rsT inf_le_left a1 (t c), ← rsT_rsT inf_le_left a2 (t c'), ht, ht, rsT_mul, rsT_mul,
      rsT_pow' a1, rsT_pow' a2, rsT_pbT m (hV c) a1, rsT_pbT m (hV c') a2, rsT_rsT inf_le_right a1,
      rsT_rsT inf_le_right a2, ← _root_.mul_assoc, ← _root_.mul_pow, pbT_cocycle hL m _ _ _ h3]
  ·
    change rsT (t fun _ => h.j i) (h.W i) = _
    have a : h.W i ≤ LB.wchart L (fun _ : Fin 1 => m) (fun _ => h.j i) ⊓ h.W i := le_inf (hWc i) le_rfl
    rw [← rsT_rsT inf_le_left a, ht, rsT_mul, rsT_pow' a,
      rsT_pbT m (show LB.wchart L (fun _ : Fin 1 => m) (fun _ => h.j i) ⊓ h.W i ≤ m ⁻¹ᵁ (L.U (h.j i) ⊓ L.U (h.j i))
        from fun y hy => ⟨pullbackBundleChart_le_preimage _ hy.1, h.le i hy.2⟩) a, rsT_rsT inf_le_right a, rsT_self,
      GlobalTheory.KS.AdjDlog.pbT_g_self hL m (h.j i) (h.le i), one_pow, _root_.one_mul, hF]

end GlobalTheory.Heat.Glue
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

theorem class_limit_norm_le : ∀ (p : ℕ) [Fact p.Prime] (X Y : Type) [AddCommGroup X] [AddCommGroup Y] (e : X ≃+ Y) (β : LinearMap.BilinForm ℤ X) (be : LinearMap.BilinForm ℤ Y) (sc sc' : ℝ), 0 < sc → (∀ a b, sc * (β a b : ℝ) = sc' * (be (e a) (e b) : ℝ)) → ∀ (m : ℕ) (t : Y → PadicAlgCl p), (∀ μ, ‖t μ‖ ≤ Real.exp (-(sc' * (be μ μ : ℝ) / 2))) → ∀ (v : PadicAlgCl p) (ν : Y), (∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset Y, ∀ S : Finset Y, (∀ μ ∈ S, CongMod m μ ν) → (∀ μ ∈ S₀, CongMod m μ ν → μ ∈ S) → ‖v - ∑ μ ∈ S, t μ‖ ≤ δ) → ∀ μ : X, CongMod m (e μ) ν → (∀ μ' : X, CongMod m μ' μ → β μ μ ≤ β μ' μ') → ‖v‖ ≤ Real.exp (-(sc * (β μ μ : ℝ)) / 2) := by
  intro p _ X Y _ _ e β be sc sc' hsc hid m t ht v ν hv μ hμν hmin
  set R := Real.exp (-(sc * (β μ μ : ℝ)) / 2) with hR
  have hR0 : 0 ≤ R := (Real.exp_pos _).le
  have hterm : ∀ μ' : Y, CongMod m μ' ν → ‖t μ'‖ ≤ R := by
    intro μ' h'
    obtain ⟨w1, hw1⟩ := h'
    obtain ⟨w2, hw2⟩ := hμν
    have hc : CongMod m (e.symm μ') μ := by
      refine ⟨e.symm (w1 - w2), ?_⟩
      have : μ' = e μ + m • (w1 - w2) := by rw [hw1, hw2, smul_sub]; abel
      rw [this, map_add (f := _), map_nsmul, AddEquiv.symm_apply_apply]
    have hle := hmin _ hc
    have hle' : sc * (β μ μ : ℝ) ≤ sc' * (be μ' μ' : ℝ) := by
      have h2 := hid (e.symm μ') (e.symm μ')
      rw [AddEquiv.apply_symm_apply] at h2
      rw [← h2]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hle) hsc.le
    refine (ht μ').trans ?_
    rw [hR]
    apply Real.exp_le_exp.mpr
    linarith
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  obtain ⟨S₀, hS₀⟩ := hv δ hδ
  have h1 := hS₀ (S₀.filter (fun x => CongMod m x ν)) (fun x hx => (Finset.mem_filter.mp hx).2)
    (fun x hx hc => Finset.mem_filter.mpr ⟨hx, hc⟩)
  have h2 : ‖∑ x ∈ S₀.filter (fun x => CongMod m x ν), t x‖ ≤ R :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hR0 fun x hx => hterm x (Finset.mem_filter.mp hx).2
  calc ‖v‖ = ‖(v - ∑ x ∈ S₀.filter (fun x => CongMod m x ν), t x) + ∑ x ∈ S₀.filter (fun x => CongMod m x ν), t x‖ := by
          rw [sub_add_cancel]
    _ ≤ ‖v - ∑ x ∈ S₀.filter (fun x => CongMod m x ν), t x‖ + ‖∑ x ∈ S₀.filter (fun x => CongMod m x ν), t x‖ := norm_add_le _ _
    _ ≤ R + δ := by linarith

end GlobalTheory.UPoinc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc

theorem isE8_apply_zero_zero_pos {W : Matrix (Fin 8) (Fin 8) ℤ} (hW : IsE8 W) : 0 < W 0 0 := by
  have h := hW.1.diag_pos (i := 0)
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply] at h
  have : (0:ℝ) < (W 0 0 : ℝ) := by push_cast at h; linarith
  exact_mod_cast this

theorem qW_add_smul_single {r : ℕ} (W : Matrix (Fin 8) (Fin 8) ℤ) (b : LinearMap.BilinForm ℤ (Fin r → ℤ))
    (μ : Fin 8 → Fin r → ℤ) (x : Fin r → ℤ) (s : ℤ) :
    qW W b (μ + s • (Pi.single 0 x : Fin 8 → Fin r → ℤ)) = qW W b μ +
      s * (∑ u, ∑ v, W u v * (b ((Pi.single 0 x : Fin 8 → Fin r → ℤ) u) (μ v) + b (μ u) ((Pi.single 0 x : Fin 8 → Fin r → ℤ) v)))
      + s ^ 2 * (W 0 0 * b x x) := by
  set e : Fin 8 → Fin r → ℤ := Pi.single 0 x with he
  have h3 : ∑ u, ∑ v, W u v * b (e u) (e v) = W 0 0 * b x x := by
    rw [Fintype.sum_eq_single 0]
    · rw [Fintype.sum_eq_single 0]
      · simp [he]
      · intro v hv; simp [he, Pi.single_apply, hv]
    · intro u hu; simp [he, Pi.single_apply, hu]
  have hpt : ∀ u v, W u v * b ((μ + s • e) u) ((μ + s • e) v) = W u v * b (μ u) (μ v)
      + s * (W u v * (b (e u) (μ v) + b (μ u) (e v))) + s ^ 2 * (W u v * b (e u) (e v)) := by
    intro u v
    simp only [Pi.add_apply, Pi.smul_apply, map_add (f := _), map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    ring
  unfold qW
  simp_rw [hpt, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [h3]

theorem psd_of_min : ∀ {r N : ℕ}, 0 < N → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (b : LinearMap.BilinForm ℤ (Fin r → ℤ)) (μ : Fin 8 → Fin r → ℤ), (∀ α : Fin 8 → Fin r → ℤ, (∀ u i, ∃ m : ℤ, α u i = μ u i + N * m) → qW W b μ ≤ qW W b α) → ∀ x, 0 ≤ b x x := by
  intro r N hN W hW b μ hmin x
  by_contra hx
  push_neg at hx
  have hW0 := isE8_apply_zero_zero_pos hW
  set e : Fin 8 → Fin r → ℤ := Pi.single 0 x with he
  set B : ℤ := ∑ u, ∑ v, W u v * (b (e u) (μ v) + b (μ u) (e v)) with hB
  set s : ℤ := (N : ℤ) * (|B| + 1) with hs
  have hmin' := hmin (μ + s • e) (by
    intro u i
    refine ⟨(|B| + 1) * e u i, ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hs]
    ring)
  rw [qW_add_smul_single] at hmin'
  have hD : W 0 0 * b x x ≤ -1 := by nlinarith
  have hN1 : (1:ℤ) ≤ N := by exact_mod_cast hN
  have hBabs : -|B| ≤ B := neg_abs_le B
  have hBabs2 : B ≤ |B| := le_abs_self B
  have hA : 0 ≤ |B| := abs_nonneg B
  have hs1 : |B| + 1 ≤ s := by rw [hs]; nlinarith
  have h1 : s * B ≤ s * |B| := by nlinarith
  have h2 : s ^ 2 * (W 0 0 * b x x) ≤ - s ^ 2 := by nlinarith
  nlinarith

end GlobalTheory.Poinc
end

section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc.QWDom

open Matrix in
theorem exists_pos_posSemidef_sub_smul_one {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (hA : A.PosDef) :
    ∃ c : ℝ, 0 < c ∧ (A - c • (1 : Matrix n n ℝ)).PosSemidef := by
  obtain ⟨c, hc, hle⟩ : ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ hA.1.eigenvalues i := by
    rcases isEmpty_or_nonempty n with h | h
    · exact ⟨1, one_pos, fun i => (IsEmpty.false i).elim⟩
    · obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image Finset.univ hA.1.eigenvalues Finset.univ_nonempty
      exact ⟨_, hA.eigenvalues_pos i0, fun i => hi0 i (Finset.mem_univ _)⟩
  refine ⟨c, hc, ?_⟩
  have hs := hA.1.spectral_theorem
  have h1 : c • (1 : Matrix n n ℝ) = Unitary.conjStarAlgAut ℝ _ hA.1.eigenvectorUnitary (c • 1) := by
    rw [map_smul, map_one]
  rw [h1]
  conv => arg 1; arg 1; rw [hs]
  rw [← map_sub, Unitary.conjStarAlgAut_apply]
  rw [Unitary.isUnit_coe.posSemidef_star_right_conjugate_iff]
  rw [smul_one_eq_diagonal, diagonal_sub]
  exact PosSemidef.diagonal fun i => by simpa using hle i

open Matrix in
theorem gram_nonneg_int {s : ℕ} {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) (hβ : ∀ y, 0 ≤ β y y)
    (y : Fin s → X) (z : Fin s → ℤ) : 0 ≤ ∑ u, ∑ v, z u * β (y u) (y v) * z v := by
  have h := hβ (∑ u, z u • y u)

  simp only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply, smul_eq_mul] at h
  have e : ∑ u, ∑ v, z u * β (y u) (y v) * z v = ∑ x, z x * ∑ x1, z x1 * β (y x1) (y x) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    ring
  rw [e]; exact h

open Matrix in
theorem gram_nonneg_rat {s : ℕ} {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) (hβ : ∀ y, 0 ≤ β y y)
    (y : Fin s → X) (q : Fin s → ℚ) :
    0 ≤ ∑ u, ∑ v, (q u : ℝ) * (β (y u) (y v) : ℝ) * (q v : ℝ) := by
  set D : ℕ := ∏ u, (q u).den with hD
  have hDpos : (0 : ℝ) < D := by
    have : 0 < D := Finset.prod_pos fun u _ => (q u).den_pos
    exact_mod_cast this
  have hz : ∀ u, ∃ z : ℤ, (q u : ℝ) * D = z := by
    intro u
    obtain ⟨k, hk⟩ : (q u).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ u)
    refine ⟨(q u).num * k, ?_⟩
    rw [hk]
    have hq : (q u : ℝ) = (q u).num / (q u).den := by exact_mod_cast (Rat.num_div_den (q u)).symm
    have hd : ((q u).den : ℝ) ≠ 0 := by exact_mod_cast (q u).den_nz
    rw [hq]; push_cast; field_simp
  choose z hz using hz
  have h0 : (0 : ℝ) ≤ ∑ u, ∑ v, (z u : ℝ) * (β (y u) (y v) : ℝ) * (z v : ℝ) := by
    exact_mod_cast gram_nonneg_int β hβ y z
  have : ∑ u, ∑ v, (z u : ℝ) * (β (y u) (y v) : ℝ) * (z v : ℝ) =
      (D : ℝ) ^ 2 * ∑ u, ∑ v, (q u : ℝ) * (β (y u) (y v) : ℝ) * (q v : ℝ) := by
    simp only [← hz, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    ring
  rw [this] at h0
  exact (mul_nonneg_iff_of_pos_left (by positivity)).mp h0

open Matrix in
theorem gram_posSemidef {s : ℕ} {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X)
    (hsym : ∀ a b, β a b = β b a) (hβ : ∀ y, 0 ≤ β y y) (y : Fin s → X) :
    (Matrix.of fun u v => (β (y u) (y v) : ℝ)).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext u v
    simp [conjTranspose_apply, hsym (y u) (y v)]
  · have hcl : IsClosed {x : Fin s → ℝ | 0 ≤ ∑ u, ∑ v, x u * (β (y u) (y v) : ℝ) * x v} :=
      isClosed_le continuous_const (by fun_prop)
    have hx : 0 ≤ ∑ u, ∑ v, x u * (β (y u) (y v) : ℝ) * x v :=
      (DenseRange.piMap fun _ => Rat.denseRange_cast (𝕜 := ℝ)).induction_on x hcl
        fun q => gram_nonneg_rat β hβ y q
    simp only [star_trivial, dotProduct, mulVec, Matrix.of_apply, Finset.mul_sum]
    refine le_of_le_of_eq hx (Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_)
    ring

open Matrix in
theorem qW_ge : ∀ (s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ), PosW W → ∃ c : ℝ, 0 < c ∧ ∀ (X : Type) [AddCommGroup X] (β : LinearMap.BilinForm ℤ X), (∀ a b, β a b = β b a) → (∀ y, 0 ≤ β y y) → ∀ y : Fin s → X, c * (∑ u, β (y u) (y u) : ℤ) ≤ (qW W β y : ℤ) := by
  intro s W hW
  obtain ⟨c, hc, hP⟩ := exists_pos_posSemidef_sub_smul_one hW
  refine ⟨c / 2, by positivity, fun X _ β hsym hβ y => ?_⟩
  have hM := gram_posSemidef β hsym hβ y
  have ht := GlobalTheory.trace_mul_nonneg_of_posSemidef hP hM
  rw [Matrix.sub_mul, trace_sub, Matrix.smul_mul, Matrix.one_mul, trace_smul, sub_nonneg] at ht
  simp only [trace, diag, Matrix.mul_apply, Matrix.map_apply, Matrix.add_apply, transpose_apply, Matrix.of_apply,
    smul_eq_mul] at ht
  have e : ∑ u, ∑ v, ((W u v + W v u : ℤ) : ℝ) * (β (y v) (y u) : ℝ) = 2 * (qW W β y : ℝ) := by
    simp only [qW, Int.cast_sum, Int.cast_mul, Int.cast_add, add_mul, Finset.sum_add_distrib]
    rw [two_mul]
    congr 1
    · refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
      rw [hsym]
    · rw [Finset.sum_comm]
  push_cast at ht e ⊢
  linarith

end GlobalTheory.Poinc.QWDom
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompHS

set_option autoImplicit false

namespace GlobalTheory.ModifGeomConn

theorem geometricallyConnected_of_geometricallyIrreducible {X Y : Scheme.{0}} (f : X ⟶ Y)
    [GeometricallyIrreducible f] : GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  have : IrreducibleSpace ↥(Limits.pullback f x) :=
    GeometricallyIrreducible.geometrically_irreducibleSpace _ _ _ (.of_hasPullback _ _)
  infer_instance

theorem geometricallyConnected_modif : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (sX : X ⟶ Sp F) (n : ℕ) [SmoothOfRelativeDimension n sX] (U : X.Opens) (M : Modif sX U n) [IsIntegral M.X] [GeometricallyConnected sX], (U : Set X).Nonempty → GeometricallyConnected M.str := by
  intro F _ X _ sX n _ U M _ _ hU
  have : Smooth sX := SmoothOfRelativeDimension.smooth n sX
  have : GeometricallyIntegral sX := GlobalTheory.geometricallyIntegral_of_smooth sX
  obtain ⟨x, hx⟩ := hU
  have : Surjective (U.ι ≫ sX) := ⟨fun s => ⟨⟨x, hx⟩, Subsingleton.elim _ _⟩⟩
  have h2 : GeometricallyConnected (U.ι ≫ sX) := geometricallyConnected_of_geometricallyIrreducible _
  have := M.iso
  have h3 : GeometricallyConnected (M.opn.ι ≫ M.str) := by
    have e : M.opn.ι ≫ M.str = (M.σ ∣_ U) ≫ (U.ι ≫ sX) := by
      rw [Modif.str, ← Category.assoc, ← Category.assoc, morphismRestrict_ι]
    rw [e]
    rw [GeometricallyConnected.eq_geometrically] at h2 ⊢
    exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).2 h2
  exact GlobalTheory.CompactVar.geometricallyConnected_of_denseRange M.opn.ι M.str
    (by rw [Scheme.Opens.range_ι]; exact M.dense)

end GlobalTheory.ModifGeomConn
end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaOneMap_baseTuple_of_characterisation_extremal : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → IoExt R → ∀ (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m), OMPins T R κ v₀ O i → OneMapRow0 T R κ v₀ O i := by
  first | exact @GlobalTheory.OneMapTies.oneMapRow0_of_ties_core | exact GlobalTheory.OneMapTies.oneMapRow0_of_ties_core | (intros; apply GlobalTheory.OneMapTies.oneMapRow0_of_ties_core <;> assumption)
end
