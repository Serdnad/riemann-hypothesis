module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1207
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1208
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1209
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef.SecRat

theorem isIntegral_of_isGenOver (k K : Type) [Field k] [Field K] [Algebra k K] (C : Scheme.{0})
    [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C) (hx : IsGenOver k x) : IsIntegral C := by
  have : SmoothOfRelativeDimension 1 (strHom k (X := C)) := hx.1.1
  have : Smooth (strHom k (X := C)) := SmoothOfRelativeDimension.smooth 1 _
  have hred : IsReduced C := isReduced_of_smooth_of_isReduced (strHom k C)
  have hd : IsDominant x := hx.2.1.1
  have hden : DenseRange x.base := hd.denseRange
  have hcl : closure {x.base default} = (Set.univ : Set C) := by
    have hr : Set.range x.base = {x.base default} := by
      ext y; constructor
      · rintro ⟨p, rfl⟩; rw [Subsingleton.elim p default]; rfl
      · rintro rfl; exact ⟨_, rfl⟩
    rw [← hr]; exact hden.closure_range
  have hirr : IsIrreducible (Set.univ : Set C) := hcl ▸ isIrreducible_singleton.closure
  have : IrreducibleSpace C := { isPreirreducible_univ := hirr.2, toNonempty := ⟨x.base default⟩ }
  exact (isIntegral_iff_irreducibleSpace_and_isReduced C).2 ⟨this, hred⟩

theorem not_isUnit_evAt {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (b : Sp R ⟶ X)
    {U : X.Opens} (h : ⊤ ≤ b ⁻¹ᵁ U) (f : Γ(X, U)) (hf : b (IsLocalRing.closedPoint R) ∉ X.basicOpen f) :
    ¬ IsUnit (evAt b h f) := by
  intro hu
  apply hf
  have h1 : (b.appLE U ⊤ h).hom f = (Scheme.ΓSpecIso (.of R)).inv.hom (evAt b h f) := by
    simp [evAt]
  have h2 : (Sp R).basicOpen ((b.appLE U ⊤ h).hom f) = ⊤ ⊓ (Sp R).basicOpen ((b.app U).hom f) := by
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply, Scheme.basicOpen_res]
  have h3 : IsLocalRing.closedPoint R ∈ (Sp R).basicOpen ((b.appLE U ⊤ h).hom f) := by
    rw [h1, basicOpen_eq_of_affine]
    exact (PrimeSpectrum.mem_basicOpen _ _).2 fun hm => (IsLocalRing.mem_maximalIdeal _).1 hm hu
  rw [h2, ← Scheme.preimage_basicOpen] at h3
  exact h3.2

theorem evAt_coord {R : Type} [CommRing R] {C : Scheme.{0}} (x : Sp R ⟶ C) {W : C.Modules} {r m : ℕ}
    (σ : (lbPow (det W r) m).Sec) (c₀ c : Chart W r) (V' : C.Opens) (h₀ : V' ≤ c₀.U) (h₁ : V' ≤ c.U)
    (hx' : ⊤ ≤ x ⁻¹ᵁ V') (M : Matrix (Fin r) (Fin r) Γ(C, V'))
    (hM : ∀ j, resM W h₀ (c₀.e j) = ∑ i, M i j • resM W h₁ (c.e i))
    (h0 : ⊤ ≤ x ⁻¹ᵁ (lbPow (det W r) m).U (fun _ => c₀)) (h1 : ⊤ ≤ x ⁻¹ᵁ (lbPow (det W r) m).U (fun _ => c)) :
    evAt x h1 (σ.f (fun _ => c)) = (M.map (evAt x hx')).det ^ m * evAt x h0 (σ.f (fun _ => c₀)) := by
  have hV : V' ≤ (lbPow (det W r) m).U (fun _ => c) ⊓ (lbPow (det W r) m).U (fun _ => c₀) :=
    fun y hy => ⟨Set.mem_iInter.2 fun _ => h₁ hy, Set.mem_iInter.2 fun _ => h₀ hy⟩
  have hxV : ⊤ ≤ x ⁻¹ᵁ ((lbPow (det W r) m).U (fun _ => c) ⊓ (lbPow (det W r) m).U (fun _ => c₀)) :=
    hx'.trans (x.preimage_mono hV)
  have hcc : ⊤ ≤ x ⁻¹ᵁ (c.U ⊓ c₀.U) := hx'.trans (x.preimage_mono (le_inf h₁ h₀))
  have e := congrArg (evAt x hxV) (σ.compat (fun _ => c) (fun _ => c₀))
  rw [(GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk).2.2.1 R C x _ _ _ h1 hxV, map_mul, (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk).2.2.1 R C x _ _ _ h0 hxV] at e
  rw [e]
  congr 1
  have hd : evAt x hcc (c.isFrame.detUnit c₀.isFrame (inf_le_left : c.U ⊓ c₀.U ≤ c.U) inf_le_right).val =
      (M.map (evAt x hx')).det := by
    rw [← (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk).2.2.1 R C x _ _ (le_inf h₁ h₀) hcc hx']
    have hr := IsFrame.res_detUnit c.isFrame c₀.isFrame (inf_le_left : c.U ⊓ c₀.U ≤ c.U) inf_le_right (le_inf h₁ h₀)
    refine (congrArg (evAt x hx') (congrArg Units.val hr)).trans ?_
    rw [IsFrame.val_detUnit, Module.Basis.det_apply, RingHom.map_det]
    congr 1
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply, Module.Basis.toMatrix_apply, hM]
    simp only [← IsFrame.basis_apply c.isFrame h₁]
    rw [Module.Basis.repr_sum_self]
  rw [← hd, ← map_pow, ← (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk).2.2.1 R C x _ _ (fun y hy => ⟨Set.mem_iInter.1 hy.1 PUnit.unit, Set.mem_iInter.1 hy.2 PUnit.unit⟩ : (lbPow (det W r) m).U (fun _ => c) ⊓ (lbPow (det W r) m).U (fun _ => c₀) ≤ c.U ⊓ c₀.U) hcc hxV]
  congr 1
  dsimp only [lbPow, LB.LinComb]
  rw [Fintype.prod_unique, zpow_natCast, Units.val_pow_eq_pow_val]
  erw [map_pow]
  congr 1

theorem val_lt_one {k K : Type} [Field k] [Field K] [Algebra k K] (v : Place k K) (a : v.O) (ha : ¬ IsUnit a) :
    v.1 (a : K) < 1 := by
  have h1 : v.1 (a : K) ≤ 1 := (Valuation.mem_valuationSubring_iff _ _).1 a.2
  refine lt_of_le_of_ne h1 fun h => ha ?_
  have h0 : (a : K) ≠ 0 := fun h0 => by rw [h0, map_zero] at h; exact zero_ne_one h
  have hi : (a : K)⁻¹ ∈ v.O := (Valuation.mem_valuationSubring_iff _ _).2 (by rw [map_inv₀, h, inv_one])
  exact isUnit_iff_exists_inv.2 ⟨⟨_, hi⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩

theorem sec_eq_zero {X : Scheme.{0}} {L : LB X} (σ : L.Sec) (h : ∀ j, σ.f j = 0) : σ = 0 := by
  obtain ⟨f, hc⟩ := σ
  have : f = fun _ => 0 := funext h
  subst this
  rfl

end GlobalTheory.Nef.SecRat


open GlobalTheory.Nef.SecRat in
theorem GlobalTheory.Nef.sec_detPow_rational : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (W : C.Modules) (r : ℕ), IsVB W r → ∀ (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)), (V₀ : Set C).Nonempty → IsFrame s → ∀ (m : ℕ) (σ : (lbPow (det W r) m).Sec), σ ≠ 0 → ∃ f : K, f ≠ 0 ∧ ∀ (v : Place k K) (g : Matrix (Fin r) (Fin r) K), LocFrame x s v g → v.1 (f * g.det ^ m) ≤ 1 ∧ ∀ b : Sp v.O ⟶ C, spMap v.O.subtype ≫ b = x → b (IsLocalRing.closedPoint v.O) ∉ Out.nonzeroLocus σ → v.1 (f * g.det ^ m) < 1 := by
  intro k K _ _ _ _ _ C _ x hx W r hW V₀ s hV₀ hs m σ hσ
  haveI := isIntegral_of_isGenOver k K C x hx
  let c₀ : Chart W r := ⟨V₀, s, hs⟩
  have hUeq : ∀ c : Chart W r, (((lbPow (det W r) m).U (fun _ => c) : C.Opens) : Set C) = c.U := fun c =>
    Set.ext fun y => ⟨fun hy => Set.mem_iInter.1 hy PUnit.unit, fun hy => Set.mem_iInter.2 fun _ => hy⟩
  have hle : ∀ c : Chart W r, c.U ≤ (lbPow (det W r) m).U (fun _ => c) := fun c y hy =>
    Set.mem_iInter.2 fun _ => hy
  obtain ⟨hx0, hinj0, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_generic_injective_fraction K C x hx.2.1 ((lbPow (det W r) m).U fun _ => c₀)
    (by rw [hUeq]; exact hV₀)
  refine ⟨evAt x hx0 (σ.f fun _ => c₀), ?_, ?_⟩
  · intro hf
    apply hσ
    have h0 : σ.f (fun _ => c₀) = 0 := hinj0 (by rw [hf, map_zero])
    refine sec_eq_zero σ fun j => ?_
    have hj : j = fun _ => j PUnit.unit := funext fun _ => rfl
    rw [hj]
    generalize j PUnit.unit = c
    by_cases hne : (((lbPow (det W r) m).U fun _ => c : C.Opens) : Set C).Nonempty
    · have hne2 : ((((lbPow (det W r) m).U fun _ => c) ⊓ (lbPow (det W r) m).U (fun _ => c₀) :
          C.Opens) : Set C).Nonempty :=
        nonempty_preirreducible_inter (Opens.isOpen _) (Opens.isOpen _) hne (by rw [hUeq]; exact hV₀)
      obtain ⟨hxj, hinjj, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_generic_injective_fraction K C x hx.2.1 _ hne
      obtain ⟨hx2, -, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_generic_injective_fraction K C x hx.2.1 _ hne2
      apply hinjj
      have e := congrArg (evAt x hx2) (σ.compat (fun _ => c) (fun _ => c₀))
      rw [(GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk).2.2.1 K C x _ _ _ hxj hx2, map_mul, (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk).2.2.1 K C x _ _ _ hx0 hx2, h0,
        map_zero, mul_zero] at e
      rw [e, map_zero]
    · exact eq_zero_of_basicOpen_eq_bot _ (eq_bot_iff.2 fun y hy => hne ⟨y, C.basicOpen_le _ hy⟩)
  · rintro v g ⟨b, V, t, V', h₀, h₁, hx', M, hb, hbV, ht, hM, rfl⟩
    let c : Chart W r := ⟨V, t, ht⟩
    have hbj : ⊤ ≤ b ⁻¹ᵁ (lbPow (det W r) m).U (fun _ => c) := hbV.trans (b.preimage_mono (hle c))
    have hxj : ⊤ ≤ x ⁻¹ᵁ (lbPow (det W r) m).U (fun _ => c) := hx'.trans (x.preimage_mono (h₁.trans (hle c)))
    have key := evAt_coord x σ c₀ c V' h₀ h₁ hx' M hM hx0 hxj
    have hval : v.1 (evAt x hx0 (σ.f fun _ => c₀) * (M.map (evAt x hx')).det ^ m) =
        v.1 ((evAt b hbj (σ.f fun _ => c) : v.O) : K) := by
      rw [mul_comm, ← key]
      congr 1
      subst hb
      exact (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk).1 v.O K C v.O.subtype b _ hbj hxj _
    refine ⟨?_, ?_⟩
    · rw [hval]
      exact (Valuation.mem_valuationSubring_iff _ _).1 (evAt b hbj _).2
    · intro b' hb' hout
      have e : spMap (algebraMap K K) ≫ x = x := by
        rw [Algebra.algebraMap_self, spMap, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
      obtain ⟨b₀, -, huniq⟩ := GlobalTheory.T.existsUnique_centre_functionFieldPlace_curve k K K C x hx v
      have hbb : b' = b := (huniq b' (hb'.trans e.symm)).trans (huniq b (hb.trans e.symm)).symm
      subst hbb
      have hnu := not_isUnit_evAt b' hbj (σ.f fun _ => c) (fun hm => hout (Opens.mem_iSup.2 ⟨_, hm⟩))
      rw [hval]
      exact val_lt_one v _ hnu
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

namespace GlobalTheory.Nef

theorem tan_triv_eq_zero : ∀ (k K E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] [Field E] [Algebra k E] [Algebra K E] [IsScalarTower k K E] [FiniteDimensional K E] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (G : Over C) [GrpObj G], IsSemiAbelian G → ∀ (W : C.Modules) (r : ℕ) (i : W ⟶ Lie G), Mono i → ∀ (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)), (V₀ : Set C).Nonempty → IsFrame s → ∀ w : Fin r → E, HasTan G (spMap (algebraMap K E) ≫ x) (triv G (spMap (algebraMap K E) ≫ x)) (fun j => i.app V₀ (s j)) w → w = 0 := by
  intro k K E _ _ _ _ _ _ _ _ _ _ C _ x hx G _ hG W r i hi V₀ s hV₀ hs w hw
  haveI := hG
  haveI := hi
  haveI : IsIntegral C := LieSemineg.isIntegral_curve hx.1.1 hx.1.2.2
  haveI : Smooth G.hom := hG.smooth
  obtain ⟨h₀, -, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_generic_injective_fraction K C x hx.2.1 V₀ hV₀
  have hp₀ : x (IsLocalRing.closedPoint K) ∈ V₀ := (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk.2.2.2.1 K C x V₀).1 h₀
  obtain ⟨U₁, n, om, hpU₁, hom⟩ := exists_isFrame_omega G (x (IsLocalRing.closedPoint K))
  obtain ⟨V', U, hpV', hV'le, c⟩ := GlobalTheory.Conormal.exists_isChart (he := sec_hom η[G])
    (show x (IsLocalRing.closedPoint K) ∈ V₀ ⊓ U₁ from ⟨hp₀, hpU₁⟩)
  have hV : V' ≤ V₀ := hV'le.trans inf_le_left
  have hVU : V' ≤ U₁ := hV'le.trans inf_le_right
  obtain ⟨hx', hinj, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_generic_injective_fraction K C x hx.2.1 V' ⟨_, hpV'⟩
  have hb : ⊤ ≤ (spMap (algebraMap K E) ≫ x) ⁻¹ᵁ V' := fun z _ => hx' (Set.mem_univ _)
  have hev : ∀ g : Γ(C, V'), evAt (spMap (algebraMap K E) ≫ x) hb g = algebraMap K E (evAt x hx' g) :=
    fun g => GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk.1 K E C (algebraMap K E) x V' hx' hb g
  have key : ∀ f : Γ(G.left, U), ∑ j, w j * algebraMap K E (evAt x hx'
      (dualApp (i.app V₀ (s j)) hV (dUnit G c.le f))) = 0 := by
    intro f
    have h2 : ⊤ ≤ ((spMap (algebraMap K E) ≫ x) ≫ unitSec G) ⁻¹ᵁ U := fun z _ => c.le (hb (Set.mem_univ z))
    have hU : ⊤ ≤ (triv G (spMap (algebraMap K E) ≫ x)) ⁻¹ᵁ U := fun z _ => h2 (Set.mem_univ _)
    have := hw U hU V' hV c.le hb f
    simp only [hev] at this
    rw [← this]
    have e1 : evAt (triv G (spMap (algebraMap K E) ≫ x)) hU f = PowerSeries.C (R := E) (evAt _ h2 f) :=
      GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk.1 E (PowerSeries E) G.left (PowerSeries.C (R := E)) _ U h2 hU f
    rw [e1]
    simp
  have key2 : ∀ e' : Γ(omega G, V'), ∑ j, w j * algebraMap K E (evAt x hx'
      (dualApp (i.app V₀ (s j)) hV e')) = 0 := by
    intro e'
    obtain ⟨f, rfl⟩ := c.d_surjective (sec_hom η[G]) e'
    exact key f
  haveI : Nonempty V' := ⟨⟨_, hpV'⟩⟩
  let N : Matrix (Fin r) (Fin n) Γ(C, V') := fun j a => dualApp (i.app V₀ (s j)) hV (resM (omega G) hVU (om a))
  have hN : LinearIndependent Γ(C, V') N.row := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hl : (∑ j, g j • resM (Lie G) hV (i.app V₀ (s j))) = 0 := by
      refine hom.dual_ext hVU (fun a => ?_)
      have := congrFun hg a
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Matrix.row, N] at this
      rw [dualApp_sum, LinearMap.sum_apply, dualApp_zero, LinearMap.zero_apply]
      simpa only [dualApp_smul, LinearMap.smul_apply, smul_eq_mul, dualApp_res, GlobalTheory.LB.resG_self] using this
    have hs' : ∑ j, g j • resM W hV (s j) = 0 := by
      apply QCoh.injective_app_of_mono i V'

      simp only [map_sum, map_zero, Scheme.Modules.Hom.app_smul, Twist.app_resM]
      exact hl
    have hli := (hs.basis hV).linearIndependent
    rw [hs.coe_basis hV, Fintype.linearIndependent_iff] at hli
    exact hli g hs'
  obtain ⟨σ, hσ⟩ := LieSemineg.exists_det_ne_zero N hN
  let φ : Γ(C, V') →+* E := (algebraMap K E).comp (evAt x hx')
  have hφ : Function.Injective φ := (algebraMap K E).injective.comp hinj
  have hA : ((N.submatrix id σ).map φ).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact fun h => hσ (hφ (h.trans (map_zero φ).symm))
  refine Matrix.eq_zero_of_vecMul_eq_zero hA ?_
  funext a
  simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Matrix.submatrix_apply, id, Pi.zero_apply, N, φ,
    RingHom.comp_apply]
  exact key2 _

end GlobalTheory.Nef
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

section TanDer

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] {R : Type} [CommRing R] (s : S)
  (β : S.presheaf.stalk s →+* R) {n : ℕ} {V : S.Opens} (τ : Fin n → Γ(Lie G, V)) (w : Fin n → R)

def tanVal {U : G.left.Opens} {V' : S.Opens} (hV : V' ≤ V) (he : V' ≤ unitSec G ⁻¹ᵁ U) (hs' : s ∈ V')
    (f : Γ(G.left, U)) : R :=
  ∑ i, w i * β (S.presheaf.germ V' s hs' (dualApp (τ i) hV (dUnit G he f)))

theorem tanVal_mono {U : G.left.Opens} {V' V'' : S.Opens} (hV : V' ≤ V) (he : V' ≤ unitSec G ⁻¹ᵁ U)
    (hs' : s ∈ V') (k : V'' ≤ V') (hs'' : s ∈ V'') (f : Γ(G.left, U)) :
    tanVal G s β τ w (k.trans hV) (k.trans he) hs'' f = tanVal G s β τ w hV he hs' f := by
  unfold tanVal
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← resM_dUnit G he k f, dualApp_resM]
  congr 2
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

theorem tanVal_indep {U : G.left.Opens} {V₁ V₂ : S.Opens} (hV₁ : V₁ ≤ V) (he₁ : V₁ ≤ unitSec G ⁻¹ᵁ U)
    (hs₁ : s ∈ V₁) (hV₂ : V₂ ≤ V) (he₂ : V₂ ≤ unitSec G ⁻¹ᵁ U) (hs₂ : s ∈ V₂) (f : Γ(G.left, U)) :
    tanVal G s β τ w hV₁ he₁ hs₁ f = tanVal G s β τ w hV₂ he₂ hs₂ f :=
  (tanVal_mono G s β τ w hV₁ he₁ hs₁ (inf_le_left : V₁ ⊓ V₂ ≤ V₁) ⟨hs₁, hs₂⟩ f).symm.trans
    (tanVal_mono G s β τ w hV₂ he₂ hs₂ (inf_le_right : V₁ ⊓ V₂ ≤ V₂) ⟨hs₁, hs₂⟩ f)

theorem tanVal_resG {U U' : G.left.Opens} (k : U' ≤ U) {V' : S.Opens} (hV : V' ≤ V)
    (he : V' ≤ unitSec G ⁻¹ᵁ U') (hs' : s ∈ V') (f : Γ(G.left, U)) :
    tanVal G s β τ w hV he hs' (resG _ k f) =
      tanVal G s β τ w hV (he.trans ((unitSec G).preimage_mono k)) hs' f := by
  unfold tanVal
  simp only [dUnit_resG]

variable {s}

theorem mem_inf_unitSec (hs : s ∈ V) {U : G.left.Opens} (hU : unitSec G s ∈ U) : s ∈ V ⊓ unitSec G ⁻¹ᵁ U :=
  Opens.mem_inf.2 ⟨hs, hU⟩

def tanCan (hs : s ∈ V) {U : G.left.Opens} (hU : unitSec G s ∈ U) (f : Γ(G.left, U)) : R :=
  tanVal G s β τ w (V' := V ⊓ unitSec G ⁻¹ᵁ U) inf_le_left inf_le_right (mem_inf_unitSec G hs hU) f

theorem tanCan_eq (hs : s ∈ V) {U : G.left.Opens} (hU : unitSec G s ∈ U) {V' : S.Opens} (hV : V' ≤ V)
    (he : V' ≤ unitSec G ⁻¹ᵁ U) (hs' : s ∈ V') (f : Γ(G.left, U)) :
    tanCan G β τ w hs hU f = tanVal G s β τ w hV he hs' f :=
  tanVal_indep G s β τ w _ _ _ _ _ _ f

theorem tanCan_res (hs : s ∈ V) {U U' : G.left.Opens} (k : U' ≤ U) (hU' : unitSec G s ∈ U') (f : Γ(G.left, U)) :
    tanCan G β τ w hs hU' (resG _ k f) = tanCan G β τ w hs (k hU') f := by
  rw [tanCan, tanVal_resG]
  exact (tanCan_eq G β τ w hs (k hU') _ _ _ f).symm

theorem tanCan_germ_eq (hs : s ∈ V) {U U' : G.left.Opens} (hU : unitSec G s ∈ U) (hU' : unitSec G s ∈ U')
    (f : Γ(G.left, U)) (f' : Γ(G.left, U'))
    (h : G.left.presheaf.germ U _ hU f = G.left.presheaf.germ U' _ hU' f') :
    tanCan G β τ w hs hU f = tanCan G β τ w hs hU' f' := by
  obtain ⟨W, hW, iU, iU', e⟩ := TopCat.Presheaf.germ_eq _ _ hU hU' f f' h
  have h1 := tanCan_res G β τ w hs iU.le hW f
  have h2 := tanCan_res G β τ w hs iU'.le hW f'
  have e' : resG _ iU.le f = resG _ iU'.le f' := e
  rw [← h1, ← h2, e']

theorem tanCan_add (hs : s ∈ V) {U : G.left.Opens} (hU : unitSec G s ∈ U) (a b : Γ(G.left, U)) :
    tanCan G β τ w hs hU (a + b) = tanCan G β τ w hs hU a + tanCan G β τ w hs hU b := by
  unfold tanCan tanVal
  simp only [map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem tanCan_mul (hs : s ∈ V) {U : G.left.Opens} (hU : unitSec G s ∈ U) (a b : Γ(G.left, U))
    (ε : G.left.presheaf.stalk (unitSec G s) →+* S.presheaf.stalk s)
    (hε : ∀ f : Γ(G.left, U), ε (G.left.presheaf.germ U _ hU f) =
      S.presheaf.germ (V ⊓ unitSec G ⁻¹ᵁ U) s (mem_inf_unitSec G hs hU) ((unitSec G).appLE U _ inf_le_right f)) :
    tanCan G β τ w hs hU (a * b) = β (ε (G.left.presheaf.germ U _ hU a)) * tanCan G β τ w hs hU b +
      β (ε (G.left.presheaf.germ U _ hU b)) * tanCan G β τ w hs hU a := by
  rw [hε, hε]
  unfold tanCan tanVal
  simp only [dUnit_mul, map_add (f := _), map_smul, smul_eq_mul, map_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => by ring

def tanStalk (hs : s ∈ V) (x : G.left.presheaf.stalk (unitSec G s)) : R :=
  tanCan G β τ w hs (TopCat.Presheaf.germ_exist _ x).choose_spec.choose
    (TopCat.Presheaf.germ_exist _ x).choose_spec.choose_spec.choose

theorem tanStalk_germ (hs : s ∈ V) {U : G.left.Opens} (hU : unitSec G s ∈ U) (f : Γ(G.left, U)) :
    tanStalk G β τ w hs (G.left.presheaf.germ U _ hU f) = tanCan G β τ w hs hU f := by
  unfold tanStalk
  apply tanCan_germ_eq
  exact (TopCat.Presheaf.germ_exist _ _).choose_spec.choose_spec.choose_spec

end TanDer

theorem germ_exist_two {X : Scheme.{0}} (p : X) (x y : X.presheaf.stalk p) :
    ∃ (U : X.Opens) (hU : p ∈ U) (a b : Γ(X, U)), X.presheaf.germ U p hU a = x ∧ X.presheaf.germ U p hU b = y := by
  obtain ⟨U₁, h₁, a, rfl⟩ := TopCat.Presheaf.germ_exist _ x
  obtain ⟨U₂, h₂, b, rfl⟩ := TopCat.Presheaf.germ_exist _ y
  exact ⟨U₁ ⊓ U₂, Opens.mem_inf.2 ⟨h₁, h₂⟩, resG _ inf_le_left a, resG _ inf_le_right b,
    TopCat.Presheaf.germ_res_apply _ _ _ _ _, TopCat.Presheaf.germ_res_apply _ _ _ _ _⟩

theorem exists_stalkDer_of_lie : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R], ∀ (s : S) (π : S.presheaf.stalk s →+* G.left.presheaf.stalk (unitSec G s)) (ε : G.left.presheaf.stalk (unitSec G s) →+* S.presheaf.stalk s) (m : G.left.presheaf.stalk (unitSec G s) →+* G.left.presheaf.stalk (unitSec G s)) (β : S.presheaf.stalk s →+* R) (n : ℕ) (V : S.Opens) (hs : s ∈ V) (τ : Fin n → Γ(Lie G, V)) (w : Fin n → R), StalkData G s π ε m → ∃ δ : G.left.presheaf.stalk (unitSec G s) →+ R, (∀ f g, δ (f * g) = β (ε f) * δ g + β (ε g) * δ f) ∧ (∀ a, δ (π a) = 0) ∧ ∀ (U : G.left.Opens) (hU : unitSec G s ∈ U) (V' : S.Opens) (hV : V' ≤ V) (he : V' ≤ unitSec G ⁻¹ᵁ U) (hs' : s ∈ V') (f : Γ(G.left, U)), δ (G.left.presheaf.germ U _ hU f) = ∑ i, w i * β (S.presheaf.germ V' s hs' (dualApp (τ i) hV (dUnit G he f))) := by
  intro S G _ R _ s π ε m β n V hs τ w hD
  have hI := GlobalTheory.T.groupSchemeUnitStalkData_germ S G s π ε m hD
  refine ⟨AddMonoidHom.mk' (tanStalk G β τ w hs) ?_, ?_, ?_, ?_⟩
  · intro x y
    obtain ⟨U, hU, a, b, rfl, rfl⟩ := germ_exist_two (unitSec G s) x y
    rw [← map_add (f := _), tanStalk_germ, tanStalk_germ, tanStalk_germ, tanCan_add]
  · intro x y
    obtain ⟨U, hU, a, b, rfl, rfl⟩ := germ_exist_two (unitSec G s) x y
    simp only [AddMonoidHom.mk'_apply]
    rw [← map_mul, tanStalk_germ, tanStalk_germ, tanStalk_germ,
      tanCan_mul G β τ w hs hU a b ε (fun f => hI.2.1 U hU _ _ inf_le_right f)]
  · intro a
    obtain ⟨V₀, h₀, a₀, rfl⟩ := TopCat.Presheaf.germ_exist _ a
    have hU : unitSec G s ∈ G.hom ⁻¹ᵁ V₀ := by
      show (unitSec G ≫ G.hom) s ∈ V₀
      rw [sec_hom]
      exact h₀
    rw [hI.1 V₀ h₀ _ hU le_rfl a₀]
    simp only [AddMonoidHom.mk'_apply, tanStalk_germ, tanCan, tanVal, dUnit_base, map_zero, mul_zero,
      Finset.sum_const_zero]
  · intro U hU V' hV he hs' f
    simp only [AddMonoidHom.mk'_apply]
    rw [tanStalk_germ]
    exact tanCan_eq G β τ w hs hU hV he hs' f

end GlobalTheory.Nef
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem isSec_pull {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] (n : ℕ) (b : Fn0 A)
    {D : Type} [CommRing D] [Algebra R D] {D' : Type} [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D')
    (x : Pt A D) (s : RootFn A D) (hs : IsSec n b x s) :
    IsSec n b (D := D') (spOver φ ≫ x) (fun E _ _ ψ z ↦ s E (ψ.comp φ) z) := by
  refine ⟨?_, ?_⟩
  · intro E _ _ E' _ _ α β z hz
    have hz' : z ^ n = spOver (α.comp φ) ≫ x := by rw [hz, ← spOver_comp, Category.assoc]
    exact hs.1 E E' (α.comp φ) β z hz'
  · intro E _ _ α z w hz hw
    have hz' : z ^ n = spOver (α.comp φ) ≫ x := by rw [hz, ← spOver_comp, Category.assoc]
    exact hs.2 E (α.comp φ) z w hz' hw

theorem exists_isSecDiff : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ),
    HasRoots A n → ∀ b : Fn0 A, IsTorsChar n b → ∀ S : SecFam A,
    (∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), IsSec n b x (S D x)) → ∃ u : Fn1 A, IsSecDiff n S u := by
  intro R _ A _ _ n hR b _ S hS
  have key : ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
      (φ : D →ₐ[R] D') (x : Pt A D),
      let x' : Pt A D' := spOver φ ≫ x
      ∃ e : D', ∀ (E : Type) [CommRing E] [Algebra R E] (ψ : D' →ₐ[R] E)
        (z : Pt A E), z ^ n = spOver ψ ≫ spOver φ ≫ x →
          S D' x' E ψ z - S D x E (ψ.comp φ) z = ψ e := by
    intro D _ _ D' _ _ φ x x'
    exact (isSec_sub_existsUnique R A n hR b D' x' (S D' x')
      (fun E _ _ ψ z ↦ S D x E (ψ.comp φ) z) (hS D' x')
      (isSec_pull n b φ x (S D x) (hS D x))).exists
  refine ⟨fun D _ _ D' _ _ φ x ↦ Classical.choose (key D D' φ x), ?_⟩
  intro D _ _ D' _ _ φ x E _ _ ψ z hz
  exact (Classical.choose_spec (key D D' φ x) E ψ z hz).symm

end GlobalTheory.PtExt
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.PtExt.cupZ_pull_apply_fv : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) (m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left) (m₂ : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (snd A B).left) (a : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (b : Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (E'' : Type) [CommRing E''] [Algebra R E''] (φ : E →ₐ[R] E') (ψ : E' →ₐ[R] E'') (z : Pt (A ⊗ B) E), (cupZ _ (m₁.coef.pullbackOneCocycle a) (m₂.coef.pullbackOneCocycle b)).1 _ _ _ (trivMap φ z) (trivMap ψ (spOver φ ≫ z)) = ψ (fv a E E' φ (z ≫ fst A B)) * fv b E' E'' ψ (spOver φ ≫ z ≫ snd A B) := by
  intro R _ A B m₁ m₂ a b E _ _ E' _ _ E'' _ _ φ ψ z
  have e1 : fv (m₁.coef.pullbackOneCocycle a) E E' φ z = fv a E E' φ (z ≫ fst A B) := by
    rw [GlobalTheory.T.crystallineCocycleOnTrivialThickenings_pullback R A (A ⊗ B) (fst A B) m₁ a]; rfl
  have e2 : fv (m₂.coef.pullbackOneCocycle b) E' E'' ψ (spOver φ ≫ z) = fv b E' E'' ψ (spOver φ ≫ z ≫ snd A B) := by
    rw [GlobalTheory.T.crystallineCocycleOnTrivialThickenings_pullback R B (A ⊗ B) (snd A B) m₂ b]; simp only [Fn1.pull, Category.assoc]
  rw [cupZ_apply]
  change ψ (fv (m₁.coef.pullbackOneCocycle a) E E' φ z) *
    fv (m₂.coef.pullbackOneCocycle b) E' E'' ψ (spOver φ ≫ z) = _
  rw [e1, e2]
end
