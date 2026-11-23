module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle060
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2658
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2659
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle083
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelObjectOfDescendedData
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DivMemOfForallPowSuccDivPowMem

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.ThetaDiv

theorem resG_top_injective {X : Scheme.{0}} {W : X.Opens} (hW : ⊤ ≤ W) :
    Function.Injective (resG X (le_top : W ≤ ⊤)) := by
  obtain rfl : W = ⊤ := top_le_iff.1 hW
  intro x y h
  have e : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 (Opposite.op (⊤ : X.Opens)) := rfl
  simpa only [resG, e, CategoryTheory.Functor.map_id, CommRingCat.hom_id, RingHom.id_apply] using h

theorem div_of_mem_nonzeroLocus : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : ZH.RatModel o Ω) (δ : LB M.Z) {I : Type} (t : I → δ.Sec) (th : I → Ω), δ.IsLB → ZM.SecCoord δ t M.pt th → ∀ (a : I) (z : M.Z), z ∈ nonzeroLocus (t a) → M.Div th a z := by
  intro o Ω _ _ _ M δ I t th _ hsc a z hz
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
  have hDU : M.Z.basicOpen ((t a).f k) ≤ δ.U k := M.Z.basicOpen_le _
  have hD : ((M.Z.basicOpen ((t a).f k) : M.Z.Opens) : Set M.Z).Nonempty := ⟨z, hk⟩
  have hptD := M.top_le_preimage_pt hD
  have hptU : ⊤ ≤ M.pt ⁻¹ᵁ δ.U k := fun x hx => hDU (hptD hx)
  obtain ⟨τ, -, hτ⟩ := hsc
  let j : PUnit → δ.ι := fun _ => k
  have hj : (δ.pull M.pt).U j ≤ M.pt ⁻¹ᵁ δ.U (j PUnit.unit) := LB.wchart_le δ _ j PUnit.unit
  have hW : ⊤ ≤ (δ.pull M.pt).U j := fun x _ => Set.mem_iInter.2 fun _ => hptU (x := x) trivial
  have inj := resG_top_injective hW
  let e := Scheme.ΓSpecIso (CommRingCat.of Ω)
  have hc : ∀ b, resG (Sp Ω) (le_top : (δ.pull M.pt).U j ≤ ⊤) ((M.pt.appLE (δ.U k) ⊤ hptU).hom ((t b).f k)) =
      resG (Sp Ω) le_top (e.inv.hom (th b)) * (τ.s j).val := by
    intro b
    rw [← hτ b j hj]
    show (M.pt.appLE _ ⊤ hptU ≫ (Sp Ω).presheaf.map (homOfLE le_top).op).hom _ = _
    rw [Scheme.Hom.appLE_map]
  have hv : ∀ b, valF M.pt (δ.U k) ((t b).f k) = e.hom.hom ((M.pt.appLE (δ.U k) ⊤ hptU).hom ((t b).f k)) :=
    fun b => dif_pos hptU
  have hei : ∀ x : Ω, e.hom.hom (e.inv.hom x) = x := fun x => by
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
  have key : ∀ b, valF M.pt (δ.U k) ((t b).f k) * th a = valF M.pt (δ.U k) ((t a).f k) * th b := by
    intro b
    have h1 : (M.pt.appLE (δ.U k) ⊤ hptU).hom ((t b).f k) * e.inv.hom (th a) =
        (M.pt.appLE (δ.U k) ⊤ hptU).hom ((t a).f k) * e.inv.hom (th b) := by
      apply inj
      rw [map_mul, map_mul, hc b, hc a]
      ring
    have h2 := congrArg e.hom.hom h1
    rwa [map_mul, map_mul, hei, hei, ← hv, ← hv] at h2
  have hua : valF M.pt (δ.U k) ((t a).f k) ≠ 0 :=
    ((GlobalTheory.Points.le_preimage_basicOpen_iff M.pt hptU ((t a).f k)).1 hptD).ne_zero
  have hth : th a ≠ 0 := by
    intro h0
    apply hua
    rw [hv]
    have h1 := hc a
    rw [h0, map_zero, map_zero, zero_mul] at h1
    rw [inj (h1.trans (map_zero _).symm), map_zero]
  refine ⟨hth, fun b => ?_⟩
  have hu : IsUnit (resG M.Z hDU ((t a).f k)) :=
    RingedSpace.isUnit_res_basicOpen M.Z.toLocallyRingedSpace.toRingedSpace ((t a).f k)
  have hval : valF M.pt _ (resG M.Z hDU ((t b).f k) * ((hu.unit⁻¹ : (Γ(M.Z, M.Z.basicOpen ((t a).f k)))ˣ) : Γ(M.Z, M.Z.basicOpen ((t a).f k)))) = th b / th a := by
    rw [← ZH.RatModel.res_apply M _ hD, map_mul, map_units_inv, IsUnit.unit_spec, ZH.RatModel.res_resG,
      ZH.RatModel.res_resG, ZH.RatModel.res_apply, ZH.RatModel.res_apply]
    field_simp
    linear_combination key b
  exact hval ▸ ZH.RatModel.valF_mem_O hk _

end GlobalTheory.ThetaDiv

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.TupleBundle

theorem resG_injective_of_top {X : Scheme.{0}} {V : X.Opens} (h : ⊤ ≤ V) : Function.Injective (resG X h) := by
  obtain rfl : V = ⊤ := top_unique h
  have e : (homOfLE h : (⊤ : X.Opens) ⟶ ⊤) = 𝟙 _ := Subsingleton.elim _ _
  intro a b hab
  simpa [resG, e] using hab

theorem resG_resG {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (a : Γ(X, U)) :
    resG X h2 (resG X h1 a) = resG X (h2.trans h1) a := by
  show (X.presheaf.map _ ≫ X.presheaf.map _).hom a = _
  rw [← Functor.map_comp]
  rfl

theorem resG_appLE {X Y : Scheme.{0}} (f : Y ⟶ X) {U : X.Opens} {V W : Y.Opens} (h : V ≤ f ⁻¹ᵁ U) (h2 : W ≤ V)
    (a : Γ(X, U)) : resG Y h2 ((f.appLE U V h).hom a) = (f.appLE U W (h2.trans h)).hom a := by
  show (f.appLE U V h ≫ Y.presheaf.map _).hom a = _
  rw [Scheme.Hom.appLE_map]

variable {Ω : Type} [Field Ω]

def ev (V : (Sp Ω).Opens) (hV : ⊤ ≤ V) : Γ(Sp Ω, V) →+* Ω :=
  (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom.comp (resG (Sp Ω) hV)

theorem ev_injective (V : (Sp Ω).Opens) (hV : ⊤ ≤ V) : Function.Injective (ev V hV) :=
  (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv.injective.comp (resG_injective_of_top hV)

theorem ev_resG {V W : (Sp Ω).Opens} (hV : ⊤ ≤ V) (hW : ⊤ ≤ W) (h : W ≤ V) (a : Γ(Sp Ω, V)) :
    ev W hW (resG (Sp Ω) h a) = ev V hV a := by
  simp only [ev, RingHom.comp_apply, resG_resG]

theorem ev_resG_top {V : (Sp Ω).Opens} (hV : ⊤ ≤ V) (x : Ω) :
    ev V hV (resG (Sp Ω) le_top ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom x)) = x := by
  have e : (homOfLE (hV.trans le_top) : (⊤ : (Sp Ω).Opens) ⟶ ⊤) = 𝟙 _ := Subsingleton.elim _ _
  simp only [ev, RingHom.comp_apply, resG_resG]
  simp [resG, e]

theorem ev_appLE {X : Scheme.{0}} (x : Sp Ω ⟶ X) {U : X.Opens} {V : (Sp Ω).Opens} (hV : ⊤ ≤ V) (h : V ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)) : ev V hV ((x.appLE U V h).hom f) = valF x U f := by
  simp only [ev, RingHom.comp_apply, resG_appLE, valF, dif_pos (hV.trans h)]

end GlobalTheory.TupleBundle

namespace GlobalTheory.TupleBundle

theorem exists_lb_of_hasDiv : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : ZH.RatModel o Ω) (J : Type)
    [Finite J] (v : J → Ω), M.HasDiv v → ∃ (δ : LB M.Z) (t : J → δ.Sec), δ.IsLB ∧ (⨆ a, nonzeroLocus (t a)) = ⊤ ∧
    (∀ a z, z ∈ nonzeroLocus (t a) ↔ M.Div v a z) ∧ ZM.SecCoord δ t M.pt v := by
  intro o Ω _ _ _ M J _ v hv
  let U : {a // v a ≠ 0} → M.Z.Opens := fun k => ⟨{z | M.Div v k.1 z}, M.isOpen_setOf_div v k.1⟩
  have hU : ⨆ k, U k = ⊤ := by
    refine top_unique fun z _ => ?_
    obtain ⟨i, hi⟩ := hv z
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, hi.1⟩, hi⟩
  obtain ⟨g, hLB, hGT⟩ := ZH.RatModel.exists_isLB_genTriv_of_ratios o Ω M {a // v a ≠ 0} U (fun k => v k.1) hU
    (fun k => k.2) (fun k k' z hz => hz.1.2 k'.1)
  let δ : LB M.Z := ⟨{a // v a ≠ 0}, U, g⟩
  have hsec : ∀ a, ∃ σ : δ.Sec, M.HasVal (H := δ) (fun k => v k.1) σ (v a) := fun a =>
    hGT.exists_sec_hasVal (v a) fun k z hz => hz.2 a
  choose t ht using hsec
  have hnz : ∀ a z, z ∈ nonzeroLocus (t a) ↔ M.Div v a z := by
    intro a z
    simp only [nonzeroLocus, TopologicalSpace.Opens.mem_iSup]
    constructor
    · rintro ⟨k, hk⟩
      have hzk : z ∈ U k := M.Z.basicOpen_le _ hk
      have hval : valF M.pt (U k) ((t a).f k) = v a / v k.1 := ht a k ⟨z, hzk⟩
      have hu := (ZH.RatModel.isUnit_valF_iff (M := M) hzk ((t a).f k)).2 hk
      rw [ZH.RatModel.isUnit_O_iff] at hu
      simp only [hval] at hu
      obtain ⟨h1, h2⟩ := hu
      have hk0 := k.2
      have ha0 : v a ≠ 0 := (div_ne_zero_iff.1 h1).1
      refine ⟨ha0, fun j => ?_⟩
      have e : v j / v a = (v j / v k.1) * (v a / v k.1)⁻¹ := by field_simp
      rw [e]
      exact mul_mem (hzk.2 j) h2
    · intro h
      refine ⟨⟨a, h.1⟩, ?_⟩
      have hzk : z ∈ U ⟨a, h.1⟩ := h
      rw [← ZH.RatModel.isUnit_valF_iff (M := M) hzk, ZH.RatModel.isUnit_O_iff]
      have hv1 : valF M.pt (U ⟨a, h.1⟩) ((t a).f ⟨a, h.1⟩) = 1 := (ht a ⟨a, h.1⟩ ⟨z, hzk⟩).trans (div_self h.1)
      simp only [hv1, inv_one]
      exact ⟨one_ne_zero, one_mem _⟩
  refine ⟨δ, t, hLB, ?_, hnz, ?_⟩
  · refine top_unique fun z _ => ?_
    obtain ⟨i, hi⟩ := hv z
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (hnz i z).2 hi⟩
  · have hgen : ∀ k : {a // v a ≠ 0}, ⊤ ≤ M.pt ⁻¹ᵁ U k := fun k w _ => by
      show M.pt w ∈ U k
      rw [M.pt_apply w]
      exact ZH.RatModel.div_genericPoint (M := M) k.2
    have hW : ∀ j, ⊤ ≤ (δ.pull M.pt).U j := fun j w _ =>
      Set.mem_iInter.2 fun _ => hgen (j PUnit.unit) (x := w) trivial
    let τ : (δ.pull M.pt).Gen := ⟨fun j => Units.map (resG (Sp Ω) (le_top : (δ.pull M.pt).U j ≤ ⊤)).toMonoidHom
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom.toMonoidHom
        (Units.mk0 (v (j PUnit.unit).1)⁻¹ (inv_ne_zero (j PUnit.unit).2)))⟩
    have hτ : ∀ j, ((τ.s j : Γ(Sp Ω, (δ.pull M.pt).U j)ˣ) : Γ(Sp Ω, (δ.pull M.pt).U j)) =
        resG (Sp Ω) le_top ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (v (j PUnit.unit).1)⁻¹) := fun j => rfl
    refine ⟨τ, fun j j' => ?_, fun i j h => ?_⟩
    · have hle : (δ.pull M.pt).U j ⊓ (δ.pull M.pt).U j' ≤ M.pt ⁻¹ᵁ (U (j PUnit.unit) ⊓ U (j' PUnit.unit)) :=
        le_inf (inf_le_left.trans (LB.wchart_le δ (fun _ => M.pt) j PUnit.unit))
          (inf_le_right.trans (LB.wchart_le δ (fun _ => M.pt) j' PUnit.unit))
      have e0 : (δ.pull M.pt).g j j' = Semi.res hle (pullU M.pt _ (δ.g (j PUnit.unit) (j' PUnit.unit))) :=
        (Fintype.prod_unique fun _ : PUnit.{1} =>
          Semi.res hle (pullU M.pt _ (δ.g (j PUnit.unit) (j' PUnit.unit))) ^ (1 : ℤ)).trans (zpow_one _)
      have hne : ((U (j PUnit.unit) ⊓ U (j' PUnit.unit) : M.Z.Opens) : Set M.Z).Nonempty :=
        ⟨genericPoint M.Z, ZH.RatModel.div_genericPoint (M := M) (j PUnit.unit).2,
          ZH.RatModel.div_genericPoint (M := M) (j' PUnit.unit).2⟩
      have hg := hGT.g_eq (j PUnit.unit) (j' PUnit.unit) hne
      have hV : ⊤ ≤ (δ.pull M.pt).U j ⊓ (δ.pull M.pt).U j' := le_inf (hW j) (hW j')
      refine Units.ext (ev_injective _ hV ?_)
      rw [e0]
      show ev _ hV (resG (Sp Ω) inf_le_left (τ.s j : Γ(Sp Ω, _))) =
        ev _ hV ((M.pt.appLE _ _ hle).hom (δ.g (j PUnit.unit) (j' PUnit.unit) : Γ(M.Z, _)) *
          resG (Sp Ω) inf_le_right (τ.s j' : Γ(Sp Ω, _)))
      rw [map_mul, ev_resG (hW j), ev_resG (hW j'), ev_appLE, hτ, hτ, ev_resG_top, ev_resG_top]
      have h1 := (j PUnit.unit).2
      have h2 := (j' PUnit.unit).2
      have hg' : valF M.pt (U (j PUnit.unit) ⊓ U (j' PUnit.unit)) (δ.g (j PUnit.unit) (j' PUnit.unit) : Γ(M.Z, _)) =
          v (j' PUnit.unit).1 / v (j PUnit.unit).1 := hg
      rw [hg']
      field_simp
    · have hne : (U (j PUnit.unit) : Set M.Z).Nonempty :=
        ⟨genericPoint M.Z, ZH.RatModel.div_genericPoint (M := M) (j PUnit.unit).2⟩
      have hv' : valF M.pt (U (j PUnit.unit)) ((t i).f (j PUnit.unit)) = v i / v (j PUnit.unit).1 :=
        ht i (j PUnit.unit) hne
      refine ev_injective _ (hW j) ?_
      simp only [map_mul, hτ]
      rw [ev_appLE, ev_resG_top]
      change _ = v i * ev _ (hW j) (resG (Sp Ω) le_top ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (v (j PUnit.unit).1)⁻¹))
      rw [ev_resG_top, hv', div_eq_mul_inv]

end GlobalTheory.TupleBundle
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.siegelFamily_tangentBound_nonconstant : ∀ (h n : ℕ), 1 ≤ h → 3 ≤ n → Odd n → ∀ (K : Type) [Field K] [IsAlgClosed K] (r : ℕ) (β : cycAway n →+* K) (c : SiegPre h n (zetaAway n) (spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β))), c.Principal → (∀ (lam : (Fin r → K) →ₗ[K] K) (c' : SiegPre h n (zetaAway n) (spMap ((algebraMap K (DualNumber K)).comp β))), SiegPB c' c (spMap (dirMap lam)) → SiegPB c' c (constPt (spMap (dirMap lam))) → lam = 0) → r ≤ h * (h + 1) / 2 := by
  first | exact @GlobalTheory.SiegelTangentBound.main | exact GlobalTheory.SiegelTangentBound.main | (intros; apply GlobalTheory.SiegelTangentBound.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

open GlobalTheory.CechPic

namespace GlobalTheory.DescGalRig

variable {S : Scheme.{0}}

theorem one_left (A : Over S) [GrpObj A] : (1 : A ⟶ A).left = A.hom ≫ eSec A := by
  have hu : (toUnit A).left = A.hom := (Category.comp_id _).symm.trans (Over.w (toUnit A))
  show (toUnit A ≫ η[A]).left = _
  rw [Over.comp_left, hu]
  rfl

theorem eSec_lift_one' (A : Over S) [GrpObj A] : eSec A ≫ (lift (𝟙 A) (1 : A ⟶ A)).left = eSec (A ⊗ A) := by
  apply pullback.hom_ext
  · change eSec A ≫ (lift (𝟙 A) (1 : A ⟶ A)).left ≫ (fst A A).left = eSec (A ⊗ A) ≫ (fst A A).left
    show (η[A] ≫ lift (𝟙 A) (1 : A ⟶ A) ≫ fst A A).left = (η[A ⊗ A] ≫ fst A A).left
    simp [Hom.one_def]
  · change eSec A ≫ (lift (𝟙 A) (1 : A ⟶ A)).left ≫ (snd A A).left = eSec (A ⊗ A) ≫ (snd A A).left
    show (η[A] ≫ lift (𝟙 A) (1 : A ⟶ A) ≫ snd A A).left = (η[A ⊗ A] ≫ snd A A).left
    simp [Hom.one_def]

variable {X Y : Scheme.{0}}

theorem one_left_comm {π : X ⟶ Y} {A : Over X} [GrpObj A] {A₀ : Over Y} [GrpObj A₀] {φ : A.left ⟶ A₀.left}
    (gp : IsGrpPullback A A₀ π φ) : (1 : A ⟶ A).left ≫ φ = φ ≫ (1 : A₀ ⟶ A₀).left := by
  rw [one_left, one_left, Category.assoc, GlobalTheory.PolBaseChange.eSec_comm gp, ← Category.assoc, ← gp.1.w,
    Category.assoc]

theorem lift_one_comm {π : X ⟶ Y} {A : Over X} [GrpObj A] {A₀ : Over Y} [GrpObj A₀] {φ : A.left ⟶ A₀.left}
    {φ₂ : (A ⊗ A).left ⟶ (A₀ ⊗ A₀).left} (gp : IsGrpPullback A A₀ π φ) (sq : IsSquare φ φ₂) :
    (lift (1 : A ⟶ A) (𝟙 A)).left ≫ φ₂ = φ ≫ (lift (1 : A₀ ⟶ A₀) (𝟙 A₀)).left := by
  have a₁ := congrArg (fun q => q.left) (lift_fst (1 : A ⟶ A) (𝟙 A))
  have a₂ := congrArg (fun q => q.left) (lift_snd (1 : A ⟶ A) (𝟙 A))
  have b₁ := congrArg (fun q => q.left) (lift_fst (1 : A₀ ⟶ A₀) (𝟙 A₀))
  have b₂ := congrArg (fun q => q.left) (lift_snd (1 : A₀ ⟶ A₀) (𝟙 A₀))
  simp only [Over.comp_left, Over.id_left] at a₁ a₂ b₁ b₂
  apply GlobalTheory.SquareDescent.square_hom_ext A₀
  · rw [Category.assoc, sq.1, ← Category.assoc, a₁, Category.assoc, b₁, one_left_comm gp]
  · rw [Category.assoc, sq.2, ← Category.assoc, a₂, Category.assoc, b₂, Category.id_comp, Category.comp_id]

theorem lift_one_comm' {π : X ⟶ Y} {A : Over X} [GrpObj A] {A₀ : Over Y} [GrpObj A₀] {φ : A.left ⟶ A₀.left}
    {φ₂ : (A ⊗ A).left ⟶ (A₀ ⊗ A₀).left} (gp : IsGrpPullback A A₀ π φ) (sq : IsSquare φ φ₂) :
    (lift (𝟙 A) (1 : A ⟶ A)).left ≫ φ₂ = φ ≫ (lift (𝟙 A₀) (1 : A₀ ⟶ A₀)).left := by
  have a₁ := congrArg (fun q => q.left) (lift_fst (𝟙 A) (1 : A ⟶ A))
  have a₂ := congrArg (fun q => q.left) (lift_snd (𝟙 A) (1 : A ⟶ A))
  have b₁ := congrArg (fun q => q.left) (lift_fst (𝟙 A₀) (1 : A₀ ⟶ A₀))
  have b₂ := congrArg (fun q => q.left) (lift_snd (𝟙 A₀) (1 : A₀ ⟶ A₀))
  simp only [Over.comp_left, Over.id_left] at a₁ a₂ b₁ b₂
  apply GlobalTheory.SquareDescent.square_hom_ext A₀
  · rw [Category.assoc, sq.1, ← Category.assoc, a₁, Category.assoc, b₁, Category.id_comp, Category.comp_id]
  · rw [Category.assoc, sq.2, ← Category.assoc, a₂, Category.assoc, b₂, one_left_comm gp]

theorem exists_gen_of_side {π : X ⟶ Y} {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)} {A : Over X} [GrpObj A]
    {A₀ : Over Y} [GrpObj A₀] {φ : A.left ⟶ A₀.left} {φ₂ : (A ⊗ A).left ⟶ (A₀ ⊗ A₀).left}
    {P : LB (A ⊗ A).left} {P₀ : LB (A₀ ⊗ A₀).left} (hG : GlobalTheory.ZM.IsGaloisCover Ga ρ π) (hA₀ : IsAbelianScheme A₀)
    (gp : IsGrpPullback A A₀ π φ) (hP : P.IsLB) (hP₀ : P₀.IsLB) (i : LBIso P (P₀.pull φ₂))
    (h0 : ∃ t : (P₀.pull (eSec (A₀ ⊗ A₀))).Gen, t.IsGen)
    (k : A.left ⟶ (A ⊗ A).left) (k₀ : A₀.left ⟶ (A₀ ⊗ A₀).left) (hk : k ≫ φ₂ = φ ≫ k₀)
    (he : eSec A₀ ≫ k₀ = eSec (A₀ ⊗ A₀)) (hgen : ∃ t : (P.pull k).Gen, t.IsGen) :
    ∃ t : (P₀.pull k₀).Gen, t.IsGen := by
  have := hG.fin
  have := hG.etale
  have := hG.onto
  have hN := LB.isLB_pull hP₀ k₀
  refine GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange GlobalTheory.SemiRigid.globalFns Y X π A₀ _ hA₀ hN
    inferInstance inferInstance inferInstance ?_ ?_
  · obtain ⟨t, ht⟩ := h0
    exact gen_chartPull (chartPullOut P₀ (fun _ : PUnit => k₀) (fun _ => 1) (eSec A₀)
      (fun _ => eSec (A₀ ⊗ A₀)) (fun _ => he.symm)) t ht
  · have hiso : LBIso (P.pull k) ((P₀.pull φ₂).pull k) :=
      i.chartPull (chartPullPull P k) (chartPullPull (P₀.pull φ₂) k)
    have htrans : ∀ {U : Scheme.{0}} {L M : LB U}, L.IsLB → M.IsLB → LBIso L M →
        (∃ t : L.Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen := by
      intro U L M hL hM h H
      obtain ⟨w, hw⟩ := h.chartPull (chartPullId L) (chartPullPull M (𝟙 U))
      obtain ⟨t, ht⟩ := H
      obtain ⟨a, ha⟩ := gen_chartPull (chartPullPull L (𝟙 U)) t ht
      obtain ⟨c, hc, -⟩ := exists_up ((isGen_iff w).1 hw) hM hL a ha
      exact gen_chartPull (chartPullUnpull M _ (Category.id_comp _)) c hc
    obtain ⟨t, ht⟩ := htrans (LB.isLB_pull hP k) (LB.isLB_pull (LB.isLB_pull hP₀ φ₂) k) hiso hgen
    obtain ⟨u, hu⟩ := gen_chartPull (chartPullIn P₀ (fun _ : PUnit => φ₂) (fun _ => 1) k) t ht
    have hc : pullback.fst A₀.hom π ≫ k₀ = (gp.1.isoPullback.inv ≫ k) ≫ φ₂ := by
      rw [Category.assoc, hk, ← Category.assoc, gp.1.isoPullback_inv_fst]
    apply gen_chartPull (chartPullOut P₀ (fun _ : PUnit => k₀) (fun _ => 1) (pullback.fst A₀.hom π)
      (fun _ => gp.1.isoPullback.inv ≫ (k ≫ φ₂)) (fun _ => by rw [← Category.assoc, ← hc]))
      (LB.pullGen P₀ (fun _ : PUnit => k ≫ φ₂) (fun _ => 1) u gp.1.isoPullback.inv)
    exact DVR.pullGen_isGen _ _ _ u hu _

end GlobalTheory.DescGalRig

theorem GlobalTheory.DescGalRig.exists_gen_lift_of_descent : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∃ t : (P₀.pull (eSec (G2 A₀))).Gen, t.IsGen) → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → (∃ t : (P₀.pull (lift (1 : A₀ ⟶ A₀) (𝟙 A₀)).left).Gen, t.IsGen) ∧ (∃ t : (P₀.pull (lift (𝟙 A₀) (1 : A₀ ⟶ A₀)).left).Gen, t.IsGen) := by
  intro X Y π Ga _ ρ A _ _ A₀ _ _ φ φ₂ P P₀ hG _ hA₀ gp sq hP hP₀ i h0 h₁ h₂
  exact ⟨GlobalTheory.DescGalRig.exists_gen_of_side hG hA₀ gp hP hP₀ i h0 _ _ (GlobalTheory.DescGalRig.lift_one_comm gp sq)
      (GlobalTheory.SquareDescent.eSec_lift_one A₀) h₁,
    GlobalTheory.DescGalRig.exists_gen_of_side hG hA₀ gp hP hP₀ i h0 _ _ (GlobalTheory.DescGalRig.lift_one_comm' gp sq)
      (GlobalTheory.DescGalRig.eSec_lift_one' A₀) h₂⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.DescSymm

open GlobalTheory.CechPic

theorem eSec_swap {S : Scheme.{0}} (A : Over S) [GrpObj A] :
    eSec (A ⊗ A) ≫ (lift (snd A A) (fst A A)).left = eSec (A ⊗ A) := by
  apply GlobalTheory.SquareDescent.square_hom_ext A
  · rw [Category.assoc, ← Over.comp_left, lift_fst, GlobalTheory.SquareDescent.eSec_snd, GlobalTheory.SquareDescent.eSec_fst]
  · rw [Category.assoc, ← Over.comp_left, lift_snd, GlobalTheory.SquareDescent.eSec_fst, GlobalTheory.SquareDescent.eSec_snd]

theorem lbIso_swap : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∃ t : (P₀.pull (eSec (G2 A₀))).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → LBIso P₀ (P₀.pull (lift (snd A₀ A₀) (fst A₀ A₀)).left) := by
  intro X Y π Ga _ ρ A _ _ A₀ _ _ φ φ₂ P P₀ hπ hA hA₀ gp hsq hP hP₀ iP ⟨r, hr⟩ iS
  have := hπ.fin
  have := hπ.etale
  have := hπ.onto
  have hA₂₀ : IsAbelianScheme (G2 A₀) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA₀ hA₀
  have hpb := GlobalTheory.SiegelDescent.isPullback_square gp.1 φ₂ hsq
  have hsw : (lift (snd A A) (fst A A)).left ≫ φ₂ = φ₂ ≫ (lift (snd A₀ A₀) (fst A₀ A₀)).left := by
    apply GlobalTheory.SquareDescent.square_hom_ext A₀
    · rw [Category.assoc, hsq.1, Category.assoc, ← Over.comp_left, lift_fst, ← Category.assoc, ← Over.comp_left,
        lift_fst, hsq.2]
    · rw [Category.assoc, hsq.2, Category.assoc, ← Over.comp_left, lift_snd, ← Category.assoc, ← Over.comp_left,
        lift_snd, hsq.1]
  have h₂ := LB.isLB_pull hP₀ (lift (snd A₀ A₀) (fst A₀ A₀)).left
  have hN := LB.isLB_div h₂ hP₀
  have cN := (CechPic.cls_div h₂ hP₀ hN).trans (by rw [CechPic.cls_pull hP₀ _ h₂])
  have z₀ : CechPic.pull (eSec (G2 A₀)) (CechPic.cls _ hP₀) = 0 :=
    (CechPic.cls_eq_zero_iff (LB.isLB_pull hP₀ _)).2 ⟨r, hr⟩
  have c₁ : CechPic.cls _ hP = CechPic.pull φ₂ (CechPic.cls _ hP₀) :=
    (CechPic.cls_eq_iff hP (LB.isLB_pull hP₀ _)).2 iP
  have c₂ : CechPic.cls _ hP = CechPic.pull (lift (snd A A) (fst A A)).left (CechPic.cls _ hP) :=
    ((CechPic.cls_eq_iff hP (LB.isLB_pull hP _)).2 iS).trans (CechPic.cls_pull hP _ _)
  refine GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange GlobalTheory.SemiRigid.globalFns Y X π (G2 A₀) _ hA₂₀ hN
    inferInstance inferInstance inferInstance ((CechPic.cls_eq_zero_iff (LB.isLB_pull hN _)).1 ?_)
    ((CechPic.cls_eq_zero_iff (LB.isLB_pull hN _)).1 ?_)
  · rw [CechPic.cls_pull hN, cN, map_sub, ← CechPic.pull_comp, eSec_swap, z₀, sub_zero]
  · rw [CechPic.cls_pull hN, cN, ← hpb.isoPullback_inv_fst, CechPic.pull_comp, map_sub, ← CechPic.pull_comp φ₂,
      ← hsw, CechPic.pull_comp, ← c₁, ← c₂, sub_self, map_zero]

end GlobalTheory.DescSymm
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.semiAbelian_baseChange_normal_domain_generic_fibre : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (χ : Sp R ⟶ S), IsLocallyNoetherian (Over.mk χ ⊗ G).left ∧ GlobalTheory.IsNormalScheme (Over.mk χ ⊗ G).left ∧ IsPreimmersion ((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left ∧ ∀ W : (Over.mk χ ⊗ G).left.Opens, Function.Injective ((((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left.app W).hom) := by
  first | exact @GlobalTheory.SemiAbGenericFibre.baseChange_normal_generic | exact GlobalTheory.SemiAbGenericFibre.baseChange_normal_generic | (intros; apply GlobalTheory.SemiAbGenericFibre.baseChange_normal_generic <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.finite_over_projectiveSpace_projective_ample_twist : ∀ (o : Type) [CommRing o] [IsNoetherianRing o] (n k : ℕ) (Z : Scheme.{0}) (p : Z ⟶ PSpace o n), 1 ≤ k → IsFinite p → IsProjOver (p ≫ PSpace.str o n) ∧ (lbPow ((ProjSpace.O1 o n).pull p) k).IsLB ∧ IsAmpleLB (lbPow ((ProjSpace.O1 o n).pull p) k) ∧ ∀ (Y : Scheme.{0}) (h : Y ⟶ Z), LBIso ((lbPow ((ProjSpace.O1 o n).pull p) k).pull h) (lbPow ((ProjSpace.O1 o n).pull (h ≫ p)) k) := by
  first | exact @GlobalTheory.FiniteOverPSpace.isProjOver_and_isAmpleLB | exact GlobalTheory.FiniteOverPSpace.isProjOver_and_isAmpleLB | (intros; apply GlobalTheory.FiniteOverPSpace.isProjOver_and_isAmpleLB <;> assumption)
end
