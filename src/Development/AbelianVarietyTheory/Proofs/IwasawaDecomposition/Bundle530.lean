module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2118
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle046
public import Mathlib.RingTheory.HahnSeries.PowerSeries
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSideReadingLevelZeroMoved
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle034
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle316
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle448
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle003
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
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.ShFam GlobalTheory.LocM
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM.PolFibre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {S : Scheme.{0}}
  {t : SAB H S} {K : Type} [Field K] {x : Sp K ⟶ S} {u : SAB H (Sp K)}

theorem exists_to_fibre (m : SABMap u t x) :
    ∃ φ : u.G.left ⟶ ((Over.pullback x).obj t.G).left, IsGrpPullback u.G ((Over.pullback x).obj t.G) (𝟙 _) φ ∧
      LBIso u.PP.L ((t.PP.L.pull (pullback.fst t.G.hom x)).pull φ) := by
  have hM := LB.isLB_pull t.PP.isLB (pullback.fst t.G.hom x)
  obtain ⟨φ, hφ, e, -⟩ := GlobalTheory.Ex.UnifModel.exists_cancel (g := 𝟙 _) (f := x) (m.cart.congr (Category.id_comp _).symm rfl)
    (isGrpPullback_pullback t.G x) t.PP.isLB hM u.PP.isLB (GlobalTheory.Ex.UnifModel.iso_of_map m)
    ⟨Out.CubePf.idIsoL _, Out.CubePf.idIsoL_isGen hM⟩
  exact ⟨φ, hφ, e⟩

theorem exists_of_fibre (m : SABMap u t x) :
    ∃ φ : ((Over.pullback x).obj t.G).left ⟶ u.G.left, IsGrpPullback ((Over.pullback x).obj t.G) u.G (𝟙 _) φ ∧
      LBIso (t.PP.L.pull (pullback.fst t.G.hom x)) (u.PP.L.pull φ) := by
  have hM := LB.isLB_pull t.PP.isLB (pullback.fst t.G.hom x)
  obtain ⟨φ, hφ, e, -⟩ := GlobalTheory.Ex.UnifModel.exists_cancel (g := 𝟙 _) (f := x)
    ((isGrpPullback_pullback t.G x).congr (Category.id_comp _).symm rfl) m.cart t.PP.isLB u.PP.isLB hM
    ⟨Out.CubePf.idIsoL _, Out.CubePf.idIsoL_isGen hM⟩ (GlobalTheory.Ex.UnifModel.iso_of_map m)
  exact ⟨φ, hφ, e⟩

theorem ample_kTriv_of_polAt (m : SABMap u t x) (hp : GlobalTheory.LN.PolAt t x) :
    RelAmple u.G u.PP.L ∧ KTriv u.G u.PP.L := by
  obtain ⟨φ, hφ, e⟩ := exists_to_fibre m
  exact amplePt _ _ (𝟙 _) _ _ φ hφ _ _ (LB.isLB_pull t.PP.isLB _) u.PP.isLB e hp.2.1 hp.2.2

theorem polAt_of_map (m : SABMap u t x) (hp : IsProper (pullback.snd t.G.hom x)) (hA : RelAmple u.G u.PP.L)
    (hK : KTriv u.G u.PP.L) : GlobalTheory.LN.PolAt t x := by
  obtain ⟨φ, hφ, e⟩ := exists_of_fibre m
  have h := amplePt _ _ (𝟙 _) _ _ φ hφ _ _ u.PP.isLB (LB.isLB_pull t.PP.isLB _) e hA hK
  exact ⟨hp, h.1, h.2⟩

end GlobalTheory.LocM.PolFibre
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.KeyOpen

theorem glue_units {Z : Scheme.{0}} [IsReduced Z] (V : Z.Opens) (P : Z.Opens → Prop)
    (hP : ∀ p ∈ V, ∃ W : Z.Opens, IsAffineOpen W ∧ W ≤ V ∧ P W ∧ p ∈ W)
    (R : ∀ (L : Type) [Field L], (Sp L ⟶ Z) → L → Prop)
    (uniq : ∀ (L : Type) [Field L] (z : Sp L ⟶ Z), ⊤ ≤ z ⁻¹ᵁ V → ∀ x y, R L z x → R L z y → x = y)
    (loc : ∀ W : Z.Opens, IsAffineOpen W → W ≤ V → P W → ∃ a : Γ(Z, W)ˣ,
      ∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ W), R L z (ev z W hz a.val)) :
    ∃ a : Γ(Z, V)ˣ, ∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ V), R L z (ev z V hz a.val) := by
  let I := {W : Z.Opens // IsAffineOpen W ∧ W ≤ V ∧ P W}
  choose a ha using fun i : I => loc i.1 i.2.1 i.2.2.1 i.2.2.2
  have hc : ∀ p ∈ V, ∃ i : I, p ∈ i.1 := fun p hp => by
    obtain ⟨W, hW, hWV, hPW, hpW⟩ := hP p hp
    exact ⟨⟨W, hW, hWV, hPW⟩, hpW⟩
  have hcov : V ≤ iSup fun i : I => i.1 := fun p hp => TopologicalSpace.Opens.mem_iSup.2 (hc p hp)
  have key : ∀ (i j : I) (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ (i.1 ⊓ j.1)),
      ev z _ hz (resG Z inf_le_left (a i).val) = ev z _ hz (resG Z inf_le_right (a j).val) := by
    intro i j L _ z hz
    have hi := GlobalTheory.FlagMod.le_preimage_mono inf_le_left hz
    have hj := GlobalTheory.FlagMod.le_preimage_mono inf_le_right hz
    rw [GlobalTheory.FlagMod.ev_res z _ hz hi, GlobalTheory.FlagMod.ev_res z _ hz hj]
    exact uniq L z (GlobalTheory.FlagMod.le_preimage_mono i.2.2.1 hi) _ _ (ha i L z hi) (ha j L z hj)
  obtain ⟨s, hs, -⟩ := Z.sheaf.existsUnique_gluing' (fun i : I => i.1) V (fun i => homOfLE i.2.2.1)
    hcov (fun i => (a i).val) (fun i j =>
      GlobalTheory.FlagMod.ext_ev_field (a := resG Z inf_le_left (a i).val) (b := resG Z inf_le_right (a j).val)
        fun L _ z hz => key i j L z hz)
  obtain ⟨t, ht, -⟩ := Z.sheaf.existsUnique_gluing' (fun i : I => i.1) V (fun i => homOfLE i.2.2.1)
    hcov (fun i => (a i)⁻¹.val) (fun i j =>
      GlobalTheory.FlagMod.ext_ev_field (a := resG Z inf_le_left (a i)⁻¹.val) (b := resG Z inf_le_right (a j)⁻¹.val)
        fun L _ z hz => by
          have e := key i j L z hz
          have e₁ := map_units_inv (((ev z _ hz).comp (resG Z inf_le_left)) : Γ(Z, i.1) →+* L) (a i)
          have e₂ := map_units_inv (((ev z _ hz).comp (resG Z inf_le_right)) : Γ(Z, j.1) →+* L) (a j)
          simp only [RingHom.coe_comp, Function.comp_apply] at e₁ e₂
          rw [e₁, e₂, e])
  obtain ⟨s, t, hs, ht⟩ : ∃ s t : Γ(Z, V), (∀ i : I, resG Z i.2.2.1 s = (a i).val) ∧
      ∀ i : I, resG Z i.2.2.1 t = (a i)⁻¹.val := ⟨s, t, hs, ht⟩
  have hval : ∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ V), ∃ i : I, ∃ hi : ⊤ ≤ z ⁻¹ᵁ i.1,
      ev z V hz s = ev z i.1 hi (a i).val ∧ ev z V hz t = ev z i.1 hi (a i)⁻¹.val := by
    intro L _ z hz
    obtain ⟨i, hi⟩ := hc (z (IsLocalRing.closedPoint L)) (hz (Set.mem_univ _))
    have hi' : ⊤ ≤ z ⁻¹ᵁ i.1 := ((IsLocalRing.closed_point_mem_iff (U := z ⁻¹ᵁ i.1)).1 hi).ge
    exact ⟨i, hi', (GlobalTheory.FlagMod.ev_res z i.2.2.1 hi' hz s).symm.trans (congrArg _ (hs i)),
      (GlobalTheory.FlagMod.ev_res z i.2.2.1 hi' hz t).symm.trans (congrArg _ (ht i))⟩
  have hst : s * t = 1 := GlobalTheory.FlagMod.ext_ev_field fun L _ z hz => by
    obtain ⟨i, hi, e₁, e₂⟩ := hval L z hz
    rw [map_mul, map_one, e₁, e₂, ← map_mul, Units.mul_inv, map_one]
  refine ⟨⟨s, t, hst, by rw [mul_comm, hst]⟩, fun L _ z hz => ?_⟩
  obtain ⟨i, hi, e₁, -⟩ := hval L z hz
  show R L z (ev z V hz s)
  rw [e₁]
  exact ha i L z hi

end GlobalTheory.KeyOpen

namespace GlobalTheory.KeyOpen

end GlobalTheory.KeyOpen
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

namespace GlobalTheory.GenExt
open GlobalTheory.FlagMod

theorem generic_le {X : Scheme.{0}} {G W : X.Opens} (hG : IsAffineOpen G) [IsDomain Γ(X, G)]
    (hW : W ≤ G) (hne : ∃ x, x ∈ W) :
    ⊤ ≤ (spMap (algebraMap Γ(X, G) (FractionRing Γ(X, G))) ≫ tau hG) ⁻¹ᵁ W := by
  intro y _
  obtain ⟨x, hx⟩ := hne
  obtain ⟨q, hq⟩ := hG.range_fromSpec.ge (hW hx)
  have hq' : q ∈ (tau hG ⁻¹ᵁ W : (Sp Γ(X, G)).Opens) := by
    show hG.fromSpec q ∈ W
    rw [hq]; exact hx
  have hsp : (spMap (algebraMap Γ(X, G) (FractionRing Γ(X, G)))) y ⤳ q := by
    refine (PrimeSpectrum.le_iff_specializes (R := Γ(X, G)) ((spMap (algebraMap Γ(X, G) (FractionRing Γ(X, G)))) y) q).1 ?_
    show Ideal.comap _ y.asIdeal ≤ q.asIdeal
    rw [@Ideal.eq_bot_of_prime _ _ y.asIdeal y.2]
    exact Ideal.comap_bot_le_of_injective _ (IsFractionRing.injective Γ(X, G) (FractionRing Γ(X, G)))
  exact hsp.mem_open (tau hG ⁻¹ᵁ W).isOpen hq'

theorem extend_of_integral_at_dvr : ∀ (X : Scheme.{0}) (G W₀ : X.Opens) (hle : W₀ ≤ G), IsAffineOpen G → IsDomain Γ(X, G) → IsNoetherianRing Γ(X, G) → IsIntegrallyClosed Γ(X, G) → Countable Γ(X, G) → (∃ x, x ∈ W₀) → Function.Injective (resG X hle) ∧ ∀ f₀ : Γ(X, W₀), (∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (z : Sp R ⟶ X), Countable R → ⊤ ≤ z ⁻¹ᵁ G → ∀ h : ⊤ ≤ (spMap (algebraMap R K) ≫ z) ⁻¹ᵁ W₀, ev (spMap (algebraMap R K) ≫ z) W₀ h f₀ ∈ (algebraMap R K).range) → ∃ f : Γ(X, G), resG X hle f = f₀ := by
  intro X G W₀ hle hG hD hN hI hC hne
  let K := FractionRing Γ(X, G)
  let η : Sp K ⟶ X := spMap (algebraMap Γ(X, G) K) ≫ tau hG
  have hηG : ⊤ ≤ η ⁻¹ᵁ G := le_preimage_comp _ (tau_le hG le_rfl)
  have key : ∀ (W : X.Opens) (hW : W ≤ G) (h : ⊤ ≤ η ⁻¹ᵁ W) (a : Γ(X, G)),
      ev η W h (resG X hW a) = algebraMap Γ(X, G) K a := by
    intro W hW h a
    rw [ev_res η hW h hηG, ev_spMap_tau hG]
  have hW₀ : ⊤ ≤ η ⁻¹ᵁ W₀ := generic_le hG hle hne
  refine ⟨fun a b e => IsFractionRing.injective Γ(X, G) K (by rw [← key W₀ hle hW₀, ← key W₀ hle hW₀, e]), ?_⟩
  intro f₀ hf
  have hKc : Countable K := by
    have hs : Function.Surjective (fun p : Γ(X, G) × nonZeroDivisors Γ(X, G) => IsLocalization.mk' K p.1 p.2) :=
      fun x => by
        obtain ⟨p, e⟩ := IsLocalization.mk'_surjective (nonZeroDivisors Γ(X, G)) x
        exact ⟨p, e⟩
    exact hs.countable
  have hint : _root_.IsIntegral Γ(X, G) (ev η W₀ hW₀ f₀) := by
    apply GlobalTheory.isIntegral_of_forall_mem_discreteValuationSubring Γ(X, G) K
    intro V hV hBV
    let ι : Γ(X, G) →+* V := (algebraMap Γ(X, G) K).codRestrict V.toSubring hBV
    have hz : ⊤ ≤ (spMap ι ≫ tau hG) ⁻¹ᵁ G := le_preimage_comp _ (tau_le hG le_rfl)
    have hc : (algebraMap V K).comp ι = algebraMap Γ(X, G) K := RingHom.ext fun _ => rfl
    have he : spMap (algebraMap V K) ≫ spMap ι ≫ tau hG = η := by
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]
    have h' : ⊤ ≤ (spMap (algebraMap V K) ≫ spMap ι ≫ tau hG) ⁻¹ᵁ W₀ := by rw [he]; exact hW₀
    obtain ⟨v, hv⟩ := hf V K (spMap ι ≫ tau hG) inferInstance hz h'
    rw [ev_congr he W₀ h' hW₀] at hv
    rw [← hv]
    exact v.2
  obtain ⟨f, hf'⟩ := (IsIntegrallyClosed.isIntegral_iff (K := K)).1 hint
  refine ⟨f, ext_ev_loc fun p hp => ?_⟩
  obtain ⟨s, hsle, hps⟩ := hG.exists_basicOpen_le ⟨p, hp⟩ (hle hp)
  have hN : ⊤ ≤ η ⁻¹ᵁ X.basicOpen s := generic_le hG (X.basicOpen_le s) ⟨p, hps⟩
  have inj : Function.Injective (ev η (X.basicOpen s) hN) := by
    haveI := hG.isLocalization_basicOpen s
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨a, m⟩, e⟩ := IsLocalization.surj (Submonoid.powers s) x
    have h1 : algebraMap Γ(X, G) K a = 0 := by
      rw [← key _ (X.basicOpen_le s) hN a]
      change ev η _ hN (algebraMap Γ(X, G) Γ(X, X.basicOpen s) a) = 0
      rw [← e, map_mul, hx, zero_mul]
    have ha : a = 0 := IsFractionRing.injective Γ(X, G) K (by rw [h1, map_zero])
    have hu : IsUnit (algebraMap Γ(X, G) Γ(X, X.basicOpen s) m) := IsLocalization.map_units _ m
    rw [ha, map_zero] at e
    exact hu.mul_left_eq_zero.1 e
  have hres : resG X hsle (resG X hle f) = resG X hsle f₀ := by
    apply inj
    rw [ev_res η hsle hN hW₀, ev_res η hsle hN hW₀, key W₀ hle hW₀, hf']
  refine ⟨X.basicOpen s, hps, fun S _ z hz hzN => ?_⟩
  rw [← ev_res z hsle hzN hz, ← ev_res z hsle hzN hz (f₀), hres]

end GlobalTheory.GenExt
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

namespace GlobalTheory.ArcIntegral

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := (Spec.map_comp _ _).symm

theorem ev_factor {Z : Scheme.{0}} {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (z₁ : Sp A ⟶ Z) (z₂ : Sp B ⟶ Z)
    (e : z₂ = spMap φ ≫ z₁) (W : Z.Opens) (h₁ : ⊤ ≤ z₁ ⁻¹ᵁ W) (h₂ : ⊤ ≤ z₂ ⁻¹ᵁ W) (f : Γ(Z, W)) :
    ev z₂ W h₂ f = φ (ev z₁ W h₁ f) := by
  subst e
  rw [GlobalTheory.FlagMod.ev_spMap φ z₁ W h₁]
  rfl

theorem point_cases (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (x : Sp R) :
    (∃ p : Sp K, spMap (algebraMap R K) p = x) ∨ x = IsLocalRing.closedPoint R := by
  by_cases h : x.asIdeal = ⊥
  · refine Or.inl ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K), PrimeSpectrum.ext ?_⟩
    rw [h]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)
  · refine Or.inr (PrimeSpectrum.ext ?_)
    exact IsLocalRing.eq_maximalIdeal (x.isPrime.isMaximal h)

theorem spMap_closedPoint {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (f : A →+* B)
    [IsLocalHom f] : spMap f (IsLocalRing.closedPoint B) = IsLocalRing.closedPoint A :=
  IsLocalRing.comap_closedPoint f

theorem spMap_closedPoint_of_surjective {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) (hf : Function.Surjective f) :
    spMap f (IsLocalRing.closedPoint B) = IsLocalRing.closedPoint A :=
  haveI : (IsLocalRing.closedPoint B).asIdeal.IsMaximal := IsLocalRing.maximalIdeal.isMaximal B
  PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective f hf))

theorem mk_le_continuum_of_finite {A B : Type} [CommRing A] [CommRing B] (g : A →+* B) (hg : g.Finite)
    (hA : Cardinal.mk A ≤ Cardinal.continuum) : Cardinal.mk B ≤ Cardinal.continuum := by
  letI := g.toAlgebra
  haveI : Module.Finite A B := hg
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A B
  refine (Cardinal.mk_le_of_surjective hf).trans ?_
  rw [show Cardinal.mk (Fin n → A) = Cardinal.mk A ^ n by simp]
  exact (pow_le_pow_left' hA n).trans (Cardinal.power_nat_le Cardinal.aleph0_le_continuum)

theorem mem_range_of_map {R K A B : Type} [CommRing R] [IsDomain R] [ValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [CommRing A] [IsDomain A] [Field B] [Algebra A B] [IsFractionRing A B] (e : R →+* A)
    [IsLocalHom e] (la : K →+* B) (hla : ∀ r, la (algebraMap R K r) = algebraMap A B (e r)) (x : K)
    (hx : la x ∈ (algebraMap A B).range) : x ∈ (algebraMap R K).range := by
  rcases ValuationRing.isInteger_or_isInteger R x with ⟨r, hr⟩ | ⟨r, hr⟩
  · exact ⟨r, hr⟩
  by_cases h0 : x = 0
  · exact ⟨0, by simp [h0]⟩
  obtain ⟨t, ht⟩ := hx
  have h1 : algebraMap A B (e r * t) = 1 := by
    rw [map_mul, ht, ← hla, show algebraMap R K r = x⁻¹ from hr, ← map_mul, inv_mul_cancel₀ h0, map_one]
  have h2 : e r * t = 1 := IsFractionRing.injective A B (h1.trans (map_one _).symm)
  have hu : IsUnit r := isUnit_of_map_unit e r (IsUnit.of_mul_eq_one _ h2)
  obtain ⟨u, rfl⟩ := hu
  refine ⟨(u⁻¹ : Rˣ), ?_⟩
  have h3 : algebraMap R K ((u⁻¹ : Rˣ) : R) * x⁻¹ = 1 := by
    rw [← show algebraMap R K u = x⁻¹ from hr, ← map_mul, Units.inv_mul, map_one]
  exact (mul_inv_eq_one₀ (inv_ne_zero h0 |> fun h => by simpa using h)).1 h3

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem range_j_subset {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) :
    Set.range Y.j ⊆ abLocus Y.t.G := by
  rintro _ ⟨x, rfl⟩
  have h : Y.jQ x ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
    rw [Y.ab_gen]; exact ⟨x, rfl⟩
  rw [Model.j, Scheme.Hom.comp_apply]
  exact h

theorem exists_frac_lift {A K L : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] [Field L]
    (f : A →+* L) (hf : Function.Injective f) : ∃ fK : K →+* L, fK.comp (algebraMap A K) = f :=
  ⟨IsFractionRing.lift hf, RingHom.ext fun x => by rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap hf x]⟩

theorem exists_away_lift {A S L : Type} [CommRing A] [CommRing S] [Algebra A S] (x : A) [IsLocalization.Away x S]
    [CommRing L] (f : A →+* L) (hf : IsUnit (f x)) : ∃ F : S →+* L, ∀ a, F (algebraMap A S a) = f a :=
  ⟨IsLocalization.Away.lift x hf, IsLocalization.Away.lift_eq x hf⟩

theorem isUnit_map_X {A : Type} [CommRing A] (κ : A →+* ℂ) :
    IsUnit ((HahnSeries.ofPowerSeries ℤ ℂ).comp (PowerSeries.map κ) PowerSeries.X) := by
  rw [RingHom.comp_apply, PowerSeries.map_X, HahnSeries.ofPowerSeries_X]
  exact isUnit_iff_ne_zero.2 (HahnSeries.single_ne_zero one_ne_zero)

end GlobalTheory.ArcIntegral
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.CopyRead

section Copy

variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {px : PreX B.toPre} {I : ColIn B px} {hX : B.fields.Ok} {T : TwDat B}
  {Wt : Set B.places.Pl}

def cpR (z : Dat a.st I hX T Wt) :
    @RealDat3 b.st.toD7 _ _ _ _ _ _ (famR b.st I hX (usedOf I T Wt) z.Xg z.tr) (coreJ b z.core).Q.c.F _ _ ((by exact @alg B C a b (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instField (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instNF (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (Formalism.L2.Pj.instCMHost (@Late.st B C a).toD7) (@Formalism.L2.Pj.Par.H (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.l (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.c (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instField (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instNF (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (Formalism.L2.Pj.instCMHost (@Late.st B C a).toD7) (@Formalism.L2.Pj.Par.H (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.l (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.c (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))))) (@Dat.alg (@Late.st B C a) px I hX T Wt z))) :=
  (by with_unfolding_all exact ((real3 b (iK := z.alg) z.R) :))



theorem rrT_copy (z₀ : Dat a.st I hX T Wt) (z : Dat b.st I hX T Wt) (h1 : z.Xg = z₀.Xg) (h2 : z.tr = z₀.tr)
    (h3 : HEq z.core (coreJ b z₀.core)) (h4 : HEq z.R (real3 b (iK := z₀.alg) z₀.R)) (y₀ : Hd z₀.R.toRealDat) (bb : Bool) (E : Hs)
    (jE : E.T →ₗ[ℂ] (y₀.C z₀.F.lv2).Amb 0) (n : ℕ) (c : Module.Basis (Fin n) ℂ E.T)
    (Xo : InfinitePlace B.LL → Matrix (Fin n) (Fin n) ℂ) (h : RrT z₀.F y₀ bb jE n c Xo) :
    ∀ (y : Hd z.R.toRealDat) (jE' : E.T →ₗ[ℂ] (y.C z.F.lv2).Amb 0), HEq jE' jE → RrT z.F y bb jE' n c Xo := by
  obtain @⟨Xg, tr, core, al, alg_eq, R, cG, geo, pins, lev, idG, good, mu, l1, l2⟩ := z
  dsimp only at h1 h2 h3 h4
  subst h1 h2
  obtain rfl : core = coreJ b z₀.core := eq_of_heq h3
  have e : al = (by with_unfolding_all exact ((alg b z₀.alg) :)) := by
    refine Algebra.algebra_ext _ _ fun y => B.embLL.injective ?_
    exact (alg_eq y).trans ((by with_unfolding_all exact ((z₀.alg_eq ((y))).symm : _)))
  subst e
  obtain rfl : R = cpR b z₀ := eq_of_heq (h4.trans ((by with_unfolding_all exact ((HEq.refl (cpR b z₀)) :))))
  intro y jE' hj
  exact (by with_unfolding_all exact (((@rr_eta_tr B C a b _ _ _ _ _ _ _ _ _ z₀.alg _ z₀.R z₀.F).2 y₀ ((y)) bb E jE ((jE')) n c ((Xo)) ((hj)) h) : _))

end Copy



theorem coords {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
    {Y : Read (A3 := A3) R.toRealDat F.lv2 X0} (Z : RationalReadingWithoutCongruence R F X0 Y) (y : Hd R.toRealDat)
    (heq_eigen_embedding_zero : D.what₂.EE0 →ₗ[ℂ] (y.C F.lv2).Amb 0) (hinj : Function.Injective heq_eigen_embedding_zero) (n : ℕ) (c : Module.Basis (Fin n) ℂ D.what₂.EE0)
    (Xo : InfinitePlace D.what₂.LL → Matrix (Fin n) (Fin n) ℂ) (h : RrT F y false (E := ⟨D.what₂.EE0⟩) heq_eigen_embedding_zero n c Xo)
    (hz : ∀ v, HEq (Y.Iz.jE v).1 (heq_eigen_embedding_zero v)) :
    ∃ ε : X0.s.RR.V ≃ₗ[D.what₂.LL] (Fin n → D.what₂.LL), (∀ x, X0.s.jEE x = ∑ i, D.what₂.embLL (ε x i) • c i) ∧
      ∀ v, v ≠ A3.A.v0 → ∀ x x', Formalism.HermitianLatticesTheory.majAt X0.s.RR.b X0.s.RR.X v x x' =
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL (Fin n)) Xo v (ε x) (ε x') := by
  obtain ⟨rfl, a0, b0⟩ := h
  refine ⟨Z.eRR0.symm, fun x => hinj ?_, fun v hv x x' => ?_⟩
  · have h := Z.jEE0 (Z.eRR0.symm x)
    rw [Z.eRR0.apply_symm_apply] at h
    exact (eq_of_heq (hz _)).symm.trans (h.trans (a0 (Z.eRR0.symm x)).symm)
  · have h := Z.met0 v hv (Z.eRR0.symm x) (Z.eRR0.symm x')
    rw [Z.eRR0.apply_symm_apply, Z.eRR0.apply_symm_apply] at h
    exact h.trans (GoodSideLattices.majAt_cast rfl _ Xo v (b0 v).1 _ _).symm

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z₀ : w.Lt} {hX : B.fields.Ok} {Wt : Set B.places.Pl}
  {z₀ : Dat (w.st Z₀) w.I hX T Wt} {q : RowPk w z₀}



theorem RRset_two {o o' : q.Over} (s : Side0 o) (s' : Side0 o') (μ : (w.D o.Z).what₂.Tup) :
    s.p0.s.RRset μ = (s'.p0.s.RRset μ) := by
  have h : ∀ k, s.p0.s.downTo μ k = (by with_unfolding_all exact ((s'.p0.s.downTo ((μ)) k) : _)) := by
    intro k
    induction k with
    | zero => exact (by with_unfolding_all exact ((Eq.refl (s.p0.s.downTo μ 0)) :))
    | succ k ih => exact (by with_unfolding_all exact ((congrArg (fun φ : type_of% (s.p0.s.downTo μ k) => φ.comp (s.p0.s.io μ k)) ih) :))
  have hi := congrArg (fun φ : type_of% (s.p0.s.downTo μ (w.D o.Z).R.m) =>
    (s.p0.s.multZero μ).toLinearEquiv.toLinearMap ∘ₗ φ ∘ₗ (s.p0.s.multTop μ).symm.toLinearEquiv.toLinearMap) (h (w.D o.Z).R.m)
  exact (by with_unfolding_all exact ((congrArg (fun φ : s.p0.s.Amb μ →ₗ[ℂ] (w.D o.Z).what₂.EE0 =>
    φ '' ((fun x => (s.p0.s.V0 μ ⊓ (s.p0.s.V0 μ ⊓ LinearMap.ker φ)ᗮ).starProjection x) ''
      ((s.p0.s.Mtilde μ).carrier ∩ (s.p0.s.V0 μ : Set (s.p0.s.Amb μ))))) hi) :))



theorem rrT_moved {o : q.Over} (m : Moved o) (hc : m.Copy) (hco : m.Coh) (b : Bool) {n c Xo}
    (h : RrT z₀.F q.y b (q.t.ch b).jE n c Xo) : RrT m.z.F m.y b (m.t.ch b).jE n c Xo :=
  rrT_copy (B := B) (C := w.C) (a := Z₀) o.Z z₀ m.z m.Xg m.tr ((by with_unfolding_all exact (hc.core :))) ((by with_unfolding_all exact (hc.R :))) q.y b _ _ n c Xo h m.y _ (hco.jE b)

theorem lat_tr {K : Type} [Field K] [NumberField K] [StarRing K] (e : K →+* ℂ) {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] {n : ℕ} (c : Module.Basis (Fin n) ℂ V) (Xo : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    {ι : Type} (P : ι → HeightOneSpectrum (𝓞 K)) {S S' : ι → Set V} (hS : S = S') {RR RR' : HLat K} (hR : RR' = RR)
    {j : RR.V →ₛₗ[e] V} {j' : RR'.V →ₛₗ[e] V} (hj : HEq j' j)
    (h : ∃ ε : RR.V ≃ₗ[K] (Fin n → K), (∀ x, j x = ∑ i, e (ε x i) • c i) ∧
      (∀ v, v ≠ InfinitePlace.mk e → ∀ x x', Formalism.HermitianLatticesTheory.majAt RR.b RR.X v x x' =
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) Xo v (ε x) (ε x')) ∧
      ∀ x : RR.V, x ∈ RR.L ↔ ∀ u, ∃ d : 𝓞 K, d ∉ (P u).asIdeal ∧ d • x ∈ Submodule.span (𝓞 K) {z | j z ∈ S u}) :
    ∃ ε : RR'.V ≃ₗ[K] (Fin n → K), (∀ x, j' x = ∑ i, e (ε x i) • c i) ∧
      (∀ v, v ≠ InfinitePlace.mk e → ∀ x x', Formalism.HermitianLatticesTheory.majAt RR'.b RR'.X v x x' =
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) Xo v (ε x) (ε x')) ∧
      ∀ x : RR'.V, x ∈ RR'.L ↔ ∀ u, ∃ d : 𝓞 K, d ∉ (P u).asIdeal ∧ d • x ∈ Submodule.span (𝓞 K) {z | j' z ∈ S' u} := by
  subst hS hR
  cases hj
  exact h



theorem good_copy {K : Ctx} {P : Pre2 K w} (x : St P) (N : NStage B w.C (P.q.W x.o.η x.o.hη)) (m : Moved (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over)) (hc : m.Copy)
    (hco : m.Coh) (s : Side0 (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over)) (hR : s.RR = x.s.RR) (hj : HEq s.jEE x.s.jEE) : GoodSideLattices.Good m s := by
  obtain ⟨n, c, Xo, h⟩ := rrT_exists (w.st P.Z₀).toD7 (Gc B w.px) (PlS B w.px) (PlI B w.px) (TupU w.I (usedOf w.I T P.Wt))
    (famR (w.st P.Z₀) w.I P.hX (usedOf w.I T P.Wt) P.z.Xg P.z.tr) P.z.core.Q.c.F P.z.R P.z.F P.z.cG P.z.pins P.intersectionNumber_baseChange P.q.y false
    (P.q.p.ch false).EE (P.q.t.ch false).jE (P.q.t.ch false).jE_inj (P.q.t.ch false).jE_range
  have h0 := rrT_moved x.m x.copy x.coh false h
  have h1 := rrT_moved m hc hco false h
  have h2 := coords x.r.Z x.m.y ((by with_unfolding_all exact ((x.m.t.ch false).jE :))) ((by with_unfolding_all exact ((x.m.t.ch false).jE_inj :))) n ((by with_unfolding_all exact (c :))) ((by with_unfolding_all exact (Xo :))) ((by with_unfolding_all exact (h0 :))) ((by with_unfolding_all exact (x.pin.heq_eigen_embedding_zero :)))
  obtain ⟨ε, h2, h3⟩ := h2
  have h4 : (fun u : B.places.Pl => ((by with_unfolding_all exact ((x.s.p0.s.RRset ((w.D x.o.Z).what₂.muAt u)) :)) : Set (P.q.p.ch false).EE.T)) =
      fun u => (by with_unfolding_all exact ((s.p0.s.RRset ((w.D (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))).what₂.muAt u)) :)) :=
    funext fun u => (by with_unfolding_all exact ((RRset_two x.s s ((w.D x.o.Z).what₂.muAt u)) :))
  have h5 := lat_tr (K := B.LL) B.embLL c Xo ((by with_unfolding_all exact ((fun u : B.places.Pl => (w.D x.o.Z).plEq u) :))) h4 hR hj
    ⟨(by with_unfolding_all exact (ε :)), (by with_unfolding_all exact (h2 :)), (by with_unfolding_all exact (h3 :)), (by with_unfolding_all exact (x.r.Z.rr0 :))⟩
  obtain ⟨ε', k1, k2, k3⟩ := h5
  exact ⟨n, c, Xo, ε', h1, k1, k2, (by with_unfolding_all exact (k3 :))⟩

end GlobalTheory.Mem.R3.Rw.CopyRead

end
end
