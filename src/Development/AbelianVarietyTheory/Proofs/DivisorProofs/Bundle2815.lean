module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2767
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle164
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2375
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CohomologyLogDerivativeAdjointEndomorphisms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle025
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle022
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.GlActionMemBalFormsOfSemilinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2719
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2721
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
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

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

namespace GlobalTheory.IntegralFamTriple

variable {R : Type} [CommRing R] [IsDomain R]

def Rel (Q : DegPre R) {k : ℕ} {β : Q.X} (σ : Q.SecB k β)
    (s : LB.Sec (LB.LinComb Q.P.L (DegPre.famφ Q (FractionRing R) β) (DegPre.famε k))) (r : R) : Prop :=
  ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF Q (FractionRing R)).left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι),
    Good Q.P.L z J → sval σ (x ≫ (DegPre.prB Q (FractionRing R)).left) z J =
      gs (x ≫ (DegPre.BF Q (FractionRing R)).hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) * sval s x z J

theorem gs_zero {Y Z : Scheme.{0}} (f : Z ⟶ Y) (z : Z) : gs f z ⊤ (0 : Γ(Y, ⊤)) = 0 := by
  rw [gs_eq f z ⊤ trivial, map_zero, map_zero]

theorem sval_secScale {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (c : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (DVR.SecOps.secScale c s) r z J = gs r z ⊤ c * sval s r z J :=
  (gs_mul r z _ (hJ.mem φ r) _ _).trans (congrArg (· * _) (gs_res r z le_top (hJ.mem φ r) c))

theorem rel_scale {Q : DegPre R} {k : ℕ} {β : Q.X} {σ : Q.SecB k β}
    {s : LB.Sec (LB.LinComb Q.P.L (DegPre.famφ Q (FractionRing R) β) (DegPre.famε k))} {r : R} (h : Rel Q σ s r) (a : R) :
    Rel Q (DVR.SecOps.secScale (Out.scal Q.P.A.hom a) σ) s (a * r) := by
  intro Z x z J hJ
  rw [sval_secScale _ _ _ _ hJ, h Z x z J hJ, ← _root_.mul_assoc, map_mul, gs_mul _ z ⊤ trivial]
  refine congrArg (· * _) (congrArg (· * _) ?_)
  have e : (x ≫ (DegPre.prB Q (FractionRing R)).left) ≫ Q.P.A.hom = x ≫ (DegPre.BF Q (FractionRing R)).hom := by
    rw [Category.assoc, Over.w]
  rw [← e]
  exact gs_pull _ Q.P.A.hom z ⊤ trivial _

theorem rel_cast {Q : DegPre R} {k : ℕ} {F : Fam Q (FractionRing R) k} {a b : Q.X} (h : a = b) (σ : Q.SecB k b)
    (e : Q.SecB k b = Q.SecB k a) {r : R} (H : Rel Q σ (F.s b) r) : Rel Q (cast e σ) (F.s a) r := by
  subst h
  simpa only [cast_eq] using H

theorem isUnit_gs {Q : DegPre R} {r : R} (hr : r ≠ 0) {Z : Scheme.{0}} (x : Z ⟶ (DegPre.BF Q (FractionRing R)).left) (z : Z) :
    IsUnit (gs (x ≫ (DegPre.BF Q (FractionRing R)).hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
  have e : x ≫ (DegPre.BF Q (FractionRing R)).hom =
      (x ≫ (fst (TF (R := R) (FractionRing R)) Q.P.A).left ≫ jFK (R := R) (FractionRing R)) ≫ jK R := by
    rw [← Over.w (fst (TF (R := R) (FractionRing R)) Q.P.A)]
    simp only [Category.assoc]
    rfl
  rw [e]
  set q := x ≫ (fst (TF (R := R) (FractionRing R)) Q.P.A).left ≫ jFK (R := R) (FractionRing R)
  rw [← gs_pull q (jK R) z ⊤ (Set.mem_univ _), gs_eq q z (jK R ⁻¹ᵁ ⊤) (Set.mem_univ _)]
  have n := congrArg (fun t => t.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n
  have u : IsUnit (algebraMap R (FractionRing R) r) := by
    have : algebraMap R (FractionRing R) r ≠ 0 := fun h0 =>
      hr (IsFractionRing.injective R (FractionRing R) (by rw [h0, map_zero]))
    exact this.isUnit
  have u' : IsUnit ((jK R).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
    rw [show jK R = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) from rfl, ← n]; exact u.map _
  exact (u'.map _).map _

theorem shiftEq_of_rel (Q : DegPre R) (k : ℕ) (F : Fam Q (FractionRing R) k) (mu α : Q.X) (r : R) (σ : Q.SecB k α)
    (σ₁ : Q.SecB k (α + k • mu)) (h₀ : Rel Q σ (F.s α) r) (h₁ : Rel Q σ₁ (F.s (α + k • mu)) r) :
    ShiftEq Q k mu α σ σ₁ 0 σ₁ := by
  intro u hu hc z J hJ
  have fe := (secRel_iff Q.P.isLB _ _ (F.s (α + k • mu)) _ _ (F.s α) (DegPre.trF Q (FractionRing R) mu).left _ _ u).1
    (F.fe mu α u hu hc) _ (𝟙 _) z J hJ
  have a₁ := h₁ _ (𝟙 _) z J hJ
  have a₀ := h₀ _ (DegPre.trF Q (FractionRing R) mu).left z J hJ
  have w : (DegPre.trF Q (FractionRing R) mu).left ≫ (DegPre.BF Q (FractionRing R)).hom =
      (DegPre.BF Q (FractionRing R)).hom := Over.w _
  simp only [Category.id_comp] at a₁ fe
  rw [w] at a₀
  have z0 : Out.scal (DegPre.BF Q (FractionRing R)).hom (0 : R) = 0 := by simp [Out.scal]
  rw [Over.comp_left, a₀, a₁, fe, z0, gs_zero, zero_mul, add_zero]
  ring

theorem exists_triple : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] (Dd : DegData R (maximalIdeal R)) (k : ℕ), 1 ≤ k → ∀ (mu mu' α : Dd.toPre.X), ∃ (σ : Dd.toPre.SecB k α) (σ₁ : Dd.toPre.SecB k (α + k • mu)) (σ₂ : Dd.toPre.SecB k (α + k • mu + k • mu')) (e : Dd.toPre.SecB k (α + k • mu + k • mu') = Dd.toPre.SecB k (α + k • (mu + mu'))), ShiftEq Dd.toPre k mu α σ σ₁ 0 σ₁ ∧ ShiftEq Dd.toPre k mu' (α + k • mu) σ₁ σ₂ 0 σ₂ ∧ ShiftEq Dd.toPre k (mu + mu') α σ (cast e σ₂) 0 (cast e σ₂) ∧ ∃ (z : (DegPre.BF Dd.toPre (FractionRing R)).left) (J : ((DegPre.BF Dd.toPre (FractionRing R)).left ⟶ Dd.toPre.P.A.left) → Dd.toPre.P.L.ι), Good Dd.toPre.P.L z J ∧ IsUnit (sval σ (DegPre.trF Dd.toPre (FractionRing R) (mu + mu') ≫ DegPre.prB Dd.toPre (FractionRing R)).left z J) := by
  intro R _ _ _ _ _ Dd k hk mu mu' α
  obtain ⟨s₀, hs₀⟩ := GlobalTheory.FamFree.exists_sec_ne_zero (D := Dd.toPre) (F := FractionRing R) GlobalTheory.CMClaims.secTwist hk α
  obtain ⟨F, hFα, -⟩ := GlobalTheory.FamFree.exists_fam_single GlobalTheory.CMClaims.laws.globalFns Dd.tau_bimult hk α s₀
  obtain ⟨r₀, hr₀, σ₀, h₀⟩ := GlobalTheory.T.exists_clear_denominator_bundleSection_genericFibre R Dd.toPre k α (F.s α)
  obtain ⟨r₁, hr₁, σ₁, h₁⟩ := GlobalTheory.T.exists_clear_denominator_bundleSection_genericFibre R Dd.toPre k (α + k • mu) (F.s (α + k • mu))
  obtain ⟨r₂, hr₂, σ₂, h₂⟩ := GlobalTheory.T.exists_clear_denominator_bundleSection_genericFibre R Dd.toPre k (α + k • (mu + mu')) (F.s (α + k • (mu + mu')))
  have g₀ := rel_scale (Q := Dd.toPre) (σ := σ₀) h₀ (r₁ * r₂)
  have g₁ := rel_scale (Q := Dd.toPre) (σ := σ₁) h₁ (r₀ * r₂)
  have g₂ := rel_scale (Q := Dd.toPre) (σ := σ₂) h₂ (r₀ * r₁)
  rw [show r₁ * r₂ * r₀ = r₀ * r₁ * r₂ by ring] at g₀
  rw [show r₀ * r₂ * r₁ = r₀ * r₁ * r₂ by ring] at g₁
  have hX : α + k • mu + k • mu' = α + k • (mu + mu') := by rw [smul_add, add_assoc]
  have e : Dd.toPre.SecB k (α + k • mu + k • mu') = Dd.toPre.SecB k (α + k • (mu + mu')) := by rw [hX]
  have g₂' := rel_cast (F := F) hX _ e.symm g₂
  refine ⟨_, _, cast e.symm (DVR.SecOps.secScale (Out.scal Dd.toPre.P.A.hom (r₀ * r₁)) σ₂), e,
    shiftEq_of_rel Dd.toPre k F mu α _ _ _ g₀ g₁,
    shiftEq_of_rel Dd.toPre k F mu' (α + k • mu) _ _ _ g₁ g₂', ?_, ?_⟩
  · rw [cast_cast, cast_eq]
    exact shiftEq_of_rel Dd.toPre k F (mu + mu') α _ _ _ g₀ g₂
  · obtain ⟨z, J, hJ, hu⟩ := GlobalTheory.T.exists_unit_value_translated_bundleSection R Dd.toPre k α (mu + mu') (F.s α) (by rw [hFα]; exact hs₀)
    refine ⟨z, J, hJ, ?_⟩
    rw [Over.comp_left, g₀ _ _ z J hJ]
    exact (isUnit_gs (mul_ne_zero (mul_ne_zero hr₀ hr₁) hr₂) _ z).mul hu

end GlobalTheory.IntegralFamTriple
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
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.KSCechData

open GlobalTheory.KS GlobalTheory.LogKSBal

theorem constFn_spMap {R K : Type} [CommRing R] [CommRing K] (x₀ : R →+* K) {Y : Scheme.{0}} (q : Y ⟶ Sp K)
    (O : Y.Opens) (r : R) : constFn (q ≫ spMap x₀) O r = constFn q O (x₀ r) := by
  refine ext_valR _ _ fun B _ y hy => ?_
  have e : y ≫ q = spMap (Spec.preimage (y ≫ q)).hom := (Spec.map_preimage _).symm
  generalize (Spec.preimage (y ≫ q)).hom = β at e
  rw [valR_constFn q y hy e, valR_constFn (q ≫ spMap x₀) y hy (β := β.comp x₀)
    (by rw [← Category.assoc, e, GlobalTheory.LogKSLoc.spMap_comp'])]
  rfl

theorem constFn_neg {K : Type} [CommRing K] {Y : Scheme.{0}} (q : Y ⟶ Sp K) (O : Y.Opens) (r : K) :
    constFn q O (-r) = -constFn q O r := by
  simp [constFn]

theorem exists_ksCoc_of_ksRel : ∀ {R : Type} [CommRing R] {K : Type} [Field K] (x₀ : R →+* K) (P : Out.PolAV (Sp R)) {A : Over (Sp K)} [GrpObj A] (m : A.left ⟶ P.A.left), m ≫ P.A.hom = A.hom ≫ spMap x₀ → ∀ {g : ℕ} (e : Fin g → Fld P.A.left) (dd : Fin g → ∀ O : A.left.Opens, Γ(A.left, O) → Γ(A.left, O)), (∀ a, IsField ⊤ (e a)) → (∀ a (O : P.A.left.Opens) (f : Γ(P.A.left, O)), dd a (m ⁻¹ᵁ O) ((m.app O).hom f) = pbT m (e a O f) (m ⁻¹ᵁ O)) → ∀ (D : Derivation ℤ R R) (M : Matrix (Fin g) (Fin g) R), KSRel P.A (𝟙 P.A.left) P.L e ⇑D M → ∃ L : LB P.A.left, Finite L.ι ∧ L.IsLB ∧ (∀ i, IsAffineOpen (L.U i)) ∧ LBIso P.L L ∧ ∃ d : L.ι → ∀ O : P.A.left.Opens, Γ(P.A.left, O) → Γ(A.left, m ⁻¹ᵁ O), ∀ φ, GlobalTheory.KS.IsDlog m L dd φ → GlobalTheory.KS.KSCoc A.hom P.A.hom m (fun r => x₀ (D r)) L.U dd d (fun a => GlobalTheory.KS.lc A.hom (fun b => -x₀ (M a b)) φ) := by
  intro R _ K _ x₀ P A _ m hm g e dd he hdd D M hKS
  obtain ⟨J, W, j, d, hcov, hWj, hlift, hdiff⟩ := hKS
  have := P.isAb.proper
  have : CompactSpace P.A.left := QuasiCompact.compactSpace_of_compactSpace P.A.hom
  have hloc : ∀ x : P.A.left, ∃ (Ω : P.A.left.Opens) (k : J), IsAffineOpen Ω ∧ x ∈ Ω ∧ Ω ≤ W k := by
    intro x
    have h2 : x ∈ ⨆ k, W k := by
      rw [hcov]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h2
    obtain ⟨_, ⟨Ω, hΩ, rfl⟩, hx, hle⟩ := P.A.left.isBasis_affineOpens.exists_subset_of_mem_open hk (W k).isOpen
    exact ⟨Ω, k, hΩ, hx, hle⟩
  obtain ⟨s, hfin, Ω, κ, hΩ, hΩW, hs⟩ : ∃ (s : Type) (_ : Finite s) (Ω : s → P.A.left.Opens) (κ : s → J),
      (∀ a, IsAffineOpen (Ω a)) ∧ (∀ a, Ω a ≤ W (κ a)) ∧ ⨆ a, Ω a = ⊤ := by
    choose Ω κ hΩ hxΩ hΩW using hloc
    obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => (Ω x : Set P.A.left))
      (fun x => (Ω x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hxΩ x⟩)
    refine ⟨s, inferInstance, fun a => Ω a, fun a => κ a, fun a => hΩ a, fun a => hΩW a, top_le_iff.1 fun x _ => ?_⟩
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, ha⟩, hxa⟩
  have hle : ∀ a : s, Ω a ≤ P.L.U (j (κ a)) := fun a => (hΩW a).trans (hWj (κ a))
  let L := GlobalTheory.FinAffineCharts.refineLB P.L Ω (fun a => j (κ a)) hle
  have happ : ∀ (O : P.A.left.Opens) (f : Γ(P.A.left, O)), (m.app O).hom f = pbT m f (m ⁻¹ᵁ O) :=
    fun O f => GlobalTheory.KS.AdjDlog.app_eq_pbT m O f
  have hconst : ∀ (O : P.A.left.Opens) (r : R), pbT m (constFn P.A.hom O r) (m ⁻¹ᵁ O) =
      constFn A.hom (m ⁻¹ᵁ O) (x₀ r) := fun O r => by
    rw [pbT_constFn _ _ le_rfl, hm, constFn_spMap]
  refine ⟨L, hfin, GlobalTheory.FinAffineCharts.refineLB_isLB P.isLB _ _ hle hs,
    fun a => hΩ a, GlobalTheory.FinAffineCharts.iso_refineLB P.isLB _ _ hle,
    fun a O f => pbT m (d (κ a) O f) _, fun φ hφ => ⟨fun a => ⟨fun O hO f f' => ?_, fun O hO f f' => ?_,
      fun O O' h hO f => ?_, fun O hO r => ?_⟩, fun a b O hO f => ?_⟩⟩
  · rw [(hlift _).1.1 _ (hO.trans (hΩW a)), pbT_add]
  · rw [(hlift _).1.2.1 _ (hO.trans (hΩW a)), pbT_add, pbT_mul, pbT_mul, happ, happ]
  · rw [(hlift _).1.2.2 _ _ h (hO.trans (hΩW a)), ← rsT_of_le h, pbT_rsT _ h le_rfl,
      rsT_pbT _ le_rfl (m.preimage_mono h)]
  · rw [(hlift _).2 _ (hO.trans (hΩW a)), hconst]
  · have hO' : O ≤ Ω a ⊓ Ω b := hO
    have hU : Ω a ⊓ Ω b ≤ P.L.U (j (κ a)) ⊓ P.L.U (j (κ b)) := inf_le_inf (hle a) (hle b)
    have hab : m ⁻¹ᵁ O ≤ m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b := m.preimage_mono hO
    have hab' : m ⁻¹ᵁ O ≤ m ⁻¹ᵁ (Ω a ⊓ Ω b) := m.preimage_mono hO
    have hg : (L.g a b).val = rsT (P.L.g (j (κ a)) (j (κ b))).val (Ω a ⊓ Ω b) :=
      GlobalTheory.KS.AdjDlog.val_res hU _
    have hφ' : ∀ c, rsT (φ c a b) (m ⁻¹ᵁ O) =
        pbT m (dlg P.A (𝟙 P.A.left) P.L (e c) (j (κ a)) (j (κ b)) O) (m ⁻¹ᵁ O) := fun c => by
      have h₁ : pbT m (L.g a b).val (m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b) * φ c a b =
          pbT m (e c (Ω a ⊓ Ω b) (L.g a b).val) (m ⁻¹ᵁ (Ω a ⊓ Ω b)) :=
        (hφ c a b).trans ((congrArg (dd c (m ⁻¹ᵁ (Ω a ⊓ Ω b))) (happ (Ω a ⊓ Ω b) (L.g a b).val).symm).trans
          (hdd c (Ω a ⊓ Ω b) (L.g a b).val))
      have h₂ : rsT (pbT m (L.g a b).val (m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b) * φ c a b) (m ⁻¹ᵁ O) =
          rsT (pbT m (e c (Ω a ⊓ Ω b) (L.g a b).val) (m ⁻¹ᵁ (Ω a ⊓ Ω b))) (m ⁻¹ᵁ O) :=
        congrArg (rsT · (m ⁻¹ᵁ O)) h₁
      have h₃ : rsT (pbT m (L.g a b).val (m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b)) (m ⁻¹ᵁ O) =
          pbT m (P.L.g (j (κ a)) (j (κ b))).val (m ⁻¹ᵁ O) :=
        (rsT_pbT m (O₀ := Ω a ⊓ Ω b) (fun p hp => hp) hab _).trans
          ((congrArg (pbT m · (m ⁻¹ᵁ O)) hg).trans (pbT_rsT m hU hab' _))
      have h₄ : rsT (e c (Ω a ⊓ Ω b) (L.g a b).val) O = e c O (rsT (P.L.g (j (κ a)) (j (κ b))).val O) := by
        refine (rsT_of_le hO' _).trans (((he c).2.2 _ _ hO' le_top _).symm.trans (congrArg (e c O) ?_))
        refine (rsT_of_le (O₀ := Ω a ⊓ Ω b) hO' _).symm.trans ?_
        rw [← rsT_rsT hU hO']
        exact congrArg (fun z => rsT z O) hg
      rw [rsT_mul, h₃, rsT_pbT m le_rfl hab', ← pbT_rsT m hO' le_rfl, h₄] at h₂
      rw [dlg, GlobalTheory.KS.AdjDlog.pbT_id _ _ (hO'.trans hU), GlobalTheory.KS.AdjDlog.pbT_id _ _ (hO'.trans hU), pbT_mul, ← h₂,
        pbT_rsT m (hO'.trans hU) le_rfl, mul_right_comm, ← pbT_mul, Units.mul_inv,
        pbT_one m (m.preimage_mono (hO'.trans hU)), _root_.one_mul]
    have key := hdiff (κ a) (κ b) O (hO'.trans (inf_le_inf (hΩW a) (hΩW b))) f
    rw [← pbT_sub, ← neg_sub, key, pbT_neg, pbT_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hdd, lc, rsT_sum, Finset.sum_mul, pbT_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [rsT_mul, rsT_constFn _ hab, hφ', pbT_mul, pbT_mul, hconst, constFn_neg]
    ring

end GlobalTheory.KSCechData
end
end

section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
open Matrix

namespace GlobalTheory.Poinc

theorem exists_pos_nat_mul_eq_int_family {κ : Type} [Fintype κ] (f : κ → ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∃ z : κ → ℤ, ∀ k, (z k : ℚ) = D * f k := by
  classical
  refine ⟨∏ k, (f k).den, Finset.prod_pos (fun k _ => (f k).den_pos),
    fun k => (f k).num * ((∏ k, (f k).den) / (f k).den : ℕ), fun k => ?_⟩
  obtain ⟨m, hm⟩ : (f k).den ∣ ∏ k, (f k).den := Finset.dvd_prod_of_mem _ (Finset.mem_univ k)
  dsimp only
  rw [hm, Nat.mul_div_cancel_left _ (f k).den_pos]
  push_cast
  rw [← Rat.mul_den_eq_num]
  ring

theorem int_matrix_rat_kernel_eq_zero {ι I : Type} [Fintype ι] [Fintype I] (A : Matrix ι I ℤ)
    (hA : ∀ x, A *ᵥ x = 0 → x = 0) (x : I → ℚ) (hx : A.map (Int.cast : ℤ → ℚ) *ᵥ x = 0) : x = 0 := by
  obtain ⟨D, hD, z, hz⟩ := exists_pos_nat_mul_eq_int_family x
  have h1 : A *ᵥ z = 0 := by
    funext i
    apply Int.cast_injective (α := ℚ)
    have := congrFun hx i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at this ⊢
    push_cast
    simp only [hz, mul_left_comm _ (D : ℚ), ← Finset.mul_sum, this, mul_zero]
  have h2 := hA z h1
  funext j
  have := hz j
  rw [h2, Pi.zero_apply, Int.cast_zero, eq_comm, mul_eq_zero] at this
  rcases this with h | h
  · exact absurd h (Nat.cast_ne_zero.mpr hD.ne')
  · exact h

theorem exists_vecMul_eq_nat_smul {ι I : Type} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]
    (A : Matrix ι I ℤ) (hA : ∀ x, A *ᵥ x = 0 → x = 0) (w : I → ℤ) :
    ∃ D : ℕ, 0 < D ∧ ∃ ν : ι → ℤ, ν ᵥ* A = (D : ℤ) • w := by
  set Aq := A.map (Int.cast : ℤ → ℚ) with hAq
  have hinj : Function.Injective Aq.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact int_matrix_rat_kernel_eq_zero A hA x hx
  let f : Module.Dual ℚ (I → ℚ) :=
    { toFun := fun x => (fun i => (w i : ℚ)) ⬝ᵥ x
      map_add' := fun x y => dotProduct_add _ _ _
      map_smul' := fun c x => by simp [dotProduct_smul] }
  obtain ⟨l, hl⟩ := LinearMap.dualMap_surjective_of_injective hinj f
  set lv : ι → ℚ := fun c => l (fun j => if c = j then 1 else 0) with hlvdef
  have hlv : ∀ y, l y = lv ⬝ᵥ y := by
    intro y
    rw [LinearMap.pi_apply_eq_sum_univ l y]
    simp [dotProduct, lv, mul_comm]
  have key : ∀ i, (w i : ℚ) = (lv ᵥ* Aq) i := by
    intro i
    have := LinearMap.congr_fun hl (Pi.single i 1)
    simp only [LinearMap.dualMap_apply, Matrix.mulVecLin_apply, hlv] at this
    rw [Matrix.dotProduct_mulVec, dotProduct_single, mul_one] at this
    rw [this]
    simp [f, dotProduct_single]
  obtain ⟨D, hD, ν, hν⟩ := exists_pos_nat_mul_eq_int_family lv
  refine ⟨D, hD, ν, ?_⟩
  funext i
  apply Int.cast_injective (α := ℚ)
  simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul]
  push_cast
  rw [key i]
  simp only [Matrix.vecMul, dotProduct, hν, Aq, Matrix.map_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros
  ring

theorem exists_nat_mul_eq_sum_of_injective {M ι : Type} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    [Fintype ι] [DecidableEq ι] (g : M →ₗ[ℤ] (ι → ℤ)) (hg : Function.Injective g) (w : M →ₗ[ℤ] ℤ) :
    ∃ D : ℕ, 0 < D ∧ ∃ ν : ι → ℤ, ∀ x, (D : ℤ) * w x = ∑ c, ν c * g x c := by
  classical
  set e := (Module.Free.chooseBasis ℤ M).equivFun with he
  set A := LinearMap.toMatrix' (g ∘ₗ e.symm.toLinearMap) with hAdef
  have hA : ∀ x, A *ᵥ x = 0 → x = 0 := by
    intro x hx
    rw [hAdef, LinearMap.toMatrix'_mulVec] at hx
    have h := hg (hx.trans (map_zero g).symm)
    simpa using h
  obtain ⟨D, hD, ν, hν⟩ :=
    exists_vecMul_eq_nat_smul A hA (fun i => w (e.symm (fun j => if i = j then 1 else 0)))
  refine ⟨D, hD, ν, fun x => ?_⟩
  have h1 : g x = A *ᵥ e x := by rw [hAdef, LinearMap.toMatrix'_mulVec]; simp
  have h2 : w x = ∑ i, e x i * w (e.symm (fun j => if i = j then 1 else 0)) := by
    have := LinearMap.pi_apply_eq_sum_univ (w ∘ₗ e.symm.toLinearMap) (e x)
    simpa using this
  have h3 : ∑ c, ν c * g x c = ν ⬝ᵥ (A *ᵥ e x) := by rw [h1]; rfl
  rw [h3, Matrix.dotProduct_mulVec, hν, h2]
  simp [dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]

theorem linForm_eq_sum_qW_lifts : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (N : ℕ) [NeZero N], 3 ≤ N →
    (∃ ε : Fin 8 → ℤ, Nat.Coprime N (2 * (∑ u, ∑ v, W u v * ε u * ε v).natAbs)) → ∀ r : ℕ,
    ∀ μ : ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) →
    ∀ ℓ : LinearMap.BilinForm ℤ (Fin r → ℤ) →ₗ[ℤ] ℤ, ∃ (D : ℕ) (ν : (Fin 8 → Fin r → ZMod N) → ℤ), 0 < D ∧
      ∀ b : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b x y = b y x) → (D : ℤ) * ℓ b = ∑ c, ν c * qW W b (μ c) := by
  intro W hW N hN0 hN hε r μ hμ ℓ
  let S : Submodule ℤ (LinearMap.BilinForm ℤ (Fin r → ℤ)) :=
    { carrier := {b | ∀ x y, b x y = b y x}
      add_mem' := by intro a b ha hb x y; simp [ha x y, hb x y]
      zero_mem' := by intro x y; simp
      smul_mem' := by intro c b hb x y; simp [hb x y] }
  let Φ : LinearMap.BilinForm ℤ (Fin r → ℤ) →ₗ[ℤ] ((Fin 8 → Fin r → ZMod N) → ℤ) :=
    { toFun := fun b c => qW W b (μ c)
      map_add' := by intro a b; funext c; simp [qW, mul_add, Finset.sum_add_distrib]
      map_smul' := by intro k b; funext c; simp [qW, Finset.mul_sum, mul_left_comm] }
  have hinj : Function.Injective (Φ ∘ₗ S.subtype) := by
    intro x y hxy
    apply Subtype.ext
    have hs : ∀ u v, ((x : LinearMap.BilinForm ℤ (Fin r → ℤ)) - (y : LinearMap.BilinForm ℤ (Fin r → ℤ))) u v = ((x : LinearMap.BilinForm ℤ (Fin r → ℤ)) - (y : LinearMap.BilinForm ℤ (Fin r → ℤ))) v u := by
      intro u v; simp [x.2 u v, y.2 u v]
    have h0 : ∀ c, qW W ((x : LinearMap.BilinForm ℤ (Fin r → ℤ)) - (y : LinearMap.BilinForm ℤ (Fin r → ℤ))) (μ c) = 0 := by
      intro c
      have := congrFun hxy c
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.coe_mk, AddHom.coe_mk, Φ] at this
      simp only [qW, LinearMap.sub_apply, mul_sub, Finset.sum_sub_distrib] at this ⊢
      rw [this, sub_self]
    exact sub_eq_zero.mp (GlobalTheory.T.symm_bilinForm_eq_zero_of_weightedQuadraticSum_lifts W hW N hN r hε μ hμ _ hs h0)
  obtain ⟨D, hD, ν, hν⟩ := exists_nat_mul_eq_sum_of_injective (Φ ∘ₗ S.subtype) hinj (ℓ ∘ₗ S.subtype)
  exact ⟨D, ν, hD, fun b hb => hν ⟨b, hb⟩⟩

end GlobalTheory.Poinc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.LeastVec

def cross {s : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X)
    (x y : Fin s → X) : ℤ :=
  ∑ u, ∑ v, W u v * (β (x u) (y v) + β (y u) (x v))

theorem qW_add_zsmul {s : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X)
    (x y : Fin s → X) (n : ℤ) :
    qW W β (x + n • y) = qW W β x + n * cross W β x y + n ^ 2 * qW W β y := by
  unfold qW cross
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, map_add (f := _), LinearMap.add_apply, map_zsmul, LinearMap.smul_apply, smul_eq_mul]
  ring

theorem least_lt_add_smul : ∀ (s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ), PosW W → ∀ (X : Type) [AddCommGroup X] (β : LinearMap.BilinForm ℤ X), (∀ a b, β a b = β b a) → (∀ a, 0 ≤ β a a) → ∀ (H : AddSubgroup (Fin s → X)), (∀ mu ∈ H, mu ≠ 0 → 0 < qW W β mu) → ∀ mu₀ ∈ H, mu₀ ≠ 0 → (∀ mu ∈ H, mu ≠ 0 → qW W β mu₀ ≤ qW W β mu) → ∀ N₁ : ℕ, 3 ≤ N₁ → ∀ nu ∈ H, nu ≠ 0 → qW W β mu₀ < qW W β (mu₀ + N₁ • nu) := by
  intro s W hW X _ β hs hβ H hpos mu₀ hmu₀ _ hmin N₁ hN nu hnu hnu0
  have hq := qW_add_zsmul W β mu₀ nu
  have h1 : 0 ≤ qW W β (mu₀ + nu) := qW_nonneg hW hs hβ _
  rw [← one_zsmul nu, hq 1] at h1
  simp only [one_mul, one_pow] at h1
  have hN' : qW W β (mu₀ + N₁ • nu) = qW W β mu₀ + (N₁ : ℤ) * cross W β mu₀ nu + (N₁ : ℤ) ^ 2 * qW W β nu := by
    rw [← hq, natCast_zsmul]
  rw [hN']
  have hle := hmin nu hnu hnu0
  have hp := hpos nu hnu hnu0
  have hN3 : (3 : ℤ) ≤ N₁ := by exact_mod_cast hN
  set B := cross W β mu₀ nu
  set q0 := qW W β mu₀
  set qn := qW W β nu
  have hNn : (0 : ℤ) ≤ N₁ := by omega
  have e1 : (N₁ : ℤ) * (-q0 - qn) ≤ (N₁ : ℤ) * B := mul_le_mul_of_nonneg_left (by linarith) hNn
  have e2 : (N₁ : ℤ) * q0 ≤ (N₁ : ℤ) * qn := mul_le_mul_of_nonneg_left hle hNn
  have e3 : 0 < (N₁ : ℤ) * ((N₁ : ℤ) - 2) * qn := by
    apply mul_pos (mul_pos (by omega) (by omega)) hp
  nlinarith

end GlobalTheory.Poinc.LeastVec
end
end

section

open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.exists_supportingForm_gap_off_smoothCone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (φ : InvFun O) (d : ℕ) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] [Module.Free ℤ X] [Module.Finite ℤ X], IsPolFanOn bar φ X → ∀ (r m : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X) (a : Fin m → X), IsCone bar φ γ → Supports bar φ d γ a → ∀ lam : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, (∀ j, 0 ≤ lam (γ j)) → ∀ K : ℤ, ∃ D₀ : ℕ, ∀ D, D₀ ≤ D → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → (D * d : ℝ) * φ.evalZ β ≤ (D * ∑ i, β (a i) (a i) + lam β : ℤ)) ∧ ∀ (ρ : LinearMap.BilinForm ℤ X), IsCone bar φ ![ρ] → (∀ j, ρ ≠ γ j) → (D * d : ℝ) * φ.evalZ ρ + K ≤ (D * ∑ i, ρ (a i) (a i) + lam ρ : ℤ) := by
  first | exact @GlobalTheory.Poinc.Gap.exists_gap | exact GlobalTheory.Poinc.Gap.exists_gap | (intros; apply GlobalTheory.Poinc.Gap.exists_gap <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.genericPoint_comp_structure_eq_specMap_constants : ∀ (X : Scheme.{0}) [IsIntegral X] (R : Type) [CommRing R] (p : X ⟶ Sp R), gp X ≫ p = spMap (cst p) := by
  first | exact @GlobalTheory.Desc.gp_comp_eq_spMap_cst | exact GlobalTheory.Desc.gp_comp_eq_spMap_cst | (intros; apply GlobalTheory.Desc.gp_comp_eq_spMap_cst <;> assumption)
end
