module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1109
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle357
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2294
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2293
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2289
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle381
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2353
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2299
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1069
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2650
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2651
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2652
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues

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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenericVal

theorem exists_affine_le_preimage {X : Scheme.{0}} {Ω : Type} [CommRing Ω] [IsLocalRing Ω] (x : Sp Ω ⟶ X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ ⊤ ≤ x ⁻¹ᵁ U := by
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := x.base (IsLocalRing.closedPoint Ω)) (U := ⊤) trivial
  refine ⟨U, hU, fun p _ => ?_⟩
  have hsp : (p : PrimeSpectrum Ω) ⤳ IsLocalRing.closedPoint Ω :=
    (PrimeSpectrum.le_iff_specializes (R := Ω) p (IsLocalRing.closedPoint Ω)).1
      (show p.asIdeal ≤ IsLocalRing.maximalIdeal Ω from IsLocalRing.le_maximalIdeal p.isPrime.ne_top)
  exact hsp.mem_open (x ⁻¹ᵁ U).isOpen hyU

theorem valR_generic : ∀ (X : Scheme.{0}) (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (x : Sp Ω ⟶ X) (dd : Fld X) (δ : Derivation ℤ Ω Ω) (δL : Derivation ℤ (FractionRing Ω) (FractionRing Ω)), IsField ⊤ dd → (∀ (O : X.Opens) (f : Γ(X, O)), ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd O f) = δ (valR x O f)) → (∀ ω, δL (algebraMap Ω (FractionRing Ω) ω) = algebraMap Ω (FractionRing Ω) (δ ω)) → ∀ (O : X.Opens) (f : Γ(X, O)), ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) ⁻¹ᵁ O → valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) O (dd O f) = δL (valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) O f) := by
  intro X Ω _ _ _ x dd δ δL hF hx hδL O f hO
  obtain ⟨U, hU, hxU⟩ := exists_affine_le_preimage x
  set ξ := spMap (algebraMap Ω (FractionRing Ω)) ≫ x with hξ
  have hξU : ⊤ ≤ ξ ⁻¹ᵁ U := fun q _ => hxU (show (spMap (algebraMap Ω (FractionRing Ω))).base q ∈ (⊤ : (Sp Ω).Opens) from trivial)
  let q₀ : Sp (FractionRing Ω) := default
  have hq : ξ.base q₀ ∈ O ⊓ U := ⟨hO trivial, hξU trivial⟩
  obtain ⟨s, hsle, hsmem⟩ := hU.exists_basicOpen_le (V := O ⊓ U) ⟨ξ.base q₀, hq⟩ hq.2
  set W := X.basicOpen s with hWdef
  have hWO : W ≤ O := hsle.trans inf_le_left
  have hWU : W ≤ U := X.basicOpen_le s
  have hW : ⊤ ≤ ξ ⁻¹ᵁ W := fun q _ => by
    rw [Subsingleton.elim q q₀]; exact hsmem
  letI : Algebra Γ(X, U) Γ(X, W) := (resG X hWU).toAlgebra
  haveI : IsLocalization.Away s Γ(X, W) := hU.isLocalization_basicOpen s
  obtain ⟨⟨a, m⟩, hm⟩ := IsLocalization.surj (Submonoid.powers s) (resG X hWO f)
  have hmu : IsUnit (resG X hWU (m : Γ(X, U))) := IsLocalization.map_units Γ(X, W) m
  change resG X hWO f * resG X hWU (m : Γ(X, U)) = resG X hWU a at hm
  have vres : ∀ {V' : X.Opens} (e : W ≤ V') (g : Γ(X, V')), valR ξ W (resG X e g) = valR ξ V' g :=
    fun e g => GlobalTheory.Points.valR_res ξ e hW g
  have vU : ∀ g : Γ(X, U), valR ξ U g = algebraMap Ω (FractionRing Ω) (valR x U g) := fun g =>
    GlobalTheory.Points.valR_spMap_comp _ x U hxU g
  have hdd : ∀ g : Γ(X, U), dd W (resG X hWU g) = resG X hWU (dd U g) := fun g => hF.2.2 U W hWU le_top g
  have hddO : dd W (resG X hWO f) = resG X hWO (dd O f) := hF.2.2 O W hWO le_top f
  have hL := hF.2.1 W le_top (resG X hWO f) (resG X hWU (m : Γ(X, U)))
  rw [hm, hdd, hdd, hddO] at hL
  have e1 := congrArg (valR ξ W) hL
  have e2 := congrArg (valR ξ W) hm
  simp only [GlobalTheory.Points.valR_add ξ W hW, GlobalTheory.Points.valR_mul ξ W hW, vres, vU, hx U _ hxU] at e1 e2
  have hM : IsUnit (algebraMap Ω (FractionRing Ω) (valR x U (m : Γ(X, U)))) := by
    have h1 := hmu.map (GlobalTheory.Points.valMap ξ W hW).hom
    rwa [← GlobalTheory.Points.valR_eq, vres, vU] at h1
  have e3 := congrArg δL e2
  rw [Derivation.leibniz, hδL, hδL, smul_eq_mul, smul_eq_mul] at e3
  apply hM.mul_left_cancel
  linear_combination -e1 - e3

end GlobalTheory.GenericVal
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

namespace GlobalTheory.SecScalVal

theorem val_of_secScal : ∀ (X₂ Y : Scheme.{0}) (L₂ : LB X₂) (f₂ : Y ⟶ X₂) (k : ℕ) (σ : SecM (𝟙 X₂) L₂ k) (s : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ)))) (c : Γ(Y, ⊤)), GeneratorPullback.SecScal L₂ (fun _ : Fin 1 => f₂) (fun _ => (k : ℤ)) s (fun _ : Fin 1 => 𝟙 X₂) (fun _ => (k : ℤ)) σ f₂ c → ∀ (F : Type) [CommRing F] (ξ : Sp F ⟶ Y) (i : L₂.ι), ⊤ ≤ (ξ ≫ f₂) ⁻¹ᵁ L₂.U i → valR (ξ ≫ f₂) _ (σ.f fun _ => i) = valR ξ ⊤ c * valR ξ _ (s.f fun _ => i) := by
  intro X₂ Y L₂ f₂ k σ s c hs F _ ξ i hi
  have hc := hs (fun _ => i) (fun _ => i) (fun a b _ => by rcases a <;> rcases b <;> rfl)
  have hW : ⊤ ≤ ξ ⁻¹ᵁ (LB.wchart L₂ (fun _ : Fin 1 => f₂) (fun _ => i) ⊓
      LB.wchart L₂ (fun _ : Fin 1 => f₂ ≫ 𝟙 X₂) (fun _ => i)) := by
    intro y _
    have hy := hi (Set.mem_univ y)
    refine ⟨Set.mem_iInter.2 fun _ => ?_, Set.mem_iInter.2 fun _ => ?_⟩
    · simpa using hy
    · simpa using hy
  have hv := congrArg (valR ξ _) hc
  rw [GlobalTheory.ZH.CrdCalc.valR_mul ξ _ hW] at hv
  erw [GlobalTheory.ZH.CrdCalc.valR_res ξ _ hW, GlobalTheory.ZH.CrdCalc.valR_res ξ _ hW,
    GlobalTheory.ZH.CrdCalc.valR_res ξ _ hW] at hv
  have hσ : ⊤ ≤ ξ ⁻¹ᵁ f₂ ⁻¹ᵁ LB.wchart L₂ (fun _ : Fin 1 => 𝟙 X₂) (fun _ => i) :=
    hW.trans (ξ.preimage_mono (inf_le_right.trans
      (fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k)))
  have hσ' : ⊤ ≤ (ξ ≫ f₂) ⁻¹ᵁ LB.wchart L₂ (fun _ : Fin 1 => 𝟙 X₂) (fun _ => i) := hσ
  rw [GlobalTheory.ZH.CrdCalc.valR_eq ξ _ hσ] at hv
  exact (GlobalTheory.ZH.CrdCalc.valR_eq (ξ ≫ f₂) _ hσ' _).trans hv

end GlobalTheory.SecScalVal
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

namespace GlobalTheory.FormalOrigin

theorem exists_formalPoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → IsIntegral G.left → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (D : R → R) (W : G.left.Opens) (d : Fld G.left), IsLift G D W d → ⊤ ≤ (η[G]).left ⁻¹ᵁ W → ∃ (Ω : Type) (_ : CommRing Ω) (_ : IsDomain Ω) (_ : IsLocalRing Ω) (φ : R →+* Ω) (x : Sp Ω ⟶ G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dΩ : Derivation ℤ Ω Ω), IsAdicComplete ((maximalIdeal R).map φ) Ω ∧ x ≫ G.hom = spMap φ ∧ ⊤ ≤ x ⁻¹ᵁ W ∧ (∀ r, dΩ (φ r) = φ (D r)) ∧ (∀ a r, δ a (φ r) = 0) ∧ (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) ∧ (∀ O f, O ≤ W → ⊤ ≤ x ⁻¹ᵁ O → valR x O (d O f) = dΩ (valR x O f)) ∧ ∀ O (f : Γ(G.left, O)), ⊤ ≤ x ⁻¹ᵁ O → valR x O f = 0 → f = 0 := by
  intro R _ _ _ _ _ _ G _ _ hsm hint n v dd hdd D W d hd hW
  have hx0W : origin G ∈ W := hW (show IsLocalRing.closedPoint R ∈ (⊤ : (Sp R).Opens) from trivial)
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  obtain ⟨D', hD'⟩ := GlobalTheory.T.exists_derivation_of_vectorFieldLift_near_unit R G D W d hd hW
  choose δ hδ using fun a => GlobalTheory.T.exists_stalk_derivation_of_vectorFieldOnOpen G.left ⊤ (dd a) (hdd a).1 (origin G) trivial
  obtain ⟨dA, hdA⟩ := GlobalTheory.T.exists_stalk_derivation_of_vectorFieldOnOpen G.left W d hd.1 (origin G) hx0W
  have hcomm : ∀ a b s, δ a (δ b s) = δ b (δ a s) := by
    intro a b s
    obtain ⟨O, hO, f, rfl⟩ := TopCat.Presheaf.germ_exist G.left.presheaf s
    rw [hδ b O hO le_top, hδ a O hO le_top, hδ a O hO le_top, hδ b O hO le_top,
      GlobalTheory.T.invariantVectorFields_commute_of_commGroupScheme R G (v a) (v b) (dd a) (dd b) (hdd a) (hdd b)]
  have hconst : ∀ a r, δ a (constO G r) = 0 := by
    intro a r
    rw [← GlobalTheory.T.germ_origin_constantSection_eq_originStalkConstants R G ⊤ trivial r, hδ a ⊤ trivial le_top, GlobalTheory.T.invariantVectorField_apply_constant_eq_zero R G (v a) (dd a) (hdd a), map_zero]
  have hdc : ∀ r, dA (constO G r) = constO G (D' r) := by
    intro r
    rw [← GlobalTheory.T.germ_origin_constantSection_eq_originStalkConstants R G W hx0W r, hdA W hx0W le_rfl, hd.2 W le_rfl, ← hD', GlobalTheory.T.germ_origin_constantSection_eq_originStalkConstants]
  obtain ⟨z, hz0, hz1, hm⟩ := GlobalTheory.T.smooth_commGroup_local_coordinates_at_origin R G hsm n v dd hdd δ (fun a O hO f => hδ a O hO le_top f)
  obtain ⟨T, hT⟩ := GlobalTheory.T.exists_ringHom_eq_taylor _ R n (evO G) δ
  have hTC : ∀ r, T (constO G r) = MvPowerSeries.C r := by
    intro r
    rw [hT, GlobalTheory.T.derivationTaylorPowerSeries_of_derivations_kill _ R n (evO G) δ _ (fun i => hconst i r), GlobalTheory.T.groupSchemeStalkEvalAtOrigin_originStalkConstants]
  have hT0 : ∀ s, MvPowerSeries.constantCoeff (T s) = evO G s := by
    intro s
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hT]
    show (∏ i, (((0 : Fin n →₀ ℕ) i).factorial : ℚ))⁻¹ • evO G (iterOp _ 0 s) = _
    rw [iterOp_zero]
    simp
  haveI : IsLocalHom (evO G) := Scheme.isLocalHom_stalkClosedPointTo (R := CommRingCat.of R) (η[G]).left
  have : IsLocalHom T := ⟨fun s hs => by
    have h1 : IsUnit (evO G s) := by rw [← hT0]; exact (MvPowerSeries.isUnit_iff_constantCoeff).1 hs
    exact (isUnit_map_iff (evO G) s).1 h1⟩
  obtain ⟨dΩ, hdΩC, hdΩ⟩ := GlobalTheory.T.derivation_extends_taylorPowerSeriesRing R _ (constO G) (evO G) (GlobalTheory.T.groupSchemeStalkEvalAtOrigin_originStalkConstants R G) n δ z hz0 hz1 hm hconst dA D' hdc
  have hval : ∀ (O : G.left.Opens) (hO : origin G ∈ O) (f : Γ(G.left, O)),
      valR (spMap T ≫ G.left.fromSpecStalk (origin G)) O f = T ((G.left.presheaf.germ O (origin G) hO).hom f) :=
    fun O hO f => GlobalTheory.FlagBundle.valR_spMap_fromSpecStalk T hO f
  have htop : ∀ O : G.left.Opens, ⊤ ≤ (spMap T ≫ G.left.fromSpecStalk (origin G)) ⁻¹ᵁ O → origin G ∈ O :=
    fun O h => (GlobalTheory.T.preimage_spMap_fromSpecStalk_whole_iff_mem G.left (origin G) _ T inferInstance O).1 h
  refine ⟨MvPowerSeries (Fin n) R, inferInstance, NoZeroDivisors.to_isDomain _, inferInstance, MvPowerSeries.C,
    spMap T ≫ G.left.fromSpecStalk (origin G), fun a => intDer (MvPowerSeries.pderiv (R := R) a), intDer dΩ,
    GlobalTheory.T.mvPowerSeries_isAdicComplete_map_C_of_noetherian R _ ‹_› n, ?_, (GlobalTheory.T.preimage_spMap_fromSpecStalk_whole_iff_mem G.left (origin G) _ T inferInstance W).2 hx0W, fun r => ?_, fun a r => ?_,
    fun a O f hO => ?_, fun O f hOW hO => ?_, fun O f hO hf => ?_⟩
  · rw [Category.assoc, GlobalTheory.T.spec_map_fromSpecStalk_origin_comp_structure_eq R G _ T]
    congr 1
    exact RingHom.ext hTC
  · rw [← hD']; exact hdΩC r
  · exact MvPowerSeries.pderiv_C
  · have h := htop O hO
    rw [hval O h, hval O h, ← hδ a O h le_top, hT, hT, GlobalTheory.T.derivationTaylorPowerSeries_derivation_eq_pderiv _ R n (evO G) δ hcomm]
    rfl
  · have h := htop O hO
    rw [hval O h, hval O h, ← hdA O h hOW, hT, hT]
    exact (hdΩ _).symm
  · have h := htop O hO
    rw [hval O h, hT] at hf
    have h0 := GlobalTheory.T.derivationTaylorPowerSeries_injective_localRing R _ (constO G) (evO G) (GlobalTheory.T.groupSchemeStalkEvalAtOrigin_originStalkConstants R G) n δ z hz0 hz1 hm _ hf
    exact germ_injective_of_isIntegral G.left (origin G) h (h0.trans (map_zero _).symm)

end GlobalTheory.FormalOrigin
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

namespace GlobalTheory.Heat.Adjust

theorem valR_const {K R : Type} [CommRing K] [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp K) (f : K →+* R)
    (q : Sp R ⟶ X) (hq : q ≫ p = spMap f) (U : X.Opens)
    (h : ⊤ ≤ q ⁻¹ᵁ U) (a : K) : valR q U (constFn p U a) = f a := by
  refine (HolHom.valR_appLE q p ⊤ U le_top _ h).trans ?_
  rw [hq, ← Category.comp_id (spMap f),
    HolHom.valR_spMap f (𝟙 _) ⊤ le_rfl, HolHom.valR_eq _ _ le_rfl]
  congr 1
  exact congrArg (fun g : CommRingCat.of K ⟶ CommRingCat.of K => g.hom a)
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv_hom_id

theorem eq_zero_of_valR_points {X : Scheme.{0}} (U : X.Opens) (s : Γ(X, U))
    (h : ∀ (S : Type) [CommRing S] (g : Sp S ⟶ X), ⊤ ≤ g ⁻¹ᵁ U → valR g U s = 0) : s = 0 := by
  refine GlobalTheory.KS.eq_of_rsT_eq (J := {W : X.affineOpens // W.1 ≤ U}) (fun W => W.1.1) (fun W => W.2) ?_ s 0 ?_
  · intro x hx
    obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨W, hW⟩, hWU⟩, hxW⟩
  · rintro ⟨⟨W, hW⟩, hWU⟩
    have hW' : IsAffineOpen W := hW
    have hle : ⊤ ≤ hW'.fromSpec ⁻¹ᵁ W := hW'.fromSpec_preimage_self.ge
    have e := h Γ(X, W) hW'.fromSpec (hle.trans (hW'.fromSpec.preimage_mono hWU))
    rw [← HolHom.valR_res (A := Γ(X, W)) hW'.fromSpec hWU s hle, HolHom.valR_eq _ _ hle, HolHom.evalHom] at e
    rw [GlobalTheory.KS.rsT_zero, GlobalTheory.KS.rsT_of_le hWU]
    have e2 : hW'.fromSpec.appLE W ⊤ hle = (Scheme.ΓSpecIso Γ(X, W)).inv := by
      rw [Scheme.Hom.appLE, hW'.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
      exact (congrArg _ ((Spec Γ(X, W)).presheaf.map_id _)).trans (Category.comp_id _)
    erw [e2] at e
    erw [Iso.inv_hom_id] at e
    exact e

theorem inv_constFn {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (v : TanM (𝟙 (Sp R)) G)
    (dd : Fld G.left) (hinv : IsInv G v dd) (V : G.left.Opens) (r : R) : dd V (constFn G.hom V r) = 0 := by
  refine eq_zero_of_valR_points _ _ fun S _ a hV => ?_
  obtain ⟨φ', hφ'⟩ := Spec.map_surjective (R := CommRingCat.of R) (S := CommRingCat.of S) (a ≫ G.hom)
  let φ : R →+* S := φ'.hom
  have hφ : a ≫ G.hom = spMap φ := hφ'.symm
  let x : Over.mk (spMap φ) ⟶ G := Over.homMk a hφ
  let φε : R →+* DualNumber S := (algebraMap S (DualNumber S)).comp φ
  let π : Over.mk (spMap φε) ⟶ Over.mk (spMap φ) :=
    Over.homMk (spMap (algebraMap S (DualNumber S))) (by
      show spMap (algebraMap S (DualNumber S)) ≫ spMap φ = spMap φε
      simp only [spMap, φε, ← Spec.map_comp]; rfl)
  let ie : Over.mk (spMap φ) ⟶ Over.mk (spMap φε) :=
    Over.homMk (spMap (TrivSqZeroExt.fstHom S S S).toRingHom) (by
      show spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap φε = spMap φ
      simp only [spMap, φε, ← Spec.map_comp]
      congr 1)
  obtain ⟨v'', hv₁, hv₂⟩ := InvWt.exists_tan_over G v φ
  have hιπ : ie ≫ π = 𝟙 _ := by
    ext1
    show spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _
    simp only [spMap, ← Spec.map_comp]
    rw [← Spec.map_id]; congr 1
  have hiev : ie ≫ v'' = 1 := by
    ext1
    exact hv₂
  have hW : ie ≫ (π ≫ x * v'') = x := by
    rw [MonObj.comp_mul, ← Category.assoc, hιπ, Category.id_comp, hiev, _root_.mul_one]
  have hWa : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ (π ≫ x * v'').left = a :=
    congrArg (·.left) hW
  have htr : IsTr G φ a v (π ≫ x * v'').left := by
    let e : tEpsG (a ≫ G.hom) ⟶ Over.mk (spMap φε) := Over.homMk (𝟙 _) (by
      show 𝟙 _ ≫ spMap φε = spMap (algebraMap S (DualNumber S)) ≫ a ≫ G.hom
      rw [hφ]
      simp only [Category.id_comp, spMap, φε]
      rw [← Spec.map_comp]; rfl)
    refine ⟨e ≫ π ≫ x, e ≫ v'', ?_, ?_, ?_⟩
    · show 𝟙 _ ≫ spMap (algebraMap S (DualNumber S)) ≫ a = _
      rw [Category.id_comp]
    · show 𝟙 _ ≫ v''.left = _
      rw [Category.id_comp, hv₁]
    · rw [← MonObj.comp_mul]
      show 𝟙 _ ≫ _ = _
      rw [Category.id_comp]
  rw [← hinv.2 S φ a (π ≫ x * v'').left V _ hφ hV htr,
    valR_const G.hom φε _ (Over.w (π ≫ x * v'')) V (InvWt.top_le_preimage_of_fst _ a V hWa hV)]
  simp [φε, TrivSqZeroExt.algebraMap_eq_inl]

theorem isField_add_comb {Z : Scheme.{0}} {n : ℕ} {U : Z.Opens} (d₀ : Fld Z) (dd : Fin n → Fld Z)
    (y : Fin n → Γ(Z, U)) (h₀ : IsField U d₀) (h : ∀ a, IsField ⊤ (dd a)) :
    IsField U (fun W f => d₀ W f + ∑ a, rsT (y a) W * dd a W f) := by
  refine ⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' hWW hW f => ?_⟩
  · simp only [h₀.1 W hW, fun a => (h a).1 W le_top, mul_add, Finset.sum_add_distrib]
    ring
  · simp only [h₀.2.1 W hW, fun a => (h a).2.1 W le_top, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    have e : ∀ (g : Γ(Z, W)) (u : Fin n → Γ(Z, W)), ∑ a, rsT (y a) W * (g * u a) = ∑ a, g * (rsT (y a) W * u a) :=
      fun g u => Finset.sum_congr rfl fun a _ => by ring
    rw [e, e]
    ring

  · simp only [h₀.2.2 W W' hWW hW, fun a => (h a).2.2 W W' hWW le_top, map_add (f := _), map_sum, map_mul]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← GlobalTheory.KS.rsT_of_le hWW (rsT (y a) W), GlobalTheory.KS.rsT_rsT hW hWW]

theorem isWt_rsT {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
    {oa : Q.OAct O} (Y : Ray oa) {α : Q.X} {V V' : Y.H.left.Opens} (h : V' ≤ V) {f : Γ(Y.H.left, V)}
    (hf : IsWt Y α V f) : IsWt Y α V' (rsT f V') := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [GlobalTheory.KS.rsT_of_le h]
  refine (HolHom.valR_res a' h f hV').trans (Eq.trans ?_ (congrArg _ (HolHom.valR_res a h f hV)).symm)
  exact hf S φ x x' c a a' ha ha' (hV.trans (a.preimage_mono h)) (hV'.trans (a'.preimage_mono h)) hq hc

theorem isLift_add_invComb : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (V : Dd.toPre.P.A.left.Opens) (d₀ : Fld Y.H.left) (y : Fin n → Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)), IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V) d₀ → (∀ (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d₀ _ f)) → (∀ a, IsWt Y 0 _ (y a)) → IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V) (fun W f => d₀ W f + ∑ a, rsT (y a) W * dd a W f) ∧ (∀ (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') ((fun W f => d₀ W f + ∑ a, rsT (y a) W * dd a W f) _ f)) := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hinv D V d₀ y hd hw hy
  refine ⟨⟨isField_add_comb d₀ dd y hd.1 fun a => (hinv a).1, fun W hW r => ?_⟩, fun α V' hV' f hf => ?_⟩
  · simp only [hd.2 W hW r, fun a => inv_constFn Y.H (v a) (dd a) (hinv a) W r, mul_zero, Finset.sum_const_zero,
      add_zero]
  · exact WtAlg.isWt_add (hw α V' hV' f hf) (WtAlg.isWt_sum _ _ fun a _ =>
      WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (isWt_rsT Y hV' (hy a)) (IsInv.isWt Y (v a) (dd a) (hinv a) α _ f hf))

end GlobalTheory.Heat.Adjust
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
open GlobalTheory.TangentOrigin


theorem _root_.GlobalTheory.T.exists_vectorField_coeffs_glued_from_affineOpens : ∀ {X : Scheme.{0}} {n : ℕ} (W : X.Opens) (δ : Fld X) (dd : Fin n → Fld X), IsField W δ → (∀ a, IsField ⊤ (dd a)) →
    (∀ V V' : X.Opens, IsAffineOpen V → IsAffineOpen V' → V ≤ W → V' ≤ V →
      ∃! c : Fin n → Γ(X, V'), ∀ f : Γ(X, V), rsT (δ V f) V' = ∑ a, c a * rsT (dd a V f) V') →
    ∃ c : Fin n → Γ(X, W), ∀ O, O ≤ W → ∀ f, δ O f = ∑ a, rsT (c a) O * dd a O f := by
  first | exact @GlobalTheory.VertCoeffGlue.exists_coeff | exact GlobalTheory.VertCoeffGlue.exists_coeff | (intros; apply GlobalTheory.VertCoeffGlue.exists_coeff <;> assumption)
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
open ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.exists_raynaudGauge_generator_weight_neg : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (mu : Q.X) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H), (x ≫ Y.q) * Q.c mu = 1 → ∀ ψ₀ : LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c mu).left) fun _ => -1), ψ₀.IsGen → ∃ e : LB.Gen (LB.LinComb Q.P.L (K := Fin 2) ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1]), e.IsGen ∧ (∀ (j : Fin 2 → Q.P.L.ι) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ LB.wchart Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] j → IsWt Y (-mu) (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V))) ∧ ∀ (T : Over (Sp R)) (y : T ⟶ Y.H) (z : T.left) (J : (T.left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → val e y.left z J * val ψ₀ T.hom z J * val Q.rig T.hom z J * val ((Y.Φ T (y * (toUnit T ≫ x))).s mu) (𝟙 _) z J = 1 := by
  first | exact @GlobalTheory.Heat.ShiftGauge.exists_gauge | exact GlobalTheory.Heat.ShiftGauge.exists_gauge | (intros; apply GlobalTheory.Heat.ShiftGauge.exists_gauge <;> assumption)
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

theorem _root_.GlobalTheory.T.raynaudFourierTerm_chartFunctions_isWeight : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (k : ℕ) (α : Q.X) (σ : Q.SecB k α) (τ : SecM Y.q.left Q.P.L k), IsTerm Y k α σ τ → ∀ (j : Fin 1 → Q.P.L.ι) (V : Y.H.left.Opens), V ≤ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) j → IsWt Y α V (rsT (τ.f j) V) := by
  first | exact @GlobalTheory.Heat.TermWt.isWt_term | exact GlobalTheory.Heat.TermWt.isWt_term | (intros; apply GlobalTheory.Heat.TermWt.isWt_term <;> assumption)
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

namespace GlobalTheory.HeatMod

theorem isWt_fourierTerm : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (Ω : Type) [CommRing Ω] [StarRing Ω] [Module Ω Q.X] (oa : Q.OAct Ω) (Y : Ray oa), ∀ (k : ℕ) (α : Q.X) (σ : Q.SecB k α) (τ : SecM Y.q.left Q.P.L k), IsTerm Y k α σ τ → ∀ (j : Q.P.L.ι) (W : Y.H.left.Opens), (∃ V : Q.P.A.left.Opens, W = Y.q.left ⁻¹ᵁ V) → W ≤ Y.q.left ⁻¹ᵁ Q.P.L.U j → IsWt Y α W (rsT (τ.f fun _ => j) W) := by
  intro R _ _ Q Ω _ _ _ oa Y k α σ τ hT j W _ hW
  exact GlobalTheory.Heat.TermWt.isWt_term Y k α σ τ hT (fun _ => j) W fun _ hx => Set.mem_iInter.2 fun _ => hW hx

end GlobalTheory.HeatMod
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

theorem _root_.GlobalTheory.T.raynaudFourierTerm_localFunction_isWeight : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (k : ℕ) (α : Q.X) (σ : Q.SecB k α) (τ : SecM Y.q.left Q.P.L k), IsTerm Y k α σ τ → ∀ (j : Q.P.L.ι) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ Y.q.left ⁻¹ᵁ Q.P.L.U j → IsWt Y α (Y.q.left ⁻¹ᵁ V) (rsT (τ.f fun _ => j) (Y.q.left ⁻¹ᵁ V)) := by
  first | exact @GlobalTheory.Heat.isWt_rsT_of_isTerm | exact GlobalTheory.Heat.isWt_rsT_of_isTerm | (intros; apply GlobalTheory.Heat.isWt_rsT_of_isTerm <;> assumption)
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

theorem _root_.GlobalTheory.T.exists_vectorField_extending_affineDerivation : ∀ (Z : Scheme.{0}) (U : Z.Opens), IsAffineOpen U → ∀ δ : Γ(Z, U) → Γ(Z, U), (∀ a b, δ (a + b) = δ a + δ b) → (∀ a b, δ (a * b) = a * δ b + b * δ a) → ∃ d : Fld Z, IsField U d ∧ d U = δ := by
  first | exact @GlobalTheory.DerFieldExt.exists_field | exact GlobalTheory.DerFieldExt.exists_field | (intros; apply GlobalTheory.DerFieldExt.exists_field <;> assumption)
end
