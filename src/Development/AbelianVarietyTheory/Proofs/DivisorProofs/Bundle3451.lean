module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle937
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3404
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3095
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2788
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2694
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3037
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassifiedOfSmall
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle017
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3446
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle582
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3348
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2881
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3406
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3124
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3294
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3166
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2697
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2695
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3106
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle630
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

theorem RepFam.smoothOfRelativeDimension : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ F : RepFam b N, IsQProjOver F.s → SmoothOfRelativeDimension (D.a * (D.n - 1)) F.s := by
  intro p _ D R _ _ b N hN hNp F hq
  have hlft : LocallyOfFiniteType F.s := by
    obtain ⟨M, i, hi, hqc, hi'⟩ := hq
    have := isProper_str R M
    rw [← hi']
    infer_instance
  have hsm : Smooth F.s := by
    refine GlobalTheory.T.smooth_of_artinian_squareZero_lifting_noetherian_base R F.X F.s hlft ?_
    intro C C₀ _ _ _ _ π hπ hker t x₀ hx
    obtain ⟨β, rfl⟩ : ∃ β : R →+* C, t = spMap β :=
      ⟨(Spec.preimage t).hom, by simp [spMap]⟩
    have hcomp : spMap π ≫ spMap β = spMap (π.comp β) := by
      simp [spMap, ← Spec.map_comp]
    have hs₀ : x₀ ≫ F.s = spMap (π.comp β) := by rw [hx, hcomp]
    obtain ⟨o₀, ⟨m₀⟩⟩ := GlobalTheory.T.exists_harrisTaylorObjectPullback p D R b N _ _ F.s _ F.univ x₀ hs₀
    obtain ⟨o', ⟨m'⟩⟩ := GlobalTheory.T.harrisTaylor_formally_smooth_squareZero_lift p D R b N hN hNp C C₀ π β hπ (by rw [← hker, pow_two]) o₀
    obtain ⟨x, ⟨hxs, ⟨mx⟩⟩, -⟩ := F.rep (Sp C) (spMap β) o'
    obtain ⟨mc⟩ := GlobalTheory.T.harrisTaylorObjectPullback_comp p D R b N _ _ _ _ _ _ o₀ o' F.univ (spMap π) x m' mx
    refine ⟨x, ?_, hxs⟩
    exact (F.rep (Sp C₀) (spMap (π.comp β)) o₀).unique
      ⟨by rw [Category.assoc, hxs, hcomp], ⟨mc⟩⟩ ⟨hs₀, ⟨m₀⟩⟩
  exact GlobalTheory.T.smoothOfRelativeDimension_of_universal_firstOrder_tangent R F.X F.s _ hsm (GlobalTheory.T.exists_universal_tangent_harrisTaylor_representingFamily p D R b N hN hNp F hq hsm)

end GlobalTheory.UPel.HT
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.classical_traits_fourier_terms_all_levels : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (id : ℤ → ℤ) g p (X₁.M.Z.presheaf.stalk z₁)), PosW W → (∀ y, ∃ c : CTrait X₁ p z₁, (∀ a, Φ.ev y a = c.val a) ∧ ∃ e : Φ.X y ≃ₗ[ℤ] c.T.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = c.sc * c.T.β (e a) (e b)) → Φ.Four W (X₁.S.r * X₁.S.N) := by
  first | exact @GlobalTheory.Poinc.four_of_classical | exact GlobalTheory.Poinc.four_of_classical | (intros; apply GlobalTheory.Poinc.four_of_classical <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.UChart

theorem w_zero_mul_conj_eq_norm {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    H.w0 * H.bar H.w0 = (((H.d + 1) / 4 : ℕ) : 𝓞 E) := by
  obtain ⟨m, hm⟩ : ∃ m, H.d + 1 = 4 * m := ⟨(H.d + 1) / 4, by have := H.d_mod; omega⟩
  have e : (H.d + 1) / 4 = m := by omega
  have hm' : (H.d : 𝓞 E) + 1 = 4 * m := by exact_mod_cast hm
  rw [e, GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator]
  have h4 : (4 : 𝓞 E) ≠ 0 := by norm_num
  apply mul_left_cancel₀ h4
  linear_combination (-(2 * H.w0 + H.rt - 1)) * H.two_weight_eq_one_add_root - H.rt_sq + hm'

theorem exists_sab_pelUnif_of_norm {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type)
    [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R) (D : DegData R (maximalIdeal R))
    [inst : Module (𝓞 E) D.toPre.X] (oD : letI := H.starRing; D.toPre.OAct (𝓞 E))
    (hw : letI := H.starRing; TraceFormTwistIso D.toPre oD H.w0) :
    ∃ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), P.D = D ∧ HEq P.mod inst ∧ HEq P.oD oD := by
  letI := H.starRing
  obtain ⟨G, iG, cG, A, hG, ⟨U⟩⟩ := GlobalTheory.T.hasSemiAbelianUniformisation_complete_normal_base R hR D
  obtain ⟨oA, oG, hl⟩ := GlobalTheory.T.exists_ringAction_extension_to_uniformised_semiAbelian R hR D A G hG U (𝓞 E) oD
  have hd := H.d_mod
  let t : SAB H (Sp R) :=
    { G := G
      semi := hG
      act := ofRingAct oG
      PP := U.LG
      cub := U.cubG
      sym := GlobalTheory.isSymmetric_of_symmetry_generator U.LG U.symG U.symG_gen U.symG_rig
      adj := fun a => GlobalTheory.Mum.UnifAdjoint.lbIso_cubeLB_star R hR.1 D A G hG U (𝓞 E) oD oA oG hl a
      prim := GlobalTheory.T.lbIso_cubeLB_of_even_norm R hR D A G hG U (𝓞 E) oD oA oG hl H.w0 ((H.d + 1) / 4)
        (by show H.w0 + H.bar H.w0 = 1; rw [GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel]) (w_zero_mul_conj_eq_norm H) (by omega)
        (Nat.even_iff.2 (by omega)) hw }
  exact ⟨t, ⟨D, oD, A, oA, U, rfl, hl, hw⟩, rfl, HEq.rfl, HEq.rfl⟩

end GlobalTheory.UChart
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.MumDesc

theorem image_unif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre), F.Alg → ∀ (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∃ (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso (abelian₂ G U.LG.L) ((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left) := by
  intro R _ _ _ hR D D' F hF A' G' _ _ hG' U' oA oG hlin G _ _ hG inc pr hi hp hip hpi
  obtain ⟨G₀, _, _, A₀, hG₀, ⟨U₀⟩⟩ := GlobalTheory.T.hasSemiAbelianUniformisation_complete_normal_base R hR D
  obtain ⟨ε, u, u', hε, hu, -, he, huu, hadj⟩ :=
    GlobalTheory.T.idempotent_image_iso_uniformised_factor_with_adjoint_pair R hR D D' F hF A' G' hG' U' oA oG hlin G hG inc pr hi hp hip hpi A₀ G₀ hG₀ U₀
  obtain ⟨U, hU⟩ := GlobalTheory.T.exists_uniformisation_along_group_iso_lbIso R hR D A₀ G G₀ ε hε hG₀ U₀
  refine ⟨A₀, U, GlobalTheory.T.mumfordBundle_retract_of_adjoint_pairs _ G G' G₀ U.LG.L U'.LG.L U₀.LG.L U.LG.isLB U'.LG.isLB U₀.LG.isLB inc u u'
    (oG.act F.e) (oG.act (Star.star F.e)) (oG.act F.f) hi hu ?_ ?_ hadj
    (GlobalTheory.T.semiAbelian_groupAction_star_adjoint_bundle R hR D' A' G' hG' U' F.O F.o oA oG hlin F.e) (he ▸ hU)⟩
  · rw [← hpi, ← Category.assoc, hip, Category.id_comp]
  · rw [huu, oG.map_mul, oG.map_mul]

end GlobalTheory.MumDesc
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem laurentPolynomial_cohomology_strictlyHenselian_vanishing : GlobalTheory.EtC.C5 := fun q _ A _ hA hq n i => GlobalTheory.T.multiplicativeGroup_cohomology_strictlyHenselian q A hA hq n i

end GlobalTheory.EtC
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

theorem GlobalTheory.RigChart.toroidalForFanKS_of_rigidForFan : GlobalTheory.RigChart.RigidForFan → GlobalTheory.Published.ToroidalForFanKS := by
  intro h E _ _ _ H Dw hr φ h₁ h₂ l Xo c
  obtain ⟨Y, BD, d, k, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈⟩ := h E H Dw hr φ h₁ h₂ l Xo c
  exact ⟨Y, BD, d, k, a₁, a₂, a₃, a₄, a₅, a₆, a₇, GlobalTheory.T.logKodairaSpencer_iso_smooth_snc_toroidalModel E H Dw l Xo c Y hr a₃ a₄ a₈⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

theorem _root_.GlobalTheory.T.harrisTaylor_auxiliary_symplectic_level_representable : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N M e : ℕ), 3 ≤ N → N.Coprime p → 3 ≤ M → Odd M → M.Coprime p → e.Coprime p → M.Coprime e → (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) → SDRep (Module.finrank ℤ D.La / 2) M e → HasLevelStructureOfLevel b N (Module.finrank ℤ D.La / 2) M := by
  first | (exact @GlobalTheory.UPel.HT.harrisTaylorModuli_symplecticLevel_representable) | (exact GlobalTheory.UPel.HT.harrisTaylorModuli_symplecticLevel_representable) | (intros; apply GlobalTheory.UPel.HT.harrisTaylorModuli_symplecticLevel_representable  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.DescentPow

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {C : UCompact Xo c}

theorem exists_uCTrait_norm_eqAt (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z)
    (φ : InvFun (𝓞 E)) (ι : ℕ) (D : EffCartierData Y.Z)
    (hord : UValThru Xo c C.i (πY ≫ X₁.π) Set.univ φ D.idealSheaf ι)
    (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ Y.Z) (hy : Set.range (gPt p ≫ y ≫ πY ≫ X₁.π) ⊆ Set.range C.i)
    (z₁ : X₁.M.Z) (hz : πY (y (cPt p)) = z₁) :
    ∃ t : UCTrait X₁ p z₁, t.y = y ≫ πY ∧ ∀ f, EqAt Y D (y (cPt p)) f →
      ‖Y.val (gPt p ≫ y) f‖ = Real.exp (-(t.sc * (ι * φ.evalZ t.T.be))) := by
  obtain ⟨T, ι', j, ξ, hint, hj, hloc, hξ, hT⟩ := GlobalTheory.T.exists_unitaryTrait_of_classicalPoint E H Dw l Xo c C X₁ Y πY p y hy
  have hgen : gPt p ≫ y = spMap ι' ≫ jK T.V ≫ ξ := by
    rw [← hξ, ← Category.assoc, ← Category.assoc]
    congr 1
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext v
    exact hj v
  refine ⟨⟨y ≫ πY, ?_, T, ι', hint, ?_⟩, rfl, fun f hf => ?_⟩
  · rw [Scheme.Hom.comp_apply]; exact hz
  · rw [← Category.assoc, ← Category.assoc, hgen]
    simp only [Category.assoc]
    rw [hT]
  · obtain ⟨tK, h1, h2⟩ := T.gen
    obtain ⟨a, ha, hI⟩ := hord T.V T.cdvr T.ϖ T.irr ξ T.y (by rw [← hT]) trivial T.t tK h1 h2 T.P T.be T.lev T.mono
    have hc : ξ (closedPoint T.V) = y (cPt p) := by
      rw [← hξ, Scheme.Hom.comp_apply]
      exact congrArg ξ (IsLocalRing.comap_closedPoint j).symm
    rw [← hc] at hf
    have key := GlobalTheory.T.norm_localEquation_eq_uniformiser_pow_classicalPoint _ _ Y D T.V T.ϖ a ξ p ι' j hint hj hI f hf
    rw [hξ] at key
    have hpos : 0 < ‖ι' (algebraMap T.V (FractionRing T.V) T.ϖ)‖ := by
      refine norm_pos_iff.2 ?_
      rw [map_ne_zero, Ne, IsFractionRing.to_map_eq_zero_iff]
      exact T.irr.ne_zero
    show _ = Real.exp (-(-Real.log ‖ι' (algebraMap T.V (FractionRing T.V) T.ϖ)‖ * (ι * φ.evalZ T.be)))
    rw [key, ← ha, neg_mul, neg_neg, mul_comm, Real.exp_nat_mul, Real.exp_log hpos]

theorem val_comp_of_centre (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z)
    (hHom : X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY) {q : ℕ} [Fact q.Prime] (y : Sp (OO q) ⟶ Y.Z) {z : X₁.M.Z}
    (hz : πY (y (cPt q)) = z) {a : X₁.Ω₁} (ha : a ∈ X₁.M.O z) :
    Y.val (gPt q ≫ y) a = X₁.M.val (gPt q ≫ y ≫ πY) a := by
  have hs : πY ((gPt q ≫ y) (closedPoint (PadicAlgCl q))) ⤳ z :=
    hz ▸ (RatModel.gPt_specializes (M := Y) rfl _).map πY.continuous
  have := hHom.val_comp (gPt q ≫ y) (closedPoint (PadicAlgCl q)) (RatModel.O_le_of_specializes hs ha)
  rw [← Category.assoc]
  exact this.symm

theorem exists_idealSheaf_comap_uValThru : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (ι : ℕ) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z) (D : GlobalTheory.EffCartierData Y.Z), 1 ≤ ι → X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY → IsProper πY → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y.Z → (∀ y ∈ D.idealSheaf.support, X₁.π (πY y) ∉ Set.range C.i) → UValThru Xo c C.i (πY ≫ X₁.π) Set.univ φ D.idealSheaf ι → ∃ (ι' : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι' ∧ (∀ y ∈ (J₁.comap πY).support, X₁.π (πY y) ∉ Set.range C.i) ∧ UValThru Xo c C.i (πY ≫ X₁.π) Set.univ φ (J₁.comap πY) ι' := by
  intro E _ _ _ H Dw hpq φ hφ l Xo c C X₁ ι Y πY D hι hHom hprop hnorm hsupp hord
  obtain ⟨d, hd, hA⟩ := GlobalTheory.T.exists_unitaryApproxPoincareSeries E H Dw hpq l Xo c C X₁ φ hφ
  obtain ⟨k, hk⟩ : ι ∣ Nat.lcm ι d := Nat.dvd_lcm_left ι d
  obtain ⟨m, hm⟩ : d ∣ Nat.lcm ι d := Nat.dvd_lcm_right ι d
  have hL0 : 0 < Nat.lcm ι d := Nat.lcm_pos hι hd
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hk; omega
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hm; omega
  have hAL : UApproxAt X₁ φ (Nat.lcm ι d) := hm ▸ GlobalTheory.T.unitaryApproxPoincareSeriesAt_mul E H Dw l Xo c C X₁ φ d m hm0 hA

  have hord' : UValThru Xo c C.i (πY ≫ X₁.π) Set.univ φ (D.nsmul k).idealSheaf (Nat.lcm ι d) := by
    intro W _ _ _ hW ϖ hϖ χ y hy hA' t tK h1 h2 P be hbe hmono
    obtain ⟨a, ha, hI⟩ := hord W hW ϖ hϖ χ y hy hA' t tK h1 h2 P be hbe hmono
    refine ⟨k * a, ?_, ?_⟩
    · rw [hk]; push_cast; rw [ha]; ring
    · rw [GlobalTheory.TorRef.Scale.idlAlong_nsmul, hI, Ideal.span_singleton_pow, ← pow_mul, mul_comm a k]
  have hsub : ∀ y ∈ (D.nsmul k).idealSheaf.support, y ∈ D.idealSheaf.support := by
    intro y hy
    obtain ⟨j, hj⟩ := D.exists_mem y
    rw [(D.nsmul k).mem_support_iff j hj] at hy
    rw [D.mem_support_iff j hj]
    intro h
    apply hy
    change y ∈ Y.Z.basicOpen (D.f j ^ k)
    rw [Scheme.basicOpen_pow _ _ hk0]
    exact h

  obtain ⟨W, hWi, hWc⟩ := GlobalTheory.T.exists_open_compactification_generic_subset_moduli E H Dw l Xo c C
  let U : Y.Z.Opens := (πY ≫ X₁.π) ⁻¹ᵁ W ⊓ ⟨((D.nsmul k).idealSheaf.support : Set Y.Z)ᶜ, (D.nsmul k).idealSheaf.support.isClosed.isOpen_compl⟩
  have hU : (U : Set Y.Z).Nonempty := by
    have e : Y.pt ≫ πY ≫ X₁.π = spMap (AlgHom.id X₁.o₁ X₁.Ω₁).toRingHom ≫ spMap (ratHull X₁.S.R).val.toRingHom ≫ X₁.u ≫ C.i := by
      rw [← Category.assoc, hHom, Category.assoc, X₁.comp]
    have e' := congrArg (fun h : Sp X₁.Ω₁ ⟶ C.Z => h (closedPoint X₁.Ω₁)) e
    simp only [Scheme.Hom.comp_apply] at e'
    have hr : X₁.π (πY (Y.pt (closedPoint X₁.Ω₁))) ∈ Set.range C.i := ⟨_, e'.symm⟩
    refine ⟨Y.pt (closedPoint X₁.Ω₁), ?_, ?_⟩
    · show (πY ≫ X₁.π) _ ∈ (W : Set C.Z)
      rw [Scheme.Hom.comp_apply]
      exact hWi hr
    · intro hs
      exact hsupp _ (hsub _ hs) hr
  have hDU : ∀ x ∈ (D.nsmul k).idealSheaf.support, x ∉ U := fun x hx hxU => hxU.2 hx
  have hrange : ∀ {q : ℕ} [Fact q.Prime] (y : Sp (OO q) ⟶ Y.Z), Set.range (gPt q ≫ y) ⊆ U →
      Set.range (gPt q ≫ y ≫ πY ≫ X₁.π) ⊆ Set.range C.i := by
    intro q _ y hy
    have h := hWc q (y ≫ πY ≫ X₁.π) (by
      rintro _ ⟨w, rfl⟩
      have h1 : (πY ≫ X₁.π) ((gPt q ≫ y) w) ∈ (W : Set C.Z) := (hy ⟨w, rfl⟩).1
      simpa only [Scheme.Hom.comp_apply] using h1)
    simpa only [Category.assoc] using h
  obtain ⟨J, hJ⟩ := GlobalTheory.T.exists_idealSheaf_pullback_eq_divisor_of_approx X₁.o₁ X₁.Ω₁ X₁.M Y πY hHom hprop (@GlobalTheory.IsNormalScheme.pred _ X₁.normal) hnorm U (D.nsmul k) hU hDU (by
    intro z₀ _ x hxz hx
    obtain ⟨p, hp, y₀, hcen⟩ := GlobalTheory.T.exists_classicalPoint_centred_closedPoint_arithmetic _ _ Y x hx U hU
    obtain ⟨c₀, hc₀y, hc₀⟩ := exists_uCTrait_norm_eqAt X₁ Y πY φ (Nat.lcm ι d) (D.nsmul k) hord' p y₀ (hrange y₀ hcen.2) z₀
      (by rw [hcen.1, hxz])
    refine ⟨p, hp, y₀, hcen, fun e => ?_⟩
    obtain ⟨f, hf0, hfall⟩ := hAL p z₀ c₀ e
    have hfO : X₁.M.stalkHom z₀ f ∈ X₁.M.O z₀ := (X₁.M.stalkEquiv z₀ f).2
    refine ⟨X₁.M.stalkHom z₀ f, hfO, fun f' hf' => ?_, ?_⟩
    · rw [hc₀ f' (hcen.1 ▸ hf'), val_comp_of_centre X₁ Y πY hHom y₀ (by rw [hcen.1, hxz]) hfO, ← hf0]
      show _ = ‖X₁.M.val (gPt p ≫ c₀.y) _‖
      rw [hc₀y]
    · intro q hq y hyz hyU f' hf'
      have hpq : p = q := GlobalTheory.T.prime_eq_of_classicalPoint_same_centre X₁.M.Z p q (y₀ ≫ πY) (y ≫ πY) (by
        rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hcen.1, hxz, hyz])
      subst hpq
      obtain ⟨t, hty, ht⟩ := exists_uCTrait_norm_eqAt X₁ Y πY φ (Nat.lcm ι d) (D.nsmul k) hord' p y (hrange y hyU) z₀ hyz
      have hcv : ∀ a, t.val a = Y.val (gPt p ≫ y) (X₁.M.stalkHom z₀ a) := fun a => by
        rw [val_comp_of_centre X₁ Y πY hHom y hyz (a := X₁.M.stalkHom z₀ a) (X₁.M.stalkEquiv z₀ a).2]
        show X₁.M.val (gPt p ≫ t.y) _ = _
        rw [hty]
      rcases hfall t with h1 | ⟨h, hh, h2⟩
      · left
        rw [← hcv, ht f' hf']
        exact h1
      · right
        refine ⟨X₁.M.stalkHom z₀ h, ⟨(X₁.M.stalkEquiv z₀ h).2, ?_⟩, ?_⟩
        · by_contra hne
          push_neg at hne
          apply (IsLocalRing.mem_maximalIdeal _).1 hh
          have hu : IsUnit (X₁.M.stalkEquiv z₀ h) :=
            (RatModel.isUnit_O_iff _).2 ⟨hne.1, hne.2⟩
          exact (MulEquiv.isUnit_map (X₁.M.stalkEquiv z₀)).1 hu
        · rw [← hcv, ← hcv]
          exact h2)
  refine ⟨Nat.lcm ι d, J, hL0, ?_, ?_⟩
  · rw [hJ]
    intro y hy
    exact hsupp y (hsub y hy)
  · rw [hJ]
    exact hord'

end GlobalTheory.UPoinc.DescentPow
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_siegPB_lift_of_quotient_lift : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] (e : C), e ∈ IsLocalRing.maximalIdeal C → (∀ a ∈ IsLocalRing.maximalIdeal C, a * e = 0) → ∀ (β : cycAway n →+* C) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → (∀ c₀ : SiegPre g n (zetaAway n) (spMap ((Ideal.Quotient.mk (Ideal.span {e})).comp β)), SiegPB c₀ c (spMap (Ideal.Quotient.mk (Ideal.span {e}))) → ∃ f : Sp (C ⧸ Ideal.span {e}) ⟶ F.X, f ≫ F.s = spMap ((Ideal.Quotient.mk (Ideal.span {e})).comp β) ∧ SiegPB c₀ F.univ f) → ∃ f : Sp C ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  first | exact @GlobalTheory.SmallClassify.classified_of_small | exact GlobalTheory.SmallClassify.classified_of_small | (intros; apply GlobalTheory.SmallClassify.classified_of_small <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.exists_section_separating_two_points_ample : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (M : LB X) (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (ρ : ℚ) (h : ℕ → ℚ) (x₁ x₂ : X), M.IsLB → IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB N → (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![M] : ℚ) = interNumRed ℂ C ![toLB G] / m + ρ * interNumRed ℂ C ![N]) → IsClosed ({x₁} : Set X) → IsClosed ({x₂} : Set X) → x₁ ≠ x₂ → (∀ e, 0 < h e) → (∀ (z : X) (e : ℕ), z ⤳ x₁ ∨ z ⤳ x₂ → 1 ≤ e → topologicalKrullDim (closure ({z} : Set X)) = e → 2 * (e : ℚ) ^ e < h e ^ e * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ)) → ∑ e ∈ Finset.Icc 1 n, h e < ρ → ∃ s : M.Sec, (x₁ ∈ nonzeroLocus s ∧ x₂ ∉ nonzeroLocus s) ∨ (x₂ ∈ nonzeroLocus s ∧ x₁ ∉ nonzeroLocus s) := by
  first | exact @GlobalTheory.PairStep.exists_sec_separating_two_points_of_ample | exact GlobalTheory.PairStep.exists_sec_separating_two_points_of_ample | (intros; apply GlobalTheory.PairStep.exists_sec_separating_two_points_of_ample <;> assumption)
end
