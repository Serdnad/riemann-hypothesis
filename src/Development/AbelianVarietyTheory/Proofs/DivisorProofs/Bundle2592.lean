module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle848
public import Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle037
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNormalFormArcDatumFramedPointRootOfUnity
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle040
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2555
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2589
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle027
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle625
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

namespace GlobalTheory.ValLocal

theorem exists_dvd_away {A : Type} [CommRing A] [IsDedekindDomain A] (q : Ideal A) [q.IsPrime] (a b : A) (hb : b ≠ 0) :
    ∃ s r : A, s ∉ q ∧ (s * a = r * b ∨ s * b = r * a) := by
  by_cases hq : q = ⊥
  · exact ⟨b, a, by simpa [hq] using hb, Or.inl (mul_comm _ _)⟩
  haveI := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hq (Localization.AtPrime q)
  have hinj : Function.Injective (algebraMap A (Localization.AtPrime q)) :=
    IsLocalization.injective _ q.primeCompl_le_nonZeroDivisors
  have key : ∀ (u v : A) (z : Localization.AtPrime q), algebraMap A _ u * z = algebraMap A _ v →
      ∃ s r : A, s ∉ q ∧ s * v = r * u := by
    intro u v z hz
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj q.primeCompl z
    refine ⟨s, r, s.2, hinj ?_⟩
    rw [map_mul, map_mul, ← hz, ← hrs]
    ring
  obtain ⟨z, hz | hz⟩ := ValuationRing.cond (algebraMap A (Localization.AtPrime q) a) (algebraMap A _ b)
  · obtain ⟨s, r, hs, h⟩ := key a b z hz
    exact ⟨s, r, hs, Or.inr h⟩
  · obtain ⟨s, r, hs, h⟩ := key b a z hz
    exact ⟨s, r, hs, Or.inl h⟩

theorem exists_integral_frac {F : Type} [Field F] [NumberField F] (W : ValuationSubring F) (x : W) :
    ∃ a s : W, IsIntegral ℤ (a : F) ∧ IsIntegral ℤ (s : F) ∧ IsUnit s ∧ x * s = a := by
  have hmem : ∀ y : 𝓞 F, (y : F) ∈ W := fun y => by
    have h : IsIntegral W (y : F) := y.isIntegral_coe.tower_top
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h
    rw [← hz]
    exact z.2
  let φ : 𝓞 F →+* W := (algebraMap (𝓞 F) F).codRestrict W.toSubring hmem
  have hφ : ∀ y : 𝓞 F, ((φ y : W) : F) = (y : F) := fun _ => rfl
  let q : Ideal (𝓞 F) := (IsLocalRing.maximalIdeal W).comap φ
  have hunit : ∀ s : 𝓞 F, s ∉ q → IsUnit (φ s) := fun s hs => by
    by_contra h
    exact hs ((IsLocalRing.mem_maximalIdeal _).2 h)
  obtain ⟨a, b, hb, hx⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (x : F)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbF : (b : F) ≠ 0 := by exact_mod_cast hb0
  have hxb : (x : F) * b = a := by
    rw [← hx]
    exact div_mul_cancel₀ _ hbF
  obtain ⟨s, r, hs, h | h⟩ := exists_dvd_away q a b hb0
  · refine ⟨φ r, φ s, r.isIntegral_coe, s.isIntegral_coe, hunit s hs, Subtype.ext ?_⟩
    have h' : (s : F) * a = r * b := by exact_mod_cast congrArg (fun y : 𝓞 F => (y : F)) h
    show (x : F) * s = r
    apply mul_right_cancel₀ hbF
    rw [← h', ← hxb]
    ring
  · have h' : (s : F) * b = r * a := by exact_mod_cast congrArg (fun y : 𝓞 F => (y : F)) h
    have hxr : x * φ r = φ s := by
      apply Subtype.ext
      show (x : F) * r = s
      apply mul_right_cancel₀ hbF
      rw [h', ← hxb]
      ring
    exact ⟨φ s, φ r, s.isIntegral_coe, r.isIntegral_coe,
      isUnit_of_mul_isUnit_right (hxr ▸ hunit s hs), hxr⟩

theorem preimmersion_flat :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F), IsBaseRing β → ∀ (W : ValuationSubring c.F) (b : O →+* W), W.subtype.comp b = β → IsPreimmersion (spMap b) ∧ Flat (spMap b) := by
  intro E _ _ _ H l c O _ β hβ W b hb
  haveI := c.fin
  haveI : NumberField c.F := {}
  letI : Algebra O W := b.toAlgebra
  have hbv : ∀ o : O, ((b o : W) : c.F) = β o := fun o => by rw [← hb]; rfl
  have hinj : Function.Injective b := fun u v h => hβ.1 (by rw [← hbv, ← hbv, h])
  let S : Submonoid O := (IsUnit.submonoid W).comap b
  haveI : IsLocalization S W := by
    refine (isLocalization_iff S W).2 ⟨fun y => y.2, fun z => ?_, fun {u v} h => ⟨1, by rw [hinj h]⟩⟩
    obtain ⟨a, s, ha, hs, hu, hz⟩ := exists_integral_frac W z
    obtain ⟨a', ha'⟩ := hβ.2 _ ha
    obtain ⟨s', hs'⟩ := hβ.2 _ hs
    have e1 : b a' = a := Subtype.ext (by rw [hbv, ha'])
    have e2 : b s' = s := Subtype.ext (by rw [hbv, hs'])
    refine ⟨⟨a', ⟨s', ?_⟩⟩, ?_⟩
    · show IsUnit (b s')
      rwa [e2]
    · show z * b s' = b a'
      rw [e1, e2, hz]
  refine ⟨IsPreimmersion.of_isLocalization (R := O) (S := W) S, ?_⟩
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  exact (RingHom.flat_algebraMap_iff (R := O) (S := W)).2 (IsLocalization.flat W S)

end GlobalTheory.ValLocal
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.exists_baseChange_rigidifiedSection_of_scalarMultiple : ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (rig : LB.Gen (L.pull (eSec G))) (θ : L.Sec) (n : ℕ) (w : Fin n → (epsR R ⟶ G)) (x : KeyIn R'), L.IsLB → IsFibreOf x G L rig θ w f → ∀ (θ₀ : L.Sec) (b : R), IsMul (X := G) θ b θ₀ → ∃ (th₀ : x.P.L.Sec) (hth₀ : ∀ s : Sp R', ∃ z : x.P.A.left, x.P.A.hom z = s ∧ z ∈ Out.nonzeroLocus th₀), (∀ i, LB.Sec.f x.th i = constFn x.P.A.hom _ (f b) * LB.Sec.f th₀ i) ∧ IsFibreOf ⟨x.P, x.g_pos, x.rig, x.rig_gen, th₀, hth₀, x.v, x.basis⟩ G L rig θ₀ w f := by
  first | exact @GlobalTheory.KeySwapSec.exists_isFibreOf_of_isMul | exact GlobalTheory.KeySwapSec.exists_isFibreOf_of_isMul | (intros; apply GlobalTheory.KeySwapSec.exists_isFibreOf_of_isMul <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels

noncomputable section

namespace GlobalTheory.FramedExt

theorem eSec_hom {S : Scheme.{0}} (X : Over S) [GrpObj X] : eSec X ≫ X.hom = 𝟙 _ := by
  simp [eSec]

theorem dualMapR_comp_algebraMap {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') :
    (Chart.dualMapR f).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp f := by
  ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem dual_ext {R R' : Type} [CommRing R] [CommRing R'] (F₁ F₂ : DualNumber R →+* DualNumber R')
    (h : ∀ a : R, F₁ (algebraMap R (DualNumber R) a) = F₂ (algebraMap R (DualNumber R) a))
    (hε : F₁ DualNumber.eps = F₂ DualNumber.eps) : F₁ = F₂ := by
  refine RingHom.ext fun x => ?_
  have hx : x = algebraMap R (DualNumber R) x.fst + algebraMap R (DualNumber R) x.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [hx, map_add (f := _), map_add (f := _), map_mul, map_mul, h, h, hε]

theorem generates_of_flat {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {R R₂ : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing R₂] [IsDomain R₂] (φ : R →+* R₂) (hφ : Function.Injective φ) (G : SAB H (Sp R)) (G₂ : SAB H (Sp R₂)) (m : SABMap G₂ G (spMap φ)) (wI : G₂.PP.L.Iso (G.PP.L.pull m.φ)) (hwI : LB.Gen.IsGen wI) (θ : G.PP.L.Sec) (θ₂ : G₂.PP.L.Sec) (hθ : IsoMaps wI θ₂ (thfPull G.PP.L m.φ θ)) : Generates (X := G.G) θ → Generates (X := G₂.G) θ₂ := by
  intro hgen
  letI := φ.toAlgebra
  have : FaithfulSMul R R₂ := (faithfulSMul_iff_algebraMap_injective _ _).2 hφ
  have : Module.Flat R R₂ := inferInstance
  haveI : IsSeparated G.G.hom := G.semi.separated
  haveI : QuasiCompact G.G.hom := G.semi.quasiCompact
  haveI : CompactSpace G.G.left := QuasiCompact.compactSpace_of_compactSpace G.G.hom
  have hinter : ∀ U W : G.G.left.Opens, IsAffineOpen U → IsAffineOpen W → IsAffineOpen (U ⊓ W) :=
    fun U W hU hW => isAffineHom_diagonal_iff.mp (inferInstance : IsAffineHom (pullback.diagonal G.G.hom)) ⊤
      (isAffineOpen_top _) U le_top W le_top hU hW
  have Hpb : IsPullback m.φ G₂.G.hom G.G.hom (Spec.map (CommRingCat.ofHom (algebraMap R R₂))) := m.cart.1
  exact fun s' => ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.flatBC_iso G.G.hom G₂.G.hom m.φ Hpb hinter G.PP.L G.PP.isLB θ hgen
    G₂.PP.L G₂.PP.isLB wI hwI θ₂ _ hθ (fun _ _ => rfl) s'

theorem isFibreOf_trans {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (hL : L.IsLB) (rig : (L.pull (eSec G)).Gen) (θ : L.Sec) {n : ℕ} (w : Fin n → (epsR R ⟶ G)) (k : KeyIn R') (k' : KeyIn R'') (f : R →+* R') (g : R' →+* R'') : IsFibreOf k G L rig θ w f → KeyPB k' k g → IsFibreOf k' G L rig θ w (g.comp f) := by
  intro H H'
  obtain ⟨φ, he, w₀, hg, F, hp, hw, hr, hs, hF, hε, hv⟩ := H
  obtain ⟨φ', he', w', hg', F', hp', hw', hr', hs', hF', hε', hv'⟩ := H'
  have g₀ := (isGen_iff w₀).1 hw
  have g' := (isGen_iff w').1 hw'
  obtain ⟨w'', T⟩ := exists_comp k.P.isLB w₀ w' g₀ g' hL k'.P.isLB
  have he'' : eSec k'.P.A ≫ φ' ≫ φ = spMap (g.comp f) ≫ eSec G := by
    rw [← Category.assoc, he', Category.assoc, he, spMap_comp, Category.assoc]
  refine ⟨φ' ≫ φ, he'', w'', hg'.trans hg, F'.comp F, (hp'.comp hp).congr (spMap_comp f g).symm rfl,
    (isGen_iff w'').2 (T.pgen_comp k.P.isLB g₀ g'), ?_, ?_, fun a => ?_, ?_, fun i => ?_⟩
  · have r₀ := (maps_iff w₀ _ (fun _ => eSec G) _ k.rig rig (spMap f) _
      (rigPull_le φ (spMap f) he L) (fun _ => rfl)).1 hr
    have r₁ := (maps_iff w' _ (fun _ => eSec k.P.A) _ k'.rig k.rig (spMap g) _
      (rigPull_le φ' (spMap g) he' k.P.L) (fun _ => rfl)).1 hr'
    have r₂ := T.pmaps_comp k.P.isLB (fun _ => he') r₀ r₁
    rw [← spMap_comp] at r₂
    exact (maps_iff w'' _ (fun _ => eSec G) _ k'.rig rig (spMap (g.comp f)) _
      (rigPull_le (φ' ≫ φ) (spMap (g.comp f)) he'' L) (fun _ => rfl)).2 r₂
  · refine GlobalTheory.KeyPow.appLE_eq_of_stalk w'' θ k'.th fun z j k₀ hj hk => ?_
    obtain ⟨i, hi⟩ := exists_chart k.P.isLB (φ' z)
    have a := GlobalTheory.KeyComp.stalk_of_appLE_eq w₀ θ k.th hs (𝟙 _ ≫ φ') z j i hj hi
    have b := GlobalTheory.KeyComp.stalk_of_appLE_eq w' k.th k'.th hs' (𝟙 _) z i k₀ hi hk
    rw [T _ (𝟙 _) z j i k₀ hj hi hk, ← Category.assoc, a, b, Units.val_mul, _root_.mul_assoc]
  · rw [RingHom.comp_apply, hF, hF', RingHom.comp_apply]
  · rw [RingHom.comp_apply, hε, hε']
  · rw [← Category.assoc, hv', Category.assoc, hv, spMap_comp, Category.assoc]
    rfl

theorem isFibreOf_descend {R R₂ K : Type} [CommRing R] [CommRing R₂] [CommRing K] (φ : R →+* R₂) (f : R₂ →+* K) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (G₂ : Over (Sp R₂)) [GrpObj G₂] [IsCommMonObj G₂] (L : LB G.left) (hL : L.IsLB) (rig : (L.pull (eSec G)).Gen) (L₂ : LB G₂.left) (hL₂ : L₂.IsLB) (rig₂ : (L₂.pull (eSec G₂)).Gen) (ψ : G₂.left ⟶ G.left) (hψ : IsGrpPullback G₂ G (spMap φ) ψ) (he : eSec G₂ ≫ ψ = spMap φ ≫ eSec G) (wI : L₂.Iso (L.pull ψ)) (hwI : LB.Gen.IsGen wI) (hrig : LB.Gen.Maps (LB.linCombIso wI (fun _ => eSec G₂) fun _ => 1) rig₂ (rigPullOf ψ (spMap φ) he L rig)) (θ : L.Sec) (θ₂ : L₂.Sec) (hθ : IsoMaps wI θ₂ (thfPull L ψ θ)) {n : ℕ} (w : Fin n → (epsR R ⟶ G)) (w₂ : Fin n → (epsR R₂ ⟶ G₂)) (hw : ∀ i, (w₂ i).left ≫ ψ = spMap (Chart.dualMapR φ) ≫ (w i).left) (k : KeyIn K) : IsFibreOf k G L rig θ w (f.comp φ) → IsFibreOf k G₂ L₂ rig₂ θ₂ w₂ f := by
  intro H
  obtain ⟨φk, hek, e, hg, F, hp, hgen, hr, hs, hF, hε, hv⟩ := H
  obtain ⟨ψ₂, hfac, hbase⟩ : ∃ ψ₂ : k.P.A.left ⟶ G₂.left, ψ₂ ≫ ψ = φk ∧ ψ₂ ≫ G₂.hom = k.P.A.hom ≫ spMap f :=
    ⟨hψ.1.lift φk (k.P.A.hom ≫ spMap f) (by rw [hp.1.w, spMap_comp, Category.assoc]),
      hψ.1.lift_fst _ _ _, hψ.1.lift_snd _ _ _⟩
  subst hfac
  have hp₂ : IsGrpPullback k.P.A G₂ (spMap f) ψ₂ := hψ.cancel (hp.congr (spMap_comp φ f) rfl) hbase
  have he₂ : eSec k.P.A ≫ ψ₂ = spMap f ≫ eSec G₂ := by
    apply hψ.1.hom_ext
    · rw [Category.assoc, hek, Category.assoc, he, spMap_comp, Category.assoc]
    · rw [Category.assoc, hbase, ← Category.assoc, eSec_hom, Category.assoc, eSec_hom]
      simp
  have gI := (isGen_iff wI).1 hwI
  have g₀ := (isGen_iff e).1 hgen
  obtain ⟨e₂, T⟩ := exists_cancel hL wI e gI g₀ hL₂ k.P.isLB
  have hFe : F = (Chart.dualMapR f).comp (Chart.dualMapR φ) := dual_ext _ _ (fun a => by
      simp only [hF, RingHom.comp_apply]
      ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
    (by rw [hε]; ext <;> simp [Chart.dualMapR])
  refine ⟨ψ₂, he₂, e₂, hg, Chart.dualMapR f, hp₂, (isGen_iff e₂).2 (T.pgen_cancel hL gI g₀), ?_, ?_,
    fun a => ?_, ?_, fun i => ?_⟩
  · have r₀ := (maps_iff wI _ (fun _ => eSec G) _ rig₂ rig (spMap φ) _
      (rigPull_le ψ (spMap φ) he L) (fun _ => rfl)).1 hrig
    have r'' := (maps_iff e _ (fun _ => eSec G) _ k.rig rig (spMap (f.comp φ)) _
      (rigPull_le (ψ₂ ≫ ψ) (spMap (f.comp φ)) hek L) (fun _ => rfl)).1 hr
    rw [spMap_comp] at r''
    have r₂ := T.pmaps_cancel hL (fun _ => he₂) r₀ r''
    exact (maps_iff e₂ _ (fun _ => eSec G₂) _ k.rig rig₂ (spMap f) _
      (rigPull_le ψ₂ (spMap f) he₂ L₂) (fun _ => rfl)).2 r₂
  · have hθ' : ∀ (j : (L.pull ψ).ι) (i : L₂.ι) (hle : (L.pull ψ).U j ⊓ L₂.U i ≤ ψ ⁻¹ᵁ L.U (j PUnit.unit)),
        (Scheme.Hom.appLE ψ (L.U (j PUnit.unit)) ((L.pull ψ).U j ⊓ L₂.U i) hle).hom (θ.f (j PUnit.unit)) =
          (show Γ(G₂.left, (L.pull ψ).U j ⊓ L₂.U i) from (wI.s (j, i)).val) * resG _ inf_le_right (θ₂.f i) := by
      intro j i hle
      refine Eq.trans ?_ (hθ j i)
      dsimp only [thfPull]
      first
        | (erw [Scheme.Hom.appLE_map])
        | (simp only [Scheme.Hom.appLE_map])
        | (rw [← Scheme.Hom.appLE_map ψ _ (homOfLE inf_le_left).op]; rfl)
    refine GlobalTheory.KeyPow.appLE_eq_of_stalk e₂ θ₂ k.th fun z j k₀ hj hk => ?_
    obtain ⟨jL, hjL⟩ := exists_chart hL (ψ (ψ₂ z))
    have a := GlobalTheory.KeyComp.stalk_of_appLE_eq e θ k.th hs (𝟙 _) z jL k₀ hjL hk
    have b := GlobalTheory.KeyComp.stalk_of_appLE_eq wI θ θ₂ hθ' (𝟙 _ ≫ ψ₂) z jL j hjL hj
    rw [Category.assoc] at b
    rw [T _ (𝟙 _) z jL j k₀ hjL hj hk, b, Units.val_mul, _root_.mul_assoc] at a
    exact (Units.mul_right_inj _).1 a
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]
  · apply hψ.1.hom_ext
    · rw [Category.assoc, hv i, Category.assoc, hw, ← Category.assoc, hFe, spMap_comp]
    · rw [Category.assoc, hbase, ← Category.assoc, Over.w (k.v i), Category.assoc, Over.w (w₂ (Fin.cast hg i))]
      simp only [epsR, Over.mk_hom]
      rw [← spMap_comp, ← spMap_comp, dualMapR_comp_algebraMap]

theorem exists_framed_ext : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (T T' : CDVR) (iT : T.Fr →+* T'.Fr) (φ : T.V →+* T'.V), (∀ a : T.V, algebraMap T'.V T'.Fr (φ a) = iT (algebraMap T.V T.Fr a)) → ∀ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)), SABMap t' G (spMap (algebraMap T.V T.Fr)) → ∀ (n : ℕ) (w : Fin n → (epsR T.V ⟶ G.G)), IsLieBasis w → ∀ (θ : G.PP.L.Sec), Generates (X := G.G) θ → ∀ (k : KeyIn T.Fr), IsFibreOf k G.G G.PP.L G.PP.rig θ w (algebraMap T.V T.Fr) → ∃ (G' : SAB H (Sp T'.V)) (t'' : SAB H (Sp T'.Fr)) (_ : SABMap t'' t' (spMap iT)) (_ : SABMap t'' G' (spMap (algebraMap T'.V T'.Fr))) (n' : ℕ) (w' : Fin n' → (epsR T'.V ⟶ G'.G)) (θ' : G'.PP.L.Sec) (k' : KeyIn T'.Fr), IsLieBasis w' ∧ Generates (X := G'.G) θ' ∧ IsFibreOf k' G'.G G'.PP.L G'.PP.rig θ' w' (algebraMap T'.V T'.Fr) ∧ KeyPB k' k iT := by
  intro E _ _ _ H T T' iT φ hφ G t' m2 n w hw θ hθ k hk
  have hφ' : (algebraMap T'.V T'.Fr).comp φ = iT.comp (algebraMap T.V T.Fr) := RingHom.ext hφ
  have hsq : spMap iT ≫ spMap (algebraMap T.V T.Fr) = spMap (algebraMap T'.V T'.Fr) ≫ spMap φ := by
    rw [← spMap_comp, ← spMap_comp, hφ']
  have tr : ∀ {S S' : Scheme.{0}} {s : SAB H S} {s' : SAB H S'} {f g : S' ⟶ S}, f = g → SABMap s' s f →
      Nonempty (SABMap s' s g) := by
    intro S S' s s' f g h m
    subst h
    exact ⟨m⟩
  obtain ⟨G₂, ⟨m⟩⟩ : ∃ G₂ : SAB H (Sp T'.V), Nonempty (SABMap G₂ G (spMap φ)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap φ) G
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨t₂, ⟨p⟩⟩ : ∃ t₂ : SAB H (Sp T'.Fr), Nonempty (SABMap t₂ t' (spMap iT)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap iT) t'
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨a₂, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m2 p
  obtain ⟨b₂⟩ := tr hsq a₂
  obtain ⟨m2', -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m b₂
  obtain ⟨w', hw', hww⟩ := GlobalTheory.exists_isLieBasis_baseChange _ _ φ G.G G₂.G m.φ m.cart G.semi.smooth n w hw
  obtain ⟨k', hk'⟩ := GlobalTheory.KeyPow.exists_keyPB_ring k iT
  obtain ⟨wI, hwI, hrI, -⟩ := m.lin
  obtain ⟨θ₂, hθ₂⟩ := GlobalTheory.ArcQ.NormalForm.exists_isoMaps wI hwI G.PP.isLB G₂.PP.isLB (thfPull G.PP.L m.φ θ)
  have he : eSec G₂.G ≫ m.φ = spMap φ ≫ eSec G.G := m.cm.e_comm.trans (congrArg (· ≫ eSec G.G) m.base)
  have hr : ∀ (e : Sp T'.V ⟶ Sp T.V) (_ : m.cm.e = e) (he : eSec G₂.G ≫ m.φ = e ≫ eSec G.G),
      rigPullOf m.φ e he G.PP.L G.PP.rig = m.cm.rigPull G.PP.L G.PP.rig := by
    rintro _ rfl _
    rfl
  have hrig : LB.Gen.Maps (LB.linCombIso wI (fun _ => eSec G₂.G) fun _ => 1) G₂.PP.rig
      (rigPullOf m.φ (spMap φ) he G.PP.L G.PP.rig) := by
    rw [hr _ m.base he]; exact hrI
  have h1 := isFibreOf_trans G.G G.PP.L G.PP.isLB G.PP.rig θ w k k' (algebraMap T.V T.Fr) iT hk hk'
  rw [← hφ'] at h1
  have hinj : Function.Injective φ := fun a b hab => IsFractionRing.injective T.V T.Fr
    (iT.injective (by rw [← hφ a, ← hφ b, hab]))
  exact ⟨G₂, t₂, p, m2', n, w', θ₂, k', hw', generates_of_flat φ hinj G G₂ m wI hwI θ θ₂ hθ₂ hθ,
    isFibreOf_descend φ (algebraMap T'.V T'.Fr) G.G G₂.G G.PP.L G.PP.isLB G.PP.rig G₂.PP.L G₂.PP.isLB G₂.PP.rig m.φ
      m.cart he wI hwI hrig θ θ₂ hθ₂ w w' hww k' h1, hk'⟩

end GlobalTheory.FramedExt
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.ZConvIdent
open GlobalTheory.WeilM
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem conjU_mul {D : D7} (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E)
    (h : J = c • V.gram) (g k : GA D V) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c h (g * k) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c h g * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c h k := by
  apply Subtype.ext
  simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU, map_mul]

theorem thetaSum_finset_sum {F : Type} [Field F] [NumberField F] {κ ι : Type} [Fintype κ] (s : Finset ι)
    (f : ι → (κ → AdeleRing (𝓞 F) F) → ℂ) (hf : ∀ k ∈ s, f k ∈ schA F κ) :
    thetaSum F (∑ k ∈ s, f k) = ∑ k ∈ s, thetaSum F (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [thetaSum]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      thetaSum_add F (hf a (Finset.mem_insert_self a s)) (Submodule.sum_mem _ fun k hk => hf k (Finset.mem_insert_of_mem hk)),
      ih fun k hk => hf k (Finset.mem_insert_of_mem hk)]

theorem translates_kerSmall_le_theta : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j))
    (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j)))
    (e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G i j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t i j e Bs Γ X) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (hv : ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ Bs.v₁),
    ∃ (z : GA D (G.V (.grid i j)) →₀ ℂ) (Φ : (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank +
        (G.V (.grid i j)).rank) → AF D.host.F) → ℂ) (a : GA D (G.V (.grid i j)) → GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB Γ.V'.J) (C₀ : ℝ),
      zdeg z ≠ 0 ∧ Φ ∈ Γ.M'.So Bs.ψ Bs.τ₁ ∧
      ∀ g u, ‖translates z (kerSmall W Θ' g g₁) u‖ ≤
        C₀ * ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' Φ (a u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (g, g₁))‖ := by
  intro D T L sc G μ₀ hL W B ρ t i j M hM Θ Θ' hΘ g₁ e Bs Γ X om om' h hTr hv
  obtain ⟨ΦB, hB, z, hz, hS⟩ := GlobalTheory.T.exists_routeDatum_translationCombination_goodPlace hL W B ρ t i j M hM Θ Θ' hΘ g₁ e Bs Γ X om om' h hTr hv
  obtain ⟨ξ, hξ, hk⟩ := GlobalTheory.T.small_route_kernel_eq_unit_norm_mul_theta hL W B ρ t i j M hM Θ Θ' hΘ g₁ e Bs Γ X om om' h hTr hv ΦB hB
  refine ⟨z, _, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU _ (-1) h.JW₁, 1, hz, hS, fun g u => le_of_eq ?_⟩
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil'
  have hpres : ∀ p φ, φ ∈ schA D.host.F _ → om' p φ ∈ schA D.host.F _ := fun p φ hφ => hW.pres p φ hφ
  have hB0 := hB.1
  set a := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU _ (-1) h.JW₁
  set hh := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (g, g₁)
  have ha : ∀ x y, a (x * y) = a x * a y := conjU_mul _ _ _
  have e1 : translates z (kerSmall W Θ' g g₁) u =
      ξ (g, g₁) * z.sum fun k c => c * thetaSum D.host.F (om' (a u, hh) (om' (a k, 1) ΦB)) := by
    rw [translates, Finsupp.mul_sum]
    refine Finsupp.sum_congr fun k _ => ?_
    rw [hk, ha, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
    ring
  have e2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' (z.sum fun k c => c • om' (a k, 1) ΦB) (a u) hh =
      z.sum fun k c => c * thetaSum D.host.F (om' (a u, hh) (om' (a k, 1) ΦB)) := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta, map_finsuppSum, Finsupp.sum, thetaSum_finset_sum]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, thetaSum_smul]
    · intro k _
      rw [map_smul]
      exact Submodule.smul_mem _ _ (hpres _ _ (hpres _ _ hB0))
  rw [e1, e2, norm_mul, hξ, one_mul]

end GlobalTheory.ZConvIdent
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_adelicWeilRep_unitaryPair_schroedingerModel : ∀ (D : D7) (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (n d : ℕ) (X : Spc D.host.F D.host.E n) (Y : Spc D.host.F D.host.E d) (r s r' s' : ℕ),
      X.IsHerm D.sp.cm.sig B r s → Y.IsSkew D.sp.cm.sig B r' s' →
      ∀ Mo : Model D.sp.cm.sig X Y, Mo.IsGood B.ψ →
      ∀ χX χW : Chr D.host.F D.host.E, GlobalTheory.LFun.IsHecke D.host.F D.host.E χX → GlobalTheory.LFun.IsHecke D.host.F D.host.E χW →
        GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χX n →
        GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χW d →
        ∃ om, Mo.IsWeil B.ψ χX χW om := by
  first | exact @GlobalTheory.WeilSchrodinger.exists_isWeil | exact GlobalTheory.WeilSchrodinger.exists_isWeil | (intros; apply GlobalTheory.WeilSchrodinger.exists_isWeil <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open MonObj

namespace GlobalTheory.HtGen

attribute [local instance] Over.cartesianMonoidalCategory

section Cover

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

end Cover

section Chars

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

abbrev TorsK {K : Type} [Field K] (ξ : Sp K ⟶ X) (q : ℕ) : Subgroup (Over.mk ξ ⟶ t.G) := (powMonoidHom q).ker



variable {t} in
def InducedBy {K : Type} [Field K] {ξ : Sp K ⟶ X} {q : ℕ} (χ : TorsK t ξ q →* Kˣ) {R : Type} [CommRing R]
    (x : Sp R ⟶ X) (u : R →+* K) {O : Type} [CommRing O] (ψ : R →+* O) {z : Sp O ⟶ X} (c : TorsChar t z q) : Prop :=
  ∀ (σ : Over.mk x ⟶ t.G) (k : TorsK t ξ q) (a : R) (w : Over.mk (spMap (algebraMap O O) ≫ z) ⟶ t.G),
    σ ^ q = 1 → k.1.left = spMap u ≫ σ.left → w.left = spMap ψ ≫ σ.left → u a = χ k → (c.χ O w : O) = ψ a

end Chars

end GlobalTheory.HtGen
end
end
