module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2264
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2486
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2211
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2265
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2523
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliLawsOfPrincipalLevelFieldOfDefinition
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle005
public import Development.AbelianVarietyTheory.Definitions.CMLattices.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2520
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1723
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1115
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2521
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotOntoOfCharAlone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1374
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle409
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle179
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2522
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2525
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle052
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelSpanOverClasses

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.AbVar.IsogTate

variable {K : Type} [Field K] (l : ℕ) [Fact l.Prime]

theorem vmap_comp' {A B C : AbVar K} (f : A ⟶ B) (g : B ⟶ C) :
    vmap l (f ≫ g) = vmap l g ∘ₗ vmap l f := by
  simp only [vmap, tmap_comp, LinearMap.baseChange_comp]

theorem vmap_nsmul_id (A : AbVar K) (n : ℕ) (x : Vl l A) :
    vmap l (n • 𝟙 A) x = (n : ℚ_[l]) • x := by
  have h1 : tmap l A A (n • 𝟙 A) = (n : ℤ_[l]) • LinearMap.id := by
    rw [map_nsmul, tmap_id, Nat.cast_smul_eq_nsmul]
  rw [vmap, h1, LinearMap.baseChange_smul, LinearMap.baseChange_id]
  rw [LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]

theorem tmap_injective_of_finite_ker {A B : AbVar K} (f : A ⟶ B) (hG : Finite (ptMap f).ker) :
    Function.Injective (tmap l A B f) := by
  have hp : l.Prime := Fact.out
  set N := Nat.card (ptMap f).ker with hN
  have hN0 : 0 < N := Nat.card_pos
  have hx : ∀ x ∈ (ptMap f).ker, x ^ N = 1 := fun x hx => by
    have := pow_card_eq_one' (G := (ptMap f).ker) (x := ⟨x, hx⟩)
    exact congrArg Subtype.val this
  refine (injective_iff_map_eq_zero _).2 fun t ht => Tate.ext fun n => ?_
  have hmem : ∀ m, t.lev m ∈ (ptMap f).ker := fun m => by
    rw [MonoidHom.mem_ker, ptMap_apply, ← lev_tmap l f t m, ht]
    rfl
  have h1 : t.lev (n + N) ^ l ^ (n + N) = 1 := t.lev_pow _
  have h2 : t.lev (n + N) ^ N = 1 := hx _ (hmem _)
  have h3 : t.lev (n + N) ^ Nat.gcd (l ^ (n + N)) N = 1 := pow_gcd_eq_one.2 ⟨h1, h2⟩
  obtain ⟨j, -, hj'⟩ := (Nat.dvd_prime_pow hp).1 (Nat.gcd_dvd_left (l ^ (n + N)) N)
  have h4 : l ^ j ≤ N := hj' ▸ Nat.le_of_dvd hN0 (Nat.gcd_dvd_right _ _)
  have h5 : j < N := lt_of_lt_of_le (Nat.lt_pow_self hp.one_lt) h4
  have h6 : t.lev (n + N) ^ l ^ N = 1 := by
    obtain ⟨c, hc⟩ := pow_dvd_pow l h5.le
    rw [hc, pow_mul, ← hj', h3, one_pow]
  show t.lev n = 1
  rw [← t.lev_add_pow n N]
  exact h6

theorem isFinite_of_tmap_injective (hl : (l : K) ≠ 0) {A B : AbVar K} (f : A ⟶ B)
    (hf : Function.Injective (tmap l A B f)) : IsFinite f.hom.left := by
  obtain ⟨C, p, i, hp, hi, rfl⟩ := GlobalTheory.T.exists_factorisation_through_abelianSubvariety K A B f
  have hpi : Function.Injective (tmap l A C p) := by
    rw [tmap_comp, LinearMap.coe_comp] at hf
    exact hf.of_comp
  obtain ⟨hA1, hA2, hA3, -, -⟩ := GlobalTheory.T.tateModule_free_finrank_two_mul_dim K l hl A
  obtain ⟨hC1, hC2, hC3, -, -⟩ := GlobalTheory.T.tateModule_free_finrank_two_mul_dim K l hl C
  have h1 : 2 * A.dim ≤ 2 * C.dim := by
    rw [← hA3, ← hC3]
    exact LinearMap.finrank_le_finrank_of_injective hpi
  have h2 : C.dim ≤ A.dim := (GlobalTheory.T.abelianVariety_dim_le_of_finite_and_of_surjective K A C p).2 hp
  have h3 : A.dim = C.dim := le_antisymm (by omega) h2
  have hpf : IsFinite p.hom.left := GlobalTheory.T.isFinite_of_surjective_of_dim_eq' K A C p h3 hp
  haveI := hi
  rw [comp_hom, Over.comp_left]
  infer_instance

theorem tmap_injective_of_vmap_injective (hl : (l : K) ≠ 0) {A B : AbVar K} (f : A ⟶ B)
    (hv : Function.Injective (vmap l f)) : Function.Injective (tmap l A B f) := by
  obtain ⟨hA1, -, -, -, -⟩ := GlobalTheory.T.tateModule_free_finrank_two_mul_dim K l hl A
  obtain ⟨hB1, -, -, -, -⟩ := GlobalTheory.T.tateModule_free_finrank_two_mul_dim K l hl B
  have hinj : ∀ (X : AbVar K) [Module.Free ℤ_[l] (Tl l X)],
      Function.Injective (fun t : Tl l X => (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] t) := by
    intro X _
    have h := Module.Flat.rTensor_preserves_injective_linearMap (M := Tl l X)
      (Algebra.linearMap ℤ_[l] ℚ_[l]) (IsFractionRing.injective ℤ_[l] ℚ_[l])
    intro s t hst
    apply (TensorProduct.lid ℤ_[l] (Tl l X)).symm.injective
    apply h
    simpa using hst
  intro s t hst
  apply hinj A
  apply hv
  simp only [vmap, LinearMap.baseChange_tmul, hst]

theorem vmap_bijective_of_isIsogeny {A B : AbVar K} (f : A ⟶ B) (hf : IsIsogeny f) :
    Function.Bijective (vmap l f) := by
  obtain ⟨n, g, hn, -, hfg, hgf⟩ := GlobalTheory.T.exists_quasiInverse_isogeny' K A B f hf
  have hn' : (n : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hb : ∀ (X : AbVar K), Function.Bijective (vmap l (n • 𝟙 X)) := fun X => by
    constructor
    · intro x y h
      rw [vmap_nsmul_id, vmap_nsmul_id] at h
      exact smul_right_injective _ hn' h
    · intro y
      exact ⟨(n : ℚ_[l])⁻¹ • y, by rw [vmap_nsmul_id, smul_smul, mul_inv_cancel₀ hn', one_smul]⟩
  refine ⟨?_, ?_⟩
  · have h := (hb A).1
    rw [← hfg, vmap_comp', LinearMap.coe_comp] at h
    exact h.of_comp
  · have h := (hb B).2
    rw [← hgf, vmap_comp', LinearMap.coe_comp] at h
    exact h.of_comp

end GlobalTheory.AV.AbVar.IsogTate

namespace GlobalTheory.AV.AbVar


open IsogTate in
theorem isFinite_iff_tmap_injective_and_isIsogeny_iff_vmap_bijective : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime],
    (l : K) ≠ 0 → ∀ (A B : AbVar K) (f : A ⟶ B),
    (IsFinite f.hom.left ↔ Function.Injective (tmap l A B f)) ∧ (IsIsogeny f ↔ Function.Bijective (vmap l f)) := by
  intro K _ l _ hl A B f
  have h1 : IsFinite f.hom.left ↔ Function.Injective (tmap l A B f) :=
    ⟨fun h => tmap_injective_of_finite_ker l f ((GlobalTheory.T.isFinite_iff_finite_ker' K A B f).1 h), isFinite_of_tmap_injective l hl f⟩
  refine ⟨h1, fun h => vmap_bijective_of_isIsogeny l f h, fun h => ?_⟩
  have hfin := h1.2 (tmap_injective_of_vmap_injective l hl f h.1)
  obtain ⟨-, -, -, hA4, hA5⟩ := GlobalTheory.T.tateModule_free_finrank_two_mul_dim K l hl A
  obtain ⟨-, -, -, hB4, hB5⟩ := GlobalTheory.T.tateModule_free_finrank_two_mul_dim K l hl B
  have hd : 2 * A.dim = 2 * B.dim := by
    rw [← hA5, ← hB5]
    exact (LinearEquiv.ofBijective _ h).finrank_eq
  exact ⟨hfin, GlobalTheory.T.surjective_of_isFinite_of_dim_eq_abelianVarietyHom K A B f (by omega) hfin⟩

end GlobalTheory.AV.AbVar
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
open TensorProduct
namespace GlobalTheory.ParForm

theorem isBaseChange_of_dual {R B M N : Type} [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N] [Module.Finite R M] [Module.Projective R M]
    [Module.Finite B N] [Module.Projective B N] (f : M →ₗ[R] N)
    (h : ∀ l : M →ₗ[R] B, ∃! δ : N →ₗ[B] B, ∀ w, δ (f w) = l w) : IsBaseChange B f := by
  let F : B ⊗[R] M →ₗ[B] N := f.liftBaseChange B
  have hF : ∀ w, F (1 ⊗ₜ w) = f w := fun w ↦ by simp [F]
  have hd : Function.Bijective F.dualMap := by
    rw [Function.bijective_iff_existsUnique]
    intro φ
    obtain ⟨δ, h1, h2⟩ := h ((φ.restrictScalars R).comp (TensorProduct.mk R B M 1))
    refine ⟨δ, ?_, fun δ' e ↦ h2 δ' fun w ↦ ?_⟩
    · refine (LinearMap.liftBaseChangeEquiv B).symm.injective (LinearMap.ext fun w ↦ ?_)
      simpa [hF] using h1 w
    · rw [← hF]
      exact LinearMap.congr_fun e (1 ⊗ₜ w)
  have hdd : Function.Bijective F.dualMap.dualMap :=
    (LinearEquiv.ofBijective _ hd).dualMap.bijective
  have hb : Function.Bijective F := by
    have e : ⇑(Module.Dual.eval B N) ∘ ⇑F = ⇑F.dualMap.dualMap ∘ ⇑(Module.Dual.eval B (B ⊗[R] M)) :=
      funext fun x ↦ rfl
    rw [← Function.Bijective.of_comp_iff' (Module.bijective_dual_eval B N), e]
    exact hdd.comp (Module.bijective_dual_eval B _)
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective F hb) hF

theorem smooth_sec {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (hs : Smooth s)
    (U : X.affineOpens) : Algebra.Smooth R (Sec s U.1) := by
  have h1 : RingHom.Smooth (s.appLE ⊤ U.1 le_top).hom :=
    HasRingHomProperty.appLE @Smooth s hs ⟨⊤, isAffineOpen_top _⟩ U le_top
  have h2 : RingHom.Smooth (secMap s U.1).hom :=
    RingHom.Smooth.respectsIso.2 _ (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv h1
  exact h2

theorem par : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Par A.hom := by
  intro H H' R _ A _ g hA hg U
  have hs : Smooth A.hom := SmoothOfRelativeDimension.smooth g A.hom
  have := smooth_sec A.hom hs U.unop
  obtain ⟨-, -, ⟨h1, h2, -⟩, -⟩ := H' R A g hA hg
  exact isBaseChange_of_dual _ (GlobalTheory.T.exists_unique_vectorField_of_globalOneForm_values H H' R A g hA hg U)

end GlobalTheory.ParForm
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.kronecker_character_frame_second : GlobalTheory.UCls.MassBound → GlobalTheory.UCls.TorusBound → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → GoodW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) → latW U (wtZ a n) ≠ ⊥ → slopeMax_sq (normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n)) (latW U (wtZ a n)) ≤ 2 * lamSup D.host.E D.R.r Dw.q D.host.d l.M (GlobalTheory.CM.logOm D.host.E χ).re ((absA Dw a : ℕ) : ℝ) ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 2 * Real.log (supConst D.host.E D.R.r D.host.d l.M (((absA Dw a : ℕ) : ℝ) + ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 1)) + Real.log |(discr c.F : ℝ)| / (Module.finrank ℚ c.F : ℝ) := by
  exact @GlobalTheory.LamMuMax.slopeMax_le
end

section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem _root_.GlobalTheory.T.moduliLaws_of_principalLevel_fieldOfDefinition : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, Formalism.L2.Theta.GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), GlobalTheory.LevGeo.Laws D j Xo c U dict → FnAlgClosed (Xo := Xo) (c := c) → (∀ p : ℕ, p.Prime → l.GoodAt p) → Laws U (xiR D) ∧ GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H := by
  first | exact @GlobalTheory.LevLaws.laws_of_level | exact GlobalTheory.LevLaws.laws_of_level | (intros; apply GlobalTheory.LevLaws.laws_of_level <;> assumption)
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory

attribute [local instance high] Submodule.module

theorem mumaxTop : GlobalTheory.Published.TamagawaSpecialUnitary → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → GoodW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) → latW U (wtZ a n) ≠ ⊥ → slopeMax_sq (normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n)) (latW U (wtZ a n)) ≤ 2 * lamSup D.host.E D.R.r Dw.q D.host.d l.M (GlobalTheory.CM.logOm D.host.E χ).re ((absA Dw a : ℕ) : ℝ) ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 2 * Real.log (supConst D.host.E D.R.r D.host.d l.M (((absA Dw a : ℕ) : ℝ) + ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 1)) + Real.log |(discr c.F : ℝ)| / (Module.finrank ℚ c.F : ℝ) := fun hT =>
  GlobalTheory.LamMuMax.slopeMax_le (GlobalTheory.T.mass_bound_of_tamagawa_unitary hT)
    GlobalTheory.T.normOneTorusClassNumberBound_proof

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.doubledWeilDatum_diag_acts_on_externalProduct : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
      (ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ)),
      Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
      ∀ ωd : GA D S × GA D (GlobalTheory.Doubling.dblSp T) →* Module.End ℂ (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) → ℂ),
        Formalism.IndefR.Datum.IsWeilDatumO ψ S (GlobalTheory.Doubling.dblSp T) χS 1 ωd →
        (∀ (h : GA D T) (hd : GA D (GlobalTheory.Doubling.dblSp T)),
          Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) hd =
            Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.L2.Theta.mt T h) 0 0 1) →
          ∃ c : ℂ, ∀ f₁ f₂ : Formalism.IndefR.Datum.WO S T → ℂ,
            Formalism.IndefR.Datum.IsThetaFunO ψ S T f₁ → Formalism.IndefR.Datum.IsThetaFunO ψ S T f₂ →
              ωd (1, hd) (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id))) = c • (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => ω (1, h) f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id)))) →
        ∀ (h : GA D T) (hd : GA D (GlobalTheory.Doubling.dblSp T)),
          Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) hd =
            Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.L2.Theta.mt T h) 0 0 1) →
          ∀ f₁ f₂ : Formalism.IndefR.Datum.WO S T → ℂ,
            Formalism.IndefR.Datum.IsThetaFunO ψ S T f₁ → Formalism.IndefR.Datum.IsThetaFunO ψ S T f₂ →
              ωd (1, hd) (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id))) = (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => ω (1, h) f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id))) := by
  first | exact @GlobalTheory.DblRestrictChar.dbl_diag_box | exact GlobalTheory.DblRestrictChar.dbl_diag_box | (intros; apply GlobalTheory.DblRestrictChar.dbl_diag_box <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevelActionOnto

def quotMap {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) (f : M →ₗ[R] M) :
    (M ⧸ I • (⊤ : Submodule R M)) →ₗ[R] (M ⧸ I • (⊤ : Submodule R M)) :=
  (I • (⊤ : Submodule R M)).mapQ (I • (⊤ : Submodule R M)) f
    (Submodule.map_le_iff_le_comap.1 (by rw [Submodule.map_smul'']; exact Submodule.smul_mono le_rfl le_top))

theorem quotMap_mk {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) (f : M →ₗ[R] M) (a : M) :
    quotMap I f ((I • (⊤ : Submodule R M)).mkQ a) = (I • (⊤ : Submodule R M)).mkQ (f a) := rfl


open Classical in
def quotEquiv {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) (f : M →ₗ[R] M) :
    (M ⧸ I • (⊤ : Submodule R M)) ≃ₗ[R] (M ⧸ I • (⊤ : Submodule R M)) :=
  if hb : Function.Bijective (quotMap I f) then LinearEquiv.ofBijective _ hb else LinearEquiv.refl R _

theorem quotEquiv_mk {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) (f : M →ₗ[R] M)
    (hb : Function.Bijective (quotMap I f)) (a : M) :
    quotEquiv I f ((I • (⊤ : Submodule R M)).mkQ a) = (I • (⊤ : Submodule R M)).mkQ (f a) := by
  unfold quotEquiv
  rw [dite_eq_left hb]
  rfl

theorem quotMap_bijective {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) (f f' : M →ₗ[R] M)
    (h1 : ∀ a, f (f' a) - a ∈ I • (⊤ : Submodule R M)) (h2 : ∀ a, f' (f a) - a ∈ I • (⊤ : Submodule R M)) :
    Function.Bijective (quotMap I f) := by
  have k1 : ∀ q, quotMap I f (quotMap I f' q) = q := fun q => by
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ q
    rw [quotMap_mk, quotMap_mk, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact h1 a
  have k2 : ∀ q, quotMap I f' (quotMap I f q) = q := fun q => by
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ q
    rw [quotMap_mk, quotMap_mk, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact h2 a
  exact ⟨Function.LeftInverse.injective k2, Function.RightInverse.surjective k1⟩

end GlobalTheory.LevelActionOnto

namespace GlobalTheory.LevelActionOnto

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)




theorem levelPin_actionPin : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (O : ∀ i, OMDat J.toCore R i Unit (fun _ => A.μ0)), GlobalTheory.Hk3.Core R F → (∀ i, OMPins J R κ v₀ O i) → RhoGeo fw O → (∀ i, OneMapRow0 J R κ v₀ O i) → J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → ∃ ℓ : ∀ i : Fin D.R.m, G → (LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l ≃ₗ[𝓞 D.host.E] LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l), ∀ (r : _root_.GlobalTheory.RealIndexBound.RunData J) (h : LawsFull r.full) (i : Fin D.R.m), letI : Algebra r.full.J.Q.c.F D.what₂.LL := ‹Algebra J.Q.c.F D.what₂.LL›; LevelPin (T := r.full) R i (ℓ i) ∧ ActionPin (T := r.full) (R := R) h.p fw i (ℓ i) := by
  intro D G _ _ Pl0 T0 A J _ R F κ v₀ fw O hc hpins hrho hrow hMb
  classical
  refine ⟨fun i g => quotEquiv J.Q.l.Mb ((O i).lev g), fun r h i => ?_⟩
  have hlev : LevIs R i (iotaW J i) J.Q.l.M (Mfr J.Q.l) (O i).lev := (hpins i).2.lift.lev
  have hι : LatEmb (Wc D i) (iotaW J i) := GlobalTheory.TraceLattice.latEmb_iotaW h i
  have hβ : IsSDFrame (Wc D i) (R.βW i) (R.ΛW i) 1 := hc.lev.βW i
  obtain ⟨h1, hm⟩ := GlobalTheory.LevelActionPinned.congr_of_levIs R i hι hβ hMb hlev
  have hbij : ∀ g, Function.Bijective (quotMap J.Q.l.Mb ((O i).lev g)) := fun g => by
    refine quotMap_bijective _ _ ((O i).lev g⁻¹) (fun a => ?_) (fun a => ?_)
    · have e1 := hm g g⁻¹ a
      have e2 := h1 a
      rw [mul_inv_cancel] at e1
      have := Submodule.sub_mem _ e2 e1
      rwa [sub_sub_sub_cancel_left] at this
    · have e1 := hm g⁻¹ g a
      have e2 := h1 a
      rw [inv_mul_cancel] at e1
      have := Submodule.sub_mem _ e2 e1
      rwa [sub_sub_sub_cancel_left] at this
  have hspec : ∀ g a, liftLa (quotEquiv J.Q.l.Mb ((O i).lev g)) a - (O i).lev g a ∈
      J.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (J.Q.Dw ((i : ℕ) + 1)).La) := fun g a => by
    rw [← Submodule.Quotient.eq]
    have := liftLa_spec (quotEquiv J.Q.l.Mb ((O i).lev g)) a
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply] at this
    rw [this]
    exact quotEquiv_mk _ _ (hbij g) a
  have hA : J.Q.l.A = 1 := h.j.pins.2.1.2
  refine ⟨?_, ?_⟩

  · change LevIs R i (iotaW J i) J.Q.l.M (Mfr J.Q.l) (fun g => liftLa (quotEquiv J.Q.l.Mb ((O i).lev g)))
    intro g
    obtain ⟨k, hk, hw⟩ := hlev g
    refine ⟨k, hk, fun a ha => ?_⟩
    obtain ⟨w, hwm, e⟩ := hw a ha
    have hd : liftLa (quotEquiv J.Q.l.Mb ((O i).lev g)) a - (O i).lev g a ∈
        (Ideal.span {(J.Q.l.M : 𝓞 D.host.E)}) • (⊤ : Submodule (𝓞 D.host.E) (J.Q.Dw ((i : ℕ) + 1)).La) := by
      rw [← J.Q.l.prod, mul_comm, Submodule.mul_smul]
      have key : ∀ f : (J.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (J.Q.Dw ((i : ℕ) + 1)).La,
          (∀ x, f x ∈ J.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (J.Q.Dw ((i : ℕ) + 1)).La)) →
          f a ∈ Mfr J.Q.l • J.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (J.Q.Dw ((i : ℕ) + 1)).La) := fun f hf => by
        refine Submodule.smul_induction_on ha (fun b hb x _ => ?_) (fun x y hx hy => ?_)
        · rw [map_smul]
          exact Submodule.smul_mem_smul hb (hf x)
        · rw [map_add (f := _)]
          exact add_mem hx hy
      exact key (liftLa (quotEquiv J.Q.l.Mb ((O i).lev g)) - (O i).lev g) (hspec g)
    rw [Submodule.ideal_span_singleton_smul] at hd
    obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hd
    have hy' : liftLa (quotEquiv J.Q.l.Mb ((O i).lev g)) a = (O i).lev g a + J.Q.l.M • y := by
      rw [← Nat.cast_smul_eq_nsmul (𝓞 D.host.E), hy, add_sub_cancel]
    have hmem : finVec (Wc D i) (iotaW J i y) ∈ latGHat (Wc D i) 1 :=
      ((GlobalTheory.MarkCoset.latG_spec D (Wc D i) 1).1 _).1 (hι.2 ▸ LinearMap.mem_range_self (iotaW J i) y)
    refine ⟨w + finVec (Wc D i) (iotaW J i y), add_mem hwm hmem, ?_⟩
    have e2 : GlobalTheory.LevelActionPinned.fvec (Wc D i) (iotaW J i) (liftLa (quotEquiv J.Q.l.Mb ((O i).lev g)) a) =
        GlobalTheory.LevelActionPinned.fvec (Wc D i) (iotaW J i) ((O i).lev g a) +
          J.Q.l.M • GlobalTheory.LevelActionPinned.fvec (Wc D i) (iotaW J i) y := by
      rw [hy', map_add (f := _), map_nsmul]
    have e3 : finVec (Wc D i) (iotaW J i (liftLa (quotEquiv J.Q.l.Mb ((O i).lev g)) a)) =
        finVec (Wc D i) (iotaW J i ((O i).lev g a)) + J.Q.l.M • finVec (Wc D i) (iotaW J i y) := e2
    rw [e3, nsmul_add, ← e]
    abel

  · obtain ⟨cc, ph, hone⟩ := hrow i
    have hkeep : ActKeeps (κ := κ) O i := fun g f hf => by
      obtain ⟨k, hk, -⟩ := hlev g
      exact (hone.1 g k hk f hf).1
    have hrho' := (hrho i).1 hkeep
    have hact_eq : ∀ g, actLev (Xo := J.Q.Xo ((i : ℕ) + 1)) J.Q.c (levFull (J.Q.Dw ((i : ℕ) + 1)) J.Q.l)
        (quotEquiv J.Q.l.Mb ((O i).lev g)) = actLev J.Q.c (O i).lev2 g := fun g => by
      have e1 : actLev (Xo := J.Q.Xo ((i : ℕ) + 1)) J.Q.c (levFull (J.Q.Dw ((i : ℕ) + 1)) J.Q.l)
          (quotEquiv J.Q.l.Mb ((O i).lev g)) = actLev (Xo := J.Q.Xo ((i : ℕ) + 1)) J.Q.c
          (fun _ : Unit => levFull (J.Q.Dw ((i : ℕ) + 1)) J.Q.l (quotEquiv J.Q.l.Mb ((O i).lev g))) () := rfl
      have e2 : actLev (Xo := J.Q.Xo ((i : ℕ) + 1)) J.Q.c (O i).lev2 g =
          actLev (Xo := J.Q.Xo ((i : ℕ) + 1)) J.Q.c (fun _ : Unit => (O i).lev2 g) () := rfl
      rw [e1, e2, GlobalTheory.OneMapAllCompare.actLev_congr (lev' := fun _ : Unit => (O i).lev2 g) J.Q.c hA (fun _ a => hspec g a)]
    obtain ⟨act, hact⟩ := GlobalTheory.FormTies.exists_isLevAct D r.full.toTop h.p ((i : ℕ) + 1) (inR_succ i) (κ i) G
      (fun g => quotEquiv J.Q.l.Mb ((O i).lev g))
    refine ⟨act, hact, fun g F => ?_⟩
    obtain ⟨hf, he⟩ := hrho' g ⟨F.1, cutR_le J.toCore.C ((i : ℕ) + 1) (κ i) F.2⟩
    have e : (act g F).1 = actLev (Xo := J.Q.Xo ((i : ℕ) + 1)) J.Q.c (O i).lev2 g F.1 := (hact g F).trans (LinearMap.congr_fun (hact_eq g) F.1)
    change ((fw.e i ⟨(act g F).1, _⟩ : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL) =
      (R.FW i).ρ g ((fw.e i ⟨F.1, _⟩ : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL)
    rw [← he]
    congr 3

end GlobalTheory.LevelActionOnto
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.weil_vacuum_scalar_eq_one_inert_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, ∀ c : ℂ, Acts (evFin F v) (om' (1, k)) (G.M'.vac v) (c • G.M'.vac v) → c = 1 := by
  first | exact @GlobalTheory.InertScalar.scalar_eq_one | exact GlobalTheory.InertScalar.scalar_eq_one | (intros; apply GlobalTheory.InertScalar.scalar_eq_one <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_normalisedTupleData_given_level_coeffMaps : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) , R.toLevCh.Is A.μ0 → R.grp_chiW → R.IsFam → R.IsModels → R.thP_vP → Nonempty (FWTie T R κ v₀) → T.pb = R.C.P.pb → Finite T0 → QGuard R → ∀ i : Fin D.R.m, VStd D i → ∀ (lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La), LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) lev → ∀ (gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E) (c0R : VV D.what₂.LL (fun τ => Bridge.lamRdef (Ptw D) τ) →ₛₗ[D.what₂.embLL] R.cX.coef.W) (c0L : ∀ i : Fin D.R.m, VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).coef.W), Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L → ∃ O' : OMDat T.toCore R i T0 id, D.what₂.embLL.toRatAlgHom.fieldRange ≤ O'.c'.F ∧ O'.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O'.s0) ∧ O'.lev = lev ∧ CoefficientBaseChange R i O'.jL (inC O'.c') (c0L i) O'.c0' := by
  first | exact @GlobalTheory.PinnedDataGiven.exists_pins_given | exact GlobalTheory.PinnedDataGiven.exists_pins_given | (intros; apply GlobalTheory.PinnedDataGiven.exists_pins_given <;> assumption)
end
