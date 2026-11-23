module

import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle300
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinates
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDpOfCompOnGens
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEtaleLiftOfSurjective
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.MinusculeCentralEigen
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic
import GroundTheory.AutomorphicForms.Bundle008
public import GroundTheory.AutomorphicForms.MacdonaldHecke
public import GroundTheory.AutomorphicForms.MacdonaldWhittakerHecke
import GroundTheory.LocalFields.LocalFourierHaar
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaMeasureSimilitude
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import GroundTheory.AutomorphicForms.SmoothRep
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Intertwining
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle302
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle296
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.CuspGenericWhittaker.CuspGeneric
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.FlatChartP

open GlobalTheory.CompanionTheory.ChartAlg

theorem flat_of_etale_poly {R D : Type} [CommRing R] [CommRing D] (i : R →+* D) {d : ℕ} (t : Fin d → D)
    (h : (MvPolynomial.eval₂Hom i t : MvPolynomial (Fin d) R →+* D).Etale) : i.Flat := by
  have h1 : (MvPolynomial.eval₂Hom i t : MvPolynomial (Fin d) R →+* D).Flat :=
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp h).1
  have h2 : (algebraMap R (MvPolynomial (Fin d) R)).Flat := RingHom.flat_algebraMap_iff.2 inferInstance
  have e : i = (MvPolynomial.eval₂Hom i t).comp (algebraMap R (MvPolynomial (Fin d) R)) := by
    ext x
    simp [MvPolynomial.algebraMap_eq]
  rw [e]
  exact RingHom.Flat.comp h2 h1

theorem rep_lift {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V : X.Opens} {d : ℕ} (hV : IsAffineOpen V)
    {T : Fin d → Γ(X, V)} (L : CrystallineSemistableComparison.B.Lift (strV q V) T R I κ) (y : PtOver X q κ (L.D ⧸ I.map L.i))
    (h1 : ∀ r, y.1.1 (Ideal.Quotient.mk I r) = Ideal.Quotient.mk _ (L.i r))
    (h2 : y.1.2 = Spec.map (CommRingCat.ofHom L.j) ≫ hV.fromSpec)
    (B : CommRingCat.{0}) (y' : PtOver X q κ B) (hy' : ⊤ ≤ y'.1.2 ⁻¹ᵁ V) :
    ∃! φ : L.D ⧸ I.map L.i →+* B, (ptFun X q κ).map (CommRingCat.ofHom φ) y = y' := by
  let e' : Γ(X, V) →+* B := GlobalTheory.Cris.evalAt y'.1.2 V hy'
  let ψ' : R ⧸ I →+* B := y'.1.1
  have hcomp : ∀ o x, Ideal.Quotient.mk I x = κ o → e' (strV q V o) = (ψ'.comp (Ideal.Quotient.mk I)) x := by
    intro o x hx
    rw [RingHom.comp_apply, hx]
    exact evalAt_base q κ ψ' y'.1.2 y'.2 hy' o
  have hkill : ∀ x ∈ I, (ψ'.comp (Ideal.Quotient.mk I)) x = 0 := fun x hx => by
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
  obtain ⟨f, ⟨hf1, hf2⟩, hu⟩ := L.univ B (ψ'.comp (Ideal.Quotient.mk I)) e' hkill hcomp
  have hJ : ∀ a ∈ I.map L.i, f a = 0 := by
    have : I.map L.i ≤ RingHom.ker f := by
      refine Ideal.map_le_iff_le_comap.2 fun x hx => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, hf1]
      exact hkill x hx
    exact fun a ha => this ha
  let φ : L.D ⧸ I.map L.i →+* B := Ideal.Quotient.lift _ f hJ
  have hφj : φ.comp L.j = e' := by
    refine RingHom.ext fun r => ?_
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (L.j r)
    rw [RingHom.comp_apply, ← hz, Ideal.Quotient.lift_mk]
    exact hf2 r z hz
  refine ⟨φ, ?_, fun φ₂ h => ?_⟩
  · refine Subtype.ext (Prod.ext ?_ ?_)
    · refine RingHom.ext fun z => ?_
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
      change φ (y.1.1 (Ideal.Quotient.mk I r)) = ψ' (Ideal.Quotient.mk I r)
      rw [h1, Ideal.Quotient.lift_mk]
      exact RingHom.congr_fun hf1 r
    · change Spec.map (CommRingCat.ofHom φ) ≫ y.1.2 = y'.1.2
      rw [h2, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφj]
      exact eq_specMap hV _ hy'
  · have a : φ₂.comp y.1.1 = ψ' := congrArg (fun z => z.1.1) h
    have b : Spec.map (CommRingCat.ofHom φ₂) ≫ y.1.2 = y'.1.2 := congrArg (fun z => z.1.2) h
    have e : e' = φ₂.comp L.j := by
      refine evalAt_specMap hV (φ₂.comp L.j) y'.1.2 ?_ hy'
      rw [← b, h2, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hf : φ₂.comp (Ideal.Quotient.mk _) = f := by
      refine hu _ ⟨?_, fun r z hz => ?_⟩
      · refine RingHom.ext fun r => ?_
        rw [← a, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, h1]
      · rw [RingHom.comp_apply, hz, e]
        rfl
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun x => ?_)
    rw [hf]
    exact (Ideal.Quotient.lift_mk _ f hJ).symm

theorem exists_flat_chart : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} (γ : DividedPowers I) (p : ℕ) (hp : p ≠ 0)
    (hn : IsNilpotent (p : R)) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I) {V : X.Opens} {d : ℕ}
    (c : Coord q V d), ∃ c' : Chart γ p q κ V d, FlatT c'.D ∧ ∀ i, ev c'.D c'.inV (c.t i) = Ideal.Quotient.mk _ (c'.t i) := by
  apply GlobalTheory.CompanionTheory.ChartP.exists_chart <;> assumption

end GlobalTheory.CompanionTheory.FlatChartP
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

open MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa
  GroundTheory.Automorphic.Spherical HeckeAlgebra PositivityTheory.JacquetShalikaLocal
open ValuativeRel (valuation)
open scoped ValuativeRel Pointwise

namespace GlobalTheory.CompanionTheory.SatakeBound

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

local notation "π" => (GLnLocal.uniformizer F : F)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem torusPow_central (t : GL (Fin n) F) (c : GL (Fin n) F)
    (h : ∃ a : F, (t : Matrix (Fin n) (Fin n) F) = diagonal fun _ => a) : t * c = c * t := by
  obtain ⟨a, ha⟩ := h
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [Units.val_mul, Units.val_mul, ha, diagonal_mul, mul_diagonal, mul_comm]

theorem torusPow_one_mem_minusculeSet :
    torusPow F n (fun _ => 1) ∈ minusculeSet F n n := by
  apply PositivityTheory.JacquetShalikaLocal.MinusculeCentralEigen.torusPow_one_mem <;> assumption

theorem inv_mul_mem_integralGL_of_mem {x : GL (Fin n) F} (hx : x ∈ minusculeSet F n n) :
    (torusPow F n (fun _ => 1))⁻¹ * x ∈ integralGL F n := by
  obtain ⟨-, h2, h3⟩ := hx
  have hπ : π ≠ 0 := Cartan.uniformizer_ne_zero F
  have hdet : (x : Matrix (Fin n) (Fin n) F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 x.isUnit).ne_zero
  set ϖ := torusPow F n (fun _ => (1 : ℤ)) with hϖ
  have hk : ϖ * x⁻¹ ∈ integralGL F n := by
    refine mem_integralGL_of_forall_mem (fun i j => ?_) ?_
    · have : (ϖ * x⁻¹ : GL (Fin n) F) i j = π * (x⁻¹ : GL (Fin n) F) i j := by
        change ((ϖ : Matrix (Fin n) (Fin n) F) * ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) i j = _
        rw [hϖ, coe_torusPow, diagonal_mul]
        simp
      rw [this]
      exact h2 i j
    · have e : (((ϖ * x⁻¹ : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F).det *
          (x : Matrix (Fin n) (Fin n) F).det = π ^ n := by
        rw [← det_mul, ← Units.val_mul, inv_mul_cancel_right, hϖ, coe_torusPow, det_diagonal]
        simp
      have e' := congrArg (valuation F) e
      rw [map_mul, map_pow, h3] at e'
      have hv : valuation F π ^ n ≠ 0 := pow_ne_zero _ ((map_ne_zero _).2 hπ)
      exact mul_right_cancel₀ hv (by rw [e', one_mul])
  have := (integralGL F n).inv_mem hk
  rw [_root_.mul_inv_rev, inv_inv] at this
  rwa [show ϖ⁻¹ * x = x * ϖ⁻¹ by
    have hc := torusPow_central (ϖ⁻¹) x ⟨π⁻¹, by
      rw [show ϖ⁻¹ = torusPow F n (fun _ => (-1 : ℤ)) by rw [hϖ, ← torusPow_neg]; congr 1, coe_torusPow]
      simp⟩
    exact hc]

section Hecke

variable {V : Type} [AddCommGroup V] [Module ℂ V]
  [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

theorem integral_minusculeHecke_form (ρ : Representation ℂ (GL (Fin n) F) V) {v : V}
    (hK : ∀ g ∈ integralGL F n, ρ g v = v) (l : V →ₗ[ℂ] ℂ) (r : ℕ) {e : ℂ}
    (hT : ∑ᶠ c : GL (Fin n) F ⧸ integralGL F n,
      (minusculeSet F n r).indicator (fun _ => (1 : ℂ)) c.out • ρ c.out v = e • v)
    (g : GL (Fin n) F) :
    ∫ x, (minusculeHecke μ r : HeckeAlgebra μ) x * l (ρ (g * x) v) ∂μ =
      (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) * (e * l (ρ g v)) := by
  classical
  set Φ : GL (Fin n) F → ℂ := fun x =>
    (minusculeHecke μ r : HeckeAlgebra μ) x * l (ρ (g * x) v) with hΦ
  have hcs : HasCompactSupport Φ := by
    refine HasCompactSupport.intro (isCompact_minusculeSet r) fun x hx => ?_
    simp only [hΦ, minusculeHecke_apply, Set.indicator_of_notMem hx, zero_mul]
  have hKΦ : ∀ x, ∀ k ∈ integralOpen F n, Φ (x * k) = Φ x := by
    intro x k hk
    simp only [hΦ]
    rw [(HeckeAlgebraLevel.val_mem _ _ (minusculeHecke μ r) k hk x).2, ← mul_assoc, map_mul,
      Module.End.mul_apply, hK k hk]
  rw [integral_eq_smul_finsum_coset μ (integralOpen F n) (isCompact_integralGL F n) hcs hKΦ,
    Complex.real_smul]
  congr 1
  change (∑ᶠ x : GL (Fin n) F ⧸ integralGL F n, Φ x.out) = _
  set L : V →ₗ[ℂ] ℂ := l ∘ₗ ρ g with hL
  have hpt : ∀ c : GL (Fin n) F ⧸ integralGL F n, Φ c.out =
      L ((minusculeSet F n r).indicator (fun _ => (1 : ℂ)) c.out • ρ c.out v) := by
    intro c
    simp only [hΦ, hL, minusculeHecke_apply, map_smul, smul_eq_mul, LinearMap.comp_apply, map_mul,
      Module.End.mul_apply]
  have hfin : (Function.support fun c : GL (Fin n) F ⧸ integralGL F n =>
      (minusculeSet F n r).indicator (fun _ => (1 : ℂ)) c.out • ρ c.out v).Finite := by
    have hc : HasCompactSupport ((minusculeSet F n r).indicator (fun _ => (1 : ℂ))) :=
      HasCompactSupport.intro (isCompact_minusculeSet r) fun x hx => Set.indicator_of_notMem hx _
    refine (finite_image_mk_tsupport (integralOpen F n) hc).subset
      fun (c : GL (Fin n) F ⧸ integralGL F n) hc' => ?_
    refine ⟨c.out, subset_tsupport _ fun h0 => hc' ?_, QuotientGroup.out_eq' c⟩
    exact (congrArg (fun t : ℂ => t • ρ c.out v) h0).trans (zero_smul ℂ _)
  have hmap : L (∑ᶠ c : GL (Fin n) F ⧸ integralGL F n,
      (minusculeSet F n r).indicator (fun _ => (1 : ℂ)) c.out • ρ c.out v) =
      ∑ᶠ c : GL (Fin n) F ⧸ integralGL F n,
        L ((minusculeSet F n r).indicator (fun _ => (1 : ℂ)) c.out • ρ c.out v) :=
    AddMonoidHom.map_finsum (L : V →+ ℂ) hfin
  simp only [hpt]
  rw [← hmap, hT, map_smul, smul_eq_mul, hL, LinearMap.comp_apply]

theorem integral_centralHecke_form {f : GL (Fin n) F → ℂ}
    (hf : ∀ g, ∀ k ∈ integralGL F n, f (g * k) = f g) (g : GL (Fin n) F) :
    ∫ x, (centralHecke μ : HeckeAlgebra μ) x * f (g * x) ∂μ =
      (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) *
        f (g * torusPow F n (fun _ => -1)) := by
  set g₀ := torusPow F n (fun _ : Fin n => (-1 : ℤ))
  have e := integral_mul_left_eq_self (μ := μ)
    (fun x => (centralHecke μ : HeckeAlgebra μ) x * f (g * x)) g₀
  rw [← e]
  have hpt : (fun y => (centralHecke μ : HeckeAlgebra μ) (g₀ * y) * f (g * (g₀ * y))) =
      (integralGL F n : Set (GL (Fin n) F)).indicator (fun _ => f (g * g₀)) := by
    funext y
    rw [centralHecke_apply]
    by_cases hy : y ∈ integralGL F n
    · have hm : g₀ * y ∈ centralSet F n := by
        rw [mem_centralSet, inv_mul_cancel_left]
        exact hy
      rw [Set.indicator_of_mem hm, Set.indicator_of_mem (show y ∈ (integralGL F n : Set (GL (Fin n) F))
        from hy), one_mul, ← mul_assoc, hf _ _ hy]
    · have hm : g₀ * y ∉ centralSet F n := by
        rw [mem_centralSet, inv_mul_cancel_left]
        exact hy
      rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (show y ∉ (integralGL F n :
        Set (GL (Fin n) F)) from hy), zero_mul]
  rw [hpt, integral_indicator (isOpen_integralGL F n).measurableSet, setIntegral_const,
    Complex.real_smul]

end Hecke

theorem rho_torusPow_neg_one {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) F) V) {v : V}
    (hK : ∀ g ∈ integralGL F n, ρ g v = v) {e : ℂ} (he : e ≠ 0)
    (hT : ∑ᶠ c : GL (Fin n) F ⧸ integralGL F n,
      (minusculeSet F n n).indicator (fun _ => (1 : ℂ)) c.out • ρ c.out v = e • v) :
    ρ (torusPow F n (fun _ => -1)) v = e⁻¹ • v := by
  set ϖ := torusPow F n (fun _ => (1 : ℤ)) with hϖ
  set c₀ : GL (Fin n) F ⧸ integralGL F n := QuotientGroup.mk ϖ with hc₀
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (integralGL F n) ϖ
  have hout : c₀.out ∈ minusculeSet F n n := by
    rw [hc₀, hk]
    have := mul_mem_minusculeSet (torusPow_one_mem_minusculeSet (F := F) (n := n))
      (integralGL F n).one_mem k.2
    rwa [one_mul] at this
  have hsum : ∑ᶠ c : GL (Fin n) F ⧸ integralGL F n,
      (minusculeSet F n n).indicator (fun _ => (1 : ℂ)) c.out • ρ c.out v = ρ ϖ v := by
    rw [finsum_eq_single _ c₀ fun c hc => ?_]
    · rw [Set.indicator_of_mem hout, one_smul, hc₀, hk, map_mul, Module.End.mul_apply, hK _ k.2]
    · rw [Set.indicator_of_notMem, zero_smul]
      intro hm
      apply hc
      rw [← QuotientGroup.out_eq' c]
      exact (QuotientGroup.eq.2 (inv_mul_mem_integralGL_of_mem hm)).symm
  have h1 : ρ ϖ v = e • v := hsum.symm.trans hT
  have hinv : torusPow F n (fun _ => (-1 : ℤ)) = ϖ⁻¹ := by
    rw [hϖ, ← torusPow_neg]
    congr 1
  have h2 : ρ ϖ⁻¹ (ρ ϖ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [h1, map_smul] at h2
  rw [hinv]
  calc ρ ϖ⁻¹ v = e⁻¹ • (e • ρ ϖ⁻¹ v) := by rw [smul_smul, inv_mul_cancel₀ he, one_smul]
    _ = e⁻¹ • v := by rw [h2]

theorem esymmL_self : esymmL n n = monomial (fun _ : Fin n => (1 : ℤ)) := by
  rw [esymmL]
  have : (Finset.univ : Finset (Fin n)).powersetCard n = {Finset.univ} := by
    simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin n))
  rw [this, Finset.sum_singleton]
  congr 1
  funext i
  simp [lamS]

theorem evalAt_esymmL_self_mul (z : Fin n → ℂˣ) :
    evalAt z (esymmL n n) * evalAt z (monomial (fun _ : Fin n => (-1 : ℤ))) = 1 := by
  rw [← map_mul, esymmL_self, monomial, monomial, AddMonoidAlgebra.single_mul_single]
  have : (fun _ : Fin n => (1 : ℤ)) + (fun _ => -1) = 0 := by
    funext i
    simp
  rw [this, one_mul, ← AddMonoidAlgebra.one_def, map_one]

theorem heckeEigenvector_whittaker : L7 := by
  apply PositivityTheory.JacquetShalikaLocal.minuscule_eigenvalue <;> assumption

end GlobalTheory.CompanionTheory.SatakeBound

end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.theta_measure_independent_choices : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ μ' : Measure (HA (AF F) σ J)) (𝓕 𝓕' : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → IsHaarH F E σ M J μ' → IsFDH F E σ M J μ' 𝓕' → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), thetaMeas σ J μ 𝓕 {X | gramE σ J X = T} = thetaMeas σ J μ' 𝓕' {X | gramE σ J X = T} := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThetaIndep.thetaMeas_gram_indep | exact GlobalTheory.CompanionTheory.SW.ThetaIndep.thetaMeas_gram_indep | (intros; apply GlobalTheory.CompanionTheory.SW.ThetaIndep.thetaMeas_gram_indep <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.theta_measure_similitude : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (γ : GL (Fin M) E) (l : F), l ≠ 0 → cT (σ : E →+* E) (γ : Matrix (Fin M) (Fin M) E) * J * (γ : Matrix (Fin M) (Fin M) E) = (algebraMap F E l) • J → ∃ (μ' : Measure (HA (AF F) σ J)) (𝓕' : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ' ∧ IsFDH F E σ M J μ' 𝓕' ∧ ∀ (n : ℕ) (T T' : Matrix (Fin n) (Fin n) E), T' = (algebraMap F E l) • T → (thetaMeas σ J μ' 𝓕' {X | gramE σ J X = T}).map (actTup (AF F) (bc (inclR (AF F)) γ)) = thetaMeas σ J μ 𝓕 {X | gramE σ J X = T'} := by
  first | exact @GlobalTheory.CompanionTheory.SW.SimTheta.theta_simil | exact GlobalTheory.CompanionTheory.SW.SimTheta.theta_simil | (intros; apply GlobalTheory.CompanionTheory.SW.SimTheta.theta_simil <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Whit

namespace GlobalTheory.CompanionTheory.AdmDict

theorem fixed_eq_fixedVectors {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (K : Subgroup G) :
    GlobalTheory.PRep.fixed ρ K = GroundTheory.Automorphic.fixedVectors ρ K := by
  ext v
  constructor
  · intro hv h hh
    simpa using hv ⟨h, hh⟩
  · intro hv h
    simpa using hv h h.2

theorem isAdmissible_iff : ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), GlobalTheory.PRep.IsAdmissible ρ ↔ GroundTheory.Automorphic.IsAdmissible ρ := by
  intro G V _ _ _ _ _ ρ
  have hs : GlobalTheory.PRep.IsSmooth ρ ↔ GroundTheory.Automorphic.IsSmooth ρ := Iff.rfl
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨hs.1 h1, fun K hc ho => ?_⟩
    have := h2 K ho hc
    rwa [fixed_eq_fixedVectors] at this
  · rintro ⟨h1, h2⟩
    refine ⟨hs.2 h1, fun K ho hc => ?_⟩
    rw [fixed_eq_fixedVectors]
    exact h2 K hc ho

end GlobalTheory.CompanionTheory.AdmDict
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.CIndCongr

variable {G W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

def mapFun (H : Subgroup G) {σ : Representation ℂ H W} {σ' : Representation ℂ H W'}
    (L : W ≃ₗ[ℂ] W') (hL : ∀ (h : H) (w : W), L (σ h w) = σ' h (L w))
    (f : cIndSpace H σ) : cIndSpace H σ' :=
  have hind : (fun g => L (f.1.1.1 g)) ∈ indSpace H σ' := by
    intro h g
    have e : f.1.1.1 ((h : G) * g) = σ h (f.1.1.1 g) := f.1.1.2 h g
    show L (f.1.1.1 ((h : G) * g)) = σ' h (L (f.1.1.1 g))
    rw [e, hL]
  have hsm : (⟨fun g => L (f.1.1.1 g), hind⟩ : indSpace H σ') ∈ smoothPart (ind H σ') := by
    obtain ⟨K, hK, hKi⟩ := cInd_right_inv H σ f
    refine GlobalTheory.CompanionTheory.BZMirOnto.isOpen_fixed_of_subgroup (ind H σ') K hK _ fun x hx => ?_
    apply Subtype.ext
    funext g
    show L (f.1.1.1 (g * x)) = L (f.1.1.1 g)
    rw [hKi g x hx]
  have hc : (⟨⟨fun g => L (f.1.1.1 g), hind⟩, hsm⟩ : smoothPart (ind H σ')) ∈ cIndSpace H σ' := by
    obtain ⟨C, hC, hf⟩ := f.2
    refine ⟨C, hC, fun g hg => hf g fun h0 => hg ?_⟩
    show L (f.1.1.1 g) = 0
    rw [h0, map_zero]
  ⟨⟨⟨fun g => L (f.1.1.1 g), hind⟩, hsm⟩, hc⟩

theorem ext_fun {H : Subgroup G} {σ : Representation ℂ H W} {f f' : cIndSpace H σ}
    (h : ∀ g, f.1.1.1 g = f'.1.1.1 g) : f = f' :=
  Subtype.ext (Subtype.ext (Subtype.ext (funext h)))

theorem nonempty_equiv_cInd :
    ∀ {G W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (H : Subgroup G) (σ : Representation ℂ H W) (σ' : Representation ℂ H W'),
    σ.Equiv σ' → Nonempty ((cInd H σ).Equiv (cInd H σ')) := by
  intro G W W' _ _ _ _ _ _ _ H σ σ' e
  let L : W ≃ₗ[ℂ] W' := e.toLinearEquiv
  have hL : ∀ (h : H) (w : W), L (σ h w) = σ' h (L w) := fun h w =>
    LinearMap.congr_fun (e.isIntertwining' h) w
  have hL' : ∀ (h : H) (w : W'), L.symm (σ' h w) = σ h (L.symm w) := fun h w => by
    apply L.injective
    rw [L.apply_symm_apply, hL, L.apply_symm_apply]
  let T : cIndSpace H σ ≃ₗ[ℂ] cIndSpace H σ' :=
    { toFun := mapFun H L hL
      map_add' := fun f f' => ext_fun fun g => map_add L (f.1.1.1 g) (f'.1.1.1 g)
      map_smul' := fun c f => ext_fun fun g => map_smul L c (f.1.1.1 g)
      invFun := mapFun H L.symm hL'
      left_inv := fun f => ext_fun fun g => L.symm_apply_apply (f.1.1.1 g)
      right_inv := fun f => ext_fun fun g => L.apply_symm_apply (f.1.1.1 g) }
  refine ⟨Representation.Equiv.mk T fun x => LinearMap.ext fun f => ext_fun fun g => ?_⟩
  rfl

end GlobalTheory.CompanionTheory.CIndCongr

end
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

theorem _root_.GlobalTheory.T.langlands_single_segment_is_segment_rep : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Δ : Segment k) (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsL {Δ} π → IsLSeg Δ π := by
  first | exact @GlobalTheory.CompanionTheory.LocGL.isLSeg_of_isL_singleton | exact GlobalTheory.CompanionTheory.LocGL.isLSeg_of_isL_singleton | (intros; apply GlobalTheory.CompanionTheory.LocGL.isLSeg_of_isL_singleton <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

theorem _root_.GlobalTheory.T.pi_tensor_irreducible_nontrivial : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ {h : ℕ} (x : Fin h → IrrGL (k := k)), Nontrivial (PiTensorProduct ℂ (fun a => (x a).2.rep.V)) := by
  first | exact @GlobalTheory.CompanionTheory.TensorIrr.nontrivial_piTensorProduct_irrGL | exact GlobalTheory.CompanionTheory.TensorIrr.nontrivial_piTensorProduct_irrGL | (intros; apply GlobalTheory.CompanionTheory.TensorIrr.nontrivial_piTensorProduct_irrGL <;> assumption)
end
