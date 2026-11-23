module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle977
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle822
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle781
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle787
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle782
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle723
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle331
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle339
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle965
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle966
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle967
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle720
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle885
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle980
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle762
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle797
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle886
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle763
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

@[expose] public section

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.exists_virtualCharacter_shintani_psi_lift : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (Module.finrank F F').Prime → s ≠ 1 → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') (θ : AlgebraicClosure F' →* ℂ), (∀ x y : AlgebraicClosure F', x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ k n : ℕ, ∃ X ∈ Virt ℂ ℂ (GHat F F' n), (∀ g, X (inl g) = psiG (fun P => ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F'))) n g) ∧ ∀ δ, X (inl δ * inr s) = shLift s (psiG (rootSum (pullθ ι θ) k) n) δ := by
  first | (exact @GlobalTheory.Shin.exists_virt_psi_lift) | (exact GlobalTheory.Shin.exists_virt_psi_lift) | (intros; apply GlobalTheory.Shin.exists_virt_psi_lift  <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.AlgTau

theorem main : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (Λ : PeriodPair) (c Ω : ℂ) (τ : ℍ), 0 < d → δ ^ 2 = -(d : K) → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf ι 𝔞 Λ → IsTauOf Λ c τ → Ω ^ 12 = latDisc Λ → (Ω * c / (2 * Real.pi * Complex.I)) ^ 12 = DD τ ∧ IsAlgebraic ℚ (jT τ) ∧ IsAlgebraic ℚ (G2s τ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 / (Ω * c / (2 * Real.pi * Complex.I)) ^ 2) ∧ ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N), IsAlgebraic ℚ (wp N x τ / (Ω * c / (2 * Real.pi * Complex.I)) ^ 2) := by
  intro K _ _ d δ ι 𝔞 Λ c Ω τ hd hδ hlat htau hΩ
  obtain ⟨-, hmul, him, -⟩ := GlobalTheory.T.fractionalIdealLattice_has_nonreal_multiplier K d δ ι 𝔞 Λ hd hδ hlat
  have hval := GlobalTheory.T.eisensteinWeierstrass_values_lattice_tau Λ c Ω τ htau
  have halg := GlobalTheory.T.algebraic_normalized_weierstrass_values_cm Λ (ι δ) Ω hmul him hΩ
  refine ⟨(GlobalTheory.QFam.jT_eq_and_pow_twelve_eq_DD Λ c τ htau).2 Ω hΩ, ?_, ?_, ?_⟩
  · have hj : IsIntegral ℤ (jT τ) := GlobalTheory.T.isIntegral_jInvariant_of_complexMultiplication Λ c τ (ι δ) htau hmul him
    exact (hj.tower_top (A := ℚ)).isAlgebraic
  · rw [hval.1]; exact halg.1
  · intro N _ x
    rw [(hval.2 N x).1]
    have hN : (N : ℂ) * (c * tors N τ x) ∈ Λ.lattice := by
      have h1 := ((GlobalTheory.T.weierstrassP_homogeneity_of_isTauOf Λ c τ htau).1 ((N : ℂ) * tors N τ x)).2
        ((GlobalTheory.T.torsionPointOfLatticeTau_lattice_membership N τ).2.2.2.1 x)
      simpa [mul_left_comm] using h1
    exact (halg.2 N (c * tors N τ x) (Nat.pos_of_ne_zero (NeZero.ne N)) hN).1

end GlobalTheory.AlgTau
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.RingContH

theorem main : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ x : H R (sp c.pt) F n, ∃ j y, pull R (spMap (c.ι.app j).hom) F n y = x) ∧ ∀ j (y : H R (sp (D.obj j)) F n), pull R (spMap (c.ι.app j).hom) F n y = 0 → ∃ (k : J) (f : j ⟶ k), pull R (spMap (D.map f).hom) F n y = 0 := by
  intro R _ F hF J _ _ D c hc n
  obtain ⟨_, cl, hsurj, heq, hzero, hpull⟩ := GlobalTheory.EtC.HCElements.main R F
  obtain ⟨h1, h2⟩ := GlobalTheory.T.ringCohomologyComplex_continuous_filtered_colimit R F hF J D c hc n
  refine ⟨fun x => ?_, fun j y hy => ?_⟩
  · obtain ⟨z, hz, rfl⟩ := hsurj (sp c.pt) n x
    obtain ⟨j, w, y, hw, hwy⟩ := h1 z hz
    refine ⟨j, cl _ n w hw, ?_⟩
    obtain ⟨h, hh⟩ := hpull (sp c.pt) (sp (D.obj j)) (spMap (c.ι.app j).hom) n w hw
    rw [hh, heq]
    exact ⟨y, hwy⟩
  · obtain ⟨w, hw, rfl⟩ := hsurj (sp (D.obj j)) n y
    obtain ⟨h, hh⟩ := hpull (sp c.pt) (sp (D.obj j)) (spMap (c.ι.app j).hom) n w hw
    rw [hh, hzero] at hy
    obtain ⟨k, f, y', hy'⟩ := h2 j w hw hy
    refine ⟨k, f, ?_⟩
    obtain ⟨h', hh'⟩ := hpull (sp (D.obj k)) (sp (D.obj j)) (spMap (D.map f).hom) n w hw
    rw [hh', hzero]
    exact ⟨y', hy'⟩

end GlobalTheory.EtC.RingContH
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.exists_holomorphicSection_of_rapid_cauchy_dbar : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (t K : ℝ) (F : ℕ → ι → Y → ℂ), 0 < t → CurvGe C la t → 0 ≤ K → (∀ m, A.IsSSec (A.kap + la) (F m)) → (∀ m, n0 A la (F m - F (m + 1)) ≤ ENNReal.ofReal (K / 4 ^ m)) → Tendsto (fun m => n1 C la (F m)) atTop (𝓝 0) → ∃ G : ι → Y → ℂ, A.IsSec (A.kap + la) G ∧ n0 A la (F 0 - G) ≤ ENNReal.ofReal (4 * K) := by
  first | exact @GlobalTheory.OTY.exists_isSec_of_rapid_cauchy | exact GlobalTheory.OTY.exists_isSec_of_rapid_cauchy | (intros; apply GlobalTheory.OTY.exists_isSec_of_rapid_cauchy <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.exists_local_hormander_iteration_step : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ C : Cover A, ∃ K : ℝ, 0 ≤ K ∧ ∀ (la : La) (t : ℝ), 0 < t → CurvGe C la t → ∀ F0 : ι → Y → ℂ, A.IsSSec (A.kap + la) F0 → ∃ F1 : ι → Y → ℂ, A.IsSSec (A.kap + la) F1 ∧ n0 A la (F0 - F1) ≤ ENNReal.ofReal (K / t) * n1 C la F0 ∧ n1 C la F1 ≤ ENNReal.ofReal (K / t) * n1 C la F0 := by
  first | exact @GlobalTheory.hormander_step | exact GlobalTheory.hormander_step | (intros; apply GlobalTheory.hormander_step <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.LogPair

theorem relSnc_pull_of_isOpenImmersion : ∀ (R : Type) [CommRing R] (X Y : Scheme.{0}) (f : X ⟶ Sp R) (e : Y ⟶ X) [IsOpenImmersion e] (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec), RelSnc f d L σ → RelSnc (e ≫ f) d (fun i => (L i).pull e) (fun i => Cartier.secPull (σ i) e) := by
  intro R _ X Y f e _ d s L σ h
  refine ⟨fun i => LB.isLB_pull (h.isLB i) e, fun y => ?_⟩
  obtain ⟨C, hC⟩ := h.chart (e y)
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWV⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (a := y) (u := (e ⁻¹ᵁ C.U : Y.Opens)) hC
      (e ⁻¹ᵁ C.U).isOpen
  have hle : W ≤ e ⁻¹ᵁ C.U := hWV
  have hap : ∀ a : Γ(X, C.U), (e.appLE C.U W hle).hom a = resG Y hle ((e.app C.U).hom a) :=
    fun _ => rfl
  refine ⟨{ U := W
            affine := hW
            t := fun a => (e.appLE C.U W hle).hom (C.t a)
            etale := GlobalTheory.T.isEtaleCoordinatesOnOpen_pull_openImmersion R X Y f e C.U W hle d C.t C.affine hW C.etale
            c := fun i _ => C.c i
            le := fun i => (hle.trans (e.preimage_mono (C.le i))).trans
              (Cartier.pull_U (L i) e (fun _ => C.c i)).ge
            e := C.e
            inj := C.inj
            u := fun i => Units.map (e.appLE C.U W hle).hom.toMonoidHom (C.u i)
            eq := fun i => ?_ }, hyW⟩
  have h1 := congrArg (e.appLE C.U W hle).hom (C.eq i)
  rw [map_mul, hap, Cartier.app_resG, Cartier.resG_resG] at h1
  refine (Cartier.resG_resG _ _ _).trans (h1.trans ?_)
  congr 1
  cases C.e i with
  | none => exact map_one _
  | some a => rfl

end GlobalTheory.LogPair
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isEtaleCoordinatesOnOpen_restrict_affineOpen : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (U W : X.Opens) (h : W ≤ U) (d : ℕ) (t : Fin d → Γ(X, U)), IsAffineOpen U → IsAffineOpen W → IsEtCoord f U t → IsEtCoord f W (fun a => resG X h (t a)) := by
  first | exact @GlobalTheory.LogPair.isEtCoord_res | exact GlobalTheory.LogPair.isEtCoord_res | (intros; apply GlobalTheory.LogPair.isEtCoord_res <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.LogPair

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX isPushout_sections)

theorem isEtCoord_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) (U : X.Opens) (d : ℕ) (t : Fin d → Γ(X, U)), IsPullback π f' f (spMap φ) → IsAffineOpen U → IsEtCoord f U t → IsAffineOpen (π ⁻¹ᵁ U) ∧ IsEtCoord f' (π ⁻¹ᵁ U) (fun a => (π.app U).hom (t a)) := by
  intro R R' _ _ φ X X' f f' π U d t H hU ht
  refine ⟨GlobalTheory.TopForm.isAffineOpen_preimage_of_isPullback H hU, ?_⟩
  letI := φ.toAlgebra
  letI := MvPolynomial.algebraMvPolynomial (R := R) (S := R') (σ := Fin d)
  have h₁ := (CommRingCat.isPushout_of_isPushout R R' (MvPolynomial (Fin d) R) (MvPolynomial (Fin d) R')).flip
  have hx : (MvPolynomial.eval₂Hom (algX f U) t).Etale := ht
  have key : ∀ (W : X'.Opens) (hle : W ≤ π ⁻¹ᵁ U),
      IsPushout (CommRingCat.ofHom (algX f U)) (CommRingCat.ofHom (algebraMap R R'))
        (π.appLE U W hle) (CommRingCat.ofHom (algX f' W)) →
      (MvPolynomial.eval₂Hom (algX f' W) fun a => (π.appLE U W hle).hom (t a)).Etale := by
    intro W hle h₂
    have e₁ : CommRingCat.ofHom (algX f U) = CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin d) R)) ≫
        CommRingCat.ofHom (MvPolynomial.eval₂Hom (algX f U) t) := by
      ext a
      exact (MvPolynomial.eval₂Hom_C _ _ a).symm
    have e₂ : CommRingCat.ofHom (algX f' W) =
        CommRingCat.ofHom (algebraMap R' (MvPolynomial (Fin d) R')) ≫
        CommRingCat.ofHom (MvPolynomial.eval₂Hom (algX f' W) fun a => (π.appLE U W hle).hom (t a)) := by
      ext a
      exact (MvPolynomial.eval₂Hom_C _ _ a).symm
    have hw := h₂.w
    rw [e₁, e₂] at h₂
    have h₃ := h₂.of_left (CommRingCat.hom_ext (MvPolynomial.ringHom_ext (fun a => ?_) fun a => ?_)) h₁
    · have := RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2 RingHom.Etale.isStableUnderBaseChange
      exact MorphismProperty.of_isPushout (P := RingHom.toMorphismProperty RingHom.Etale) h₃.flip hx
    · change (π.appLE U W hle).hom (MvPolynomial.eval₂Hom _ _ (MvPolynomial.C a)) =
        MvPolynomial.eval₂Hom _ _ (MvPolynomial.map φ (MvPolynomial.C a))
      rw [MvPolynomial.map_C, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
      exact congrArg (fun g => (CommRingCat.Hom.hom g) a) hw
    · change (π.appLE U W hle).hom (MvPolynomial.eval₂Hom _ _ (MvPolynomial.X a)) =
        MvPolynomial.eval₂Hom _ _ (MvPolynomial.map φ (MvPolynomial.X a))
      rw [MvPolynomial.map_X, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
  have h₄ := key _ inf_le_left (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.isPushout_sections f f' π H U hU)
  have tr : ∀ (W : X'.Opens) (hle : W ≤ π ⁻¹ᵁ U), W = π ⁻¹ᵁ U →
      (MvPolynomial.eval₂Hom (algX f' W) fun a => (π.appLE U W hle).hom (t a)).Etale →
      IsEtCoord f' (π ⁻¹ᵁ U) (fun a => (π.app U).hom (t a)) := by
    rintro W hle rfl h
    rw [Scheme.Hom.app_eq_appLE]
    exact h
  exact tr _ _ (inf_top_eq _) h₄

end GlobalTheory.LogPair
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isRegularOnOpenUniformised_of_locally : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.Opens) (k : (Fin g → ℂ) → ℂ), (∀ z ∈ pre u.ex U, ∃ W : A.left.Opens, W ≤ U ∧ z ∈ pre u.ex W ∧ IsReg u.ex W k) → IsReg u.ex U k := by
  first | exact @GlobalTheory.CechPer.isReg_of_locally | exact GlobalTheory.CechPer.isReg_of_locally | (intros; apply GlobalTheory.CechPer.isReg_of_locally <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.hasCechDeRhamPeriods_of_affine_basis : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (c : cechDeRhamTotalCocyclesOne (OAff (str A))) (K : Type) (W : K → A.left.affineOpens) (k : K → (Fin g → ℂ) → ℂ) (q : u.Λ → ℂ), (∀ i j, ∀ z ∈ pre u.ex (W i).1, z ∈ pre u.ex (W j).1 → ∃ l, W l ≤ W i ∧ W l ≤ W j ∧ z ∈ pre u.ex (W l).1 ∧ (∀ a : Opposite.op (W i) ⟶ Opposite.op (W l), k l z = k i z + val u.ex (W l).1 (c.1.1 _ _ a) z) ∧ ∀ a : Opposite.op (W j) ⟶ Opposite.op (W l), k l z = k j z + val u.ex (W l).1 (c.1.1 _ _ a) z) → (∀ (U : A.left.affineOpens), ∀ z ∈ pre u.ex U.1, ∃ i, W i ≤ U ∧ z ∈ pre u.ex (W i).1) → (∀ i, DifferentiableOn ℂ (k i) (pre u.ex (W i).1)) → (∀ i, ∀ z ∈ pre u.ex (W i).1, fderiv ℂ (k i) z = evForm u.ex (W i).1 z (c.1.2 (Opposite.op (W i)))) → (∀ i (l : u.Λ), ∀ z ∈ pre u.ex (W i).1, k i (z + l) = k i z + q l) → IsPer u.ex u.Λ (Hyp1.mk _ c) q := by
  first | exact @GlobalTheory.CechPer.isPer_of_basis | exact GlobalTheory.CechPer.isPer_of_basis | (intros; apply GlobalTheory.CechPer.isPer_of_basis <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.hasCechDeRhamPeriods_zero_class_eq_zero : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ q, IsPer u.ex u.Λ 0 q → q = 0 := by
  first | exact @GlobalTheory.CechPer.zero_periods_eq_zero | exact GlobalTheory.CechPer.zero_periods_eq_zero | (intros; apply GlobalTheory.CechPer.zero_periods_eq_zero <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section
namespace GlobalTheory.AbCoh.StepPrim

theorem pO1_comp {R : Type} [CommRing R] {X Y Z : Over (Sp R)} (f : X ⟶ Y) (g : Y ⟶ Z) (a : HO1 Z.hom) :
    pO1 (f ≫ g) a = pO1 f (pO1 g a) :=
  ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id).1 R R Z.left Y.left Z.hom Y.hom (RingHom.id R) g.left (ovw g) R X.left X.hom
    (RingHom.id R) f.left (ovw f) (RingHom.id R) (f ≫ g).left (ovw (f ≫ g)) (Over.comp_left _ _ _ f g)
    (fun _ ↦ rfl)).1 a |>.symm

theorem pO1_id {R : Type} [CommRing R] (A : Over (Sp R)) (a : HO1 A.hom) : pO1 (𝟙 A) a = a :=
  ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id).2.2 R A).1 a

theorem eq_zero_of_base {R : Type} [CommRing R] (a : HO1 (𝟙_ (Over (Sp R))).hom) : a = 0 := by
  haveI := ((GlobalTheory.AbCoh.Vanish.main).1 R (𝟙_ (Over (Sp R))).left (𝟙_ (Over (Sp R))).hom
    (inferInstanceAs (IsAffine (Sp R)))).1
  exact Subsingleton.elim _ _

theorem axes_defect {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (x : HO1 A.hom) :
    pO1 (lift (𝟙 A) (1 : A ⟶ A)) (pO1 μ[A] x - pO1 (fst A A) x - pO1 (snd A A) x) = 0 ∧
    pO1 (lift (1 : A ⟶ A) (𝟙 A)) (pO1 μ[A] x - pO1 (fst A A) x - pO1 (snd A A) x) = 0 := by
  have h1 : ∀ a : HO1 A.hom, pO1 (1 : A ⟶ A) a = 0 := fun a ↦ by
    rw [Hom.one_def, pO1_comp, eq_zero_of_base (pO1 η[A] a), map_zero]
  refine ⟨?_, ?_⟩
  · rw [map_sub, map_sub, ← pO1_comp, ← pO1_comp, ← pO1_comp, lift_fst, lift_snd, ← Hom.mul_def,
      _root_.mul_one, pO1_id, h1, sub_self, sub_zero]
  · rw [map_sub, map_sub, ← pO1_comp, ← pO1_comp, ← pO1_comp, lift_fst, lift_snd, ← Hom.mul_def,
      _root_.one_mul, pO1_id, h1, sub_zero, sub_self]

theorem main : ∀ (R : Type) [CommRing R] [IsLocalRing R] (t : R) (R' : Type) [CommRing R'] (σ' : R →+* R'), Function.Surjective σ' → RingHom.ker σ' = Ideal.span {t} → t ≠ 0 → (∀ a ∈ IsLocalRing.maximalIdeal R, a * t = 0) → (∀ (k : Type) [CommRing k], IsField k → ∀ (B : Over (Sp k)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → AxesVanishingStructureSheafDegOne B ∧ NoPrimitiveStructureSheafH2 B ∧ WedgeO (OAff B.hom)) → (∀ (B : Over (Sp R')) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → StructureSheafH1Primitive B) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → StructureSheafH1Primitive A := by
  intro R _ _ t R' _ σ' hsurj hker ht hmt hfield hR' A _ g hab hsm
  letI : Algebra R R' := σ'.toAlgebra
  have hkF : IsField (R ⧸ IsLocalRing.maximalIdeal R) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp inferInstance
  have hSE : SmallExt t (algebraMap R R') (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R)) := by
    refine ⟨hsurj, hker, Ideal.Quotient.mk_surjective, fun a ↦ ?_⟩
    rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    refine ⟨hmt a, fun h ↦ ?_⟩
    by_contra hna
    exact ht ((IsLocalRing.notMem_maximalIdeal.mp hna).mul_right_eq_zero.mp h)
  haveI := hsm
  haveI : Smooth A.hom := SmoothOfRelativeDimension.smooth g A.hom
  haveI : Flat A.hom := inferInstance
  have hfl2 : Flat (A ⊗ A).hom := by rw [Over.tensorObj_hom]; infer_instance
  obtain ⟨B', _, pr, pr', hab', hsm', hpr, hpr', hμ', hf', hs', he1', he2'⟩ := GlobalTheory.T.exists_abelianScheme_baseChange_and_square R R' A g hab hsm
  obtain ⟨B₀, _, pr0, pr0', hab0, hsm0, hpr0, hpr0', -, -, -, he10, he20⟩ :=
    GlobalTheory.T.exists_abelianScheme_baseChange_and_square R (R ⧸ IsLocalRing.maximalIdeal R) A g hab hsm
  intro x
  have key : pO1 μ[A] x - pO1 (fst A A) x - pO1 (snd A A) x = 0 := by
    set y := pO1 μ[A] x - pO1 (fst A A) x - pO1 (snd A A) x with hy
    have hnat := GlobalTheory.AbCoh.pull_over_baseChange_comm R R' (algebraMap R R') A (A ⊗ A) B' (B' ⊗ B')
    have ya : pullHO1 hpr'.w y = 0 := by
      have hP := hR' B' g hab' hsm' (pullHO1 hpr.w x)
      rw [hy, map_sub, map_sub, (hnat μ[A] μ[B'] pr pr' hpr.w hpr'.w hμ').1,
        (hnat (fst A A) (fst B' B') pr pr' hpr.w hpr'.w hf').1,
        (hnat (snd A A) (snd B' B') pr pr' hpr.w hpr'.w hs').1, hP]
      abel
    obtain ⟨u, hu⟩ := GlobalTheory.T.eq_smul_residueFibre_class_of_pullback_eq_zero R R' (R ⧸ IsLocalRing.maximalIdeal R) t (algebraMap R R')
      (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R)) (A ⊗ A).left (B' ⊗ B').left (B₀ ⊗ B₀).left (A ⊗ A).hom
      (B' ⊗ B').hom (B₀ ⊗ B₀).hom pr' pr0' hpr' hpr0' hSE hfl2 y ya
    have hH0 := (GlobalTheory.T.globalFunctionsConstantAfterBaseChange_of_abelianScheme R A hab) R' B'.left B'.hom pr hpr
    have hax := axes_defect A x
    have hu1 : pO1 (lift (𝟙 B₀) (1 : B₀ ⟶ B₀)) u = 0 :=
      GlobalTheory.T.residueFibre_class_eq_zero_of_smul_pullback_eq_zero R R' (R ⧸ IsLocalRing.maximalIdeal R) t (algebraMap R R')
        (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R)) (A ⊗ A).left (B' ⊗ B').left (B₀ ⊗ B₀).left (A ⊗ A).hom
        (B' ⊗ B').hom (B₀ ⊗ B₀).hom pr' pr0' hpr' hpr0' A.left B'.left B₀.left A.hom B'.hom B₀.hom pr pr0 hpr hpr0
        (lift (𝟙 A) (1 : A ⟶ A)).left (lift (𝟙 B') (1 : B' ⟶ B')).left (lift (𝟙 B₀) (1 : B₀ ⟶ B₀)).left
        (ovw _) (ovw _) (ovw _) he1' he10 hSE hfl2 inferInstance hH0 u y hu hax.1
    have hu2 : pO1 (lift (1 : B₀ ⟶ B₀) (𝟙 B₀)) u = 0 :=
      GlobalTheory.T.residueFibre_class_eq_zero_of_smul_pullback_eq_zero R R' (R ⧸ IsLocalRing.maximalIdeal R) t (algebraMap R R')
        (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R)) (A ⊗ A).left (B' ⊗ B').left (B₀ ⊗ B₀).left (A ⊗ A).hom
        (B' ⊗ B').hom (B₀ ⊗ B₀).hom pr' pr0' hpr' hpr0' A.left B'.left B₀.left A.hom B'.hom B₀.hom pr pr0 hpr hpr0
        (lift (1 : A ⟶ A) (𝟙 A)).left (lift (1 : B' ⟶ B') (𝟙 B')).left (lift (1 : B₀ ⟶ B₀) (𝟙 B₀)).left
        (ovw _) (ovw _) (ovw _) he2' he20 hSE hfl2 inferInstance hH0 u y hu hax.2
    have hu0 : u = 0 := (hfield _ hkF B₀ g hab0 hsm0).1 u hu1 hu2
    subst hu0
    exact GlobalTheory.T.smallExtension_element_mul_zeroClass_eq_zero R R' (R ⧸ IsLocalRing.maximalIdeal R) t (algebraMap R R')
      (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R)) (A ⊗ A).left (B' ⊗ B').left (B₀ ⊗ B₀).left (A ⊗ A).hom
      (B' ⊗ B').hom (B₀ ⊗ B₀).hom pr' pr0' hpr' hpr0' hSE hfl2 y hu
  rw [sub_sub, sub_eq_zero] at key
  exact key

end GlobalTheory.AbCoh.StepPrim
end
end
