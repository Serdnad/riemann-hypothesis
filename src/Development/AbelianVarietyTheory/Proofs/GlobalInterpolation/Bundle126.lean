module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle002
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsGlIsometryCompEqOfNondegenerate
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle077
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryStabilizerAnisotropicVectorEquivComplemen
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle009
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle060
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle125
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle124
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle025
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle115
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle032
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle040
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle021
public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IteratedFDerivAlgebraicDirectionsJetTransport
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle008
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerLattices
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003

@[expose] public section

section

namespace GlobalTheory.Proof.quotientMeasure_integration_formulas_unimodular

theorem quotientMeasures : GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.QuotientMeasures :=
  ⟨GlobalTheory.T.quotientInvariantMeasure_exists_unique_unimodular, GlobalTheory.T.quotientMeasure_normalised_by_haar_unique, GlobalTheory.T.existsUnique_haar_subgroup_quotient_integral_formula, GlobalTheory.T.existsUnique_haar_group_quotient_integral_formula, GlobalTheory.T.quotient_integration_formula_discrete_subgroup_left, GlobalTheory.T.weil_criterion_invariant_measure_homogeneous_space,
    GlobalTheory.T.compactSubgroup_quotient_invariant_measure⟩

end GlobalTheory.Proof.quotientMeasure_integration_formulas_unimodular
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure

theorem _root_.GlobalTheory.T.localUnitaryGroup_stabilizers_unimodular_finitePlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ v : HeightOneSpectrum (𝓞 F), UnimodularOver (Fv F v) σ J := by
  first | exact @GlobalTheory.LocalUnitaryUnimod.unimodularOver_adicCompletion | exact GlobalTheory.LocalUnitaryUnimod.unimodularOver_adicCompletion | (intros; apply GlobalTheory.LocalUnitaryUnimod.unimodularOver_adicCompletion <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure

theorem _root_.GlobalTheory.T.finiteAdelicUnitaryGroup_stabilizers_unimodular : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → UnimodularOver (Af F) σ J := by
  first | exact @GlobalTheory.FiniteAdelicUnimod.unimodularOver_finiteAdele | exact GlobalTheory.FiniteAdelicUnimod.unimodularOver_finiteAdele | (intros; apply GlobalTheory.FiniteAdelicUnimod.unimodularOver_finiteAdele <;> assumption)
end

section

open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

namespace GlobalTheory.RatOrbit

theorem hform_eq {A : Type} [CommRing A] {n : Type} [Fintype n] (s : A →+* A) (J : Matrix n n A) (a b : n → A) :
    Formalism.UG.hform s J a b = b ⬝ᵥ Jᵀ *ᵥ (⇑s ∘ a) := by
  simp only [Formalism.UG.hform, dotProduct, mulVec, transpose_apply, Function.comp, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_mem {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (s : A →+* A) (J : Matrix n n A)
    (g : GL n A) (hg : g ∈ Formalism.UG.UJ s J) (a b : n → A) :
    Formalism.UG.hform s J ((g : Matrix n n A) *ᵥ a) ((g : Matrix n n A) *ᵥ b) = Formalism.UG.hform s J a b := by
  have h : Formalism.UG.cT s (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
  have h1 : ⇑s ∘ ((g : Matrix n n A) *ᵥ a) = ((g : Matrix n n A).map s) *ᵥ (⇑s ∘ a) := by
    funext i
    exact RingHom.map_mulVec s _ _ i
  rw [hform_eq, hform_eq, h1]
  conv_rhs => rw [← h]
  simp only [Formalism.UG.cT, transpose_mul, transpose_transpose, ← mulVec_mulVec]
  rw [mulVec_transpose (g : Matrix n n A), dotProduct_comm b, ← dotProduct_mulVec, dotProduct_comm]

theorem bc_mem {R A : Type} [CommRing R] [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
    (p : R →+* A) (s : R →+* R) (t : A →+* A) (hp : ∀ x, p (s x) = t (p x)) (J : Matrix n n R)
    (g : GL n R) (hg : g ∈ Formalism.UG.UJ s J) : Formalism.UG.bc p g ∈ Formalism.UG.UJ t (J.map p) := by
  have h : Formalism.UG.cT s (g : Matrix n n R) * J * (g : Matrix n n R) = J := hg
  show Formalism.UG.cT t ((g : Matrix n n R).map p) * J.map p * (g : Matrix n n R).map p = J.map p
  rw [← GlobalTheory.UnitarySplit.map_cond p s t hp, h]

theorem sigma_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem inclR_injective (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] :
    Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)

theorem smul_ratTup {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (γ : HA R σ J) (g : GL (Fin M) E)
    (hg : Formalism.UG.bc (inclR (F := F) R) g = (γ : HR R σ J).1) (x : Fin n → Fin M → E) :
    γ • ratTup (F := F) R x = ratTup (F := F) R (fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ x a) := by
  funext a i
  show (((γ : HR R σ J).1 : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ (ratTup (F := F) R x a)) i = _
  rw [← hg]
  exact (RingHom.map_mulVec (inclR (F := F) R) _ _ i).symm

theorem rational_sphere_orbit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ x : Fin 1 → Fin M → E, hE σ J (x 0) (x 0) ≠ 0 → Function.Injective (ratTup (F := F) (AF F) : (Fin 1 → Fin M → E) → _) ∧ ∀ y : Fin 1 → Fin M → AF F ⊗[F] E, (∃ x' : Fin 1 → Fin M → E, hE σ J (x' 0) (x' 0) = hE σ J (x 0) (x 0) ∧ ratTup (F := F) (AF F) x' = y) ↔ ∃ γ ∈ ratPts (AF F) σ J, γ • ratTup (F := F) (AF F) x = y := by
  intro F E _ _ _ _ _ σ hCM M J hJ x hx
  refine ⟨?_, fun y => ⟨?_, ?_⟩⟩
  · intro a b hab
    funext k i
    exact inclR_injective F E (congrFun (congrFun hab k) i)
  · rintro ⟨x', hx', rfl⟩
    simp only [hE, hform_eq] at hx hx'
    obtain ⟨g, hg, hgx, -⟩ := GlobalTheory.HermWitt.exists_gl_isometry_mulVec_eq (c := (σ : E →+* E))
      (G := Jᵀ) two_ne_zero (sigma_sigma σ hCM) (fun a b => hJ.1 a b) hx'.symm hx
    have hU : g ∈ Formalism.UG.UJ (σ : E →+* E) J :=
      GlobalTheory.UnitarySplit.mem_of_form _ _ _ fun z w => by rw [hform_eq, hform_eq, hg]
    have hH : Formalism.UG.bc (inclR (F := F) (AF F)) g ∈ HR (AF F) σ J :=
      bc_mem (inclR (F := F) (AF F)) (σ : E →+* E) (sigR (AF F) σ) (fun t => by
        simp [inclR, sigR]) J g hU
    refine ⟨(⟨_, hH⟩ : HR (AF F) σ J), ⟨g, hU, rfl⟩, ?_⟩
    refine (smul_ratTup (AF F) σ J (⟨_, hH⟩ : HR (AF F) σ J) g rfl x).trans ?_
    congr 1
    funext a
    obtain rfl : a = 0 := Subsingleton.elim _ _
    exact hgx
  · rintro ⟨γ, ⟨g, hU, hg⟩, rfl⟩
    exact ⟨fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ x a, hform_mem _ J g hU _ _,
      (smul_ratTup (AF F) σ J γ g hg x).symm⟩

end GlobalTheory.RatOrbit
end

section

open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

noncomputable section

namespace GlobalTheory.StabiliserOfVector

open Formalism.UG (cT UJ)
open GlobalTheory.FrameStep

theorem exists_of_conj_fixed {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {y : E} (hy : σ y = y) :
    ∃ a : F, algebraMap F E a = y := by
  obtain ⟨-, hE, h2, hτ⟩ := hCM
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let K : Submodule F E := LinearMap.ker (σ.toLinearMap - LinearMap.id)
  have hK : ∀ z, z ∈ K ↔ σ z = z := fun z => by simp [K, sub_eq_zero]
  have hne : K ≠ ⊤ := by
    intro h
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
    rw [ComplexEmbedding.isReal_iff]
    ext z
    have hz : σ z = z := (hK z).1 (h ▸ Submodule.mem_top)
    have := hτ τ z
    rw [hz] at this
    exact this.symm
  have hlt := Submodule.finrank_lt hne
  have hle : Submodule.span F {(1 : E)} ≤ K := by
    rw [Submodule.span_singleton_le_iff_mem, hK, map_one]
  have heq : Submodule.span F {(1 : E)} = K := by
    refine Submodule.eq_of_le_of_finrank_le hle ?_
    rw [finrank_span_singleton one_ne_zero]
    omega
  have hmem : y ∈ Submodule.span F {(1 : E)} := heq ▸ (hK y).2 hy
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
  exact ⟨a, by rw [← ha, Algebra.algebraMap_eq_smul_one]⟩

theorem mem_ratPts_iff {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] [Nontrivial R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (g : HA R σ J) :
    g ∈ ratPts R σ J ↔ ∃ k : Matrix (Fin M) (Fin M) E, k.map (inclR (F := F) R) =
      ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) := by
  constructor
  · rintro ⟨k, -, hk⟩
    exact ⟨k, congrArg (fun u : GL (Fin M) (R ⊗[F] E) => (u : Matrix (Fin M) (Fin M) (R ⊗[F] E))) hk⟩
  · rintro ⟨k, hk⟩
    have hinj : Function.Injective (inclR (F := F) (E := E) R) := (inclR (F := F) (E := E) R).injective
    have hdet : k.det ≠ 0 := by
      intro h0
      have hu : IsUnit (k.map (inclR (F := F) R)).det := by
        rw [hk]; exact (Matrix.isUnits_det_units _)
      have h1 := (inclR (F := F) (E := E) R).map_det k
      rw [h0, map_zero] at h1
      rw [RingHom.mapMatrix_apply] at h1
      rw [← h1] at hu
      exact not_isUnit_zero hu
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero k hdet, ?_, Units.ext hk⟩
    show cT (σ : E →+* E) k * J * k = J
    apply Matrix.map_injective hinj
    have hg : cT (sigR R σ) (HA.mat R σ J g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J *
      (HA.mat R σ J g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR R J := g.2
    rw [← hk, cT_map, JR, ← Matrix.map_mul, ← Matrix.map_mul] at hg
    exact hg

theorem exists_hom_range_stabiliser : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M M' : ℕ) (J : Matrix (Fin M) (Fin M) E) (J' : Matrix (Fin M') (Fin M') E) (B : Matrix (Fin M) (Fin M') E) (x : Fin 1 → Fin M → E), M' + 1 = M → IsHermND σ J → IsHermND σ J' → Formalism.UG.cT (σ : E →+* E) B * J * B = J' → (∀ j, hE σ J (x 0) (fun i => B i j) = 0) → hE σ J (x 0) (x 0) ≠ 0 → ∃ φ : HA (AF F) σ J' →* HA (AF F) σ J, Continuous φ ∧ Function.Injective φ ∧ φ.range = Hstab (AF F) σ J x ∧ (∀ g, FrameRel J J' B (φ g) g) ∧ ∀ g, φ g ∈ ratPts (AF F) σ J ↔ g ∈ ratPts (AF F) σ J' := by
  intro F E _ _ _ _ _ σ hCM M M' J J' B x hM hJ hJ' hBB hxB hxx
  subst hM
  have hσ : ∀ y, σ (σ y) = y := by
    intro y
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hCM.2.2.2, hCM.2.2.2, star_star]
  have hfix : σ (hE σ J (x 0) (x 0)) = hE σ J (x 0) (x 0) := by

    simp only [hE, Formalism.UG.hform, map_sum, map_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hJ.1 i j]
    show σ (σ (x 0 j)) * J i j * σ (x 0 i) = σ (x 0 i) * J i j * x 0 j
    rw [hσ]; ring
  obtain ⟨a, ha⟩ := exists_of_conj_fixed σ hCM hfix
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hxx (by rw [← ha, map_zero])
  have h : GlobalTheory.GaugeEx.StepData σ J x a B J' := ⟨hJ, ha0, ha.symm, hxB, hBB.symm, hJ'⟩
  obtain ⟨-, L₁, L, c, hL, h11, h21, h22, hsum, hXB, hBX⟩ := exists_dual σ hσ h
  have : Nontrivial (AF F) := inferInstanceAs (Nontrivial (InfiniteAdeleRing F × _))
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := F) (E := E)
  set X : Matrix (Fin (M' + 1)) (Fin 1) E := (Matrix.of x).transpose with hXdef
  set ι : E →+* AF F ⊗[F] E := inclR (AF F) with hι
  have hone : ∀ k : ℕ, (1 : Matrix (Fin k) (Fin k) E).map ι = 1 := fun k =>
    Matrix.map_one _ (map_zero ι) (map_one ι)
  have hzero : ∀ k l : ℕ, (0 : Matrix (Fin k) (Fin l) E).map ι = 0 := fun k l =>
    Matrix.map_zero _ (map_zero ι)
  have h22' : L.map ι * B.map ι = 1 := by rw [← Matrix.map_mul, h22, hone]
  have hsum' : X.map ι * L₁.map ι + B.map ι * L.map ι = 1 := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add ι), hsum, hone]
  have hS : ∀ g : HA (AF F) σ J, g ∈ Hstab (AF F) σ J x ↔
      ((HA.mat (AF F) σ J g : GL (Fin (M' + 1)) (AF F ⊗[F] E)) :
        Matrix (Fin (M' + 1)) (Fin (M' + 1)) (AF F ⊗[F] E)) * X.map ι = X.map ι := by
    intro g
    refine MulAction.mem_stabilizer_iff.trans ⟨fun hg => ?_, fun hg => ?_⟩
    · ext i j
      exact congrFun (congrFun hg j) i
    · funext j i
      exact congrFun (congrFun hg i) j
  obtain ⟨e, he⟩ : ∃ e : Hstab (AF F) σ J x ≃* HA (AF F) σ J',
      ∀ g : Hstab (AF F) σ J x, FrameRel J J' B (g : HA (AF F) σ J) (e g) :=
    exists_equiv (sigR (AF F) σ) (JR (AF F) J) (JR (AF F) J') (X.map ι) (B.map ι) (L₁.map ι)
      (L.map ι) (c.map ι)
      (by rw [hL, Matrix.map_mul, Matrix.map_mul, cT_map]; rfl)
      (by rw [← Matrix.map_mul, h11, hone]) (by rw [← Matrix.map_mul, h21, hzero]) h22' hsum'
      (by rw [cT_map, JR, ← Matrix.map_mul, ← Matrix.map_mul, hXB, hzero])
      (by rw [cT_map, JR, ← Matrix.map_mul, ← Matrix.map_mul, hBX, hzero])
      (by rw [cT_map, JR, ← Matrix.map_mul, ← Matrix.map_mul, hBB]; rfl)
      (Hstab (AF F) σ J x) hS
  let φ : HA (AF F) σ J' →* HA (AF F) σ J :=
    (Hstab (AF F) σ J x).subtype.comp e.symm.toMonoidHom
  have hφ : ∀ g, φ g = (e.symm g : HA (AF F) σ J) := fun g => rfl
  have hrel : ∀ g, FrameRel J J' B (φ g) g := by
    intro g
    have := he (e.symm g)
    rwa [MulEquiv.apply_symm_apply] at this
  have hfor : ∀ g, ((HA.mat (AF F) σ J' g : GL (Fin M') (AF F ⊗[F] E)) :
      Matrix (Fin M') (Fin M') (AF F ⊗[F] E)) =
        L.map ι * ((HA.mat (AF F) σ J (φ g) : GL (Fin (M' + 1)) (AF F ⊗[F] E)) :
        Matrix (Fin (M' + 1)) (Fin (M' + 1)) (AF F ⊗[F] E)) * B.map ι := by
    intro g
    have hr := hrel g
    rw [FrameRel, ← hι] at hr
    rw [Matrix.mul_assoc]
    erw [hr, ← Matrix.mul_assoc, h22', Matrix.one_mul]
  have hback : ∀ g, ((HA.mat (AF F) σ J (φ g) : GL (Fin (M' + 1)) (AF F ⊗[F] E)) :
        Matrix (Fin (M' + 1)) (Fin (M' + 1)) (AF F ⊗[F] E)) =
        X.map ι * L₁.map ι +
          B.map ι * ((HA.mat (AF F) σ J' g : GL (Fin M') (AF F ⊗[F] E)) :
            Matrix (Fin M') (Fin M') (AF F ⊗[F] E)) * L.map ι := by
    intro g
    have hr := hrel g
    rw [FrameRel, ← hι] at hr
    have h3 := congrArg (((HA.mat (AF F) σ J (φ g) : GL (Fin (M' + 1)) (AF F ⊗[F] E)) :
      Matrix (Fin (M' + 1)) (Fin (M' + 1)) (AF F ⊗[F] E)) * ·) hsum'
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.mul_one] at h3
    rw [(hS (φ g)).1 (e.symm g).2] at h3
    erw [hr] at h3
    exact h3.symm
  have cm : Continuous fun g : HA (AF F) σ J' => HA.mat (AF F) σ J' g := continuous_subtype_val
  have cφ : ∀ f : HA (AF F) σ J' → HA (AF F) σ J',
      (Continuous fun g => ((HA.mat (AF F) σ J' (f g) : GL (Fin M') (AF F ⊗[F] E)) :
            Matrix (Fin M') (Fin M') (AF F ⊗[F] E))) →
      Continuous fun g => ((HA.mat (AF F) σ J (φ (f g)) : GL (Fin (M' + 1)) (AF F ⊗[F] E)) :
        Matrix (Fin (M' + 1)) (Fin (M' + 1)) (AF F ⊗[F] E)) := by
    intro f hf
    simp only [hback]
    exact continuous_const.add ((continuous_const.matrix_mul hf).matrix_mul continuous_const)
  refine ⟨φ, ?_, Subtype.val_injective.comp e.symm.injective, ?_, hrel, fun g => ?_⟩
  · refine continuous_into (AF F) σ J _ (cφ id (Units.continuous_val.comp cm)) ?_
    simp only [← map_inv]
    exact cφ (fun g => g⁻¹) (Units.continuous_coe_inv.comp cm)
  · ext h
    constructor
    · rintro ⟨g, rfl⟩
      exact (e.symm g).2
    · intro hh
      exact ⟨e ⟨h, hh⟩, by rw [hφ, MulEquiv.symm_apply_apply]⟩
  · rw [mem_ratPts_iff, mem_ratPts_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨L * k * B, by rw [hfor, ← hk, Matrix.map_mul, Matrix.map_mul]⟩
    · rintro ⟨k, hk⟩
      exact ⟨X * L₁ + B * k * L, by
        rw [hback, ← hk, Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul,
          Matrix.map_mul]⟩

end GlobalTheory.StabiliserOfVector
end
end

section

namespace GlobalTheory.VolIndepClosed

theorem volIndep (D : Formalism.BasicNotions.D7) : GlobalTheory.IndefiniteRowSideFullHecke.IsometryTransportFrames.VolIndep D :=
  (GlobalTheory.VolIndepCompare.volumeIndependence_iff D).1 (GlobalTheory.VolumeIndep.volumeIndependence D)

end GlobalTheory.VolIndepClosed
end

section

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

theorem _root_.GlobalTheory.T.exists_lFam_normOne_of_mod_four_eq_three : ∀ d M : ℕ, d.Prime → d % 4 = 3 → 100 ≤ d → 3 ≤ M → ∃ 𝓕 : LFam, 𝓕.B = (4 * (d : ℝ) * (M : ℝ) ^ 2) ∧ ∀ p : ℕ, p.Prime → 𝓕.lam 0 p ≠ 0 → GlobalTheory.Mem.An.NormOne d M p := by
  first | exact @GlobalTheory.Hk.exists_lFam_ray | exact GlobalTheory.Hk.exists_lFam_ray | (intros; apply GlobalTheory.Hk.exists_lFam_ray <;> assumption)
end

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

theorem _root_.GlobalTheory.T.norm_kappa_sq_mul_det_splitPrime : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]), ∀ u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ), Formalism.L2.Th1.H.IsIsom (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ¬ q ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) ≠ 0 → ‖ι B.kappa‖ ^ 2 * ‖ι (LinearMap.det (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)))‖ = 1 := by
  first | exact @GlobalTheory.MomN.norm_kappa_sq_mul_norm_det | exact GlobalTheory.MomN.norm_kappa_sq_mul_norm_det | (intros; apply GlobalTheory.MomN.norm_kappa_sq_mul_norm_det <;> assumption)
end

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.AlgJetsRat

variable {D : D7} {N N' : ℕ}

theorem jet_embV_mem (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (F : VC D N N' → ℂ) (hF : ContDiff ℂ ⊤ F)
    (hT : ∀ α, _root_.Formalism.MainNotions.TaylorLogMetric.taylor D F α ∈ Qbar) {m : ℕ} (A : Fin m → Matrix (Fin N') (Fin N) D.host.E) :
    iteratedFDeriv ℂ m F 0 (fun j => embV D (tor0 D cc δ) (A j)) ∈ Qbar := by
  rw [GlobalTheory.JetTransport.mlin_expand]
  refine IntermediateField.sum_mem _ fun f _ => IntermediateField.mul_mem _ ?_ ?_
  · exact IntermediateField.prod_mem _ fun j _ => GlobalTheory.JetTransport.embT_mem _ _
  · rw [GlobalTheory.JetTransport.iFD_coord F hF f]
    refine IntermediateField.mul_mem _ (IntermediateField.prod_mem _ fun i _ => ?_) (hT _)
    exact IntermediateField.natCast_mem _ _

end GlobalTheory.AlgJetsRat

open GlobalTheory.AlgJetsRat in
theorem GlobalTheory.algJets_of_taylor : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ δ₀ : ℂ) (B : Base D cc δ) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (F : VC D N N' → ℂ), δ / δ₀ ∈ Qbar → δ₀ ≠ 0 → ContDiff ℂ ⊤ F → (∀ α, _root_.Formalism.MainNotions.TaylorLogMetric.taylor D F α ∈ Qbar) → ∀ (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)), (∀ x, e x ∈ S.La ↔ x ∈ La D B.tor L L') → (∀ x ∈ La D B.tor L L', ∃ (n : ℕ) (A : Matrix (Fin N') (Fin N) D.host.E), 0 < n ∧ x = δ • embV D B.tor A ∧ (n : D.host.E) • A ∈ YYl D L L') → S.AlgJets δ₀ (fun z => F (e.symm z)) := by
  intro D cc δ δ₀ B N N' L L' F hδ hδ₀ hF hT g S e he hLa k ys hys
  have hc : ∀ j, ∃ (c : ℂ) (A : Matrix (Fin N') (Fin N) D.host.E),
      c ∈ Qbar ∧ e.symm (δ₀⁻¹ • ys j) = c • embV D B.tor A := by
    intro j
    obtain ⟨s, hs, hsy⟩ := hys j
    have hx : e.symm ((s : ℂ) • ys j) ∈ La D B.tor L L' := (he _).1 (by simpa using hsy)
    obtain ⟨n, A, -, hA, -⟩ := hLa _ hx
    have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    refine ⟨δ / δ₀ * (s : ℂ)⁻¹, A, IntermediateField.mul_mem _ hδ
      (IntermediateField.inv_mem _ (IntermediateField.natCast_mem _ s)), ?_⟩
    have h1 : e.symm (ys j) = (s : ℂ)⁻¹ • (δ • embV D B.tor A) := by
      rw [← hA, map_smul, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [map_smul, h1, smul_smul, smul_smul]
    congr 1
    field_simp
  choose c A hcQ hcA using hc
  show iteratedFDeriv ℂ k (F ∘ ((e.symm : (Fin g → ℂ) ≃L[ℂ] VC D N N') : (Fin g → ℂ) →L[ℂ] VC D N N')) 0
    (fun j => δ₀⁻¹ • ys j) ∈ Qbar
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ hF _ le_top,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp only [ContinuousLinearEquiv.coe_coe, map_zero, hcA]
  rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]
  exact IntermediateField.mul_mem _ (IntermediateField.prod_mem _ fun j _ => hcQ j)
    (jet_embV_mem cc δ F hF hT A)
end
end
