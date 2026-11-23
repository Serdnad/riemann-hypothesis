module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1546
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1489
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle429
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle993
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAutomorphicFormIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle520
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1486
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1036
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1490
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1491
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import ReciprocityTheory.SemistableReduction.Bundle002

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory.QSA

theorem nrm_smul_eq_sq_mul {R : Type*} [CommRing R] {a b : R} (t : R) (x : ℍ[R, a, b]) :
    nrm (t • x) = t ^ 2 * nrm x := by
  simp [nrm]; ring

theorem nrm_sum_orthIdem_smul {R : Type*} [CommRing R] {a b : R} {ι : Type} [Fintype ι] (η : ι → R)
    (y : ι → ℍ[R, a, b]) (h1 : ∀ i, η i * η i = η i) (h2 : ∀ i j, i ≠ j → η i * η j = 0)
    (h3 : ∑ i, η i = 1) : nrm (∑ i, η i • y i) = ∑ i, η i * nrm (y i) := by
  classical
  have key : ∀ i, η i * nrm (∑ j, η j • y j) = η i * nrm (y i) := by
    intro i
    have hs : η i • (∑ j, η j • y j) = η i • y i := by
      rw [Finset.smul_sum, Finset.sum_eq_single i]
      · rw [smul_smul, h1]
      · intro j _ hj
        rw [smul_smul, h2 i j (Ne.symm hj), zero_smul]
      · simp
    have := congrArg nrm hs
    rwa [nrm_smul_eq_sq_mul, nrm_smul_eq_sq_mul, sq, h1] at this
  calc nrm (∑ i, η i • y i) = ∑ i, η i * nrm (∑ j, η j • y j) := by
        rw [← Finset.sum_mul, h3, one_mul]
    _ = _ := Finset.sum_congr rfl fun i _ => key i

def quatStdBasis {R : Type*} [CommRing R] (a b : R) : Fin 4 → ℍ[R, a, b] :=
  ![⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩]

theorem nrm_intertwiner_comb {R : Type*} [CommRing R] {a b c : R} (p q : ℍ[R, a, b]) (hp : p.re = 0) (hq : q.re = 0)
    (hpp : p * p = algebraMap R ℍ[R, a, b] c) (hqq : q * q = algebraMap R ℍ[R, a, b] c) :
    ∑ i, (![a * b, -b, -a, 1] : Fin 4 → R) i * nrm (p * quatStdBasis a b i + quatStdBasis a b i * q)
      = -8 * a * b * c := by
  have h1 := congrArg QuaternionAlgebra.re hpp
  have h2 := congrArg QuaternionAlgebra.re hqq
  simp [QuaternionAlgebra.algebraMap_eq, hp, hq] at h1 h2
  simp [Fin.sum_univ_four, quatStdBasis, nrm, hp, hq]
  linear_combination (-4 * a * b) * h1 + (-4 * a * b) * h2

theorem exists_unit_intertwiner : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ c : F, c ≠ 0 → ∀ p q : DA F a b, p.re = 0 → q.re = 0 → p * p = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c) → q * q = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c) → ∃ y : DA F a b, IsUnit (nrm y) ∧ y * q = p * y := by
  intro F _ _ a b ha hb c hc p q hp hq hpp hqq
  have hcomb := nrm_intertwiner_comb p q hp hq hpp hqq
  have hu : IsUnit (-8 * algebraMap F (AF F) a * algebraMap F (AF F) b * algebraMap F (AF F) c) := by
    have h : IsUnit (-8 * a * b * c) := by
      refine Ne.isUnit ?_
      have : (-8 : F) ≠ 0 := by norm_num
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero this ha) hb) hc
    have h' := h.map (algebraMap F (AF F))
    rwa [map_mul, map_mul, map_mul, map_neg, map_ofNat] at h'
  rw [← hcomb] at hu
  obtain ⟨η, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_orthogonal_idempotents_adele_unit_combination F (Fin 4) _ _ hu
  refine ⟨∑ i, η i • (p * quatStdBasis _ _ i + quatStdBasis _ _ i * q), ?_, ?_⟩
  · rw [nrm_sum_orthIdem_smul η _ h1 h2 h3]; exact h4
  · rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, mul_smul_comm]
    congr 1
    rw [add_mul, mul_add, mul_assoc _ q q, hqq, ← mul_assoc p p, hpp, add_comm, mul_assoc,
      Algebra.commutes]

end GlobalTheory.QSA
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

theorem _root_.GlobalTheory.T.hadamard_ineq_complex_combinations_basis : ∀ (F V : Type) [Field F] [AddCommGroup V] [Module F V] (nm : HermFam F V) (d : ℕ) (b : Module.Basis (Fin d) F V) (σ : F →+* ℂ) (P : Matrix (Fin d) (Fin d) ℂ), 0 < (nm.gram σ b).det.re ∧ ‖P.det‖ * Real.sqrt (nm.gram σ b).det.re ≤ ∏ k, cnrm nm σ (fun i => P i k) b := by
  first | exact @GlobalTheory.HSShort.hadamard_basis_comb | exact GlobalTheory.HSShort.hadamard_basis_comb | (intros; apply GlobalTheory.HSShort.hadamard_basis_comb <;> assumption)
end

section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.prismaticDieudonneHodge_of_hodgeTateDatum : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), (∀ G : PDivGroup p O, HasDatum hε G) → GlobalTheory.Published.PrismaticDieudonneHodgeAt ε := by
  first | exact @GlobalTheory.PDivLat.prismaticDieudonneHodgeAt_of_hasDatum | exact GlobalTheory.PDivLat.prismaticDieudonneHodgeAt_of_hasDatum | (intros; apply GlobalTheory.PDivLat.prismaticDieudonneHodgeAt_of_hasDatum <;> assumption)
end

section

open GlobalTheory GlobalTheory.PDivGroup

theorem GlobalTheory.T.dieudonne_hodgeFiltration_perfectField :
    ∀ (p : ℕ) [Fact p.Prime] (T : GlobalTheory.Dieu.Theory p)
      (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k),
      (∀ x : G.RigExt, (∃ m, T.red G (T.V G m) = x) ↔ x ∈ LinearMap.range G.rigOfOmega) ∧
      (∀ m, T.red G (T.V G m) = 0 ↔ ∃ n, m = T.F G n) ∧
      (∀ m, G.rigToLie (GlobalTheory.Dieu.p_eq_zero p k) (T.red G m) = 0 ↔ ∃ n, m = T.V G n) ∧
      Function.Injective G.rigOfOmega :=
  @GlobalTheory.Dieu.Theory.hodge_filtration
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
open scoped ContDiff

theorem _root_.GlobalTheory.T.whittaker_mul_torus_iterated_factorisation : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) → ∀ (π : CuspSub E a) (α : HeightOneSpectrum (𝓞 E) → Fin a → ℂˣ), (∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) → ∀ φ ∈ π.V, (∀ w ∉ S, ∀ k ∈ KGL w (n := a), act (.fin (locGL E a w k)) φ = φ) → ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) → ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin a → ℕ), (∀ w ∈ l.support, w ∉ S) → ∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := a) S, GlobalTheory.JSW.whit φ.1 (x * GlobalTheory.JSW.tl ϖ l) = (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (l w)) * GlobalTheory.JSW.whit φ.1 x := by
  first | exact @GlobalTheory.JSW.whit_mul_tl | exact GlobalTheory.JSW.whit_mul_tl | (intros; apply GlobalTheory.JSW.whit_mul_tl <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory
open scoped ContDiff

namespace GlobalTheory.WhitBump

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem shear (u : GL (Fin n) (Cinf E)) (hu : u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n)) :
    ∃ τ : Vp E n ≃ᵐ Vp E n, MeasurePreserving τ volume volume ∧
      ∀ t, nu (τ t) = nu t * (u : Matrix (Fin n) (Fin n) (Cinf E)) := GlobalTheory.T.unipotent_translation_measure_preserving E n u hu

theorem isCompact_setOf_toL (T : Set (Lie E n)) (hT : IsCompact T) (hs : T ⊆ invSet E n) :
    IsCompact {y : GL (Fin n) (Cinf E) | toL (y : Matrix (Fin n) (Fin n) (Cinf E)) ∈ T} := GlobalTheory.T.isCompact_GL_of_compact_invertibleMatrices E n T hT hs

variable [_root_.NumberField.IsTotallyComplex E]

theorem contDiffOn_bumpInf (f : Lie E n → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ invSet E n) : ContDiffOn ℝ ∞ (bumpInf f) (invSet E n) := GlobalTheory.T.whittakerBumpArchimedeanFactor_contDiffOn_invertible E n f hf hc hs

theorem exists_bumpInf_ne : ∃ f : Lie E n → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ invSet E n ∧
    bumpInf f (oneL E n) ≠ 0 := GlobalTheory.T.exists_whittakerBumpArchimedeanFactor_one_ne_zero E n

theorem psiFin_integral (u : GL (Fin n) (Af E)) (hu : u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n))
    (hk : u ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n) : psiFin (GlobalTheory.Whittaker.superDiag u) = 1 :=
  GlobalTheory.T.standardAdelicCharFinite_superDiagonalSum_integral_eq_one E n u hu hk

theorem bumpFin_spec
    (htriv : ∀ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), u ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n →
      psiFin (GlobalTheory.Whittaker.superDiag u) = 1) :
    bumpFin (E := E) (n := n) 1 = 1 ∧
    (∀ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), ∀ g, bumpFin (u * g) = psiFin (GlobalTheory.Whittaker.superDiag u) * bumpFin g) ∧
    (∀ k ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n, ∀ g, bumpFin (g * k) = bumpFin g) ∧
    ∀ g, bumpFin g ≠ 0 → ∃ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n),
      u⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n := GlobalTheory.T.whittakerBumpFiniteFactor_properties E n htriv

theorem psiN_eq (u : GA E n) :
    GlobalTheory.JSW.psiN u = psiInf (sdM ((GeneralLinearGroup.map (pInf E) u : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E))) *
      psiFin (GlobalTheory.Whittaker.superDiag (GeneralLinearGroup.map (pFin E) u)) := GlobalTheory.T.adelicGenericUnipotentCharacter_eq_arch_mul_finite E n u

end GlobalTheory.WhitBump

namespace GlobalTheory.WhitBump

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem continuous_finGL_bump : Continuous (finGL E n) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sFin E : Af E → Ad E) :=
    (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))
  exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)

variable [_root_.NumberField.IsTotallyComplex E]

theorem psiInf_add (a b : Cinf E) : psiInf (a + b) = psiInf a * psiInf b := by
  simp [psiInf, map_add (f := _), AddChar.map_add_eq_mul]

theorem bumpInf_mul (f : Lie E n → ℝ) (u : GL (Fin n) (Cinf E)) (hu : u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n))
    (x : Lie E n) :
    bumpInf f (toL ((u : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of x)) =
      psiInf (sdM (u : Matrix (Fin n) (Fin n) (Cinf E))) * bumpInf f x := by
  obtain ⟨τ, hτ, hτu⟩ := shear u hu
  have hsd : ∀ t, sdM (nu (τ t)) = sdM (nu t) + sdM (u : Matrix (Fin n) (Fin n) (Cinf E)) := fun t => by
    rw [hτu, ← nuGL_val, ← superDiag_eq_sdM, ← superDiag_eq_sdM, ← Units.val_mul, ← superDiag_eq_sdM]
    exact GlobalTheory.GamMul.UnipPlaced.superDiag_mul_unip (nuGL_mem t) hu
  have key : ∀ t, (f (toL (nu t * Matrix.of (toL ((u : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of x)))) : ℂ) *
      psiInf (-sdM (nu t)) = psiInf (sdM (u : Matrix (Fin n) (Fin n) (Cinf E))) *
        ((f (toL (nu (τ t) * Matrix.of x)) : ℂ) * psiInf (-sdM (nu (τ t)))) := fun t => by
    have e1 : Matrix.of (toL ((u : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of x)) =
        (u : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of x := rfl
    have e2 : -sdM (nu t) = sdM (u : Matrix (Fin n) (Fin n) (Cinf E)) + -sdM (nu (τ t)) := by
      rw [hsd]; abel
    rw [e1, ← Matrix.mul_assoc, ← hτu, e2, psiInf_add]
    ring
  unfold bumpInf
  simp_rw [key]
  rw [integral_const_mul]
  congr 1
  exact hτ.integral_comp' (g := fun s => (f (toL (nu s * Matrix.of x)) : ℂ) * psiInf (-sdM (nu s)))

end GlobalTheory.WhitBump

namespace GlobalTheory.WhitBump

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

theorem map_apply_bump {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (g : GL (Fin n) R) (i j : Fin n) :
    (GeneralLinearGroup.map p g : Matrix (Fin n) (Fin n) S) i j = p ((g : Matrix (Fin n) (Fin n) R) i j) := rfl

theorem pInf_mem_unipB {u : GA E n} (hu : u ∈ GlobalTheory.JSW.NA (E := E) (a := n)) :
    GeneralLinearGroup.map (pInf E) u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n) :=
  (GlobalTheory.SmGL.mem_unipB (Cinf E)).2 ⟨fun i j h => by rw [map_apply_bump, hu.1 i j h, map_zero],
    fun i => by rw [map_apply_bump, hu.2 i, map_one]⟩

omit [_root_.NumberField.IsTotallyComplex E] in
theorem pFin_mem_unipB {u : GA E n} (hu : u ∈ GlobalTheory.JSW.NA (E := E) (a := n)) :
    GeneralLinearGroup.map (pFin E) u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n) :=
  (GlobalTheory.SmGL.mem_unipB (Af E)).2 ⟨fun i j h => by rw [map_apply_bump, hu.1 i j h, map_zero],
    fun i => by rw [map_apply_bump, hu.2 i, map_one]⟩

theorem mem_NA_of {y : GL (Fin n) (Cinf E)} {k : GL (Fin n) (Af E)} (hy : y ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n))
    (hk : k ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n)) : infGL E n y * finGL E n k ∈ GlobalTheory.JSW.NA (E := E) (a := n) := by
  have hI : GeneralLinearGroup.map (pInf E) (infGL E n y * finGL E n k) = y := by simp
  have hF : GeneralLinearGroup.map (pFin E) (infGL E n y * finGL E n k) = k := by simp
  obtain ⟨hy1, hy2⟩ := (GlobalTheory.SmGL.mem_unipB (Cinf E)).1 hy
  obtain ⟨hk1, hk2⟩ := (GlobalTheory.SmGL.mem_unipB (Af E)).1 hk
  refine ⟨fun i j h => ad_ext ?_ ?_, fun i => ad_ext ?_ ?_⟩
  · rw [← map_apply_bump, hI, hy1 i j h, map_zero]
  · rw [← map_apply_bump, hF, hk1 i j h, map_zero]
  · rw [← map_apply_bump, hI, hy2 i, map_one]
  · rw [← map_apply_bump, hF, hk2 i, map_one]

end GlobalTheory.WhitBump


open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump in
theorem GlobalTheory.WhitBump.exists_bump : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), ∃ b : GA E (m + 1) → ℂ, b 1 = 1 ∧ (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) ∧ (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) ∧ (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (m + 1) u) = b g) ∧ ∀ g, ContDiffOn ℝ ∞ (chart b g) (invSet E (m + 1)) := by
  intro E _ _ _ m S
  obtain ⟨f, hf, hfc, hfs, hf1⟩ := exists_bumpInf_ne (E := E) (n := m + 1)
  obtain ⟨h1, hN, hK, hsupp⟩ := bumpFin_spec (E := E) (n := m + 1) fun u hu hk => psiFin_integral u hu hk
  set c := bumpInf f (oneL E (m + 1)) with hc
  let pI : GA E (m + 1) → GL (Fin (m + 1)) (Cinf E) := fun g => GeneralLinearGroup.map (pInf E) g
  let pF : GA E (m + 1) → GL (Fin (m + 1)) (Af E) := fun g => GeneralLinearGroup.map (pFin E) g
  refine ⟨fun g => bumpInf f (toL (pI g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E))) / c * bumpFin (pF g),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp only [pI, pF, map_one, Units.val_one, h1, mul_one]
    exact div_self hf1
  · intro u hu g
    simp only [pI, pF, map_mul, Units.val_mul]
    have e := bumpInf_mul f _ (pInf_mem_unipB hu) (toL ((GeneralLinearGroup.map (pInf E) g : GL (Fin (m + 1)) (Cinf E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)))
    erw [e]
    rw [hN _ (pFin_mem_unipB hu), psiN_eq]
    ring
  · let T := tsupport f
    let C : Set (GA E (m + 1)) := (fun q : GL (Fin (m + 1)) (Cinf E) × GL (Fin (m + 1)) (Af E) =>
      infGL E (m + 1) q.1 * finGL E (m + 1) q.2) ''
        ({y : GL (Fin (m + 1)) (Cinf E) | toL (y : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) ∈ T} ×ˢ
          (GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E (m + 1) : Set (GL (Fin (m + 1)) (Af E))))
    refine ⟨C, ?_, ?_⟩
    · refine ((isCompact_setOf_toL T hfc hfs).prod
        (GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL E (m + 1))).image ?_
      exact ((GlobalTheory.ConstTermSmooth.continuous_infGL).comp continuous_fst).mul
        (continuous_finGL_bump.comp continuous_snd)
    · intro p _ hp
      have hI : bumpInf f (toL (pI p : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E))) ≠ 0 := by
        intro h; apply hp; simp only [h, zero_div, zero_mul]
      have hF : bumpFin (pF p) ≠ 0 := by
        intro h; apply hp; simp only [h, mul_zero]
      obtain ⟨t, ht⟩ : ∃ t, f (toL (nu t * Matrix.of (toL (pI p : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E))))) ≠ 0 := by
        by_contra hall
        push_neg at hall
        have hall' : ∀ t, f (toL (nu t * (pI p : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)))) = 0 := hall
        apply hI
        unfold bumpInf
        simp [hall']
      obtain ⟨uf, huf, hk⟩ := hsupp _ hF
      refine ⟨infGL E (m + 1) (nuGL t)⁻¹ * finGL E (m + 1) uf,
        mem_NA_of (inv_mem (nuGL_mem t)) huf, ⟨(nuGL t * pI p, uf⁻¹ * pF p), ⟨?_, hk⟩, ?_⟩⟩
      · exact subset_tsupport f ht
      · refine ga_ext ?_ ?_ <;> simp [pI, pF]
  · refine ⟨GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E (m + 1),
      GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E (m + 1), fun k hk g => ?_⟩
    simp only [pI, pF, map_mul, pInf_finGL, pFin_finGL, mul_one]
    rw [hK k hk]
  · intro g
    have hsm := contDiffOn_bumpInf f hf hfc hfs
    set L := lmul (toL (pI g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E))) with hL
    have hmaps : Set.MapsTo L (invSet E (m + 1)) (invSet E (m + 1)) := fun x hx => by
      have hx' : IsUnit (Matrix.of x) := hx
      change IsUnit ((pI g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) * Matrix.of x)
      exact (pI g).isUnit.mul hx'
    have h2 : ContDiffOn ℝ ∞ (fun x : Lie E (m + 1) => bumpInf f (L x)) (invSet E (m + 1)) :=
      hsm.comp (L.contDiff.contDiffOn) hmaps
    have hl : ContDiffOn ℝ ∞ (fun x : Lie E (m + 1) => bumpInf f (L x) / c * bumpFin (pF g))
        (invSet E (m + 1)) := (h2.div_const c).mul contDiffOn_const
    refine hl.congr fun x hx => ?_
    have hx' : IsUnit (Matrix.of x) := hx
    rw [chart, dite_eq_left hx']
    simp only [pI, pF, map_mul, pInf_infGL, pFin_infGL, mul_one, Units.val_mul, IsUnit.unit_spec]
    rfl
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
open scoped CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.T.exists_pushout_torsor_nTorsion_character :
    ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ),
      (n : R) = 0 → HasRoots (A := A) n → ∀ b : Fn0 A, IsTorsChar n b →
        ∃ (u : Fn1 A) (g : Fn2 A), IsCoc (whole A) u ∧ IsAdd u g ∧
          ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), (x ^ n : Pt A D) = 1 →
            GlobalTheory.PtExt.chi n g D x = b D x :=
  @GlobalTheory.PtExt.exists_pushout_torsor
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.exists_formalSquaringPath_with_tangentVector : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R], ∀ [IsLocalRing R] [Algebra ℚ R], Smooth G.hom → QuasiSeparated G.hom → ∀ (b : Sp R ⟶ S) (n : ℕ) (V : S.Opens) (τ : Fin n → Γ(Lie G, V)) (w : Fin n → R), ⊤ ≤ b ⁻¹ᵁ V → ∃ ξ, IsPath G 2 b ξ ∧ HasTan G b ξ τ w := by
  first | exact @GlobalTheory.Nef.exists_path_tan | exact GlobalTheory.Nef.exists_path_tan | (intros; apply GlobalTheory.Nef.exists_path_tan <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.exists_genericFrame_and_localFrames_allPlaces : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (W : C.Modules) (r : ℕ), IsVB W r → ∃ (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)) (g : Place k K → Matrix (Fin r) (Fin r) K), (V₀ : Set C).Nonempty ∧ IsFrame s ∧ admitted g ∧ ∀ v, LocFrame x s v (g v) := by
  first | exact @GlobalTheory.Nef.exists_frame_locFrames | exact GlobalTheory.Nef.exists_frame_locFrames | (intros; apply GlobalTheory.Nef.exists_frame_locFrames <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.formalSquaringPath_unique_of_agree_low_degrees : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R], ∀ [IsLocalRing R], QuasiSeparated G.hom → ∀ (c : R) (n : ℕ), 0 < n → (∀ j, n ≤ j → IsUnit (c ^ j - 2)) → ∀ (b : Sp R ⟶ S) (ξ ξ' : Sp (PowerSeries R) ⟶ G.left), IsPath G c b ξ → IsPath G c b ξ' → (∀ (U : G.left.Opens) (h : ⊤ ≤ ξ ⁻¹ᵁ U) (h' : ⊤ ≤ ξ' ⁻¹ᵁ U) (f : Γ(G.left, U)) (j : ℕ), 0 < j → j < n → PowerSeries.coeff j (evAt ξ h f) = PowerSeries.coeff j (evAt ξ' h' f)) → ξ = ξ' := by
  first | exact @GlobalTheory.Nef.path_unique | exact GlobalTheory.Nef.path_unique | (intros; apply GlobalTheory.Nef.path_unique <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.isRationalFormalPath_of_integral_allPlaces : ∀ (k K E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] [Field E] [Algebra k E] [Algebra K E] [IsScalarTower k K E] [FiniteDimensional K E] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (G : Over C) [GrpObj G] (ξ : Sp (PowerSeries E) ⟶ G.left) (u : Place k E → E), (∀ p, u p ≠ 0) → {p | ord p (u p) ≠ 0}.Finite → 0 < ∑ᶠ p, ord p (u p) → (∀ p : Place k E, ∃ (b : Sp p.O ⟶ C) (ζ : Sp (PowerSeries p.O) ⟶ G.left), spMap p.O.subtype ≫ b = spMap (algebraMap K E) ≫ x ∧ IsPath G 2 b ζ ∧ ξ = spMap (sc p (u p)) ≫ ζ) → IsRatPath ξ := by
  first | exact @GlobalTheory.Nef.isRatPath_of_integral_at_places | exact GlobalTheory.Nef.isRatPath_of_integral_at_places | (intros; apply GlobalTheory.Nef.isRatPath_of_integral_at_places <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.rationalSquaringPathsRigid_descends_field_map : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], ∀ (F Ω : Type) [Field F] [Field Ω] (φ : F →+* Ω) (b : Sp F ⟶ S), RatRigid G (spMap φ ≫ b) → RatRigid G b := by
  first | exact @GlobalTheory.Nef.ratRigid_of_field_map | exact GlobalTheory.Nef.ratRigid_of_field_map | (intros; apply GlobalTheory.Nef.ratRigid_of_field_map <;> assumption)
end
