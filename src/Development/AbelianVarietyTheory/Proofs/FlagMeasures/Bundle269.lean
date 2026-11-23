module

import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle229
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle237
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle264
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocInOfUniqOfDecLow
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselOpNormPowerIntegralLtTopClosedSubgroupStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle262
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupsClosedUnitaryWCompactStatement
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle257
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle258
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NilradicalCenterIntegralCoveringRadius
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDerivAtConvolutionArchimedeanUnitaryLieAlgebr
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle002
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003
public import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle259
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle260
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

@[expose] public section

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

namespace GlobalTheory.LocOver.TermOver

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

lemma mem_img (g : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) (x : V) :
    x ∈ img g Λ ↔ ∃ y ∈ Λ, g y = x := by
  simp [img, Submodule.mem_map]

lemma img_mul (g k : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) : img (g * k) Λ = img g (img k Λ) := by
  ext x
  simp only [mem_img]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨k y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

lemma img_one (Λ : Submodule M.L.O V) : img (1 : V ≃ₗ[E] V) Λ = Λ := by
  ext x
  simp only [mem_img]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

lemma img_selfDual (H : HermSp M V) {g : V ≃ₗ[E] V} (hg : IsUnitary H g)
    {Λ : Submodule M.L.O V} (hΛ : H.IsSelfDual Λ) : H.IsSelfDual (img g Λ) := by
  apply GlobalTheory.LocOver.MoveTerm.isSelfDual_img <;> assumption

lemma img_frame (H : HermSp M V) {g : V ≃ₗ[E] V} (hg : IsUnitary H g)
    {Λ : Submodule M.L.O V} {r : ℕ} {f : Fin (r + 1) → V} {T : F} (hf : H.IsFrame Λ r f T) :
    H.IsFrame (img g Λ) r (fun b => g (f b)) T := by
  apply GlobalTheory.LocOver.MoveTerm.isFrame_img <;> assumption

lemma side (hM : M.OK) (H : HermSp M V) (r : ℕ) (Fr : FrameD H r) {Λ : Submodule M.L.O V}
    {f : Fin (r + 1) → V} (hΛ : H.IsSelfDual Λ) (hf : H.IsFrame Λ r f Fr.T) (hT : Tri E Fr.f f) :
    ∃ L : Submodule M.L.O (H.Wb Fr.f), Fr.IsInner L ∧
      ∃ n ∈ Fr.N, f = (fun b => n (Fr.f b)) ∧ Λ = img n (Fr.LamStd L) := by
  obtain ⟨h1, -, h3⟩ := GlobalTheory.T.frameDual_unipotentGroup_acts_unitriangular_onto M hM H r Fr hf.2.2.2.2
  obtain ⟨n, hn, hnf⟩ := h3 f hT
  have hu : IsUnitary H n⁻¹ := ((h1 _).1 (Fr.N.inv_mem hn)).1
  have hfr : H.IsFrame (img n⁻¹ Λ) r Fr.f Fr.T := by
    have := img_frame H hu hf
    have he : (fun b => n⁻¹ (f b)) = Fr.f := by
      funext b
      rw [hnf]
      exact n.symm_apply_apply _
    rwa [he] at this
  obtain ⟨L, hL, -, n0, hn0, hfix, hΛ0⟩ :=
    GlobalTheory.T.selfDual_lattice_frame_eq_standard_translate M hM H r Fr (img n⁻¹ Λ) (img_selfDual H hu hΛ) hfr
  refine ⟨L, hL, n * n0, Fr.N.mul_mem hn hn0, ?_, ?_⟩
  · rw [hnf]
    funext b
    change n (Fr.f b) = n (n0 (Fr.f b))
    rw [hfix]
  · rw [img_mul, ← hΛ0, ← img_mul, mul_inv_cancel, img_one]

end

theorem exists_datum : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (P : FPair H r) (t : Term V M r), H.IsTerm t → t.T = P.A.T → t.T' = P.B.T → Tri E P.A.f t.f → Tri E P.B.f t.f' → ∃ d : Datum P, IsTermOver P d t := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r P t ht hT hT' hf hf'
  obtain ⟨hsd, hfr, hfr', -, -, hg⟩ := ht
  rw [hT] at hfr
  rw [hT'] at hfr'
  obtain ⟨L, hL, n, hn, hnf, hnΛ⟩ := side hM H r P.A hsd hfr hf
  obtain ⟨L', hL', n', hn', hnf', hnΛ'⟩ := side hM H r P.B hsd hfr' hf'
  let s : Term V M r := ⟨t.abelian₂, P.A.f, P.B.f, t.T, t.T'⟩
  refine ⟨⟨L, L', hL, hL', {p | ∃ g, M.split = some g ∧ p ∈ H.iotaGraph g s}, ?_⟩, hT, hT',
    ⟨n, hn, hnf, hnΛ⟩, ⟨n', hn', hnf', hnΛ'⟩, ?_⟩
  · intro h
    ext p
    simp [h]
  · intro g hgs
    refine ⟨(hg g hgs).2.2, ?_⟩
    ext p
    constructor
    · intro hp
      exact ⟨g, hgs, hp⟩
    · rintro ⟨g', hg', hp⟩
      obtain rfl : g = g' := Option.some.inj (hgs.symm.trans hg')
      exact hp

end GlobalTheory.LocOver.TermOver
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.OrbNorm

theorem continuous_opn {n : ℕ} : Continuous (opn : Matrix (Fin n) (Fin n) ℂ → ℝ) := by
  unfold opn
  have h : Continuous (fun g : Matrix (Fin n) (Fin n) ℂ => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) g) :=
    LinearMap.continuous_of_finiteDimensional
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearEquiv.toLinearMap)
  exact continuous_norm.comp h

theorem opn_pos {k r : ℕ} {g : Mat k r} (hg : g ∈ GG k r) : 0 < opn g := by
  apply GlobalTheory.Amp.LocalInputs.opn_pos <;> assumption

theorem integrable_of_normInt {k r : ℕ} {μ : Measure (Mt k r)} {A : ℝ} (h : normInt μ A < ⊤) :
    Integrable (fun x : Mt k r => opn (Matrix.of x) ^ (-A)) μ := by
  have hm : Measurable (fun x : Mt k r => opn (Matrix.of x) ^ (-A)) :=
    ((continuous_opn.comp (continuous_id : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)))).measurable).pow_const _
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (opn_nonneg _) _)]
  exact h

theorem rpow_le {a a' x C0 A : ℝ} {M : ℕ} (ha : 0 < a) (ha' : 0 < a') (hx : 0 ≤ x) (hC : 0 < C0)
    (hA : 0 ≤ A) (h : max a a' ≤ C0 * x ^ M) :
    x ^ (-(2 * M * A)) ≤ C0 ^ (2 * A) * (a ^ (-A) * a' ^ (-A)) := by
  have hy : 0 < x ^ M := by
    have h1 : 0 < max a a' := lt_max_of_lt_left ha
    exact pos_of_mul_pos_right (lt_of_lt_of_le h1 h) hC.le
  have hCy : 0 < C0 * x ^ M := mul_pos hC hy
  have hx' : x ^ (-(2 * M * A)) = (x ^ M) ^ (-(2 * A)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    congr 1
    ring
  have h1 : (C0 * x ^ M) ^ (-A) ≤ a ^ (-A) :=
    Real.rpow_le_rpow_of_nonpos ha (le_trans (le_max_left _ _) h) (by linarith)
  have h2 : (C0 * x ^ M) ^ (-A) ≤ a' ^ (-A) :=
    Real.rpow_le_rpow_of_nonpos ha' (le_trans (le_max_right _ _) h) (by linarith)
  have key : C0 ^ (2 * A) * ((C0 * x ^ M) ^ (-A) * (C0 * x ^ M) ^ (-A)) = (x ^ M) ^ (-(2 * A)) := by
    rw [← Real.rpow_add hCy, Real.mul_rpow hC.le hy.le, ← mul_assoc, ← Real.rpow_add hC]
    have e1 : 2 * A + (-A + -A) = 0 := by ring
    have e2 : -A + -A = -(2 * A) := by ring
    rw [e1, e2, Real.rpow_zero, one_mul]
  rw [hx', ← key]
  exact mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (Real.rpow_nonneg hCy.le _) (Real.rpow_nonneg ha.le _))
    (Real.rpow_nonneg hC.le _)

theorem orbNormInt_lt_top : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μS μS' : Measure (Mt k r)) (b : ℝ) (C : Set (Mat k r)), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsHaarOn (Sset k r z) μS → IsHaarOn (Sset k r z') μS' → 2 * ((2 * (r ^ 2 + r + 1) : ℕ) : ℝ) * (2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2) < b → IsCompact C → C ⊆ Greg k r z z' → (∀ γ ∈ C, orbNormInt μS μS' b γ < ⊤) ∧ ∃ F : Mt k r × Mt k r → ℝ, Integrable F (μS.prod μS') ∧ ∀ γ ∈ C, ∀ p : Mt k r × Mt k r, Matrix.of p.1 ∈ Sset k r z → Matrix.of p.2 ∈ Sset k r z' → opn (Matrix.of (act2 γ p)) ^ (-b) ≤ F p := by
  intro k r z z' μS μS' b C hz hz' hT hT' hS hS' hb hC hCr
  obtain ⟨C0, hC0, hbd⟩ := GlobalTheory.T.besselRegularDoubleCoset_polynomial_properness k r z z' C hz hz' hT hT' hC hCr
  obtain ⟨-, -, -, hSS, -⟩ := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hz hT
  obtain ⟨-, -, -, hSS', -⟩ := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z' hz' hT'
  set M : ℕ := 2 * (r ^ 2 + r + 1) with hM
  have hM0 : 0 < M := by rw [hM]; positivity
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM0
  have hMpos : (0 : ℝ) < 2 * (M : ℝ) := by linarith
  set A : ℝ := b / (2 * (M : ℝ)) with hA
  have hA2 : 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < A := by
    rw [hA, lt_div_iff₀ hMpos]
    linarith
  have hA0 : 0 ≤ A := le_of_lt (lt_of_le_of_lt (by positivity) hA2)
  have hbA : b = 2 * (M : ℝ) * A := by
    rw [hA]
    field_simp
  have hi := integrable_of_normInt (GlobalTheory.T.besselOpNormPowerIntegral_lt_top_closedSubgroup k r (Sset k r z) μS A hSS hS hA2)
  have hi' := integrable_of_normInt (GlobalTheory.T.besselOpNormPowerIntegral_lt_top_closedSubgroup k r (Sset k r z') μS' A hSS' hS' hA2)
  have : SigmaFinite μS := hS.1
  have : SigmaFinite μS' := hS'.1
  let F : Mt k r × Mt k r → ℝ := fun p =>
    C0 ^ (2 * A) * (opn (Matrix.of p.1) ^ (-A) * opn (Matrix.of p.2) ^ (-A))
  have hF : Integrable F (μS.prod μS') := (hi.mul_prod hi').const_mul _
  have hbound : ∀ γ ∈ C, ∀ p : Mt k r × Mt k r, Matrix.of p.1 ∈ Sset k r z → Matrix.of p.2 ∈ Sset k r z' →
      opn (Matrix.of (act2 γ p)) ^ (-b) ≤ F p := by
    intro γ hγ p h1 h2
    have hg1 := opn_pos (hSS.1 h1)
    have hg2 := opn_pos (hSS'.1 h2)
    have hmax := hbd γ hγ _ h1 _ h2
    rw [hbA]
    exact rpow_le hg1 hg2 (opn_nonneg _) (by linarith) hA0 hmax
  refine ⟨fun γ hγ => ?_, F, hF, hbound⟩
  have e1 : ∀ᵐ p ∂(μS.prod μS'), Matrix.of p.1 ∈ Sset k r z := by
    rw [ae_iff]
    refine measure_mono_null (t := {x : Mt k r | Matrix.of x ∉ Sset k r z} ×ˢ Set.univ)
      (fun p hp => ⟨hp, trivial⟩) ?_
    rw [Measure.prod_prod, hS.2.2.1, zero_mul]
  have e2 : ∀ᵐ p ∂(μS.prod μS'), Matrix.of p.2 ∈ Sset k r z' := by
    rw [ae_iff]
    refine measure_mono_null (t := Set.univ ×ˢ {x : Mt k r | Matrix.of x ∉ Sset k r z'})
      (fun p hp => ⟨trivial, hp⟩) ?_
    rw [Measure.prod_prod, hS'.2.2.1, mul_zero]
  calc orbNormInt μS μS' b γ ≤ ∫⁻ p, ENNReal.ofReal (F p) ∂(μS.prod μS') := by
        unfold orbNormInt
        apply lintegral_mono_ae
        filter_upwards [e1, e2] with p h1 h2
        exact ENNReal.ofReal_le_ofReal (hbound γ hγ p h1 h2)
    _ < ⊤ := hF.lintegral_lt_top

end GlobalTheory.SgInf.OrbNorm
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.hasDerivAt_completedTensorOrbit_smoothAverage : ∀ (B : RowsAut) (F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ) (E : gInf B) (w : B.Hs), IsURep B.σs → ContDiff ℝ ∞ F → HasCompactSupport F → ∃ F' : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F' ∧ HasCompactSupport F' ∧ HasDerivAt (orbit B E (∫ g, F (fun v i j => uMat (g v) i j) • B.σs g w ∂(muInf B.I))) (∫ g, F' (fun v i j => uMat (g v) i j) • B.σs g w ∂(muInf B.I)) 0 := by
  first | exact @GlobalTheory.AverageDeriv.hasDerivAt_orbit_average | exact GlobalTheory.AverageDeriv.hasDerivAt_orbit_average | (intros; apply GlobalTheory.AverageDeriv.hasDerivAt_orbit_average <;> assumption)
end

section

open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

theorem _root_.GlobalTheory.T.nilradical_first_layer_covering_radius_le : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (lo hi rho : ℝ), IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) R → R ≤ perpIn I x R → 0 < hi → largestSize (bas I) (frm I x) R ≤ hi → (∀ N, R < N → N ≤ lamX I x → lo ≤ sizeQ (bas I) (frm I x) N R) → 0 < lo → hi ≤ rho * lo → ∀ Y ∈ nilReal I R, ∃ Y₀ ∈ nilInt I x R, ∃ Z ∈ cenReal I R, normAt I x (Y - diagEmb I Y₀ - Z) ≤ ((I.n : ℝ) ^ 2 * I.f) / 8 * I.rd * rho / Real.sqrt (2 * I.f) := by
  first | exact @GlobalTheory.Count.FirstLayer.main | exact GlobalTheory.Count.FirstLayer.main | (intros; apply GlobalTheory.Count.FirstLayer.main <;> assumption)
end

section

open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

theorem _root_.GlobalTheory.T.nilradicalCenter_integral_covering_radius : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (hi rho : ℝ), IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) R → R ≤ perpIn I x R → 0 < hi → largestSize (bas I) (frm I x) R ≤ hi → hi ^ 2 ≤ rho / 4 → ∀ Z ∈ cenReal I R, ∃ Z₀ ∈ cenInt I x R, normAt I x (Z - diagEmb I Z₀) ≤ ((I.n : ℝ) ^ 2 * I.f) * I.rd * rho / (16 * Real.sqrt I.f) := by
  first | exact @GlobalTheory.Count.CentralCover.main | exact GlobalTheory.Count.CentralCover.main | (intros; apply GlobalTheory.Count.CentralCover.main <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.hasDerivAt_convolution_archimedeanUnitaryLieAlgebra : ∀ (B : RowsAut) (A : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ) (χ : B.I.Gf → ℂ) (ψ : B.I.GA → ℂ) (E : gInf B), ContDiff ℝ ∞ A → HasCompactSupport A → Continuous χ → HasCompactSupport χ → (∀ y, ψ y = A (fun v i j => uMat (y.1 v) i j) * χ y.2) → Continuous ψ ∧ HasCompactSupport ψ ∧ ∃ ψ' : B.I.GA → ℂ, Continuous ψ' ∧ HasCompactSupport ψ' ∧ ∀ F : B.I.L2 B.μf B.fund, HasDerivAt (fun t : ℝ => B.R ((fun v => expU (t • E v)), 1) (∫ y, ψ y • B.R y F ∂(B.I.muA B.μf))) (∫ y, ψ' y • B.R y F ∂(B.I.muA B.μf)) 0 ∧ ∀ x : B.I.GA, HasDerivAt (fun t : ℝ => ∫ z, ψ ((x * ((fun v => expU (t • E v)), 1))⁻¹ * z) * B.I.ext F z ∂(B.I.muA B.μf)) (∫ z, ψ' (x⁻¹ * z) * B.I.ext F z ∂(B.I.muA B.μf)) 0 := by
  first | exact @GlobalTheory.ConvDeriv.convolution_hasDerivAt | exact GlobalTheory.ConvDeriv.convolution_hasDerivAt | (intros; apply GlobalTheory.ConvDeriv.convolution_hasDerivAt <;> assumption)
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.LatticeIndicator

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem exists_int_generators (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) :
    ∃ (k : ℕ) (x : Fin k → Fin n → E), (∀ j, x j ∈ L) ∧
      ∀ w ∈ L, ∃ m : Fin k → ℤ, w = ∑ j, m j • x j := by
  have : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hL
  have : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := L)
  refine ⟨k, fun j => s j, fun j => (s j).2, fun w hw => ?_⟩
  have : (⟨w, hw⟩ : L) ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨m, hm⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 this
  exact ⟨m, by simpa using (congrArg Subtype.val hm).symm⟩

theorem exists_int_smul_mem (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsFullLattice E L)
    (w : Fin n → E) : ∃ N : ℤ, N ≠ 0 ∧ N • w ∈ L := by
  exact _root_.GlobalTheory.IntSmulIntegerEq.exists_int_smul_mem L hL w

theorem latLoc_compact_open (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsFullLattice E L)
    (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (GlobalTheory.AdelicU.latLoc F L v : Set (Fin n → Fv F v ⊗[F] E)) ∧
      IsOpen (GlobalTheory.AdelicU.latLoc F L v : Set (Fin n → Fv F v ⊗[F] E)) := by
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  haveI : CharZero (Fv F v) := charZero_of_injective_ringHom (algebraMap F (Fv F v)).injective
  obtain ⟨k, x, hxL, hx⟩ := exists_int_generators L hL.fg
  let f : (Fin k → Fv F v) →ₗ[Fv F v] (Fin n → Fv F v ⊗[F] E) :=
    Fintype.linearCombination _ fun j i => (1 : Fv F v) ⊗ₜ[F] x j i
  have hfa : ∀ a i, f a i = ∑ j, a j ⊗ₜ[F] x j i := fun a i => by
    simp [f, Fintype.linearCombination_apply, TensorProduct.smul_tmul']
  have hm : ∀ (a : Fv F v) (m : Fin k → ℤ),
      f (fun j => m j • a) = fun i => a ⊗ₜ[F] (∑ j, m j • x j) i := fun a m => by
    funext i
    rw [hfa]
    simp only [Finset.sum_apply, Pi.smul_apply, TensorProduct.tmul_sum]
    exact Finset.sum_congr rfl fun j _ => TensorProduct.smul_tmul _ _ _
  have hf : Function.Surjective f := by
    have h1 : ∀ (a : Fv F v) (w : Fin n → E), (fun i => a ⊗ₜ[F] w i) ∈ LinearMap.range f := by
      intro a w
      obtain ⟨N, hN, h⟩ := exists_int_smul_mem L hL w
      obtain ⟨m, e⟩ := hx _ h
      refine ⟨fun j => m j • ((N : Fv F v)⁻¹ * a), ?_⟩
      rw [hm, ← e]
      funext i
      rw [Pi.smul_apply, ← TensorProduct.smul_tmul, zsmul_eq_mul, ← mul_assoc,
        mul_inv_cancel₀ (Int.cast_ne_zero.2 hN), one_mul]
    intro y
    rw [← LinearMap.mem_range, ← Finset.univ_sum_single y]
    refine sum_mem fun i _ => ?_
    generalize y i = z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add p q hp hq => rw [Pi.single_add]; exact add_mem hp hq
    | tmul a e =>
      convert h1 a (Pi.single i e) using 1
      funext j
      by_cases h : j = i
      · subst h; simp
      · simp [h]
  have hfo : IsOpenMap f := IsModuleTopology.isOpenMap_of_surjective (φ := f) hf
  have hfc : Continuous f := IsModuleTopology.continuous_of_linearMap f
  have himg : (GlobalTheory.AdelicU.latLoc F L v : Set (Fin n → Fv F v ⊗[F] E)) =
      f '' Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext y
    constructor
    · refine GlobalTheory.AdelicU.latLoc_induction (p := fun y => y ∈ f '' Set.pi Set.univ fun _ =>
        (v.adicCompletionIntegers F : Set (Fv F v))) ?_ ⟨0, fun _ _ => zero_mem _, map_zero _⟩ ?_ ?_
      · intro a ha w hw
        obtain ⟨m, rfl⟩ := hx w hw
        exact ⟨fun j => m j • a, fun j _ => zsmul_mem ha _, hm a m⟩
      · rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a + b, fun j _ => add_mem (s := v.adicCompletionIntegers F) (ha j trivial) (hb j trivial),
          map_add _ _ _⟩
      · rintro _ ⟨a, ha, rfl⟩
        exact ⟨-a, fun j _ => neg_mem (s := v.adicCompletionIntegers F) (ha j trivial), map_neg _ _⟩
    · rintro ⟨a, ha, rfl⟩
      have : f a = ∑ j, fun i => a j ⊗ₜ[F] x j i := funext fun i => by rw [hfa, Finset.sum_apply]
      rw [this]
      exact sum_mem (S := GlobalTheory.AdelicU.latLoc F L v) fun j _ =>
        GlobalTheory.AdelicU.tmul_mem_latLoc (ha j trivial) (hxL j)
  have hc : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) :=
    isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)
  have ho : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  rw [himg]
  exact ⟨(isCompact_univ_pi fun _ => hc).image hfc,
    hfo _ (isOpen_set_pi Set.finite_univ fun _ _ => ho)⟩

theorem isSB_indicator_latLoc : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsFullLattice E L → ∀ v : HeightOneSpectrum (𝓞 F), IsSB ({X : Fin 1 → Fin n → Fv F v ⊗[F] E | X 0 ∈ GlobalTheory.AdelicU.latLoc F L v}.indicator (1 : (Fin 1 → Fin n → Fv F v ⊗[F] E) → ℂ)) := by
  intro F E _ _ _ _ _ n L hL v
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  obtain ⟨hc, ho⟩ := latLoc_compact_open L hL v
  have hcl : IsClosed (GlobalTheory.AdelicU.latLoc F L v : Set (Fin n → Fv F v ⊗[F] E)) :=
    (GlobalTheory.AdelicU.latLoc F L v).toAddSubgroup.isClosed_of_isOpen ho
  have e : {X : Fin 1 → Fin n → Fv F v ⊗[F] E | X 0 ∈ GlobalTheory.AdelicU.latLoc F L v} =
      Set.pi Set.univ fun _ : Fin 1 => (GlobalTheory.AdelicU.latLoc F L v : Set (Fin n → Fv F v ⊗[F] E)) := by
    ext X
    simp [Fin.forall_fin_one]
  rw [e]
  have h1 := isCompact_univ_pi fun _ : Fin 1 => hc
  have h2 := isOpen_set_pi Set.finite_univ fun (_ : Fin 1) _ => ho
  have h3 := isClosed_set_pi (i := Set.univ) fun (_ : Fin 1) _ => hcl
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun X => ?_, ?_⟩
  · by_cases hX : X ∈ Set.pi Set.univ fun _ : Fin 1 =>
        (GlobalTheory.AdelicU.latLoc F L v : Set (Fin n → Fv F v ⊗[F] E))
    · exact ⟨_, h2, hX, fun Y hY => by rw [Set.indicator_of_mem hY, Set.indicator_of_mem hX]; rfl⟩
    · exact ⟨_, h3.isOpen_compl, hX, fun Y hY => by
        rw [Set.indicator_of_notMem hY, Set.indicator_of_notMem hX]⟩
  · exact HasCompactSupport.intro' h1 h3 fun X hX => Set.indicator_of_notMem hX _

end GlobalTheory.LatticeIndicator
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

theorem _root_.GlobalTheory.T.hermitian_frame_witness_integral_change : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (k : ℕ) (P : FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (theta M) → ∀ (d : Datum P) (t : Term V M r), IsTermOver P d t → ∀ (A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (g g' : Fin (r + 1) → V), Uni A → Uni A' → (∀ a b, A a b ∈ M.L.O ∧ A' a b ∈ M.L.O ∧ A a b - A' a b ∈ Submodule.span M.L.O {algebraMap F E (theta M)}) → Chg t.f A g → Chg t.f' A' g' → IsTermOver P d ⟨t.abelian₂, g, g', t.T, t.T'⟩ := by
  first | exact @GlobalTheory.LocOver.WitChange.witness_change | exact GlobalTheory.LocOver.WitChange.witness_change | (intros; apply GlobalTheory.LocOver.WitChange.witness_change <;> assumption)
end

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.stdLat_isOrthoLattice_and_mass_properties : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], IsCMUnram K → ∀ j : ℕ, (Cnt.stdH K j).IsSymm ∧ IsOrthoLattice (Cnt.stdH K j) (Cnt.stdLat K j) j ∧ 0 < Cnt.massU K j ∧ Cnt.massU K 0 = 1 ∧ ∀ (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V), IsOrthoLattice h L j → mass h L = Cnt.massU K j ∧ PD h := by
  first | exact @GlobalTheory.Mass.StdMass.main | exact GlobalTheory.Mass.StdMass.main | (intros; apply GlobalTheory.Mass.StdMass.main <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitianLocalSums_eq_const_mul_coordinateSums : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), ∀ (R : LocNG.Reps P) (d0 : LocNG.Datum P), ∃ κ : ℝ, 0 ≤ κ ∧ LocNG.sumSq R d0 (LocNG.BBne (H := H)) = ENNReal.ofReal κ * S.ampSq (fun d Λ => ¬ S.BBzero d Λ) ∧ LocNG.sumSq R d0 (fun t => ¬ LocNG.BBne (H := H) t) = ENNReal.ofReal κ * S.ampSq S.BBzero ∧ LocNG.sumSq R d0 (fun _ => True) = ENNReal.ofReal κ * S.ampSq (fun _ _ => True) ∧ LocNG.nn R d0 = ENNReal.ofReal κ * S.nn := by
  first | exact @GlobalTheory.HL.CoordSq.sums_eq | exact GlobalTheory.HL.CoordSq.sums_eq | (intros; apply GlobalTheory.HL.CoordSq.sums_eq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.split_place_lattice_components : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → (∀ (L : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E ⊗[F] v.adicCompletion F), y ∈ loc v L ↔ (∃ y₁ ∈ loc v L, ∀ b, (sp (y₁ b)).1 = (sp (y b)).1) ∧ ∃ y₂ ∈ loc v L, ∀ b, (sp (y₂ b)).2 = (sp (y b)).2) ∧ (∀ g : GL (Fin n) (v.adicCompletion F), ∃! h : UPts cm.sig J (v.adicCompletion F), bc ((RingHom.fst _ _).comp sp.toRingHom) h.1 = g) ∧ ∀ x y : Fin n → E ⊗[F] v.adicCompletion F, (sp (hR cm.sig J (v.adicCompletion F) x y)).1 = ∑ i, ∑ j, (sp (x i)).2 * (sp (inclE (F := F) (v.adicCompletion F) (J i j))).1 * (sp (y j)).1 := by
  first | exact @GlobalTheory.St.G.split_components | exact GlobalTheory.St.G.split_components | (intros; apply GlobalTheory.St.G.split_components <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.map_conj_gaugeMeasure_eq_inv_det_smul : ∀ (n : ℕ) (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ) (S : Subgroup (Formalism.REAL.UJ ε)), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) → (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) → (∀ g, g ∈ S ↔ uMat g - 1 ∈ A) → IsClosed (S : Set (Formalism.REAL.UJ ε)) → ∀ μ : Measure (Formalism.REAL.UJ ε), IsGaugeSub (S : Set (Formalism.REAL.UJ ε)) d μ → ∀ (m : Formalism.REAL.UJ ε) (L : Matrix (Fin d) (Fin d) ℝ), (∀ g, g ∈ S ↔ m * g * m⁻¹ ∈ S) → (∀ k, uMat m * E k * uMat m⁻¹ = ∑ i, L i k • E i) → L.det ≠ 0 → μ.map (fun u => m * u * m⁻¹) = ENNReal.ofReal |L.det|⁻¹ • μ := by
  first | exact @GlobalTheory.GaugeConjScale.map_conj_eq_inv_det_smul | exact GlobalTheory.GaugeConjScale.map_conj_eq_inv_det_smul | (intros; apply GlobalTheory.GaugeConjScale.map_conj_eq_inv_det_smul <;> assumption)
end

end

section

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.besselOrbitOpNormIntegral_finite_on_compact_regular : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μS μS' : Measure (Mt k r)) (b : ℝ) (C : Set (Mat k r)), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsHaarOn (Sset k r z) μS → IsHaarOn (Sset k r z') μS' → 2 * ((2 * (r ^ 2 + r + 1) : ℕ) : ℝ) * (2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2) < b → IsCompact C → C ⊆ Greg k r z z' → (∀ γ ∈ C, orbNormInt μS μS' b γ < ⊤) ∧ ∃ F : Mt k r × Mt k r → ℝ, Integrable F (μS.prod μS') ∧ ∀ γ ∈ C, ∀ p : Mt k r × Mt k r, Matrix.of p.1 ∈ Sset k r z → Matrix.of p.2 ∈ Sset k r z' → opn (Matrix.of (act2 γ p)) ^ (-b) ≤ F p := by
  first | exact @GlobalTheory.SgInf.OrbNorm.orbNormInt_lt_top | exact GlobalTheory.SgInf.OrbNorm.orbNormInt_lt_top | (intros; apply GlobalTheory.SgInf.OrbNorm.orbNormInt_lt_top <;> assumption)

end
end
