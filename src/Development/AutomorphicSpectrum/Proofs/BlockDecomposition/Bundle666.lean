module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle658
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle125
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle260
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.MeasProps
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsUnitScalingSelfdualHermMeasures
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.TupOfCv
public import GroundTheory.GlobalFields.Adele.Bundle003
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle038
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle064
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsEqAdelicCharMul
import GroundTheory.HeightsAndTheta.Theta.AdelicFourier
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle655
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle343
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle344
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle363
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHypothesesHold
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle631
import Development.WeilBound.ThetaLifts.Reductions.SiegelHaar
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.RapidDecay

theorem frameIdem_inl_mulVec {E : Type} [Field E] {n r : ℕ} (S : E →+* E)
    (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E) (i : Fin r) (v : Fin n → E) :
    frameIdem S J X Y (some (Sum.inl i)) *ᵥ v = fun a => X a i * ((cT S Y * J) *ᵥ v) i := by
  funext a
  simp only [frameIdem]
  rw [← Matrix.mulVec_mulVec]
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.single_apply, Finset.sum_ite_eq, ite_and]

theorem stabilises_flag_span : ∀ (E : Type) [Field E] (S : E →+* E) (n r : ℕ) (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E), cT S Y * J * X = 1 → ∀ (g : Matrix (Fin n) (Fin n) E) (j : Fin r), (∀ α β : FrameIx r, frameLev j α < 2 → frameLev j β = 2 → frameIdem S J X Y α * g * frameIdem S J X Y β = 0) → ∀ l : Fin r, l ≤ j → ∃ b : Fin r → E, g *ᵥ (fun a => X a l) = X *ᵥ b ∧ ∀ m : Fin r, j < m → b m = 0 := by
  intro E _ S n r J X Y hXY g j hg l hl
  have hcol : (fun a => X a l) = X *ᵥ Pi.single l 1 := by
    funext a; simp
  have hx : frameIdem S J X Y (some (Sum.inl l)) *ᵥ (fun a => X a l) = fun a => X a l := by
    rw [frameIdem_inl_mulVec, hcol, Matrix.mulVec_mulVec, hXY]
    funext a; simp
  have hβ : frameLev j (some (Sum.inl l) : FrameIx r) = 2 := by simp [frameLev, hl]
  set v : Fin n → E := g *ᵥ (fun a => X a l) with hv
  have hz : ∀ α : FrameIx r, frameLev j α < 2 → frameIdem S J X Y α *ᵥ v = 0 := by
    intro α hα
    have := hg α _ hα hβ
    calc frameIdem S J X Y α *ᵥ v
        = frameIdem S J X Y α *ᵥ (g *ᵥ (frameIdem S J X Y (some (Sum.inl l)) *ᵥ (fun a => X a l))) := by
          rw [hx]
      _ = (frameIdem S J X Y α * g * frameIdem S J X Y (some (Sum.inl l))) *ᵥ (fun a => X a l) := by
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = 0 := by rw [this, Matrix.zero_mulVec]
  have hsum : v = ∑ α, frameIdem S J X Y α *ᵥ v := by
    have h1 : (∑ α, frameIdem S J X Y α) *ᵥ v = ∑ α, frameIdem S J X Y α *ᵥ v :=
      map_sum (Matrix.mulVec.addMonoidHomLeft v) (fun α => frameIdem S J X Y α) Finset.univ
    rwa [sum_frameIdem, Matrix.one_mulVec] at h1
  refine ⟨fun m => if m ≤ j then ((cT S Y * J) *ᵥ v) m else 0, ?_, fun m hm => if_neg (not_le.2 hm)⟩
  refine hsum.trans ?_
  rw [Fintype.sum_option, Fintype.sum_sum_type, hz none (by simp [frameLev]), zero_add]
  have hinr : ∑ i, frameIdem S J X Y (some (Sum.inr i)) *ᵥ v = 0 := by
    refine Finset.sum_eq_zero fun i _ => hz _ ?_
    by_cases h : i ≤ j <;> simp [frameLev, h]
  rw [hinr, add_zero]
  funext a
  rw [Finset.sum_apply]
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : i ≤ j
  · have := congrFun (frameIdem_inl_mulVec S J X Y i v) a
    simp only [Matrix.mulVec, dotProduct] at this
    simpa [h] using this
  · have h0 := congrFun (hz (some (Sum.inl i)) (by simp [frameLev, h])) a
    simp only [Matrix.mulVec, dotProduct] at h0
    simpa [h] using h0

end GlobalTheory.CompanionTheory.RapidDecay
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot

theorem exists_eval_points {X : Type*} (W : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ W] :
    ∃ (N : ℕ) (x : Fin N → X) (f : Fin N → X → ℂ), (∀ i, f i ∈ W) ∧
      ∀ w ∈ W, ∀ y, w y = ∑ i, w (x i) * f i y := by
  classical
  let ev : X → Module.Dual ℂ W := fun x => (LinearMap.proj x).comp W.subtype
  have hfg : (Submodule.span ℂ (Set.range ev)).FG := IsNoetherian.noetherian _
  obtain ⟨s, hs, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
  have hch : ∀ φ : s, ∃ x, ev x = φ.1 := fun φ => hs φ.2
  choose pt hpt using hch
  let e := s.equivFin
  let x : Fin s.card → X := fun i => pt (e.symm i)
  let T : W →ₗ[ℂ] (Fin s.card → ℂ) := LinearMap.pi fun i => ev (x i)
  have hT : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    have hle : Submodule.span ℂ (s : Set (Module.Dual ℂ W)) ≤ LinearMap.ker (Module.Dual.eval ℂ W w) := by
      rw [Submodule.span_le]
      intro φ hφ
      have h1 : T w (e ⟨φ, hφ⟩) = 0 := by rw [hw]; rfl
      have h2 : ev (x (e ⟨φ, hφ⟩)) w = 0 := h1
      have h3 : ev (x (e ⟨φ, hφ⟩)) = φ := by
        show ev (pt (e.symm (e ⟨φ, hφ⟩))) = φ
        rw [Equiv.symm_apply_apply, hpt]
      rw [h3] at h2
      exact h2
    refine Subtype.ext (funext fun y => ?_)
    have hy : ev y ∈ Submodule.span ℂ (s : Set (Module.Dual ℂ W)) :=
      hspan ▸ Submodule.subset_span ⟨y, rfl⟩
    exact hle hy
  obtain ⟨L, hL⟩ := T.exists_leftInverse_of_injective hT
  refine ⟨s.card, x, fun i => (L (Pi.single i 1)).1, fun i => (L _).2, ?_⟩
  intro w hw y
  have h1 : L (T ⟨w, hw⟩) = ⟨w, hw⟩ := LinearMap.congr_fun hL _
  have h2 : T ⟨w, hw⟩ = ∑ i, w (x i) • (Pi.single i (1 : ℂ) : Fin s.card → ℂ) := by
    ext j
    simp [T, ev, Finset.sum_apply, Pi.single_apply]

  rw [h2, map_sum] at h1
  have h3 := congrArg (fun v : W => v.1 y) h1
  simp only [map_smul] at h3
  simpa [Submodule.coe_sum, Finset.sum_apply] using h3.symm

theorem rank_one_majorant_of_parts : WeilCont → WeilKFin → OrbitMaj → IwaCpt → FockTranslateSchwartzMajorant := by
  intro hCont hFin hOrb hIwa D n ψ hψ χ hχ hRes θ hθ μ 𝓕 hμ ω hω l hl hl0 Φ hΦ C hC
  have hcart : ∀ τ, IsCartanInv (gramAt D (V1 D) τ)
      ((fun _ => 1 : D.what₂.Tau → Matrix (Fin (V1 D).rank) (Fin (V1 D).rank) ℂ) τ) :=
    fun τ => GlobalTheory.AdForm.VacStd.cartan_of_gram (GlobalTheory.AdForm.VacStd.gram_of_eq _ _ 1 rfl) τ
  obtain ⟨W, hWfd, hWle, hWK⟩ :=
    hFin D n (V1 D) ψ hψ χ hχ hRes θ hθ μ 𝓕 hμ ω hω l hl (fun _ => 1) hcart Φ hΦ
  haveI := hWfd
  obtain ⟨N, x, f, hfW, hrep⟩ := exists_eval_points W
  have hcont := hCont D n (V1 D) ψ hψ χ hχ hRes θ hθ μ 𝓕 hμ ω hω Φ
  have hB : ∀ i, ∃ B : ℝ, 0 ≤ B ∧ ∀ k ∈ K D n, ‖(ω k Φ).1 (x i)‖ ≤ B := by
    intro i
    have hc : Continuous fun k : G D n => (ω k Φ).1 (x i) :=
      hcont.comp (continuous_id.prodMk continuous_const)
    obtain ⟨B, hB⟩ := HeightExists.isCompact_K.exists_bound_of_continuousOn hc.continuousOn
    exact ⟨max B 0, le_max_right _ _, fun k hk => (hB k hk).trans (le_max_left _ _)⟩
  choose B hB0 hB using hB
  obtain ⟨A₁, A₂, R, hA₁, hA₂, hiwa⟩ := hIwa D n C hC
  have hM := fun i => hOrb D n θ hθ l hl0 (f i) (hWle (hfW i)) A₁ A₂ hA₁ hA₂
  choose M hMs hMpos hMle using hM
  have hc0 : 0 ≤ (max R 0) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (le_max_right _ _) _
  refine ⟨(((max R 0) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) • ∑ i, (B i : ℂ) • M i,
    Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hMs i)), ?_⟩
  intro h hh y
  obtain ⟨m, t, k, a, b, hk, rfl, hm, ht, ha1, ha2, hR⟩ := hiwa h hh
  set c : ℝ := (max R 0) ^ ((1 : ℝ) / 2) with hc
  have e1 : ‖(ω (m * t * k) Φ).1 y‖ =
      (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ^ ((1 : ℝ) / 2) * ‖(ω k Φ).1 (HMul.hMul y a.1 : Mx D (V1 D).rank n)‖ := by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hω.levi m a hm, hω.unip t b ht,
      norm_mul, norm_mul, norm_mul, hψ.2.1, norm_npow (hom_pos _ _)]
    have hre : (((V1 D).rank : ℂ) / 2).re = (1 : ℝ) / 2 := by
      show ((((1 : ℕ) : ℂ)) / 2).re = (1 : ℝ) / 2
      norm_num
    rw [hre, Circle.norm_coe, one_mul, one_mul]
  have e2 : ‖(ω k Φ).1 (HMul.hMul y a.1 : Mx D (V1 D).rank n)‖ ≤ ∑ i, B i * ‖M i y‖ := by
    rw [hrep _ (hWK k hk)]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul]
    exact mul_le_mul (hB i k hk) (hMle i a ha1 ha2 y) (norm_nonneg _) (hB0 i)
  have e3 : (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ^ ((1 : ℝ) / 2) ≤ c :=
    Real.rpow_le_rpow (NNReal.coe_nonneg _) (hR.trans (le_max_left _ _)) (by norm_num)
  have e4 : ∀ i, M i y = ((‖M i y‖ : ℝ) : ℂ) := by
    intro i
    have h1 := hMpos i y
    apply Complex.ext
    · simp only [Complex.ofReal_re]
      rw [show M i y = (((M i y).re : ℝ) : ℂ) from Complex.ext (by simp) (by simp [h1.2])]
      simp [abs_of_nonneg h1.1]
    · simp [h1.2]
  have e5 : ‖((((c : ℝ) : ℂ) • ∑ i, (B i : ℂ) • M i) : Mx D (V1 D).rank n → ℂ) y‖ = c * ∑ i, B i * ‖M i y‖ := by
    have h1 : ((((c : ℝ) : ℂ) • ∑ i, (B i : ℂ) • M i) : Mx D (V1 D).rank n → ℂ) y =
        ((c * ∑ i, B i * ‖M i y‖ : ℝ) : ℂ) := by
      simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      push_cast
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [← e4 i]
    rw [h1, Complex.norm_real, Real.norm_of_nonneg]
    exact mul_nonneg hc0 (Finset.sum_nonneg fun i _ => mul_nonneg (hB0 i) (norm_nonneg _))
  rw [e1, e5]
  exact mul_le_mul e3 e2 (norm_nonneg _) hc0

end GlobalTheory.CompanionTheory.ThTot

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU
open GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HermSd
open scoped TensorProduct ENNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.HermCov

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def ratVec {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ) [FiniteDimensional F E]
    (A : Matrix (Fin n) (Fin n) E) : Idx n d → F :=
  Sum.elim (fun a => 1 / 2 * Algebra.trace F E (A a a)) fun q => b.repr (A q.1.1.1 q.1.1.2) q.2

def ofVec (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ) (k : Idx n d → F) :
    Matrix (Fin n) (Fin n) E := fun a c =>
  if h : a < c then ∑ l, k (Sum.inr (⟨(a, c), h⟩, l)) • b l
  else if h' : c < a then σ (∑ l, k (Sum.inr (⟨(c, a), h'⟩, l)) • b l)
  else algebraMap F E (k (Sum.inl a))

theorem ofVec_herm {σ : E →ₐ[F] E} (hinv : ∀ x, σ (σ x) = x) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (n : ℕ) (k : Idx n d → F) (a c : Fin n) : σ (ofVec σ b n k c a) = ofVec σ b n k a c := by
  rcases lt_trichotomy a c with h | h | h
  · simp only [ofVec, dif_pos h, dif_neg (not_lt_of_gt h), hinv]
  · subst h
    simp only [ofVec, lt_irrefl, dite_false, AlgHom.commutes]
  · simp only [ofVec, dif_pos h, dif_neg (not_lt_of_gt h)]

theorem ratVec_ofVec [FiniteDimensional F E] [CharZero F] (h2 : Module.finrank F E = 2)
    (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ) (k : Idx n d → F) :
    ratVec b n (ofVec σ b n k) = k := by
  funext i
  cases i with
  | inl a =>
    simp only [ratVec, Sum.elim_inl, ofVec, lt_irrefl, dite_false, Algebra.trace_algebraMap, h2]
    simp
  | inr q =>
    obtain ⟨p, l⟩ := q
    simp only [ratVec, Sum.elim_inr, ofVec, dif_pos p.2]
    rw [b.repr_sum_self]

variable (R : Type) [CommRing R] [Algebra F R]

theorem repr_inclR {d : ℕ} (b : Module.Basis (Fin d) F E) (x : E) (k : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (inclR R x) k = algebraMap F R (b.repr x k) := by
  change (Algebra.TensorProduct.basis R b).repr ((1 : R) ⊗ₜ[F] x) k = _
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp

variable [TopologicalSpace R]

theorem hermVec_map [FiniteDimensional F E] (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) E) (S : HermR R σ n)
    (hS : (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = A.map (inclR R)) (i : Idx n d) :
    hermVec R σ b n S i = algebraMap F R (ratVec b n A i) := by
  cases i with
  | inl a =>
    simp only [hermVec, toVec, HaarCoord.hermCoord, Sum.elim_inl, ratVec, hS, Matrix.map_apply]
    change _ * Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] A a a) = _
    rw [trace_tmul, one_mul, map_mul]
  | inr q =>
    simp only [hermVec, toVec, HaarCoord.hermCoord, Sum.elim_inr, ratVec, hS, Matrix.map_apply]
    exact repr_inclR R b _ _

end Alg

section Main

open GroundTheory.Global GroundTheory.Automorphic.GJMatrix GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Fth PositivityTheory.SiegelWeilFormula.KWhit.MeasP
attribute [local instance 100000] GroundTheory.Global.measurableSpace_adeleRing

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_ratHerm_iff {σ : E →ₐ[F] E} (hinv : ∀ x, σ (σ x) = x) (h2 : Module.finrank F E = 2)
    [FiniteDimensional F E] {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ)
    (hinj : Function.Injective (hermVec (AF F) σ b n)) (S : HermR (AF F) σ n) :
    S ∈ ratHerm F E σ n ↔ ∃ k : Idx n d → F, ∀ i, hermVec (AF F) σ b n S i = algebraMap F (AF F) (k i) := by
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨ratVec b n A, hermVec_map (AF F) σ b n A S hA.symm⟩
  · rintro ⟨k, hk⟩
    have hmem : (ofVec σ b n k).map (inclR (AF F)) ∈ HermR (AF F) σ n := by
      intro a c
      simp only [Matrix.map_apply]
      rw [← ofVec_herm hinv b n k a c]
      change sigR (AF F) σ ((1 : AF F) ⊗ₜ[F] _) = (1 : AF F) ⊗ₜ[F] _
      rw [HaarCoord.sigR_tmul]
    have hT : (⟨_, hmem⟩ : HermR (AF F) σ n) = S := by
      apply hinj
      funext i
      rw [hermVec_map (AF F) σ b n (ofVec σ b n k) _ rfl i, ratVec_ofVec h2, hk]
    refine ⟨ofVec σ b n k, ?_⟩
    rw [← hT]
    rfl

theorem existsUnique_sub_mem_pi {ι : Type} (x : ι → AF F) :
    ∃! k : ι → F, (fun i => x i - algebraMap F (AF F) (k i)) ∈
      Set.univ.pi fun _ : ι => fundamentalSet F := by
  choose k hk huniq using fun i => existsUnique_sub_mem_fundamentalSet F (x i)
  refine ⟨k, fun i _ => hk i, fun k' hk' => funext fun i => huniq i _ (hk' i (Set.mem_univ i))⟩

theorem hermCovol : HermCovol := by
  intro F E _ _ _ _ _ σ hCM ψ hψ n ν hν
  obtain ⟨hinv, δ, hδ, hσδ⟩ := HaarCoord.conj_facts hCM
  have h2 := hCM.2.2.1
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h2]; omega)
  obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E h2
  let e := (hermVec_isHomeomorph hCM (AF F) b n).homeomorph _
  have he : ∀ S, e S = hermVec (AF F) σ b n S := fun _ => rfl
  obtain ⟨ξ, hξ⟩ := GlobalTheory.CompanionTheory.AdeleDual.exists_eq_adelicChar_mul ψ hψ.1 hψ.2.2.1
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := hψ.2.2.2
    apply hx
    rw [hξ x, map_zero, zero_mul, AddChar.map_zero_eq_one]
    simp
  have hs : (ξ • formB σ b n).IsSymm := (formB_isSymm hinv b n).smul ξ
  have hdet : (ξ • formB σ b n).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hξ0) (formB_det hinv b n)
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (HermR (AF F) σ n) := inferInstance
  haveI : BorelSpace (HermR (AF F) σ n) := ⟨rfl⟩
  have hsd : ν.map e = adeleMeasurePi F := by
    refine GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Fth.selfDual_eq _ hs hdet _
      (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Fth.selfDual_transport e ?_ _ _ ?_ ν hν)
    · intro x y
      exact hermVec_add (AF F) b n x y
    · intro S T
      have h3 : (ξ • formB σ b n).map (algebraMap F (AF F)) =
          algebraMap F (AF F) ξ • (formB σ b n).map (algebraMap F (AF F)) := by
        ext p q
        exact map_mul (algebraMap F (AF F)) ξ (formB σ b n p q)
      rw [hξ, pair_eq (AF F) hinv h2 hδ hσδ b n S T, chiG, h3, Matrix.smul_mulVec, dotProduct_smul,
        smul_eq_mul]
      rfl
  set D : Set (Idx n 2 → AF F) := Set.univ.pi fun _ => fundamentalSet F with hD
  have hDm : MeasurableSet D := MeasurableSet.univ_pi fun _ => measurableSet_fundamentalSet F
  have hinj : Function.Injective (hermVec (AF F) σ b n) := e.injective
  refine ⟨e ⁻¹' D, IsAddFundamentalDomain.mk' (hDm.preimage e.measurable).nullMeasurableSet ?_, ?_⟩
  · intro S
    obtain ⟨k, hk, huniq⟩ := existsUnique_sub_mem_pi (e S)
    have hg : e.symm (fun i => algebraMap F (AF F) (-k i)) ∈ ratHerm F E σ n :=
      (mem_ratHerm_iff hinv h2 b n hinj _).2 ⟨fun i => -k i, fun i => by
        rw [← he, e.apply_symm_apply]⟩
    refine ⟨⟨_, hg⟩, ?_, ?_⟩
    · change e (e.symm _ + S) ∈ D
      rw [he, hermVec_add, ← he, ← he, e.apply_symm_apply]
      convert hk using 2 with i
      simp [sub_eq_add_neg, add_comm]
    · rintro ⟨g, hgm⟩ hg'
      obtain ⟨k', hk'⟩ := (mem_ratHerm_iff hinv h2 b n hinj _).1 hgm
      change e (g + S) ∈ D at hg'
      rw [he, hermVec_add, ← he] at hg'
      have hkk : (fun i => -k' i) = k := huniq _ (by
        convert hg' using 2 with i
        simp [he, hk', sub_eq_add_neg, add_comm])
      refine Subtype.ext (e.injective ?_)
      rw [e.apply_symm_apply]
      funext i
      rw [he, hk', ← hkk]
      simp
  · rw [← Measure.map_apply e.measurable hDm, hsd, adeleMeasurePi, hD, Measure.pi_pi]
    simp [adeleMeasure_fundamentalSet]

end Main

end GlobalTheory.CompanionTheory.SW.HermCov
end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegIncDual

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_equiv_prodIrr_of_cast {h h' N : ℕ} (e : h = h') (x : Fin h → IrrGL (k := k)) (y : Fin h' → IrrGL (k := k))
    (hxy : ∀ a, x a = y (Fin.cast e a)) (hd : ∑ a, (x a).1 = N) :
    ∃ hd' : ∑ a, (y a).1 = N, Nonempty ((prodIrr x hd).Equiv (prodIrr y hd')) := by
  subst e
  obtain rfl : x = y := funext fun a => by simpa using hxy a
  exact ⟨hd, ⟨Representation.Equiv.refl _⟩⟩

theorem nonempty_contra_trans {h h' N : ℕ} {x y : Fin h → IrrGL (k := k)} {z : Fin h' → IrrGL (k := k)} {hd : ∑ a, (x a).1 = N}
    {hy : ∑ a, (y a).1 = N} {hz : ∑ a, (z a).1 = N} (H₁ : Nonempty ((contra (prodIrr x hd)).Equiv (prodIrr y hy)))
    (H₂ : Nonempty ((prodIrr y hy).Equiv (prodIrr z hz))) :
    Nonempty ((contra (prodIrr x hd)).Equiv (prodIrr z hz)) :=
  H₁.elim fun φ => H₂.elim fun ψ => ⟨φ.trans ψ⟩

theorem dualCl_term (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) (hl : Δ.len = (segDual Δ).len)
    (a : Fin Δ.len) : dualCl (Δ.term a) = dec (segDual Δ) (Fin.cast hl a) := by
  have hc : ∀ x : IrrGL (k := k), x.IsCusp → (dualCl x).IsCusp := fun x hx =>
    (GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp hA x hx).1
  have hv : ((Fin.rev (Fin.cast hl a) : Fin (segDual Δ).len) : ℕ) = Δ.len - (a + 1) := by
    have h0 : ((Fin.cast hl a : Fin (segDual Δ).len) : ℕ) = a := rfl
    rw [Fin.val_rev, h0]; omega
  have ha : (a : ℕ) + 1 ≤ Δ.len := a.2
  change dualCl (Δ.first.nu ((a : ℕ) : ℂ)) =
    (segDual Δ).first.nu (((Fin.rev (Fin.cast hl a) : Fin (segDual Δ).len) : ℕ) : ℂ)
  rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_nu hA, GlobalTheory.CompanionTheory.SegDualPrec.first_segDual hc, IrrGL.nu_nu, hv, Nat.cast_sub ha]
  congr 1
  push_cast
  ring

theorem contra_prodIrr_term : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) {N : ℕ}
    (hd : ∑ a, (Δ.term a).1 = N), ∃ hd' : ∑ a, (dec (segDual Δ) a).1 = N,
      Nonempty ((contra (prodIrr Δ.term hd)).Equiv (prodIrr (dec (segDual Δ)) hd')) := by
  intro k _ _ _ _ hA Δ N hd
  have hl : Δ.len = (segDual Δ).len :=
    (GlobalTheory.CompanionTheory.SegDualPrec.len_segDual (fun x hx => (GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp hA x hx).1) Δ).symm
  have H := @GlobalTheory.CompanionTheory.ContraProd.contra_prodIrr k _ _ _ _ hA Δ.len N Δ.term hd
  obtain ⟨hd₁, H₁⟩ := H
  have H' := exists_equiv_prodIrr_of_cast hl (fun a => dualCl (Δ.term a)) (dec (segDual Δ))
    (dualCl_term hA Δ hl) hd₁
  obtain ⟨hd₂, H₂⟩ := H'
  exact ⟨hd₂, nonempty_contra_trans H₁ H₂⟩

end GlobalTheory.CompanionTheory.SegIncDual

end
end

section


theorem _root_.GlobalTheory.T.local_hypotheses_hold : PositivityTheory.Rg.BcB.G8.Fin.LocHyp := by
  first | exact @GlobalTheory.CompanionTheory.LocHypProof.locHyp | exact GlobalTheory.CompanionTheory.LocHypProof.locHyp | (intros; apply GlobalTheory.CompanionTheory.LocHypProof.locHyp <;> assumption)
end
