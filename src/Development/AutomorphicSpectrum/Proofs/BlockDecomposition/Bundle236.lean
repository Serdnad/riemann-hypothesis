module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle216
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveSolutionExistence
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle025
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle043
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle032
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle039
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle055
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Development.WeilBound.CoreStatements.ThetaDilations.SdTransport
public import Formalism.RealPlaceAnalysis.Bundle003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle107
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle049
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle061
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle217
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype

@[expose] public section

section


theorem _root_.GlobalTheory.T.wave_kernel_existence : PositivityTheory.RgBcC.AsmKerEx := by
  first | exact @GlobalTheory.CompanionTheory.WaveKer.asmKerEx | exact GlobalTheory.CompanionTheory.WaveKer.asmKerEx | (intros; apply GlobalTheory.CompanionTheory.WaveKer.asmKerEx <;> assumption)
end

section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
open GlobalTheory.CompanionTheory.WaveAll

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.Swap

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rd_csmul {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (c : ℂ) (X : Mat n) :
    Set.EqOn (Rd X (c • f)) (c • Rd X f) (GLs n) := by
  intro x hx
  have h1 : DifferentiableAt ℝ f x :=
    (hf.contDiffAt (isOpen_GLs.mem_nhds hx)).differentiableAt (by simp)
  have h3 : fderiv ℝ (c • f) x = c • fderiv ℝ f x := (h1.hasFDerivAt.const_smul c).fderiv
  simp only [Rd, Pi.smul_apply, h3]
  rfl

theorem Eu_csmul {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (c : ℂ) (s : Bool) (a b : Fin n) :
    Set.EqOn (Eu s a b (c • f)) (c • Eu s a b f) (GLs n) := by
  intro x hx
  simp only [Eu, Pi.smul_apply, Pi.add_apply, Rd_csmul hf c _ hx]
  rw [smul_comm c (1 / 2 : ℂ), smul_add c, smul_comm c]

theorem Epow_csmul (hR : RCalc) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (c : ℂ) (s : Bool) (m : ℕ) :
    ∀ a b : Fin n, Set.EqOn (Epow s m a b (c • f)) (c • Epow s m a b f) (GLs n) := by
  induction m with
  | zero =>
    intro a b x hx
    by_cases hab : a = b <;> simp [Epow, hab]
  | succ m ih =>
    intro a b x hx
    simp only [Epow, Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Eu_congr isOpen_GLs (ih d b) s a d hx]
    exact Eu_csmul (Epow_smooth hR hf s m d b) c s a d hx

theorem gel_csmul (hR : RCalc) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (c : ℂ) (s : Bool) (m : ℕ) :
    Set.EqOn (gel s m (c • f)) (c • gel s m f) (GLs n) := by
  intro x hx
  simp only [gel, Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun a _ => Epow_csmul hR hf c s m a a hx

theorem gel_add (hR : RCalc) {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hf' : ContDiffOn ℝ ∞ f' (GLs n)) (s : Bool) (m : ℕ) :
    Set.EqOn (gel s m (f + f')) (gel s m f + gel s m f') (GLs n) := by
  intro x hx
  have e : f + f' = f - (-1 : ℂ) • f' := by
    ext y
    simp
  have hm : ContDiffOn ℝ ∞ ((-1 : ℂ) • f') (GLs n) := hf'.const_smul (-1 : ℂ)
  have h := gel_sub hR hf hm s m hx
  rw [e, h]
  simp only [Pi.sub_apply, Pi.add_apply, gel_csmul hR hf' (-1) s m hx, Pi.smul_apply]
  simp

theorem gel_zero (hR : RCalc) (s : Bool) (m : ℕ) :
    Set.EqOn (gel s m (0 : Mat n → V)) 0 (GLs n) := by
  intro x hx
  have h := gel_csmul hR (contDiffOn_const (c := (0 : V)) : ContDiffOn ℝ ∞ (0 : Mat n → V) (GLs n)) 0 s m hx
  simpa using h

theorem gel_sum (hR : RCalc) {ι : Type} (S : Finset ι) {F : ι → Mat n → V}
    (hF : ∀ i, ContDiffOn ℝ ∞ (F i) (GLs n)) (s : Bool) (m : ℕ) :
    Set.EqOn (gel s m (∑ i ∈ S, F i)) (∑ i ∈ S, gel s m (F i)) (GLs n) := by
  classical
  intro x hx
  induction S using Finset.induction_on with
  | empty => simpa using gel_zero hR s m hx
  | insert i S hi ih =>
    have hS : ContDiffOn ℝ ∞ (∑ j ∈ S, F j) (GLs n) := by
      have e : (∑ j ∈ S, F j) = fun y => ∑ j ∈ S, F j y := by
        ext y
        simp only [Finset.sum_apply]
      rw [e]
      exact ContDiffOn.sum fun j _ => hF j
    rw [Finset.sum_insert hi, Finset.sum_insert hi, gel_add hR (hF i) hS s m hx, Pi.add_apply, Pi.add_apply, ih]

theorem gel_smooth (hR : RCalc) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (m : ℕ) :
    ContDiffOn ℝ ∞ (gel s m f) (GLs n) := by
  have e : gel s m f = fun x => ∑ a, Epow s m a a f x := by
    ext x
    simp only [gel, Finset.sum_apply]
  rw [e]
  exact ContDiffOn.sum fun a _ => Epow_smooth hR hf s m a a

theorem zOp_smooth (hR : RCalc) (w : List (Bool × ℕ)) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (zOp w f) (GLs n) := by
  induction w with
  | nil => exact hf
  | cons p w ih => exact gel_smooth hR ih p.1 p.2

theorem Eu_gel (hR : RCalc) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s' : Bool) (a b : Fin n)
    (s : Bool) (m : ℕ) : Set.EqOn (Eu s' a b (gel s m f)) (gel s m (Eu s' a b f)) (GLs n) := by
  intro x hx
  have hc := (hR n).1 V f hf
  have hS := hc.1
  have hG := hc.2.2.1
  set d : ℂ := if s' then -Complex.I else Complex.I with hd
  have hdB : ContDiffOn ℝ ∞ (d • Rd (Matrix.single a b Complex.I) f) (GLs n) :=
    (hS _).const_smul d
  have hsum : ContDiffOn ℝ ∞ (Rd (Matrix.single a b 1) f + d • Rd (Matrix.single a b Complex.I) f) (GLs n) :=
    (hS _).add hdB
  have e : Eu s' a b f = (1 / 2 : ℂ) • (Rd (Matrix.single a b 1) f + d • Rd (Matrix.single a b Complex.I) f) := rfl
  rw [e, gel_csmul hR hsum _ s m hx, Pi.smul_apply, gel_add hR (hS _) hdB s m hx, Pi.add_apply,
    gel_csmul hR (hS _) d s m hx, Pi.smul_apply, ← hG s m _ x hx, ← hG s m _ x hx]
  rfl

theorem Epow_gel (hR : RCalc) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s' : Bool) (m' : ℕ)
    (s : Bool) (m : ℕ) :
    ∀ a b : Fin n, Set.EqOn (Epow s' m' a b (gel s m f)) (gel s m (Epow s' m' a b f)) (GLs n) := by
  induction m' with
  | zero =>
    intro a b x hx
    by_cases hab : a = b
    · simp [Epow, hab]
    · simp only [Epow, if_neg hab]
      exact (gel_zero hR s m hx).symm
  | succ m' ih =>
    intro a b x hx
    have e : Epow s' (m' + 1) a b f = ∑ c, Eu s' a c (Epow s' m' c b f) := rfl
    rw [e, gel_sum hR _ (fun c => Eu_smooth hR (Epow_smooth hR hf s' m' c b) s' a c) s m hx]
    simp only [Epow, Finset.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Eu_congr isOpen_GLs (ih c b) s' a c hx]
    exact Eu_gel hR (Epow_smooth hR hf s' m' c b) s' a c s m hx

theorem gel_gel (hR : RCalc) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s' : Bool) (m' : ℕ)
    (s : Bool) (m : ℕ) : Set.EqOn (gel s' m' (gel s m f)) (gel s m (gel s' m' f)) (GLs n) := by
  intro x hx
  have e : gel s' m' f = ∑ a, Epow s' m' a a f := rfl
  rw [e, gel_sum hR _ (fun a => Epow_smooth hR hf s' m' a a) s m hx]
  simp only [gel, Finset.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h := Epow_gel hR hf s' m' s m a a hx
  simpa only [gel, Finset.sum_apply] using h

theorem zOp_append (w w' : List (Bool × ℕ)) (f : Mat n → V) : zOp (w ++ w') f = zOp w (zOp w' f) := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    change gel p.1 p.2 (zOp (w ++ w') f) = gel p.1 p.2 (zOp w (zOp w' f))
    rw [ih]

theorem gel_zOp (hR : RCalc) (s : Bool) (m : ℕ) (w : List (Bool × ℕ)) {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) : Set.EqOn (gel s m (zOp w f)) (zOp w (gel s m f)) (GLs n) := by
  induction w with
  | nil => exact fun _ _ => rfl
  | cons p w ih =>
    intro x hx
    change gel s m (gel p.1 p.2 (zOp w f)) x = gel p.1 p.2 (zOp w (gel s m f)) x
    rw [gel_gel hR (zOp_smooth hR w hf) s m p.1 p.2 hx]
    exact gel_congr isOpen_GLs ih p.1 p.2 hx

theorem zOp_zOp (hR : RCalc) (w w' : List (Bool × ℕ)) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (zOp w (zOp w' f)) (zOp w' (zOp w f)) (GLs n) := by
  induction w with
  | nil => exact fun _ _ => rfl
  | cons p w ih =>
    intro x hx
    change gel p.1 p.2 (zOp w (zOp w' f)) x = zOp w' (gel p.1 p.2 (zOp w f)) x
    rw [gel_congr isOpen_GLs ih p.1 p.2 hx]
    exact gel_zOp hR p.1 p.2 w' (zOp_smooth hR w hf) hx

theorem zOp_swap : RCalc → ∀ (n : ℕ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (w w' : List (Bool × ℕ)) (f : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) →
    ∀ x ∈ GLs n, zOp (w ++ w') f x = zOp (w' ++ w) f x := by
  intro hR n V _ _ w w' f hf x hx
  rw [zOp_append, zOp_append]
  exact zOp_zOp hR w w' hf hx

end GlobalTheory.CompanionTheory.WaveMult.Swap
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.RgMass

section Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sigma_sigma (hcm : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hcm.2.2.2, hcm.2.2.2]
  simp

theorem hE_self_fixed (hcm : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (x : Fin M → E) :
    σ (hE σ J x x) = hE σ J x x := by

  simp only [hE, hform, map_sum, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 : σ ((σ : E →+* E) (x j)) = x j := sigma_sigma hcm _
  have h2 : (σ : E →+* E) (x i) = σ (x i) := rfl
  rw [h1, hJ.1 i j, h2]
  ring

theorem exists_len (hcm : IsCMExt F E σ) {J : Matrix (Fin 2) (Fin 2) E} (hJ : IsHermND σ J) (hA : Aniso σ J)
    {X : Fin 1 → Fin 2 → E} (hX : X ≠ 0) : ∃ β : F, β ≠ 0 ∧ X ∈ sph σ J β := by
  have hT : ∀ a b, σ (gramE σ J X b a) = gramE σ J X a b := fun a b => by
    rw [Subsingleton.elim a b]
    exact hE_self_fixed hcm hJ _
  obtain ⟨β, e, h, -⟩ := GlobalTheory.T.hermitian_one_by_one_is_scalar F E σ hcm _ hT
  refine ⟨β, h ?_, e⟩
  rw [Matrix.det_unique]
  intro h0
  exact hX (funext fun a => by rw [Subsingleton.elim a default]; exact hA _ h0)

theorem sph_unique {J : Matrix (Fin 2) (Fin 2) E} {X : Fin 1 → Fin 2 → E} {β β' : F} (h : X ∈ sph σ J β)
    (h' : X ∈ sph σ J β') : β = β' := by
  have e : (fun _ _ => algebraMap F E β : Matrix (Fin 1) (Fin 1) E) = fun _ _ => algebraMap F E β' := h.symm.trans h'
  exact (algebraMap F E).injective (congrFun (congrFun e 0) 0)

theorem ne_zero_of_mem_sph {J : Matrix (Fin 2) (Fin 2) E} {X : Fin 1 → Fin 2 → E} {β : F} (hβ : β ≠ 0)
    (h : X ∈ sph σ J β) : X ≠ 0 := by
  rintro rfl
  refine hβ (sph_unique h ?_)
  funext a c
  simp [gramE, hE, hform]

def sphEquiv (hcm : IsCMExt F E σ) {J : Matrix (Fin 2) (Fin 2) E} (hJ : IsHermND σ J) (hA : Aniso σ J) :
    (Σ β : {β : F // β ≠ 0}, sph σ J β.1) ≃ {X : Fin 1 → Fin 2 → E | X ≠ 0} :=
  Equiv.ofBijective (fun p => ⟨p.2.1, ne_zero_of_mem_sph p.1.2 p.2.2⟩) (by
    constructor
    · rintro ⟨β, X⟩ ⟨β', X'⟩ h
      have hX : X.1 = X'.1 := congrArg Subtype.val h
      have hb : β = β' := Subtype.ext (sph_unique X.2 (hX ▸ X'.2))
      subst hb
      obtain rfl : X = X' := Subtype.ext hX
      rfl
    · rintro ⟨X, hX⟩
      obtain ⟨β, h0, hβ⟩ := exists_len hcm hJ hA hX
      exact ⟨⟨⟨β, h0⟩, ⟨X, hβ⟩⟩, rfl⟩)

theorem thetaMeas_ne (hcm : IsCMExt F E σ) {J : Matrix (Fin 2) (Fin 2) E} (hJ : IsHermND σ J) (hA : Aniso σ J)
    (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)) :
    thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin 2 → E | X ≠ 0} =
      Measure.sum fun β : {β : F // β ≠ 0} => thetaMeas σ J μ 𝓕 (sph σ J β.1) := by
  ext s hs
  simp only [thetaMeas, Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul, ENNReal.tsum_mul_left]
  congr 1
  rw [← (sphEquiv hcm hJ hA).tsum_eq, ENNReal.tsum_sigma']
  rfl

end Alg



theorem cnt : TestEx → LSide → RSide → Cnt := by
  intro hTE hL hR F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hcm hJ hAn hli hlam hμ h𝓕 hmi hm κ hκ
  obtain ⟨⟨θ, hθ⟩, -⟩ := PositivityTheory.PlacePermOperatorBicommutantSpan.theta_real F hcm.1
  obtain ⟨S, hS⟩ := hR F E σ J d b li lam μ 𝓕 mi m hcm hJ hAn hli hlam hμ h𝓕 hmi hm θ hθ
  obtain ⟨φ, A, ht, hv0, hvT⟩ := hTE F E σ J d b li lam μ 𝓕 mi m hcm hJ hAn hli hlam hμ h𝓕 hmi hm S
  have hLt := hL F E σ J d b li lam μ 𝓕 mi m hcm hJ hAn hli hlam hμ h𝓕 hmi hm θ hθ S φ A ht
  have hRt := hS S (Finset.Subset.refl _) φ A ht
  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  obtain ⟨_, _, _, _, -⟩ := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hcm.1
  obtain ⟨_, -, -, -, -, -, -, hBinf, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Ainf F)
  have := hBinf 1 2
  obtain ⟨hφc, -, -, -, hAS, hAo⟩ := ht
  have hdil : ∀ ε : ℝ, Continuous (dil θ ε : (Fin 1 → Fin 2 → Ainf F ⊗[F] E) → _) := fun ε =>
    continuous_pi fun a => continuous_pi fun i =>
      continuous_const.mul ((continuous_apply i).comp (continuous_apply a))
  have hloc : ∀ v, IsCompact (A v) ∧ MeasurableSet (A v) ∧
      ∀ s : HermR (Fv F v) σ 1, m v s (A v) < ⊤ := fun v => by
    have hRv := GlobalTheory.T.completion_is_local_ring F v
    have hRv' := hRv
    obtain ⟨_, _, _, _, -⟩ := hRv'
    have : BorelSpace (Fv F v) := ⟨rfl⟩
    obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Fv F v)
    have := hB 1 2
    obtain ⟨-, k1, k2⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hcm (Fv F v) d b (lam v) (hlam v).1
    have hco : IsCompact (A v) ∧ IsOpen (A v) := by
      by_cases hv : v ∈ S
      · exact ⟨(hAS v hv).1, (hAS v hv).2.1⟩
      · rw [hAo v hv]
        exact (GlobalTheory.T.adelic_tuple_projections F E σ hcm d b 1 2).2.2.2.1 v
    refine ⟨hco.1, hco.2.measurableSet, fun s => ?_⟩
    have := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hcm 2 J hJ (Fv F v) hRv 1 _ _ _ (k1 1 2) (k2 1) (hm v) s).1
    exact hco.1.measure_lt_top
  have hcof : ∀ᶠ v in cofinite, A v = latV b v :=
    S.finite_toSet.eventually_cofinite_notMem.mono fun v hv => hAo v (by simpa using hv)
  have key : ∀ ε : ℝ, ∫⁻ X in {X | ∀ v, projV v (projFin X) ∈ A v}, ENNReal.ofReal (φ (dil θ ε (projInf X)))
        ∂(thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin 2 → E | X ≠ 0}) =
      (κ : ℝ≥0∞) * ∑' β : {β : F // β ≠ 0},
        (∫⁻ X, ENNReal.ofReal (φ (dil θ ε X)) ∂(mi (hermScal (Ainf F) σ (algebraMap F _ β.1)))) *
          ENNReal.ofReal (∏' v, (m v (hermScal (Fv F v) σ (algebraMap F _ β.1)) (A v)).toReal) := fun ε => by
    rw [thetaMeas_ne hcm hJ hAn, Measure.restrict_sum_of_countable, lintegral_sum_measure, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun β => ?_
    have hEu : IsEulerProd b (thetaMeas σ J μ 𝓕 (sph σ J β.1)) κ (mi (hermScal (Ainf F) σ (algebraMap F _ β.1)))
        (fun v => m v (hermScal (Fv F v) σ (algebraMap F _ β.1))) := hκ β.1 β.2
    obtain ⟨-, e⟩ := GlobalTheory.T.euler_product_measure_integral F E σ hcm d b 1 2 _ κ _ _ hEu (fun Y => ENNReal.ofReal (φ (dil θ ε Y))) A
      (hφc.comp (hdil ε)).measurable.ennreal_ofReal (fun v => (hloc v).2.1) (fun v => (hloc v).2.2 _) hcof
    rw [e, mul_assoc]
  simp only [key] at hLt
  have h1 := ENNReal.Tendsto.const_mul (a := (κ : ℝ≥0∞)) hRt (Or.inr ENNReal.coe_ne_top)
  have h2 : (vol b li lam S φ A) = (κ : ℝ≥0∞) * vol b li lam S φ A :=
    tendsto_nhds_unique hLt (h1.congr fun ε => mul_left_comm _ _ _)
  have h3 : (κ : ℝ≥0∞) = 1 := by
    have h4 : (κ : ℝ≥0∞) * vol b li lam S φ A = 1 * vol b li lam S φ A := by rw [one_mul]; exact h2.symm
    exact (ENNReal.mul_left_inj hv0 hvT).1 h4
  exact_mod_cast h3

end GlobalTheory.CompanionTheory.RgMass

end
end

section

open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.CapelliEigen

open Formalism.REAL Finset Polynomial GlobalTheory.CapelliNewton

theorem etr_apply_of_eigen : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ V), Formalism.REAL.GlRel E → ∀ (P : Polynomial ℂ) (v : V), (∀ u : ℂ, Formalism.REAL.qdet E u v = P.eval u • v) → ∀ (N : ℕ) (t : ℕ → ℂ), (∀ k < N, Formalism.REAL.etr E k v = t k • v) → Formalism.REAL.etr E N v = ((-1 : Polynomial ℂ) ^ N * ((Polynomial.X - Polynomial.C (m : ℂ)) ^ (N + 1) * ((P).comp (Polynomial.X + 1) - (P)) - (P) * ∑ k ∈ Finset.range N, Polynomial.C ((-1) ^ k * t k) * (Polynomial.X - Polynomial.C (m : ℂ)) ^ (N - k))).coeff (m + 1) • v := by
  intro V _ _ m E hE P v hP N t ht
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).mp fun φ => ?_
  obtain ⟨c, hc1, hc⟩ := GlobalTheory.T.exists_monic_poly_eq_qdet (Module.End ℂ V) (m + 1) E
  have hmin : ∀ i j : Fin (m + 1), ∃ c' : ℕ → Module.End ℂ V, ∀ w : ℂ,
      qminor E (Fin.succAbove j) (Fin.succAbove i) w = ∑ d ∈ range (m + 1), w ^ d • c' d := by
    intro i j
    obtain ⟨c', hc'⟩ := GlobalTheory.qminor_polyMap (Module.End ℂ V) (m + 1) m E (Fin.succAbove j) (Fin.succAbove i) 0
    exact ⟨c', fun w => by simpa using hc' w⟩
  choose cm hcm using hmin
  let Rc : ℕ → Module.End ℂ V := fun d => ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
    (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : Module.End ℂ V) * cm i j d * epow E (N + 1) j i
  have hR : ∀ w : ℂ, ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
      (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : Module.End ℂ V) * qminor E (Fin.succAbove j) (Fin.succAbove i) w
        * epow E (N + 1) j i = ∑ d ∈ range (m + 1), w ^ d • Rc d := by
    intro w
    simp only [Rc, hcm, mul_sum, sum_mul, smul_sum, mul_smul_comm, smul_mul_assoc]
    conv_lhs => enter [2, x]; rw [sum_comm]
    rw [sum_comm]
  set Rp := polyOf m Rc φ v with hRp
  set Pq := polyOf (m + 1) c φ (etr E N v) with hPq
  have hPqe : ∀ w : ℂ, Pq.eval w = φ (qdet E w (etr E N v)) := fun w => by rw [hPq, polyOf_eval, hc]
  have hPv : ∀ w : ℂ, φ (qdet E w v) = P.eval w * φ v := fun w => by
    rw [hP, map_smul, smul_eq_mul]
  have hsq : (((-1 : ℂ) ^ N) ^ 2) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; simp
  have hrec : ∀ w : ℂ, (w - m) ^ (N + 1) * ((P.eval (w + 1) - P.eval w) * φ v) + (-1) ^ N * Rp.eval w
      = (∑ k ∈ range N, (-1) ^ k * (w - m) ^ (N - k) * t k) * (P.eval w * φ v) + (-1) ^ N * Pq.eval w := by
    intro w
    have h1 := congrArg (fun T : Module.End ℂ V => φ (T v)) (GlobalTheory.T.traced_qminor_comatrix_truncated_inverse (Module.End ℂ V) m E hE w N)
    rw [← GlobalTheory.T.qdet_add_one_sub_eq_sum_qminor', hR] at h1
    have h2 : (qdet E w * ∑ k ∈ range (N + 1), algebraMap ℂ (Module.End ℂ V) ((-1) ^ k * (w - m) ^ (N - k)) * etr E k) v
        = (∑ k ∈ range N, (-1) ^ k * (w - m) ^ (N - k) * t k) • qdet E w v
          + ((-1 : ℂ) ^ N) • qdet E w (etr E N v) := by
      have h3 : ∀ k ∈ range N, (algebraMap ℂ (Module.End ℂ V) ((-1) ^ k * (w - m) ^ (N - k)) * etr E k) v
          = ((-1) ^ k * (w - m) ^ (N - k) * t k) • v := by
        intro k hk
        rw [Module.End.mul_apply, ht k (mem_range.mp hk), Module.algebraMap_end_apply, smul_smul]
      rw [Module.End.mul_apply, sum_range_succ, LinearMap.add_apply, LinearMap.sum_apply, sum_congr rfl h3,
        ← sum_smul, map_add, map_smul, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul]
      simp
    rw [h2] at h1
    simp only [LinearMap.add_apply, Module.End.mul_apply, Module.algebraMap_end_apply, map_add (f := _), map_smul,
      LinearMap.sub_apply, map_sub, smul_eq_mul] at h1
    rw [← polyOf_eval, ← hRp, ← hPqe] at h1
    simp only [hPv] at h1
    linear_combination h1
  have hpoly : C (φ v) * ((-1 : ℂ[X]) ^ N * ((X - C (m : ℂ)) ^ (N + 1) * (P.comp (X + 1) - P)
      - P * ∑ k ∈ range N, C ((-1) ^ k * t k) * (X - C (m : ℂ)) ^ (N - k))) = Pq - Rp := by
    refine Polynomial.funext fun w => ?_
    have h1 := hrec w
    simp only [eval_mul, eval_C, eval_pow, eval_neg, eval_one, eval_sub, eval_X, eval_comp, eval_add,
      eval_finsetSum]
    have h4 : ∑ k ∈ range N, (-1) ^ k * t k * (w - m) ^ (N - k)
        = ∑ k ∈ range N, (-1) ^ k * (w - m) ^ (N - k) * t k :=
      sum_congr rfl fun k _ => by ring
    rw [h4]
    linear_combination ((-1 : ℂ) ^ N) * h1 + (Pq.eval w - Rp.eval w) * hsq
  have hco := congrArg (fun p : ℂ[X] => p.coeff (m + 1)) hpoly
  simp only [coeff_C_mul, coeff_sub] at hco
  have hPc : Pq.coeff (m + 1) = φ (etr E N v) := by
    rw [hPq, polyOf_coeff, hc1]; simp
  have hRc : Rp.coeff (m + 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt ((polyOf_natDegree _ _ _ _).trans_lt (Nat.lt_succ_self m))
  rw [hPc, hRc, sub_zero] at hco
  rw [map_sub, map_smul, smul_eq_mul, ← hco]
  ring

end GlobalTheory.CompanionTheory.CapelliEigen
end

section


theorem _root_.GlobalTheory.T.schwartz_exists_real_majorant : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (f : SchwartzMap E ℂ), ∃ F : SchwartzMap E ℂ, ∀ x, (F x).im = 0 ∧ ‖f x‖ ≤ (F x).re := by
  first | exact @GlobalTheory.CompanionTheory.SchwartzMaj.exists_nonneg_schwartz_majorant | exact GlobalTheory.CompanionTheory.SchwartzMaj.exists_nonneg_schwartz_majorant | (intros; apply GlobalTheory.CompanionTheory.SchwartzMaj.exists_nonneg_schwartz_majorant <;> assumption)
end
