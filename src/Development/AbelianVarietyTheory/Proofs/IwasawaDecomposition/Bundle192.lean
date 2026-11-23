module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle004
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle104
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle037
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle040
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle107
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle108
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle047
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle033
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle034
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle043
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle050
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle052
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle032
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle080
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle184
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle186
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle185
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle187
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
import Mathlib.SetTheory.ZFC.PSet
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle180
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle002
import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory.QCoh

theorem exists_isIrreducible_inter_open_subset {α : Type*} [TopologicalSpace α] [NoetherianSpace α]
    {T : Set α} (hT : IsClosed T) (hne : T.Nonempty) :
    ∃ Z : Set α, IsClosed Z ∧ IsIrreducible Z ∧ Z ⊆ T ∧
      ∃ U : Set α, IsOpen U ∧ (∃ x ∈ T, x ∈ U) ∧ T ∩ U ⊆ Z := by
  classical
  obtain ⟨S, hS, hc, hi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hT
  have hSne : S.Nonempty := by
    obtain ⟨x, t, ht, -⟩ := hne
    exact ⟨t, ht⟩
  obtain ⟨Z, hZ⟩ := hS.exists_maximal hSne
  have hfin : (S \ {Z}).Finite := hS.diff
  refine ⟨Z, hc Z hZ.1, hi Z hZ.1, Set.subset_sUnion_of_mem hZ.1, (⋃₀ (S \ {Z}))ᶜ, ?_, ?_, ?_⟩
  · rw [isOpen_compl_iff, Set.sUnion_eq_biUnion]
    exact hfin.isClosed_biUnion fun t ht => hc t ht.1
  · by_contra h
    have hsub : Z ⊆ ⋃₀ (hfin.toFinset : Set (Set α)) := fun x hx => by
      rw [hfin.coe_toFinset]
      by_contra hx'
      exact h ⟨x, Set.subset_sUnion_of_mem hZ.1 hx, hx'⟩
    obtain ⟨z, hz, hZz⟩ := isIrreducible_iff_sUnion_isClosed.1 (hi Z hZ.1) hfin.toFinset
      (fun z hz => hc z (hfin.mem_toFinset.1 hz).1) hsub
    have hz' := hfin.mem_toFinset.1 hz
    exact hz'.2 (le_antisymm (hZ.2 hz'.1 hZz) hZz)
  · rintro x ⟨⟨t, ht, hxt⟩, hx⟩
    by_contra hxZ
    exact hx ⟨t, ⟨ht, fun e => hxZ ((show t = Z from e) ▸ hxt)⟩, hxt⟩

variable {X : Scheme.{0}}

theorem exists_pow_vanishingIdeal_le_annihilator [IsLocallyNoetherian X] (F : X.Modules)
    [IsFiniteQC F] (Z : Closeds X) (W : X.affineOpens) (h : support F ∩ W.1 ⊆ Z) :
    ∃ k : ℕ, (Scheme.IdealSheafData.vanishingIdeal Z).ideal W ^ k ≤
      Module.annihilator Γ(X, W.1) Γ(F, W.1) := by
  have := finite_sections F W.2
  have : IsNoetherianRing Γ(X, W.1) := IsLocallyNoetherian.component_noetherian W
  refine Ideal.exists_pow_le_of_le_radical_of_fg ?_ (IsNoetherian.noetherian _)
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal, ← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical,
    ← Module.support_eq_zeroLocus, ← fromSpec_preimage_support F W.2]
  refine PrimeSpectrum.vanishingIdeal_anti_mono fun p hp => h ⟨hp, ?_⟩
  exact W.2.range_fromSpec.le ⟨p, rfl⟩

theorem pow_le_annihilator_kernel_unit (I : X.IdealSheafData) (E : X.Modules) [E.IsQuasicoherent]
    (W : X.affineOpens) {k : ℕ}
    (h : I.ideal W ^ (k + 1) ≤ Module.annihilator Γ(X, W.1) Γ(E, W.1)) :
    I.ideal W ^ k ≤ Module.annihilator Γ(X, W.1)
      Γ(kernel ((Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app E), W.1) := by
  set φ := (Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app E with hφ
  intro a ha
  refine Module.mem_annihilator.2 fun t => ?_
  have h₁ : appLinear (kernel.ι φ) W.1 t ∈ (I.ideal W • ⊤ : Submodule Γ(X, W.1) Γ(E, W.1)) := by
    have := (surjective_and_ker_unit_subschemeι I E W).2
    rw [← hφ, ← range_kernel_ι_app] at this
    exact this.le ⟨t, rfl⟩
  have h₂ : ∀ u ∈ (I.ideal W • ⊤ : Submodule Γ(X, W.1) Γ(E, W.1)), a • u = 0 := fun u hu => by
    refine Submodule.smul_induction_on hu (fun r hr n _ => ?_) fun x y hx hy => ?_
    · rw [smul_smul]
      exact Module.mem_annihilator.1 (h (pow_succ (I.ideal W) k ▸ Ideal.mul_mem_mul ha hr)) n
    · rw [smul_add, hx, hy, add_zero]
  refine injective_kernel_ι_app φ W.1 ?_
  change appLinear (kernel.ι φ) W.1 (a • t) = appLinear (kernel.ι φ) W.1 0
  rw [map_smul, map_zero]
  exact h₂ _ h₁

theorem devissage : ∀ (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X] (P : X.Modules → Prop), (∀ F : X.Modules, IsZero F → P F) → (∀ S : ShortComplex X.Modules, S.ShortExact → IsFiniteQC S.X₁ → IsFiniteQC S.X₃ → P S.X₁ → P S.X₃ → P S.X₂) → (∀ (Z : Closeds X), IsIrreducible (Z : Set X) → (∀ F : X.Modules, IsFiniteQC F → GlobalTheory.QCoh.support F ⊂ (Z : Set X) → P F) → ∀ G : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.Modules, IsFiniteQC G → P ((Scheme.Modules.pushforward (redι Z)).obj G)) → ∀ F : X.Modules, IsFiniteQC F → P F := by
  intro X _ P h0 hext hZ
  suffices H : ∀ T : Closeds X, ∀ F : X.Modules, IsFiniteQC F → support F = T → P F from
    fun F hF => H ⟨support F, isClosed_support F⟩ F hF rfl
  intro T
  induction T using WellFoundedLT.induction with
  | ind T ih =>
  intro F hF hT
  have ih' : ∀ E : X.Modules, IsFiniteQC E → support E ⊂ (T : Set X) → P E := fun E hE h =>
    ih ⟨support E, isClosed_support E⟩ h E hE rfl
  rcases (T : Set X).eq_empty_or_nonempty with he | hne
  · exact h0 F (support_eq_empty_iff.1 (hT.trans he))
  obtain ⟨Z, hZc, hZi, hZT, U, hU, ⟨x, hxT, hxU⟩, hUZ⟩ :=
    exists_isIrreducible_inter_open_subset T.isClosed hne
  obtain ⟨W, hW, hxW, hWU⟩ := exists_affine_mem_le (U := ⟨U, hU⟩) x hxU
  let Z' : Closeds X := ⟨Z, hZc⟩
  have hP := hZ Z' hZi fun E hE h => ih' E hE (h.trans_subset hZT)
  obtain ⟨k, hk⟩ := exists_pow_vanishingIdeal_le_annihilator F Z' ⟨W, hW⟩
    fun y hy => hUZ ⟨hT ▸ hy.1, hWU hy.2⟩
  have key : ∀ (k : ℕ) (E : X.Modules), IsFiniteQC E → support E ⊆ T →
      (Scheme.IdealSheafData.vanishingIdeal Z').ideal ⟨W, hW⟩ ^ k ≤
        Module.annihilator Γ(X, W) Γ(E, W) → P E := by
    intro k
    induction k with
    | zero =>
      intro E hE hET h
      refine ih' E hE ⟨hET, fun hle => ?_⟩
      have h₁ := (mem_support_iff_annihilator_le (F := E) hW ⟨x, hxW⟩).1 (hle hxT)
      rw [pow_zero, Ideal.one_eq_top] at h
      exact (hW.primeIdealOf ⟨x, hxW⟩).isPrime.ne_top (top_le_iff.1 (h.trans h₁))
    | succ k ihk =>
      intro E hE hET h
      let G := (Scheme.Modules.pullback (redι Z')).obj E
      let φ : E ⟶ (Scheme.Modules.pushforward (redι Z')).obj G :=
        (Scheme.Modules.pullbackPushforwardAdjunction (redι Z')).unit.app E
      have hepi : Epi φ := (epi_iff_forall_affine φ).2 fun V hV =>
        (surjective_and_ker_unit_subschemeι _ E ⟨V, hV⟩).1
      have hS : (ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ)).ShortExact :=
        { exact := ShortComplex.exact_kernel φ }
      have hK : IsFiniteQC (kernel φ) := inferInstance
      exact hext _ hS hK (IsFiniteQC.of_epi φ)
        (ihk _ hK ((support_subset_of_mono (kernel.ι φ)).trans hET)
          (pow_le_annihilator_kernel_unit _ E ⟨W, hW⟩ h)) (hP G inferInstance)
  exact key k F hF hT.le hk

end GlobalTheory.QCoh
end
end

section

noncomputable section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LieBase

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


open Classical in
def pointPoly (H : Host E) (Dw : Datum H) : MvPolynomial ((E →+* ℂ) × ℕ) ℝ :=
  ∏ τ : GlobalTheory.AllWt.Psi H, (C ((-1 : ℝ) ^ Dw.mult τ.1) * X (τ.1, Dw.mult τ.1)) ^ (Dw.p + Dw.q - Dw.mult τ.1)

end GlobalTheory.LieBase
end
end

section

noncomputable section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GrassTop

def wt {ι : Type} (d : ι × ℕ →₀ ℕ) : ℕ := d.sum fun x i => x.2 * i

def rel (k : ℕ) : MvPolynomial (Bool × ℕ) ℝ :=
  ∑ a ∈ Finset.range (k + 1), C ((-1 : ℝ) ^ (k - a)) * X (true, a) * X (false, k - a)

def gens (p q : ℕ) : Set (MvPolynomial (Bool × ℕ) ℝ) :=
  {f | (∃ k, 1 ≤ k ∧ f = rel k) ∨ (∃ b, f = X (b, 0) - 1) ∨ (∃ k, p < k ∧ f = X (true, k)) ∨
    (∃ k, q < k ∧ f = X (false, k))}

def J (p q : ℕ) : Ideal (MvPolynomial (Bool × ℕ) ℝ) := Ideal.span (gens p q)

def basis (p q : ℕ) : Set (MvPolynomial (Bool × ℕ) ℝ) :=
  {f | (∃ d, wt d < p * q ∧ f = monomial d 1) ∨ f = X (true, p) ^ q}

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def renVar {H : Host E} (τ : GlobalTheory.AllWt.Psi H) (y : Bool × ℕ) : (E →+* ℂ) × ℕ :=
  (if y.1 then τ.1 else conjEmb τ.1, y.2)

def ren {H : Host E} (τ : GlobalTheory.AllWt.Psi H) :
    MvPolynomial (Bool × ℕ) ℝ →ₐ[ℝ] MvPolynomial ((E →+* ℂ) × ℕ) ℝ :=
  rename (renVar τ)

end GlobalTheory.GrassTop
end
end

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.AlcZero

theorem eq_of_hcVal_eq_charZero (k : Type) [Field k] [CharZero k] (N : ℕ) (ν μ : Fin N → ℕ)
    (hν : Antitone ν) (hμ : Antitone μ) (hc : ∀ h : 0 < N, ν ⟨N - 1, by omega⟩ = 0 ∧ μ ⟨0, h⟩ ≤ ν ⟨0, h⟩)
    (hv : ∀ j, hcVal k (fun i => (μ i : k)) j = hcVal k (fun i => (ν i : k)) j) : μ = ν := by
  have hZ : ∀ j, hcVal ℤ (fun i => (μ i : ℤ)) j = hcVal ℤ (fun i => (ν i : ℤ)) j := by
    intro j
    apply Int.cast_injective (α := k)
    have h1 := hcVal_map (Int.castRingHom k) (fun i => (μ i : ℤ)) j
    have h2 := hcVal_map (Int.castRingHom k) (fun i => (ν i : ℤ)) j
    simp only [eq_intCast, Int.cast_natCast] at h1 h2
    rw [← h1, ← h2]
    exact hv j
  obtain ⟨p, hp1, hp⟩ := Nat.exists_infinite_primes (∑ i, ν i + N)
  haveI := Fact.mk hp
  apply eq_of_hcVal_eq p hp (ZMod p) N ν μ hν hμ
  · intro h
    refine ⟨(hc h).1, (hc h).2, ?_⟩
    have : ν ⟨0, h⟩ ≤ ∑ i, ν i := Finset.single_le_sum (fun i _ => Nat.zero_le (ν i)) (Finset.mem_univ _)
    omega
  · intro j
    have h1 := hcVal_map (Int.castRingHom (ZMod p)) (fun i => (μ i : ℤ)) j
    have h2 := hcVal_map (Int.castRingHom (ZMod p)) (fun i => (ν i : ℤ)) j
    simp only [eq_intCast, Int.cast_natCast] at h1 h2
    rw [h1, h2, hZ j]

end GlobalTheory.AlcZero

namespace GlobalTheory.AlcZero

theorem map_rowAct_eq {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {N : ℕ}
    (g : Matrix (Fin N) (Fin N) R) (f : MvPolynomial (Fin N × Fin N) R) :
    MvPolynomial.map φ (rowAct R (n := N) g f) = rowAct S (n := N) (g.map φ) (MvPolynomial.map φ f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [rowAct]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1

    simp [rowAct, map_sum, Matrix.map_apply]

theorem map_mem_span_map {S A : Type} [CommRing S] [CommRing A] (ψ : S →+* A) {σ : Type}
    (X : Set (MvPolynomial σ S)) (P : MvPolynomial σ S) (hP : P ∈ Submodule.span S X) :
    MvPolynomial.map ψ P ∈ Submodule.span A (MvPolynomial.map ψ '' X) := by
  induction hP using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [(MvPolynomial.map ψ).map_add]; exact add_mem hy hz
  | smul c y _ hy =>
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hy

theorem isGLSubmodule_of_stable (k : Type) [Field k] [Infinite k] (N : ℕ) (lam : DomWeight N)
    (M : Submodule k (MvPolynomial (Fin N × Fin N) k))
    (hG : ∀ g : GL (Fin N) k, ∀ f ∈ M, sqAct k N lam g f ∈ M) : GlobalTheory.Published.IsGLSubmodule k N lam M := by
  intro A _ _ g f hf
  let S := MvPolynomial (Fin N × Fin N) k
  let Y : Matrix (Fin N) (Fin N) S := Matrix.mvPolynomialX (Fin N) (Fin N) k
  let P : MvPolynomial (Fin N × Fin N) S :=
    rowAct S (n := N) Y.transpose (MvPolynomial.map (algebraMap k S) f)
  have hP : P ∈ Submodule.span S (MvPolynomial.map (algebraMap k S) '' (M : Set (MvPolynomial (Fin N × Fin N) k))) := by
    refine GlobalTheory.T.mem_span_map_of_eval_mem_of_ne_zero k _ _ M Y.det (Matrix.det_mvPolynomialX_ne_zero _ _) P ?_
    intro y hy
    let m0 : Matrix (Fin N) (Fin N) k := Matrix.of fun i j => y (i, j)
    have hm0 : Y.map (MvPolynomial.eval y) = m0 := by
      ext i j; simp [Y, m0, Matrix.mvPolynomialX]
    have hdet : m0.det ≠ 0 := by
      rw [← hm0]; rw [RingHom.map_det] at hy; exact hy
    let g0 : GL (Fin N) k := Matrix.nonsingInvUnit m0 (isUnit_iff_ne_zero.mpr hdet)
    have h1 := hG g0 f hf
    have hu : detPow k N g0 lam.detShift ≠ 0 := Units.ne_zero _
    rw [sqAct, Submodule.smul_mem_iff M hu] at h1
    have e1 : MvPolynomial.map (MvPolynomial.eval y) P = rowAct k (n := N) (m0.transpose) f := by
      simp only [P]
      rw [map_rowAct_eq, MvPolynomial.map_map]
      have : (MvPolynomial.eval y).comp (algebraMap k S) = RingHom.id k := by
        ext a; simp [S]
      rw [this, MvPolynomial.map_id, Matrix.transpose_map, hm0]
    rw [e1]
    exact h1
  let ψ : S →+* A := MvPolynomial.eval₂Hom (algebraMap k A) fun v => (g : Matrix (Fin N) (Fin N) A) v.1 v.2
  have e2 : MvPolynomial.map ψ P =
      rowAct A (n := N) (g : Matrix (Fin N) (Fin N) A).transpose (MvPolynomial.map (algebraMap k A) f) := by
    simp only [P]
    rw [map_rowAct_eq, MvPolynomial.map_map]
    have h3 : ψ.comp (algebraMap k S) = algebraMap k A := by
      ext a; simp [ψ, S]
    have h4 : (Y.transpose).map ψ = (g : Matrix (Fin N) (Fin N) A).transpose := by
      ext i j
      simp only [Y, ψ, Matrix.mvPolynomialX, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply, MvPolynomial.coe_eval₂Hom]
      exact MvPolynomial.eval₂_X _ _ _
    rw [h3, h4]
  have h5 := map_mem_span_map ψ _ P hP
  rw [Set.image_image] at h5
  have h6 : (fun x : MvPolynomial (Fin N × Fin N) k => MvPolynomial.map ψ (MvPolynomial.map (algebraMap k S) x)) =
      ⇑(MvPolynomial.map (σ := Fin N × Fin N) (algebraMap k A)) := by
    have h3 : ψ.comp (algebraMap k S) = algebraMap k A := by
      ext a; simp [ψ, S]
    funext x
    rw [MvPolynomial.map_map, h3]
  rw [h6, e2] at h5
  rw [sqAct]
  exact Submodule.smul_mem _ _ h5

end GlobalTheory.AlcZero

namespace GlobalTheory.AlcZero

theorem hw_mem_of_lt_charZero (k : Type) [Field k] [CharZero k] (N : ℕ) (ν : Fin N → ℕ) (hν : Antitone ν)
    (hlast : ∀ h : 0 < N, ν ⟨N - 1, by omega⟩ = 0)
    (M M' : Submodule k (MvPolynomial (Fin N × Fin N) k)) (hM : Good M) (hM' : Good M') (hlt : M < M')
    (hle : M' ≤ dualWeyl k N N ν) : hw k le_rfl ν ∈ M' ∧ hw k le_rfl ν ∉ M := by
  have dom := GlobalTheory.T.rowDeg_dominated_of_mem_dualWeylModule k N ν
  obtain ⟨μ, v, hμ, hvM', hvM, hvw, hraise⟩ := GlobalTheory.T.exists_dominant_highest_vector_of_lt_stable k N M M' hM hM' hlt
    ⟨∑ a, ν a, fun f hf m hm => ((dom f (hle hf) m hm).2).le⟩
  have hv0 : v ≠ 0 := fun h => hvM (h ▸ zero_mem M)
  have hwt := GlobalTheory.T.rowPolarizationOperators_action_on_rowWeight k N N μ v hvw
  have hrel := (GlobalTheory.T.rowPolarizationOperators_relations_divPow_baseChange k N N).1
  have hhw := GlobalTheory.T.trace_glMatrixUnit_pow_highestWeight_mod k _ N (rowE k N N) hrel M (fun a b f hf => hM.1 a b f hf)
    (fun a => (μ a : k)) v hraise (fun a => by rw [hwt.1 a, sub_self]; exact zero_mem M)
  have hval : ∀ j, hcVal k (fun i => (μ i : k)) j = hcVal k (fun i => (ν i : k)) j := by
    intro j
    by_contra hne
    have h1 := hhw j
    have h2 : gel k N N j v = hcVal k (fun i => (ν i : k)) j • v := GlobalTheory.T.traceRowOperatorPower_dualWeyl_field_smul k N ν hν j v (hle hvM')
    change gel k N N j v - _ ∈ M at h1
    rw [h2, ← sub_smul] at h1
    exact hvM ((Submodule.smul_mem_iff M (sub_ne_zero.mpr (Ne.symm hne))).mp h1)
  obtain ⟨m, hm⟩ : v.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (by rwa [Ne, MvPolynomial.support_eq_empty])
  have hmμ : ∀ a, μ a = rowDeg m a := fun a => by
    rw [← hvw (mem_support_iff.mp hm)]; exact (weight_rowW_apply m a)
  have hcond : ∀ h : 0 < N, ν ⟨N - 1, by omega⟩ = 0 ∧ μ ⟨0, h⟩ ≤ ν ⟨0, h⟩ := by
    intro h
    refine ⟨hlast h, ?_⟩
    have hd := (dom v (hle hvM') m hm).1 1
    have hs : (Finset.univ.filter fun a : Fin N => a.val < 1) = {⟨0, h⟩} := by
      ext a; simp [Fin.ext_iff]
    rw [hs, Finset.sum_singleton, Finset.sum_singleton] at hd
    rw [hmμ]; exact hd
  have hμν : μ = ν := eq_of_hcVal_eq_charZero k N ν μ hν hμ hcond hval
  subst hμν
  obtain ⟨c, hc⟩ := GlobalTheory.T.dualWeyl_highestWeight_space_line_field k N μ hν v (hle hvM') hvw
  have hc0 : c ≠ 0 := by rintro rfl; exact hv0 (by rw [hc, zero_smul])
  refine ⟨?_, fun h => hvM (hc ▸ M.smul_mem c h)⟩
  have : hw k le_rfl μ = c⁻¹ • v := by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [this]; exact M'.smul_mem _ hvM'

theorem nablaSq_simple_charZero : ∀ (k : Type) [Field k] [CharZero k] (N : ℕ) (lam : DomWeight N)
    (M : Submodule k (MvPolynomial (Fin N × Fin N) k)),
    M ≤ nablaSq k N lam → (∀ g : GL (Fin N) k, ∀ f ∈ M, sqAct k N lam g f ∈ M) →
      M = ⊥ ∨ M = nablaSq k N lam := by
  intro k _ _ N lam M hM hG
  haveI : Infinite k := Infinite.of_injective _ Nat.cast_injective
  have hN := factNatW N lam
  by_contra hc
  push_neg at hc
  have hMg : Good M := good_of_isGLSubmodule k N lam M (isGLSubmodule_of_stable k N lam M hG)
  have key := hw_mem_of_lt_charZero k N lam.natW hN.1 hN.2.2
  have h1 := (key ⊥ M (good_top_bot k N N).2 hMg (bot_lt_iff_ne_bot.2 hc.1) hM).1
  have h2 := (key M (nablaSq k N lam) hMg (good_nablaSq k N lam) (lt_of_le_of_ne hM hc.2) le_rfl).2
  exact h2 h1

end GlobalTheory.AlcZero
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

theorem _root_.GlobalTheory.T.affine_eigenvalue_eq_one_of_boxSum_ne_zero : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K] (P : HeightOneSpectrum (𝓞 E)), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → E) → K) (N : ℕ), FunBdd P N f → ∀ (T : (ι → E) ≃ₗ[E] (ι → E)) (b : ι → E) (χ : K), (∀ t, f (T t + b) = χ * f t) → boxSum P N N f ≠ 0 → χ = 1 := by
  first | exact @GlobalTheory.Proof.affine_eigenvalue_eq_one_of_boxSum_ne_zero.eigen_eq_one | exact GlobalTheory.Proof.affine_eigenvalue_eq_one_of_boxSum_ne_zero.eigen_eq_one | (intros; apply GlobalTheory.Proof.affine_eigenvalue_eq_one_of_boxSum_ne_zero.eigen_eq_one <;> assumption)
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.local_embedding_weil_action_finite_extension : ∀ (E K Ω : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra E K] [IsScalarTower E K Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (ι : Ω →ₐ[E] Kbar w), IsLocEmb A w ι → ∀ L : IntermediateField (w.adicCompletion E) (Kbar w), FiniteDimensional (w.adicCompletion E) L → (∀ (σ : Weil h) (g : GalLoc w), Lifts ι g σ → ((∀ z ∈ L, g z = z) ↔ ∀ x : K, (σ : G E Ω) (algebraMap K Ω x) = algebraMap K Ω x)) → L = IntermediateField.adjoin (w.adicCompletion E) (Set.range fun x : K => ι (algebraMap K Ω x)) := by
  first | exact @GlobalTheory.LocDec.eq_adjoin_of_fixing_iff_weil | exact GlobalTheory.LocDec.eq_adjoin_of_fixing_iff_weil | (intros; apply GlobalTheory.LocDec.eq_adjoin_of_fixing_iff_weil <;> assumption)
end

section

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

theorem _root_.GlobalTheory.T.adelicForm_values_near_point_spec : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (ι : Type) [Fintype ι] (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (k : Type) [Field k] (p : GA σ J → Pr (𝓞 E) (Fin n → E) k), v ∉ bad → PMap S v hv p → ∀ g ∈ AdFun S emb, (∀ x η : GA σ J, AtV v η → valAt v p g x (p (x * η)) = g (x * η)) ∧ (∀ x η : GA σ J, AtV v η → valAt v p g (x * η) = valAt v p g x) ∧ ∀ (a : ℤ) (δ x : GA σ J) (q : Pr (𝓞 E) (Fin n → E) k), (a : k) ≠ 0 → IsDia S v hv a δ → valAt v p g x (q.dil (a : k)) = valAt v p (fun y => g (y * δ)) x q := by
  first | exact @GlobalTheory.LevelHecke.ValAt.valAt_spec | exact GlobalTheory.LevelHecke.ValAt.valAt_spec | (intros; apply GlobalTheory.LevelHecke.ValAt.valAt_spec <;> assumption)
end

section

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

theorem _root_.GlobalTheory.T.upwardOperator_mem_adelicForms : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (ι : Type) [Fintype ι] (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (k : Type) [Field k] (p : GA σ J → Pr (𝓞 E) (Fin n → E) k), v ∉ bad → PMap S v hv p → ∀ (res : 𝓞 E →+* k) (t : 𝓞 E) (lam : ι → DomWeight n), ∀ g ∈ AdForms S emb lam, upAd res t v p g ∈ AdForms S emb lam := by
  first | exact @GlobalTheory.LevelHecke.UpKeeps.upAd_mem_adForms | exact GlobalTheory.LevelHecke.UpKeeps.upAd_mem_adForms | (intros; apply GlobalTheory.LevelHecke.UpKeeps.upAd_mem_adForms <;> assumption)
end

section

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

theorem _root_.GlobalTheory.T.finsum_pairsAbove_eq_affineHyperplane : ∀ (R V k W M : Type) [CommRing R] [AddCommGroup V] [Module R V] [Field k] [AddCommGroup W] [Module k W] [AddCommMonoid M] (res : R →+* k) (t : R) (p : Pr R V k) (π : V → W) (φ : Module.Dual k W) (q : W → Pr R V k) (Φ : Pr R V k → M), Function.Surjective res → res t = 0 → (∀ x : V, t • x = 0 → x = 0) → (∀ s x, res s ≠ 0 → s • x ∈ p.L → x ∈ p.L) → Red res t p.L π → (∀ x ∈ p.L, p.f x = φ (π x)) → (∀ w, φ w = 1 → (q w).Ok res ∧ (q w).IsKer p.L ∧ ∃ e, (q w).f e = 1 ∧ π (t • e) = w) → ∑ᶠ q' ∈ {q' | Pr.Inc res t p q'}, Φ q' = ∑ᶠ w ∈ {w | φ w = 1}, Φ (q w) := by
  first | exact @GlobalTheory.LevelHecke.AboveSum.finsum_above | exact GlobalTheory.LevelHecke.AboveSum.finsum_above | (intros; apply GlobalTheory.LevelHecke.AboveSum.finsum_above <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.unitary_group_points_equiv_of_change_of_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], ∀ (M : ℕ) (J J' : Matrix (Fin M) (Fin M) E) (P : GL (Fin M) E), J' = Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin M) (Fin M) E) * J * (P : Matrix (Fin M) (Fin M) E) → (∃! e : HA R σ J ≃* HA R σ J', ∀ g, FrameRelR R σ J J' (P : Matrix (Fin M) (Fin M) E) g (e g)) ∧ ∀ e : HA R σ J ≃* HA R σ J', (∀ g, FrameRelR R σ J J' (P : Matrix (Fin M) (Fin M) E) g (e g)) → Continuous e ∧ Continuous e.symm := by
  first | exact @GlobalTheory.GaugeFrameBasis.frame_basis | exact GlobalTheory.GaugeFrameBasis.frame_basis | (intros; apply GlobalTheory.GaugeFrameBasis.frame_basis <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.existsUnique_stdHermitianFibreProduct_of_rank_ge_three : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (β : F), 3 ≤ M → IsHermND σ J → β ≠ 0 → ∃! ν, IsStdX s σ J β ν := by
  first | exact @GlobalTheory.GaugeEx.existsUnique_isStdX | exact GlobalTheory.GaugeEx.existsUnique_isStdX | (intros; apply GlobalTheory.GaugeEx.existsUnique_isStdX <;> assumption)
end
