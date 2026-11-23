module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle090
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle055
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle063
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle091
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle073
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Formalism.LocalToGlobal.Columns.StdLatUnimodular
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle093
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
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP

@[expose] public section

section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW

theorem span_tau_commutant : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W) (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), Agrees a b P → ∀ (τ : L →+* ℂ) (v : ι → ℂ), v ≠ 0 → ∀ w : ι → ℂ, w ∈ Submodule.span ℂ {x | ∃ (B : GL (Fin n) ℂ) (M : Matrix ι ι ℂ), (∀ A : GL (Fin n) ℂ, M * evM P (evPt τ A) = evM P (evPt τ A) * M) ∧ x = evM P (evPt τ B) *ᵥ (M *ᵥ v)} := by
  intro L _ _ _ n a ι _ _ b P hA τ v hv w
  classical
  have hS := GlobalTheory.T.span_rationalPoint_orbit_algebraicWeight L n a ι b P hA v hv w
  refine Submodule.span_mono ?_ hS
  rintro x ⟨γ₀, hγ, rfl⟩
  obtain ⟨_, hmul⟩ := GlobalTheory.T.algebraicWeight_polyMatrix_multiplicative L n a ι b P hA
  set B : GL (Fin n) ℂ := Matrix.GeneralLinearGroup.map τ γ₀ with hBdef
  have hBv : B.val = γ₀.val.map τ := rfl
  set R : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ := fun σ =>
    if σ = τ ∨ σ = ComplexEmbedding.conjugate τ then 1 else ratPt γ₀.val σ with hRdef
  have hU := isUPt_ratPt γ₀ hγ
  have hR : IsUPt R := by
    intro σ
    by_cases h : σ = τ ∨ σ = ComplexEmbedding.conjugate τ
    · have h' : ComplexEmbedding.conjugate σ = τ ∨ ComplexEmbedding.conjugate σ = ComplexEmbedding.conjugate τ := by
        rcases h with h | h
        · right; rw [h]
        · left; rw [h, conj_conj]
      simp only [R, if_pos h, if_pos h', Matrix.transpose_one, mul_one]
    · have h' : ¬ (ComplexEmbedding.conjugate σ = τ ∨ ComplexEmbedding.conjugate σ = ComplexEmbedding.conjugate τ) := by
        rintro (h' | h')
        · exact h (Or.inr (by rw [← h', conj_conj]))
        · exact h (Or.inl (by simpa [conj_conj] using congrArg ComplexEmbedding.conjugate h'))
      simp only [R, if_neg h, if_neg h']
      exact hU σ
  have hinv : ((B⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = (ratPt γ₀.val (ComplexEmbedding.conjugate τ))ᵀ := by
    apply Units.inv_eq_of_mul_eq_one_right
    exact hU τ
  have hdec : ratPt γ₀.val = fun σ => tauPt τ B σ * R σ := by
    funext σ
    have hne := conjugate_ne_self τ
    by_cases h1 : σ = τ
    · subst h1
      simp [tauPt, R, hBv, ratPt]
    · by_cases h2 : σ = ComplexEmbedding.conjugate τ
      · subst h2
        simp only [tauPt, if_neg h1, if_true, R, or_true, mul_one]
        rw [hinv, Matrix.transpose_transpose]
      · simp [tauPt, R, h1, h2]
  have hcomm : ∀ A : GL (Fin n) ℂ, (fun σ => tauPt τ A σ * R σ) = (fun σ => R σ * tauPt τ A σ) := by
    intro A
    funext σ
    by_cases h : σ = τ ∨ σ = ComplexEmbedding.conjugate τ
    · simp [R, h]
    · have h1 : σ ≠ τ := fun e => h (Or.inl e)
      have h2 : σ ≠ ComplexEmbedding.conjugate τ := fun e => h (Or.inr e)
      simp [tauPt, h1, h2]
  refine ⟨B, evM P (upt R), ?_, ?_⟩
  · intro A
    rw [evPt_eq_upt, ← hmul _ _ hR (isUPt_tauPt τ A), ← hmul _ _ (isUPt_tauPt τ A) hR, hcomm A]
  · rw [hdec, hmul _ _ (isUPt_tauPt τ B) hR, evPt_eq_upt, Matrix.mulVec_mulVec]

end GlobalTheory.AlgWtHW
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.ProjBlowup

variable {R : Type} [CommRing R] {N : ℕ} {X : Scheme.{0}}

theorem exists_formOn_eq (a : Fin (N + 1)) (s : Γ(PSpace R N, chart R N a)) :
    ∃ (d : ℕ) (F : MvPolynomial (Fin (N + 1)) R) (hF : F.IsHomogeneous d),
      formOn (chart R N a) a le_rfl d F hF = s := by
  obtain ⟨p, rfl⟩ := (chartAlgEquiv R N a).surjective s
  obtain ⟨x, rfl⟩ := (polyEquivAway R N a).symm.surjective p
  obtain ⟨n, f, hf, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ (X_mem R N a) x
  refine ⟨n, f, by simpa using hf, ?_⟩
  rw [← chartAlgEquiv_dehom, ← awayToPoly_mk R N a n f hf]
  rfl

def pullForm (φ : X ⟶ PSpace R N) (W : X.Opens) (i : Fin (N + 1)) (hi : W ≤ φ ⁻¹ᵁ chart R N i)
    (d : ℕ) (F : MvPolynomial (Fin (N + 1)) R) (hF : F.IsHomogeneous d) : Γ(X, W) :=
  (φ.appLE (chart R N i) W hi).hom (formOn (chart R N i) i le_rfl d F hF)

section

variable {φ : X ⟶ PSpace R N} {W V : X.Opens} {i j : Fin (N + 1)} {hi : W ≤ φ ⁻¹ᵁ chart R N i}
  {d : ℕ} {F : MvPolynomial (Fin (N + 1)) R}

theorem resG_pullForm (h : V ≤ W) (hF : F.IsHomogeneous d) :
    resG X h (pullForm φ W i hi d F hF) = pullForm φ V i (h.trans hi) d F hF :=
  resG_appLE φ hi h _

theorem pullForm_zero : pullForm φ W i hi d 0 (isHomogeneous_zero _ R d) = 0 := by
  rw [pullForm, formOn_zero, map_zero]

theorem pullForm_eq_pow_mul (hj : W ≤ φ ⁻¹ᵁ chart R N j) (hF : F.IsHomogeneous d) :
    pullForm φ W i hi d F hF = pullRatio φ W i hi j ^ d * pullForm φ W j hj d F hF := by
  have hW : W ≤ φ ⁻¹ᵁ (chart R N i ⊓ chart R N j) := le_inf hi hj
  have := congrArg (φ.appLE _ W hW).hom
    (formOn_eq_ratioOn_pow_mul (U := chart R N i ⊓ chart R N j) (hi := inf_le_left) inf_le_right hF)
  rw [map_mul, map_pow, appLE_ratioOn, ← resG_formOn (hi := le_rfl) inf_le_left,
    ← resG_formOn (hi := le_rfl) inf_le_right, appLE_resG, appLE_resG] at this
  exact this

theorem pullForm_X_pow_mul (n : ℕ) (hF : F.IsHomogeneous d) {e : ℕ}
    (hG : (MvPolynomial.X j ^ n * F).IsHomogeneous e) :
    pullForm φ W i hi e _ hG = pullRatio φ W i hi j ^ n * pullForm φ W i hi d F hF := by
  rw [pullForm, pullForm, pullRatio, formOn_eq_aeval, formOn_eq_aeval, map_mul, map_pow, aeval_X, map_mul,
    map_pow]

end

def pullO (φ : X ⟶ PSpace R N) (e : ℕ) : LB X where
  ι := Fin (N + 1)
  U i := φ ⁻¹ᵁ chart R N i
  g i j := (Units.mkOfMulEqOne (pullRatio φ _ i inf_le_left j) (pullRatio φ _ j inf_le_right i)
    (pullRatio_mul_pullRatio.trans pullRatio_self)) ^ e

def pullFormSec (φ : X ⟶ PSpace R N) {e : ℕ} (F : MvPolynomial (Fin (N + 1)) R) (hF : F.IsHomogeneous e) :
    (pullO φ e).Sec where
  f i := pullForm φ _ i le_rfl e F hF
  compat i j := by
    refine (resG_pullForm inf_le_left hF).trans ((pullForm_eq_pow_mul (j := j) inf_le_right hF).trans ?_)
    exact congrArg₂ (· * ·) (Units.val_pow_eq_pow_val (Units.mkOfMulEqOne _ _ _) e).symm
      (resG_pullForm inf_le_right hF).symm

abbrev affChart (φ : X ⟶ PSpace R N) [IsClosedImmersion φ] (i : Fin (N + 1)) : X.affineOpens :=
  ⟨φ ⁻¹ᵁ chart R N i, (isAffineOpen_chart R N i).preimage φ⟩

theorem exists_pow_mul_pullForm_mem (φ : X ⟶ PSpace R N) [IsClosedImmersion φ] (J : X.IdealSheafData)
    {a : Fin (N + 1)} {d : ℕ} {F : MvPolynomial (Fin (N + 1)) R} (hF : F.IsHomogeneous d)
    (h : pullForm φ _ a le_rfl d F hF ∈ J.ideal (affChart φ a)) (b : Fin (N + 1)) :
    ∃ n, pullRatio φ _ b le_rfl a ^ n * pullForm φ _ b le_rfl d F hF ∈ J.ideal (affChart φ b) := by
  let r : Γ(X, (affChart φ b).1) := pullRatio φ _ b le_rfl a
  have ha : X.basicOpen r ≤ φ ⁻¹ᵁ chart R N a := basicOpen_pullRatio.le.trans inf_le_right
  have h1 : resG X ha (pullForm φ _ a le_rfl d F hF) ∈ J.ideal (X.affineBasicOpen r) :=
    J.ideal_le_comap_ideal (U := X.affineBasicOpen r) (V := affChart φ a) ha h
  have h2 : resG X (X.basicOpen_le r) (pullForm φ _ b le_rfl d F hF) ∈ J.ideal (X.affineBasicOpen r) := by
    rw [resG_pullForm] at h1 ⊢
    rw [pullForm_eq_pow_mul (j := a) ha]
    exact Ideal.mul_mem_left _ _ h1
  rw [← J.map_ideal_basicOpen] at h2
  have inst := (affChart φ b).2.isLocalization_basicOpen r
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff (.powers r)
    Γ(X, X.basicOpen r) _ _).1 h2
  exact ⟨n, hn⟩

theorem exists_form_of_mem (φ : X ⟶ PSpace R N) [IsClosedImmersion φ] (J : X.IdealSheafData)
    (a : Fin (N + 1)) (g : Γ(X, (affChart φ a).1)) (hg : g ∈ J.ideal (affChart φ a)) :
    ∃ e₀, ∀ e, e₀ ≤ e → ∃ (F : MvPolynomial (Fin (N + 1)) R) (hF : F.IsHomogeneous e),
      pullForm φ _ a le_rfl e F hF = g ∧ ∀ b, pullForm φ _ b le_rfl e F hF ∈ J.ideal (affChart φ b) := by
  obtain ⟨s, rfl⟩ := φ.app_surjective _ (isAffineOpen_chart R N a) g
  obtain ⟨d, F, hF, rfl⟩ := exists_formOn_eq a s
  have e₁ : pullForm φ _ a le_rfl d F hF = (φ.app (chart R N a)).hom (formOn (chart R N a) a le_rfl d F hF) := by
    rw [pullForm, Scheme.Hom.app_eq_appLE]
  choose n hn using exists_pow_mul_pullForm_mem φ J hF (e₁ ▸ hg)
  refine ⟨Finset.univ.sup n + d, fun e he => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (le_of_add_le_right he)
  refine ⟨MvPolynomial.X a ^ k * F, (isHomogeneous_X_pow a k).mul hF, ?_, fun b => ?_⟩
  · rw [pullForm_X_pow_mul k hF, pullRatio_self, one_pow, one_mul]
    exact e₁
  · obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le'
      ((Finset.le_sup (f := n) (Finset.mem_univ b)).trans (Nat.le_of_add_le_add_right he))
    rw [pullForm_X_pow_mul _ hF, pow_add, mul_assoc]
    exact Ideal.mul_mem_left _ _ (hn b)

theorem exists_generates (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R)
    (hs : IsProjOver s) (J : X.IdealSheafData) :
    ∃ (L : LB X) (m : ℕ) (σ : Fin (m + 1) → L.Sec), Generates J σ := by
  classical
  obtain ⟨N, φ, _, -⟩ := hs
  have fg : ∀ a, (J.ideal (affChart φ a)).FG := fun a => by
    have : IsNoetherianRing Γ(PSpace R N, chart R N a) :=
      isNoetherianRing_of_ringEquiv _ (chartAlgEquiv R N a).toRingEquiv
    have : IsNoetherianRing Γ(X, (affChart φ a).1) :=
      isNoetherianRing_of_surjective _ _ _ (φ.app_surjective _ (isAffineOpen_chart R N a))
    exact IsNoetherian.noetherian _
  choose S hS using fg
  choose e₀ he₀ using fun p : Σ a, S a =>
    exists_form_of_mem φ J p.1 p.2.1 (hS p.1 ▸ Ideal.subset_span p.2.2)
  choose F hF hFa hFb using fun p => he₀ p (Finset.univ.sup e₀) (Finset.le_sup (Finset.mem_univ p))
  let q := (Fintype.equivFinOfCardEq (Fintype.card_option (α := Σ a, S a))).symm
  let τ : Option (Σ a, S a) → (pullO φ (Finset.univ.sup e₀)).Sec := fun o =>
    o.elim (pullFormSec φ 0 (isHomogeneous_zero _ R _)) fun p => pullFormSec φ (F p) (hF p)
  refine ⟨_, _, fun j => τ (q j), (isCoordFamily_pullRatio φ).cover, fun k V h => ?_⟩
  have key : J.ideal (affChart φ k) = Ideal.span (Set.range fun j => (τ (q j)).f k) := by
    refine le_antisymm ?_ (Ideal.span_le.2 ?_)
    · rw [← hS k]
      refine Ideal.span_mono fun g hg => ⟨q.symm (some ⟨k, g, hg⟩), ?_⟩
      simp only [q.apply_symm_apply]
      exact hFa ⟨k, g, hg⟩
    · rintro _ ⟨j, rfl⟩
      dsimp only
      cases q j with
      | none =>
        exact (congrArg (· ∈ J.ideal (affChart φ k)) (pullForm_zero (φ := φ) (hi := le_rfl))).mpr (zero_mem _)
      | some p => exact hFb p k
  rw [← J.map_ideal (V := affChart φ k) h, key]
  erw [Ideal.map_span, ← Set.range_comp]
  rfl

end GlobalTheory.ProjBlowup
end
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.Polar

theorem qR_scalar {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (R : Type) [CommRing R] [Algebra F R] {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (r : R)
    (z : Fin M → R ⊗[F] E) :
    qR R σ J (algebraMap R (R ⊗[F] E) r • z) = r * r * qR R σ J z := by
  have hs : sigR R σ (algebraMap R (R ⊗[F] E) r) = algebraMap R (R ⊗[F] E) r := by
    simp [sigR, Algebra.TensorProduct.algebraMap_apply]
  have h : hR R σ J (algebraMap R (R ⊗[F] E) r • z) (algebraMap R (R ⊗[F] E) r • z)
      = (r * r) • hR R σ J z z := by
    rw [Algebra.smul_def (r * r), map_mul]
    simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, hs, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  simp only [qR, h, map_smul, smul_eq_mul]
  ring

theorem lrAct_scalar {S : Type} [CommRing S] {n M : ℕ} (c : S) (X : Fin n → Fin M → S) :
    lrAct (c • (1 : Matrix (Fin M) (Fin M) S)) 1 X = c • X := by
  funext a i
  simp [lrAct, Matrix.smul_mulVec, Matrix.one_apply]

theorem polar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (lam : Measure (R ⊗[F] E)) (ν : Measure R) (β : R) (m : Measure (Fin 1 → Fin M → R ⊗[F] E)), lam.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsUnit β → FibAt R σ J (tupMeas lam 1 M) ν β m → ∀ (W : Set R) (ρ : R → R), MeasurableSet W → (∀ b ∈ W, IsUnit (ρ b) ∧ ρ b * ρ b * β = b) → ∀ f : (Fin 1 → Fin M → R ⊗[F] E) → ℝ≥0∞, Measurable f → (∀ X, qR R σ J (X 0) ∉ W → f X = 0) → ∫⁻ X, f X ∂(tupMeas lam 1 M) = ∫⁻ b in W, ((modu (R ⊗[F] E) (algebraMap R (R ⊗[F] E) (ρ b) ^ M) * (modu R (ρ b * ρ b))⁻¹ : ℝ≥0) : ℝ≥0∞) * ∫⁻ X, f (algebraMap R (R ⊗[F] E) (ρ b) • X) ∂m ∂ν := by
  intro F E _ _ _ _ _ σ R _ _ _ _ _ _ _ _ _ hN M J lam ν β m hlam hν hβ hfib W ρ hW hρ f hf hf0
  obtain ⟨fib, hfam, hm⟩ := id hfib
  have h2 := hfam.2.1 f hf
  rw [Measure.restrict_univ] at h2
  rw [h2, ← lintegral_indicator hW]
  refine lintegral_congr fun b => ?_
  by_cases hb : b ∈ W
  · rw [Set.indicator_of_mem hb]
    obtain ⟨hr, hrb⟩ := hρ b hb
    set c : R ⊗[F] E := algebraMap R (R ⊗[F] E) (ρ b) with hc
    have hdet : (c • (1 : Matrix (Fin M) (Fin M) (R ⊗[F] E))).det = c ^ M := by
      simp
    have hcu : IsUnit c := hr.map _
    have h1 := GlobalTheory.GaugeEx.fibAt_similitude F E σ R hN M J J lam ν β (ρ b * ρ b) m
      (c • (1 : Matrix (Fin M) (Fin M) (R ⊗[F] E))) hlam hν (by rw [hdet]; exact hcu.pow M)
      (hr.mul hr) (fun z => by
        rw [Matrix.smul_mulVec, Matrix.one_mulVec]; exact qR_scalar σ R J (ρ b) z) hfib
    rw [hrb, hdet] at h1
    have hbu : IsUnit b := hrb ▸ (hr.mul hr).mul hβ
    have h3 := (GlobalTheory.GaugeEx.FibBasic.fibAt_basic F E σ R hN M J _ ν b _ hν hbu h1).2.2 (fib b)
      ⟨fib, hfam, rfl⟩
    have hl : lrAct (n := 1) (c • (1 : Matrix (Fin M) (Fin M) (R ⊗[F] E))) 1 = fun X => c • X :=
      funext fun X => lrAct_scalar c X
    have hcont : Continuous fun X : Fin 1 → Fin M → R ⊗[F] E => c • X := continuous_const_smul c
    rw [h3, hl, lintegral_smul_measure, lintegral_map hf hcont.measurable]
    rfl
  · rw [Set.indicator_of_notMem hb]
    have h1 := hfam.1 b
    have hae : f =ᵐ[fib b] 0 := by
      refine measure_mono_null (fun X hX => ?_) h1
      intro hX'
      apply hX
      apply hf0
      have : qR R σ J (X 0) = b := hX'.1
      rw [this]; exact hb
    rw [lintegral_congr_ae hae]
    simp

end GlobalTheory.GaugeEx.Polar
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem ax_sen_tate : ∀ (l : ℕ) [Fact l.Prime], ∀ (H : Subgroup (GQ l)) (x : ℂ_[l]),
    (∀ g ∈ H, Per.σC g x = x) →
      x ∈ closure ((fun y : Om l => (y : ℂ_[l])) '' {y | ∀ g ∈ H, g y = y}) := by
  intro l _ H x hx
  obtain ⟨c, hc, hax⟩ := GlobalTheory.T.bounded_orbit_has_nearby_fixed_point l
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hd : DenseRange (fun y : Om l => (y : ℂ_[l])) := by
    intro z
    induction z using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_closure
    | ih a => exact subset_closure ⟨a, rfl⟩
  have hδ : 0 < ε / (2 * c + 2) := by positivity
  obtain ⟨a, ha⟩ := hd.exists_dist_lt x hδ
  set δ := ε / (2 * c + 2) with hδdef
  have hmul : δ * (2 * c + 2) = ε := by
    rw [hδdef]; field_simp
  rw [dist_eq_norm] at ha
  have hsub : ∀ u v : Om l, ‖u - v‖ = ‖(u : ℂ_[l]) - (v : ℂ_[l])‖ := by
    intro u v
    rw [← PadicComplex.norm_extends, PadicComplex.coe_eq, PadicComplex.coe_eq,
      PadicComplex.coe_eq, map_sub]
  obtain ⟨y, hy, hxy⟩ := hax H a (2 * δ) (by
    intro g hg
    have h1 : ((g a : Om l) : ℂ_[l]) - (a : ℂ_[l])
        = (x - (a : ℂ_[l])) - Per.σC g (x - (a : ℂ_[l])) := by
      rw [map_sub, hx g hg, GlobalTheory.RingBasics.σC_coe]; ring
    rw [hsub, h1]
    have h2 := norm_sub_le (x - (a : ℂ_[l])) (Per.σC g (x - (a : ℂ_[l])))
    rw [GlobalTheory.RingBasics.norm_σC] at h2
    linarith)
  refine ⟨(y : ℂ_[l]), ⟨y, hy, rfl⟩, ?_⟩
  rw [hsub] at hxy
  have h3 := norm_add_le (x - (a : ℂ_[l])) ((a : ℂ_[l]) - (y : ℂ_[l]))
  rw [sub_add_sub_cancel] at h3
  rw [dist_eq_norm]
  nlinarith

end GlobalTheory.MemLoc
end

section

noncomputable section

namespace GlobalTheory.InertExchange

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.Col

theorem exists_smul_mem_of_fg {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (S : Submonoid R) (A B : Submodule R M) (hA : A.FG)
    (h : ∀ x ∈ A, ∃ s ∈ S, s • x ∈ B) : ∃ s ∈ S, ∀ x ∈ A, s • x ∈ B := by
  classical
  obtain ⟨G, rfl⟩ := hA
  have key : ∀ G' : Finset M, (G' : Set M) ⊆ G → ∃ s ∈ S, ∀ x ∈ Submodule.span R (G' : Set M), s • x ∈ B := by
    intro G'
    induction G' using Finset.induction_on with
    | empty => exact fun _ => ⟨1, S.one_mem, fun x hx => by
        simp only [Finset.coe_empty, Submodule.span_empty, Submodule.mem_bot] at hx
        simp [hx]⟩
    | insert a G' _ ih =>
      intro hsub
      simp only [Finset.coe_insert, Set.insert_subset_iff] at hsub
      obtain ⟨t, ht, hta⟩ := h a (Submodule.subset_span hsub.1)
      obtain ⟨s, hs, hsG⟩ := ih hsub.2
      refine ⟨t * s, S.mul_mem ht hs, fun x hx => ?_⟩
      rw [Finset.coe_insert, Submodule.mem_span_insert] at hx
      obtain ⟨r, y, hy, rfl⟩ := hx
      have e : (t * s) • (r • a + y) = (r * s) • (t • a) + t • (s • y) := by
        simp only [smul_add, smul_smul, mul_comm, mul_assoc, mul_left_comm]
      rw [e]
      exact B.add_mem (B.smul_mem _ hta) (B.smul_mem _ (hsG y hy))
  exact key G subset_rfl

private theorem infinite_places (E : Type) [Field E] [NumberField E] :
    Infinite (HeightOneSpectrum (𝓞 E)) := by
  have : Infinite (HeightOneSpectrum (𝓞 ℚ)) :=
    Infinite.of_surjective _ (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).surjective
  refine Infinite.of_surjective (fun w : HeightOneSpectrum (𝓞 E) => w.under (𝓞 ℚ)) fun v => ?_
  have := v.isMaximal
  obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩,
    HeightOneSpectrum.ext hl.over.symm⟩

theorem exists_smul_mem_lattice {E : Type} [Field E] [NumberField E] {n : ℕ}
    (B : Submodule (𝓞 E) (Sp E n)) (hB : Submodule.IsFullLattice E B) (x : Sp E n) :
    ∃ r ∈ nonZeroDivisors (𝓞 E), r • x ∈ B :=
  _root_.GlobalTheory.SmulMemOfIsLattice.exists_smul_mem_of_isLattice B hB x

theorem exists_pow_smul_le_of_localization_eq {E : Type} [Field E] [NumberField E] {n : ℕ}
    (P : HeightOneSpectrum (𝓞 E)) (A B : Submodule (𝓞 E) (Sp E n)) (hA : A.FG)
    (hB : Submodule.IsLattice E B)
    (h : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → localization₂ Q.asIdeal A = localization₂ Q.asIdeal B) :
    ∃ k : ℕ, P.asIdeal ^ k • A ≤ B := by
  set I : Ideal (𝓞 E) := B.colon (A : Set (Sp E n)) with hIdef
  have hI0 : I ≠ ⊥ := by
    letI := infinite_places E
    obtain ⟨Q, hQ⟩ := exists_ne P
    obtain ⟨s, hs, hsA⟩ := exists_smul_mem_of_fg Q.asIdeal.primeCompl A B hA (fun x hx => by
      have hxA : x ∈ localization₂ Q.asIdeal A := ⟨1, Q.asIdeal.primeCompl.one_mem, by simpa using hx⟩
      rw [h Q hQ] at hxA
      exact hxA)
    intro hI
    have hsI : s ∈ I := Submodule.mem_colon.2 hsA
    rw [hI, Ideal.mem_bot] at hsI
    exact hs (hsI ▸ Q.asIdeal.zero_mem)
  have hIQ : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → ¬ I ≤ Q.asIdeal := by
    intro Q hQ hle
    obtain ⟨s, hs, hsA⟩ := exists_smul_mem_of_fg Q.asIdeal.primeCompl A B hA (fun x hx => by
      have hxA : x ∈ localization₂ Q.asIdeal A := ⟨1, Q.asIdeal.primeCompl.one_mem, by simpa using hx⟩
      rw [h Q hQ] at hxA
      exact hxA)
    exact hs (hle (Submodule.mem_colon.2 hsA))
  have hrad : P.asIdeal ≤ I.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro J ⟨hIJ, hJ⟩
    by_cases hJ0 : J = ⊥
    · exact absurd (le_bot_iff.1 (hJ0 ▸ hIJ)) hI0
    · let Q : HeightOneSpectrum (𝓞 E) := ⟨J, hJ, hJ0⟩
      by_cases hQ : Q = P
      · have : Q.asIdeal = P.asIdeal := by rw [hQ]
        exact le_of_eq this.symm
      · exact absurd hIJ (hIQ Q hQ)
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  exact ⟨k, Submodule.smul_le.2 fun r hr x hx => Submodule.mem_colon.1 (hk hr) x hx⟩

theorem exists_pow_smul_le_of_locP_eq :
    ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E))
      (A B : Submodule (𝓞 E) (Sp E n)), Submodule.IsLattice E A → Submodule.IsLattice E B →
      (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → localization₂ Q.asIdeal A = localization₂ Q.asIdeal B) →
      ∃ k : ℕ, P.asIdeal ^ k • A ≤ B ∧ P.asIdeal ^ k • B ≤ A := by
  intro E _ _ _ n P A B hA hB h
  obtain ⟨k₁, h₁⟩ := exists_pow_smul_le_of_localization_eq P A B hA.fg hB h
  obtain ⟨k₂, h₂⟩ := exists_pow_smul_le_of_localization_eq P B A hB.fg hA (fun Q hQ => (h Q hQ).symm)
  refine ⟨max k₁ k₂, ?_, ?_⟩
  · exact (Submodule.smul_mono_left (Ideal.pow_le_pow_right (le_max_left k₁ k₂))).trans h₁
  · exact (Submodule.smul_mono_left (Ideal.pow_le_pow_right (le_max_right k₁ k₂))).trans h₂

end GlobalTheory.InertExchange
end
end
