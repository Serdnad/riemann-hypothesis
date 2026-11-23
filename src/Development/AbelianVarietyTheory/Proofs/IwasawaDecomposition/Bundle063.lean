module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle054
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle055
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowerTransvectionMulVecMemSpanWeightVectorsDomin
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle056
public import Formalism.GaloisCohomology.Statement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle160
public import Formalism.LocalRingCardinality.DataCD
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle015
public import Formalism.LocalRingCardinality.DataHost
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle057
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Formalism.LocalToGlobal.Divisibility.Tuples

@[expose] public section

section

open Matrix GlobalTheory.AlgWtHW

namespace GlobalTheory.UnipotentWeights

noncomputable def tGL {n : ℕ} {i j : Fin n} (h : i ≠ j) (c : ℂ) : GL (Fin n) ℂ :=
  ⟨transvection i j c, transvection i j (-c),
    by rw [transvection_mul_transvection_same i j h]; simp,
    by rw [transvection_mul_transvection_same i j h]; simp⟩

theorem diag_mul_transvection {n : ℕ} {i j : Fin n} (h : i ≠ j) (d : Fin n → ℂ) (hd : ∀ l, d l ≠ 0) (s : ℂ) :
    diagonal d * transvection i j s = transvection i j (s * d i / d j) * diagonal d := by
  ext a b
  simp only [transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.add_apply,
    diagonal_mul, mul_diagonal, single_apply, one_apply]
  by_cases ha : i = a <;> by_cases hb : j = b
  · subst ha hb; simp [h]; field_simp [hd j]
  · by_cases hab : a = b <;> simp [ha, hb, hab, mul_comm]
  · subst hb; by_cases hab : a = j
    · subst hab; simp [h]
    · simp [ha, hab]
  · by_cases hab : a = b <;> simp [ha, hb, hab, mul_comm]

theorem poly_coeff_eq (K : ℕ) (x y : ℕ → ℂ) (hxy : ∀ s : ℂ, ∑ k ∈ Finset.range (K + 1), s ^ k * x k =
    ∑ k ∈ Finset.range (K + 1), s ^ k * y k) (k : ℕ) (hk : k ≤ K) : x k = y k := by
  let Q : Polynomial ℂ := ∑ k ∈ Finset.range (K + 1), Polynomial.C (x k - y k) * Polynomial.X ^ k
  have hQ : Q = 0 := by
    apply Polynomial.funext
    intro s
    simp only [Q, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_zero]
    have := hxy s
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at this
    rw [← this]
    refine Finset.sum_congr rfl fun m _ => by ring
  have hc := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p k) hQ
  simp only [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hc
  rw [Finset.sum_eq_single k] at hc
  · simpa [sub_eq_zero] using hc
  · intro m _ hm; simp [Ne.symm hm]
  · intro hk'; exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le hk)) hk'

end GlobalTheory.UnipotentWeights

namespace GlobalTheory.UnipotentWeights

theorem prod_single_zpow {n : ℕ} (d : Fin n → ℂ) (i : Fin n) :
    ∏ l, d l ^ ((Pi.single i (1 : ℤ) : Fin n → ℤ) l) = d i := by
  rw [Finset.prod_eq_single i]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem prod_wt_shift {n : ℕ} (d : Fin n → ℂ) (hd : ∀ l, d l ≠ 0) (i j : Fin n) (μ : Fin n → ℤ) (k : ℕ) :
    ∏ l, d l ^ ((μ + (k : ℤ) • (Pi.single i 1 - Pi.single j 1) : Fin n → ℤ) l) =
      (∏ l, d l ^ μ l) * (d i / d j) ^ k := by
  have hpt : ∀ l, d l ^ ((μ + (k : ℤ) • (Pi.single i 1 - Pi.single j 1) : Fin n → ℤ) l) =
      d l ^ μ l * ((d l ^ ((Pi.single i (1 : ℤ) : Fin n → ℤ) l)) ^ k *
        ((d l ^ ((Pi.single j (1 : ℤ) : Fin n → ℤ) l)) ^ k)⁻¹) := by
    intro l
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [zpow_add₀ (hd l), mul_sub, zpow_sub₀ (hd l), div_eq_mul_inv, ← zpow_natCast, ← zpow_natCast,
      ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm ((Pi.single i (1:ℤ) : Fin n → ℤ) l), mul_comm ((Pi.single j (1:ℤ) : Fin n → ℤ) l)]
  simp_rw [hpt]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_pow,
    Finset.prod_pow, prod_single_zpow, prod_single_zpow, div_pow, div_eq_mul_inv]

end GlobalTheory.UnipotentWeights

namespace GlobalTheory


open GlobalTheory.UnipotentWeights in
theorem transvection_weightVec_expansion :
    ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ →
      ∀ (i j : Fin n), i ≠ j → ∀ (μ : Fin n → ℤ) (v : ι → ℂ), IsWtVec Φ μ v →
        ∃ (K : ℕ) (w : ℕ → ι → ℂ), w 0 = v ∧
          (∀ k : ℕ, IsWtVec Φ (μ + (k : ℤ) • (Pi.single i 1 - Pi.single j 1)) (w k)) ∧
          ∀ (s : ℂ) (B : GL (Fin n) ℂ), B.val = transvection i j s →
            Φ B *ᵥ v = ∑ k ∈ Finset.range (K + 1), s ^ k • w k := by
  intro n ι _ _ Φ hΦ i j hij μ v hv
  obtain ⟨P, hP⟩ := polyRep_transvection_entries_poly n ι Φ hΦ i j hij
  let K : ℕ := Finset.univ.sup (fun ab : ι × ι => (P ab.1 ab.2).natDegree)
  have hK : ∀ a b, (P a b).natDegree < K + 1 := fun a b =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun ab : ι × ι => (P ab.1 ab.2).natDegree) (Finset.mem_univ (a, b)))
  let w : ℕ → ι → ℂ := fun k a => ∑ b, (P a b).coeff k * v b
  have hexp : ∀ (s : ℂ) (B : GL (Fin n) ℂ), B.val = transvection i j s →
      Φ B *ᵥ v = ∑ k ∈ Finset.range (K + 1), s ^ k • w k := by
    intro s B hB
    ext a
    simp only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, w]
    simp_rw [hP s B hB a, Polynomial.eval_eq_sum_range' (hK a _) s, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ => by ring
  refine ⟨K, w, ?_, ?_, hexp⟩
  · have h0 := hexp 0 1 (by simp)
    rw [hΦ.one, one_mulVec, Finset.sum_range_succ'] at h0
    simpa using h0.symm
  · intro k D hD
    by_cases hk : K < k
    · have hw : w k = 0 := by
        funext a
        simp only [w, Pi.zero_apply]
        refine Finset.sum_eq_zero fun b _ => ?_
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hK a b) hk), zero_mul]
      rw [hw, mulVec_zero, smul_zero]
    push_neg at hk
    set d : Fin n → ℂ := fun l => D.val l l with hd_def
    have hDd : D.val = diagonal d := ((isDiag_iff_diagonal_diag _).1 hD).symm
    have hd : ∀ l, d l ≠ 0 := by
      have hdet : D.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 D.isUnit).ne_zero
      rw [hDd, det_diagonal, Finset.prod_ne_zero_iff] at hdet
      exact fun l => hdet l (Finset.mem_univ l)
    set lam : ℂ := ∏ l, D.val l l ^ μ l with hlam
    have hcomm : ∀ s : ℂ, D * tGL hij s = tGL hij (s * d i / d j) * D := by
      intro s
      ext1
      simp only [Units.val_mul, tGL]
      rw [hDd]
      exact diag_mul_transvection hij d hd s
    have hmain : ∀ s : ℂ, Φ D *ᵥ (∑ k ∈ Finset.range (K + 1), s ^ k • w k) =
        lam • ∑ k ∈ Finset.range (K + 1), (s * d i / d j) ^ k • w k := by
      intro s
      rw [← hexp s (tGL hij s) rfl, ← hexp _ (tGL hij (s * d i / d j)) rfl, mulVec_mulVec, ← hΦ.mul, hcomm,
        hΦ.mul, ← mulVec_mulVec, hv D hD, mulVec_smul]
    have hcoord : ∀ a, (Φ D *ᵥ w k) a = (lam * (d i / d j) ^ k) * w k a := by
      intro a
      refine poly_coeff_eq K (fun m => (Φ D *ᵥ w m) a) (fun m => (lam * (d i / d j) ^ m) * w m a) ?_ k hk
      intro s
      have := congrFun (hmain s) a
      simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Finset.mul_sum] at this
      rw [this]
      refine Finset.sum_congr rfl fun m _ => by ring
    ext a
    rw [hcoord a, Pi.smul_apply, smul_eq_mul, prod_wt_shift d hd i j μ k]

end GlobalTheory
end

section

open Matrix GlobalTheory.AlgWtHW

theorem _root_.GlobalTheory.T.exists_torusWeight_of_polyRep_GL_complex : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∃ μ : Fin n → ℤ, IsWt Φ μ := by
  first | exact @GlobalTheory.AlgWtHW.exists_isWt_of_isPolyRep | exact GlobalTheory.AlgWtHW.exists_isWt_of_isPolyRep | (intros; apply GlobalTheory.AlgWtHW.exists_isWt_of_isPolyRep <;> assumption)
end

section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

theorem _root_.GlobalTheory.T.isTorusWeightOfPolyRep_comp_swap : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ μ : Fin n → ℤ, IsWt Φ μ → ∀ i j : Fin n, IsWt Φ (μ ∘ Equiv.swap i j) := by
  first | exact @GlobalTheory.isWt_comp_swap | exact GlobalTheory.isWt_comp_swap | (intros; apply GlobalTheory.isWt_comp_swap <;> assumption)
end

section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

theorem _root_.GlobalTheory.T.span_rationalPoint_orbit_algebraicWeight : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W) (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), Agrees a b P → ∀ v : ι → ℂ, v ≠ 0 → ∀ w : ι → ℂ, w ∈ Submodule.span ℂ {x | ∃ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n ∧ x = evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) *ᵥ v} := by
  first | exact @GlobalTheory.AlgWtHW.span_ratPt_orbit | exact GlobalTheory.AlgWtHW.span_ratPt_orbit | (intros; apply GlobalTheory.AlgWtHW.span_ratPt_orbit <;> assumption)
end

section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

theorem _root_.GlobalTheory.T.lowerTransvection_mulVec_mem_spanWeightVectorsDominatedBy : ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ (lam ν : Fin n → ℤ), DomLE ν lam → ∀ (w : ι → ℂ), IsWtVec Φ ν w → ∀ (i j : Fin n), j < i → ∀ (s : ℂ) (T : GL (Fin n) ℂ), T.val = transvection i j s → Φ T *ᵥ w ∈ Sle Φ lam := by
  first | exact @GlobalTheory.AlgWtHW.lowerTransvection_mulVec_mem_Sle | exact GlobalTheory.AlgWtHW.lowerTransvection_mulVec_mem_Sle | (intros; apply GlobalTheory.AlgWtHW.lowerTransvection_mulVec_mem_Sle <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

theorem _root_.GlobalTheory.T.isOpen_idele_subgroup_contains_congruence_units : ∀ (F : Type) [Field F] [NumberField F] (V : Subgroup (Ideles F)), IsOpen (V : Set (Ideles F)) → ∀ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (M : ℕ), S₀ ⊆ S ∧ (∀ v ∉ S, ∀ x, IsUnitAt v x → localIdele F v x ∈ V) ∧ ∀ v ∈ S, ∀ a : Fˣ, v.valuation F ((a : F) - 1) ≤ WithZero.exp (-(M : ℤ)) → locUnit F v a ∈ V := by
  first | exact @GlobalTheory.OpenIdeleCongr.open_subgroup_contains_congr | exact GlobalTheory.OpenIdeleCongr.open_subgroup_contains_congr | (intros; apply GlobalTheory.OpenIdeleCongr.open_subgroup_contains_congr <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology

noncomputable section

namespace GlobalTheory.ShaTransport

section General

variable {R : Type*} [CommRing R] {G G' : Type*} [Group G] [TopologicalSpace G] [Group G']
  [TopologicalSpace G'] {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

theorem pairH1_id_bijective (rho : Representation R G M) (rho' : Representation R G' M)
    (e : G' →* G) (he : Continuous e) (e' : G →* G') (he' : Continuous e')
    (h1 : ∀ g, e (e' g) = g) (h2 : ∀ g, e' (e g) = g)
    (hc : ∀ g m, (LinearMap.id : M →ₗ[R] M) (rho (e g) m) = rho' g ((LinearMap.id : M →ₗ[R] M) m)) :
    Function.Bijective (pairH1DecompositionMap rho rho' e he LinearMap.id continuous_id hc) := by
  have hc' : ∀ g m, (LinearMap.id : M →ₗ[R] M) (rho' (e' g) m) = rho g ((LinearMap.id : M →ₗ[R] M) m) := by
    intro g m
    have := hc (e' g) m
    simp only [LinearMap.id_apply, h1] at this ⊢
    exact this.symm
  refine Function.bijective_iff_has_inverse.2
    ⟨pairH1DecompositionMap rho' rho e' he' LinearMap.id continuous_id hc', fun x => ?_, fun x => ?_⟩
  · obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [pairH1DecompositionMap, Submodule.mapQ_apply]
    congr 1
    exact Subtype.ext (funext fun g => by simp [compatiblePairCocycles1, h1])
  · obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [pairH1DecompositionMap, Submodule.mapQ_apply]
    congr 1
    exact Subtype.ext (funext fun g => by simp [compatiblePairCocycles1, h2])

end General

section Field

variable {F Ω Ω' : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  [Field Ω'] [Algebra F Ω'] [IsAlgClosure F Ω']

theorem autCongr_mem_Dec (σ : Ω ≃ₐ[F] Ω') {A : ValuationSubring Ω} {A₁ : ValuationSubring Ω'}
    (hA : ∀ y, σ y ∈ A₁ ↔ y ∈ A) {g : G F Ω} (hg : g ∈ Dec (F := F) A) :
    (AlgEquiv.autCongr σ g : G F Ω') ∈ Dec (F := F) A₁ := by
  rw [mem_Dec]
  ext y
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  obtain ⟨z, rfl⟩ := σ.surjective y
  have : (AlgEquiv.autCongr σ g)⁻¹ • σ z = σ ((g⁻¹ : G F Ω) z) := by
    rw [← map_inv]
    show σ ((g⁻¹ : G F Ω) (σ.symm (σ z))) = _
    rw [σ.symm_apply_apply]
  rw [this, hA, hA]
  exact apply_mem_iff_of_mem_Dec ((Dec (F := F) A).inv_mem hg) z

theorem isPlaceOver_transport (σ : Ω ≃ₐ[F] Ω') {A : ValuationSubring Ω}
    {A₁ : ValuationSubring Ω'} (hA : ∀ y, σ y ∈ A₁ ↔ y ∈ A) {v : HeightOneSpectrum (𝓞 F)}
    (h : IsPlaceOver A v) : IsPlaceOver A₁ v := by
  intro x
  rw [← h x, valuation_lt_one_iff', valuation_lt_one_iff', ← σ.commutes, hA, ← map_inv₀, hA,
    map_eq_zero_iff _ σ.injective]

theorem NS_le_comap (σ : Ω ≃ₐ[F] Ω') (S : Set (HeightOneSpectrum (𝓞 F))) :
    NS Ω S ≤ (NS Ω' S).comap (AlgEquiv.autCongr σ).toMonoidHom := by
  have hcont := GlobalTheory.ConsCompare.autCongr_continuous_cyc_inertia F Ω Ω' σ
  have hN : ((NS Ω' S).comap (AlgEquiv.autCongr σ).toMonoidHom).Normal :=
    Subgroup.Normal.comap inferInstance _
  have hcl : IsClosed (((NS Ω' S).comap (AlgEquiv.autCongr σ).toMonoidHom : Subgroup (G F Ω)) :
      Set (G F Ω)) := (isClosed_NS Ω' S).preimage hcont.1
  unfold NS
  apply Subgroup.topologicalClosure_minimal _ _ hcl
  apply Subgroup.normalClosure_le_normal
  intro g hg
  simp only [Set.mem_iUnion] at hg
  obtain ⟨v, hv, A, hA, hg⟩ := hg
  show AlgEquiv.autCongr σ g ∈ NS Ω' S
  apply Subgroup.le_topologicalClosure
  apply Subgroup.subset_normalClosure
  have hA₁ : ∀ y, σ y ∈ A.comap (σ.symm : Ω' →+* Ω) ↔ y ∈ A := fun y => by
    rw [ValuationSubring.mem_comap]
    simp
  simp only [Set.mem_iUnion]
  exact ⟨v, hv, A.comap (σ.symm : Ω' →+* Ω), isPlaceOver_transport σ hA₁ hA,
    hcont.2.2 A _ hA₁ g hg⟩

def gsMap (σ : Ω ≃ₐ[F] Ω') (S : Set (HeightOneSpectrum (𝓞 F))) : GS Ω' S →* GS Ω S :=
  QuotientGroup.map (NS Ω' S) (NS Ω S) (AlgEquiv.autCongr σ.symm).toMonoidHom (NS_le_comap σ.symm S)

theorem gsMap_mk (σ : Ω ≃ₐ[F] Ω') (S : Set (HeightOneSpectrum (𝓞 F))) (g : G F Ω') :
    gsMap σ S (toGS Ω' S g) = toGS Ω S (AlgEquiv.autCongr σ.symm g) := rfl

theorem continuous_gsMap (σ : Ω ≃ₐ[F] Ω') (S : Set (HeightOneSpectrum (𝓞 F))) :
    Continuous (gsMap σ S) :=
  (QuotientGroup.isQuotientMap_mk (NS Ω' S)).continuous_iff.2
    ((continuous_toGS Ω S).comp (GlobalTheory.ConsCompare.autCongr_continuous_cyc_inertia F Ω' Ω σ.symm).1)

theorem gsMap_gsMap_symm (σ : Ω ≃ₐ[F] Ω') (S : Set (HeightOneSpectrum (𝓞 F))) (x : GS Ω S) :
    gsMap σ S (gsMap σ.symm S x) = x := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  show toGS Ω S (AlgEquiv.autCongr σ.symm (AlgEquiv.autCongr σ.symm.symm g)) = toGS Ω S g
  congr 1
  ext y
  simp [AlgEquiv.autCongr_apply]

def transport {l : ℕ} [Fact l.Prime] (σ : Ω ≃ₐ[F] Ω') (D : LData F Ω l) : LData F Ω' l where
  S := D.S
  hS := D.hS
  A v := (D.A v).comap (σ.symm : Ω' →+* Ω)
  hA v := isPlaceOver_transport σ (fun y => by rw [ValuationSubring.mem_comap]; simp) (D.hA v)
  chi := D.chi.comp (gsMap σ _)
  hchi := by
    ext g
    have h1 := congrArg (fun f => ((f (AlgEquiv.autCongr σ.symm g) : ℤ_[l]ˣ) : ℤ_[l])) D.hchi
    have h2 := (GlobalTheory.ConsCompare.autCongr_continuous_cyc_inertia F Ω' Ω σ.symm).2.1 l g
    simp only [MonoidHom.comp_apply] at h1
    simp only [MonoidHom.comp_apply, gsMap_mk]
    rw [h1, h2]

end Field

section Sha

variable {F Ω Ω' : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  [Field Ω'] [Algebra F Ω'] [IsAlgClosure F Ω'] {l : ℕ} [Fact l.Prime]

def decMap (σ : Ω ≃ₐ[F] Ω') {A : ValuationSubring Ω} {A₁ : ValuationSubring Ω'}
    (hA : ∀ y, σ y ∈ A₁ ↔ y ∈ A) : Dec (F := F) A →* Dec (F := F) A₁ :=
  ((AlgEquiv.autCongr σ).toMonoidHom.comp (Dec (F := F) A).subtype).codRestrict _
    (fun g => autCongr_mem_Dec σ hA g.2)

theorem continuous_decMap (σ : Ω ≃ₐ[F] Ω') {A : ValuationSubring Ω} {A₁ : ValuationSubring Ω'}
    (hA : ∀ y, σ y ∈ A₁ ↔ y ∈ A) : Continuous (decMap σ hA) :=
  Continuous.subtype_mk ((GlobalTheory.ConsCompare.autCongr_continuous_cyc_inertia F Ω Ω' σ).1.comp
    continuous_subtype_val) _

theorem shaLen_transport (σ : Ω ≃ₐ[F] Ω') (D : LData F Ω l) (e : ℤ) :
    shaLen (transport σ D) e = shaLen D e := by
  have hc : ∀ g m, (LinearMap.id : QZ l →ₗ[ℤ_[l]] QZ l) (qzTw D e (gsMap σ _ g) m) =
      qzTw (transport σ D) e g ((LinearMap.id : QZ l →ₗ[ℤ_[l]] QZ l) m) := fun _ _ => rfl
  have hΦ := pairH1_id_bijective (qzTw D e) (qzTw (transport σ D) e) (gsMap σ _)
    (continuous_gsMap σ _) (gsMap σ.symm _) (continuous_gsMap σ.symm _)
    (gsMap_gsMap_symm σ _) (gsMap_gsMap_symm σ.symm _) hc
  set Φ := pairH1DecompositionMap (qzTw D e) (qzTw (transport σ D) e) (gsMap σ _) (continuous_gsMap σ _)
    LinearMap.id continuous_id hc with hΦdef
  have key : ∀ x, x ∈ Sha D e ↔ Φ x ∈ Sha (transport σ D) e := by
    intro x
    simp only [Sha, Sha1, Submodule.mem_iInf, LinearMap.mem_ker]
    refine forall_congr' fun v => ?_
    have hA₁ : ∀ y, σ.symm y ∈ D.A v ↔ y ∈ (transport σ D).A v := fun y => by
      show _ ↔ y ∈ (D.A v).comap (σ.symm : Ω' →+* Ω)
      rw [ValuationSubring.mem_comap]
      rfl
    have hA : ∀ y, σ y ∈ (transport σ D).A v ↔ y ∈ D.A v := fun y => by
      rw [← hA₁, σ.symm_apply_apply]
    have hcv : ∀ k m, (LinearMap.id : QZ l →ₗ[ℤ_[l]] QZ l)
        ((qzTw D e).comp (locFam D.S D.A v) (decMap σ.symm hA₁ k) m) =
        ((qzTw (transport σ D) e).comp (locFam (transport σ D).S (transport σ D).A v)) k
          ((LinearMap.id : QZ l →ₗ[ℤ_[l]] QZ l) m) := fun _ _ => rfl
    have hΔ := pairH1_id_bijective ((qzTw D e).comp (locFam D.S D.A v))
      ((qzTw (transport σ D) e).comp (locFam (transport σ D).S (transport σ D).A v))
      (decMap σ.symm hA₁) (continuous_decMap σ.symm hA₁) (decMap σ hA) (continuous_decMap σ hA)
      (fun g => Subtype.ext (by ext y; simp [decMap, AlgEquiv.autCongr_apply]))
      (fun g => Subtype.ext (by ext y; simp [decMap, AlgEquiv.autCongr_apply])) hcv
    have hres : resH1 (qzTw (transport σ D) e) (locFam (transport σ D).S (transport σ D).A v)
        (continuous_locFam _ _ v) (Φ x) =
        pairH1DecompositionMap _ _ (decMap σ.symm hA₁) (continuous_decMap σ.symm hA₁) LinearMap.id continuous_id hcv
          (resH1 (qzTw D e) (locFam D.S D.A v) (continuous_locFam _ _ v) x) := by
      obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rfl
    constructor
    · intro h
      exact hres.trans (by rw [h, map_zero])
    · intro h
      exact hΔ.1 (by rw [map_zero]; exact hres.symm.trans h)
  let Φe := LinearEquiv.ofBijective Φ hΦ
  have hmap : (Sha D e).map Φe.toLinearMap =
      Sha (transport σ D) e := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (key x).1 hx
    · intro hy
      refine ⟨Φe.symm y, (key _).2 ?_, Φe.apply_symm_apply y⟩
      have : Φ (Φe.symm y) = y := Φe.apply_symm_apply y
      rw [this]
      exact hy
  exact (LinearEquiv.ofSubmodules Φe _ _ hmap).length_eq.symm

theorem exists_lData_shaLen_eq : ∀ {F Ω Ω' : Type} [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] [IsAlgClosure F Ω] [Field Ω'] [Algebra F Ω'] [IsAlgClosure F Ω'] (l : ℕ)
    [Fact l.Prime] (D : Formalism.GaloisCohomology.LData F Ω l),
    ∃ D' : Formalism.GaloisCohomology.LData F Ω' l, ∀ e : ℤ, Formalism.GaloisCohomology.shaLen D' e = Formalism.GaloisCohomology.shaLen D e := by
  intro F Ω Ω' _ _ _ _ _ _ _ _ l _ D
  exact ⟨transport (IsAlgClosure.equiv F Ω Ω') D, shaLen_transport _ D⟩

end Sha

end GlobalTheory.ShaTransport
end
end

section

open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

namespace GlobalTheory.UpqHaarRight

theorem isMulRightInvariant :
    ∀ (P Q : ℕ) (μ : Measure (UpqT P Q)), μ.IsHaarMeasure → μ.IsMulRightInvariant :=
  fun P Q μ hμ => GlobalTheory.UpqUnimodular.isMulRightInvariant_of_isHaarMeasure P Q μ hμ

end GlobalTheory.UpqHaarRight
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.L2.DIV

namespace GlobalTheory.Mem.StabDet

theorem isIntegral_det {E : Type} [Field E] [NumberField E] {N : ℕ} (L : Submodule (𝓞 E) (Fin N → E))
    (hfg : L.FG) (hsp : Submodule.span E (L : Set (Fin N → E)) = ⊤) (γ : Matrix (Fin N) (Fin N) E)
    (hγ : ∀ v ∈ L, γ.mulVec v ∈ L) : IsIntegral ℤ γ.det :=
  _root_.UpperTheory.Reformulated.B.Ybf4.isIntegral_det L hfg hsp γ hγ

theorem eq_pm_one_of_unitary {R : Ranks} (H : Formalism.BasicNotions.Host R) :
    letI := H.cmStar; ∀ z : H.E, z ∈ unitary H.E → IsIntegral ℤ z → ∃ m : ℕ, 0 < m ∧ z ^ m = 1 := by
  letI := H.cmStar
  intro z hu hz
  have := H.isCMField_hostE
  obtain ⟨n, hn, hp⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one H.E ℂ hz (fun φ => by
    have h1 : star z * z = 1 := hu.1
    have h2 : φ (star z) = starRingEnd ℂ (φ z) := IsCMField.complexEmbedding_complexConj H.E φ z
    have h3 := congrArg φ h1
    rw [map_mul, h2, map_one, Complex.conj_mul'] at h3
    have h4 : ‖φ z‖ ^ 2 = 1 := by exact_mod_cast h3
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4)
  exact ⟨n, hn, hp⟩

end GlobalTheory.Mem.StabDet
end
