module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle053
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermFunPf
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle054
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps GlobalTheory.Shares

namespace GlobalTheory.Shares

theorem exists_indep_of_span_image {α : Type} {δ : ℕ} (S : Set α) (v : α → Fin δ → ℂ)
    (h : Submodule.span ℂ (v '' S) = ⊤) :
    ∃ θ : Fin δ → α, (∀ i, θ i ∈ S) ∧ LinearIndependent ℂ fun i => v (θ i) := by
  obtain ⟨b, hb, hsp, hli⟩ := exists_linearIndependent ℂ (v '' S)
  rw [h] at hsp
  let bs : Module.Basis b ℂ (Fin δ → ℂ) := Module.Basis.mk hli (by rw [Subtype.range_coe, hsp])
  let e : Fin δ ≃ b := (Pi.basisFun ℂ (Fin δ)).indexEquiv bs
  choose θ hθ hv using fun i : Fin δ => hb (e i).2
  refine ⟨θ, hθ, ?_⟩
  have : (fun i => v (θ i)) = (Subtype.val : b → Fin δ → ℂ) ∘ e := funext hv
  rw [this]
  exact hli.comp e e.injective

theorem ev_mem_sp_of_mem_span {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} (R : Rdg X)
    (u : WeightFamilies.Wt D j) (s : Set (B.Cusp j u)) (F : B.Cusp j u) (hF : F ∈ Submodule.span B.KO s) :
    R.ev (X.inc u F) ∈ R.sp u s := by
  induction hF using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [map_zero, map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul, R.ev_smul]; exact Submodule.smul_mem _ _ hx

theorem exists_valueBasis_in_spanning (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j)
    (ka wL wF : WeightFamilies.Wt D j) (N : ℕ) (w : Fin N → B.Cusp j wL) (R : Rdg X) (t : Idx D j N → ℂ) (T : ℕ)
    (Mg : Submodule B.KO (B.Cusp j ka)) (δ : ℕ) (xs : Fin δ → R.Y) (hA : AnFacts R w t ka wF T Mg xs)
    (Sh : Set (B.Cusp j wF)) (hS : Submodule.span B.KO Sh = ⊤) :
    ∃ θ : Fin δ → B.Cusp j wF, (∀ i, θ i ∈ Sh) ∧
      LinearIndependent ℂ (vals xs fun i => R.ev (X.inc wF (θ i))) := by
  refine exists_indep_of_span_image Sh (fun F q => R.ev (X.inc wF F) (xs q)) ?_
  rw [eq_top_iff]
  intro v _
  obtain ⟨f, hf, hv⟩ := hA.interp v
  have h1 : R.sp wF Set.univ ≤ R.sp wF Sh := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨F, -, rfl⟩
    exact ev_mem_sp_of_mem_span R wF Sh F (hS ▸ Submodule.mem_top)
  have h2 : LinearMap.funLeft ℂ ℂ xs f ∈ (R.sp wF Sh).map (LinearMap.funLeft ℂ ℂ xs) :=
    Submodule.mem_map_of_mem (h1 hf)
  rw [Rdg.sp, Submodule.map_span, Set.image_image] at h2
  have h3 : v = LinearMap.funLeft ℂ ℂ xs f := funext fun q => (hv q).symm
  rw [h3]
  exact h2

end GlobalTheory.Shares
end

section

-- Use the fraction-ring instances directly so repeated maps can be matched by `simp` and `rw`.
set_option backward.inferInstanceAs.wrap false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps GlobalTheory.Shares

namespace GlobalTheory.ReadingTransfer

theorem exists_coeffs {K A s μ : Type} [Field K] [CommRing A] [Algebra K A] [Fintype μ] (w : μ → A)
    (p : MvPolynomial s A) (hp : ∀ m, p.coeff m ∈ Submodule.span K (Set.range w)) :
    ∃ c : μ → MvPolynomial s K, p = ∑ k, MvPolynomial.map (algebraMap K A) (c k) * MvPolynomial.C (w k) := by
  classical
  choose f hf using fun m => (Submodule.mem_span_range_iff_exists_fun K).1 (hp m)
  refine ⟨fun k => ∑ m ∈ p.support, MvPolynomial.monomial m (f m k), ?_⟩
  ext m
  have hcf : ∀ k, (∑ m' ∈ p.support, MvPolynomial.monomial m' (f m' k)).coeff m =
      if m ∈ p.support then f m k else 0 := by
    intro k
    rw [MvPolynomial.coeff_sum]
    simp [MvPolynomial.coeff_monomial]
  rw [MvPolynomial.coeff_sum]
  simp only [mul_comm _ (MvPolynomial.C _), MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, hcf]
  by_cases hm : m ∈ p.support
  · rw [← hf m]
    simp only [hm, ↓reduceIte, Algebra.smul_def, Algebra.commutes]
  · simp only [hm, ↓reduceIte, map_zero, mul_zero, Finset.sum_const_zero]
    simpa using hm

theorem eval_comb {K A s μ F M : Type} [Field K] [CommRing A] [Algebra K A] [Fintype μ] [Field F] [CommRing M]
    [Algebra F M] (κ : K →+* F) (e : A →+* M) (he : ∀ (a : K) (x : A), e (a • x) = κ a • e x) (τ : s → F)
    (τ' : s → M) (hτ : ∀ i, τ' i = algebraMap F M (τ i)) (w : μ → A) (c : μ → MvPolynomial s K) :
    MvPolynomial.eval₂Hom e τ' (∑ k, MvPolynomial.map (algebraMap K A) (c k) * MvPolynomial.C (w k)) =
      Fintype.linearCombination F (fun k => e (w k)) (fun k => MvPolynomial.eval₂Hom κ τ (c k)) := by
  have hcomp : (algebraMap F M).comp κ = e.comp (algebraMap K A) := by
    ext a
    rw [RingHom.comp_apply, RingHom.comp_apply, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, he, map_one]
  obtain rfl : τ' = fun i => algebraMap F M (τ i) := funext hτ

  simp only [map_sum, map_mul, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, MvPolynomial.eval₂_map,
  Fintype.linearCombination_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.smul_def, MvPolynomial.eval₂_comp_left, hcomp] <;> rfl

theorem inj_transfer {F V W ι : Type} [Field F] [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    (L : V →ₗ[F] W) (hL : Function.Injective L) (v : ι → V) :
    (LinearIndependent F (fun i => L (v i)) ↔ LinearIndependent F v) ∧
    (∀ x, L x ∈ Submodule.span F (Set.range fun i => L (v i)) ↔ x ∈ Submodule.span F (Set.range v)) ∧
    Module.finrank F (Submodule.span F (Set.range fun i => L (v i))) =
      Module.finrank F (Submodule.span F (Set.range v)) := by
  have hspan : Submodule.span F (Set.range fun i => L (v i)) = (Submodule.span F (Set.range v)).map L := by
    rw [Submodule.map_span, ← Set.range_comp] <;> rfl
  refine ⟨L.linearIndependent_iff (LinearMap.ker_eq_bot.mpr hL), fun x => ?_, ?_⟩
  · rw [hspan]
    exact ⟨fun ⟨y, hy, hxy⟩ => hL hxy ▸ hy, fun hx => Submodule.mem_map_of_mem hx⟩
  · rw [hspan]
    exact (Submodule.equivMapOfInjective L hL _).finrank_eq.symm

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

noncomputable def kap (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) : B.KO →+* Kp X la N :=
  (algebraMap (X.Kl la) (Kp X la N)).comp (algebraMap B.KO (X.Kl la))

theorem emb_smul' (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (a : B.KO) (F : X.Forms) :
    emb X la N (a • F) = kap X la N a • emb X la N F := by
  rw [Formalism.MainNotions.Gaps.EtaleWeightGaps.emb_smul]
  exact (algebraMap_smul (Kp X la N) (algebraMap B.KO (X.Kl la) a) (emb X la N F)).symm

theorem emb_indep (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) {μ : Type} (w : μ → X.Forms)
    (hw : LinearIndependent B.KO w) : LinearIndependent (Kp X la N) fun k => emb X la N (w k) := by
  classical
  have hs := hw.linearIndepOn_id
  let b3 := Algebra.TensorProduct.basis (Kp X la N) (Algebra.TensorProduct.basis (X.Kl la) (Module.Basis.extend hs))
  let idx : μ → hs.extend (Set.subset_univ _) := fun k => ⟨w k, hs.subset_extend _ (Set.mem_range_self k)⟩
  have hidx : Function.Injective idx := fun k l h => hw.injective (congrArg Subtype.val h)
  have e : (fun k => emb X la N (w k)) = ⇑b3 ∘ idx := by
    funext k
    rw [Formalism.MainNotions.Gaps.EtaleWeightGaps.emb_apply]
    simp only [b3, idx, Function.comp_apply, Algebra.TensorProduct.basis_apply, Module.Basis.extend_apply_self] <;> rfl
  rw [e]
  exact b3.linearIndependent.comp idx hidx

theorem eval_injective (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) :
    Function.Injective (MvPolynomial.eval₂Hom (kap X la N)
      (fun p : Idx D j N => @algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N p))) := by
  classical
  let f : Op X la N →+* Kp X la N :=
    @algebraMap (Op X la N) (Kp X la N) _
      _
      _
  have key : ∀ Q : MvPolynomial (Idx D j N) (X.Ol la),
      MvPolynomial.aeval (f ∘ Tv X la N) Q =
        f (algebraMap (Formalism.MainNotions.Gaps.EtaleWeightGaps.Pol X la N) (Op X la N) Q) := by
    intro Q
    have heval : MvPolynomial.eval₂Hom (algebraMap (X.Ol la) (Kp X la N)) (f ∘ Tv X la N) =
        f.comp (algebraMap (Formalism.MainNotions.Gaps.EtaleWeightGaps.Pol X la N) (Op X la N)) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply, ← MvPolynomial.algebraMap_eq,
          ← IsScalarTower.algebraMap_apply (X.Ol la)
            (Formalism.MainNotions.Gaps.EtaleWeightGaps.Pol X la N) (Op X la N)] <;> rfl
      · intro p
        rw [MvPolynomial.eval₂Hom_X']
        rfl
    exact DFunLike.congr_fun heval Q
  have hinj : Function.Injective fun Q : Formalism.MainNotions.Gaps.EtaleWeightGaps.Pol X la N =>
      f (algebraMap (Formalism.MainNotions.Gaps.EtaleWeightGaps.Pol X la N) (Op X la N) Q) :=
    (IsFractionRing.injective (Op X la N) (Kp X la N)).comp
      (IsLocalization.injective (M := (Formalism.MainNotions.Gaps.EtaleWeightGaps.gI X la N).primeCompl) (S := Op X la N)
        (Formalism.MainNotions.Gaps.EtaleWeightGaps.gI X la N).primeCompl_le_nonZeroDivisors)
  have hOl : AlgebraicIndependent (X.Ol la) (f ∘ Tv X la N) :=
    algebraicIndependent_iff_injective_aeval.2 fun Q₁ Q₂ h => hinj (by simpa only [key] using h)
  haveI : Algebra.IsAlgebraic (X.Ol la) (X.Kl la) :=
    IsLocalization.isAlgebraic (S := X.Kl la) (M := nonZeroDivisors (X.Ol la))
  have hKl := algebraicIndependent_iff_injective_aeval.1 (hOl.extendScalars (X.Kl la))
  have hmap : Function.Injective (MvPolynomial.map (σ := Idx D j N) (algebraMap B.KO (X.Kl la))) :=
    MvPolynomial.map_injective _ (algebraMap B.KO (X.Kl la)).injective
  have e : ⇑(MvPolynomial.eval₂Hom (kap X la N)
        (fun p : Idx D j N => @algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N p))) =
      ⇑(MvPolynomial.aeval (R := X.Kl la)
        fun p : Idx D j N => @algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N p)) ∘
        MvPolynomial.map (algebraMap B.KO (X.Kl la)) := by
    funext Q
    simp only [Function.comp_apply, MvPolynomial.coe_eval₂Hom, MvPolynomial.aeval_def,
      MvPolynomial.eval₂_map] <;> rfl
  rw [e]
  exact hKl.comp hmap

end GlobalTheory.ReadingTransfer

namespace GlobalTheory

open ReadingTransfer

theorem reading_transfer :
    ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (R : Rdg X) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (t : Idx D j N → ℂ), R.Generic t → ∀ (u : WeightFamilies.Wt D j) (ι : Type) [Fintype ι] (p : ι → MvPolynomial (Idx D j N) X.Forms), (∀ i, OfWt X u (p i)) → (LinearIndependent (Kp X la N) (fun i => toRp X la N (p i)) ↔ LinearIndependent ℂ (fun i => R.toFn t (p i))) ∧ (∀ q, OfWt X u q → (toRp X la N q ∈ Submodule.span (Kp X la N) (Set.range fun i => toRp X la N (p i)) ↔ R.toFn t q ∈ Submodule.span ℂ (Set.range fun i => R.toFn t (p i)))) ∧ Module.finrank (Kp X la N) (Submodule.span (Kp X la N) (Set.range fun i => toRp X la N (p i))) = Module.finrank ℂ (Submodule.span ℂ (Set.range fun i => R.toFn t (p i))) := by
  intro D B P j X R la N t hgen u ι _ p hp
  classical
  let b := Module.finBasis B.KO (B.Cusp j u)
  let v : Fin (Module.finrank B.KO (B.Cusp j u)) → X.Forms := fun k => X.inc u (b k)
  have hv : LinearIndependent B.KO v :=
    b.linearIndependent.map' (X.inc u) (LinearMap.ker_eq_bot.mpr (X.inc_inj u))
  have hspan : LinearMap.range (X.inc u) = Submodule.span B.KO (Set.range v) := by
    rw [LinearMap.range_eq_map, ← b.span_eq, Submodule.map_span, ← Set.range_comp] <;> rfl
  have hcoef : ∀ q : MvPolynomial (Idx D j N) X.Forms, OfWt X u q →
      ∀ m, q.coeff m ∈ Submodule.span B.KO (Set.range v) := fun q hq m => hspan ▸ hq m
  let φ : MvPolynomial (Idx D j N) B.KO →+* Kp X la N :=
    MvPolynomial.eval₂Hom (kap X la N) (fun p => @algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N p))
  let ψ : MvPolynomial (Idx D j N) B.KO →+* ℂ := MvPolynomial.eval₂Hom R.σ t
  have hφ : Function.Injective φ := eval_injective X la N
  have hψ : Function.Injective ψ := (injective_iff_map_eq_zero ψ).2 fun Q hQ => by
    by_contra h
    exact hgen Q h hQ
  let LK := Fintype.linearCombination (Kp X la N) (fun k => emb X la N (v k))
  let LC := Fintype.linearCombination ℂ (fun k => R.ev (v k))
  have hLK : Function.Injective LK :=
    linearIndependent_iff_injective_fintypeLinearCombination.1 (emb_indep X la N v hv)
  have hLC : Function.Injective LC :=
    linearIndependent_iff_injective_fintypeLinearCombination.1 (R.indep u _ b b.linearIndependent)
  have hK : ∀ (q : MvPolynomial (Idx D j N) X.Forms) (c : Fin (Module.finrank B.KO (B.Cusp j u)) → MvPolynomial (Idx D j N) B.KO),
      q = ∑ k, MvPolynomial.map (algebraMap B.KO X.Forms) (c k) * MvPolynomial.C (v k) →
        toRp X la N q = LK fun k => φ (c k) := by
    rintro q c rfl
    exact eval_comb (kap X la N) (emb X la N) (emb_smul' X la N)
      (fun p => @algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N p))
      (fun p => algebraMap (Op X la N) (Rp X la N) (Tv X la N p))
      (fun p => IsScalarTower.algebraMap_apply (Op X la N) (Kp X la N) (Rp X la N) _) v c
  have hC : ∀ (q : MvPolynomial (Idx D j N) X.Forms) (c : Fin (Module.finrank B.KO (B.Cusp j u)) → MvPolynomial (Idx D j N) B.KO),
      q = ∑ k, MvPolynomial.map (algebraMap B.KO X.Forms) (c k) * MvPolynomial.C (v k) →
        R.toFn t q = LC fun k => ψ (c k) := by
    rintro q c rfl
    exact eval_comb R.σ R.ev R.ev_smul t (fun p _ => t p) (fun p => rfl) v c
  choose c hc using fun i => exists_coeffs v (p i) (hcoef _ (hp i))
  have eK : (fun i => toRp X la N (p i)) = fun i => LK fun k => φ (c i k) := funext fun i => hK _ _ (hc i)
  have eC : (fun i => R.toFn t (p i)) = fun i => LC fun k => ψ (c i k) := funext fun i => hC _ _ (hc i)
  obtain ⟨iK, mK, rK⟩ := inj_transfer LK hLK fun i k => φ (c i k)
  obtain ⟨iC, mC, rC⟩ := inj_transfer LC hLC fun i k => ψ (c i k)
  obtain ⟨iA, mA, rA⟩ := rank_indep_mem_embedding_invariant _ _ _ φ ψ hφ hψ ι _ c
  refine ⟨?_, ?_, ?_⟩
  · rw [eK, eC, iK, iC]
    exact iA
  · intro q hq
    obtain ⟨d, hd⟩ := exists_coeffs v q (hcoef _ hq)
    rw [eK, eC, hK _ _ hd, hC _ _ hd, mK, mC]
    exact mA d
  · rw [eK, eC, rK, rC]
    exact rA

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

namespace GlobalTheory.Shares

theorem addL_zero_pts {D : D7} {j : ℕ} (u wL : WeightFamilies.Wt D j) : addL u wL 0 = u := by
  show wadd u (wsmul 0 wL) = u
  cases u
  simp [wadd, wsmul]

theorem rdg_s_apply {D : D7} {T : Top D} {h : LawsP T} {j : ℕ} {hj : InR D j} {n : SecNorm (recB h.toLawsCore)}
    {R : Rdg (recPlusN h j hj n)} {e : R.Y ≃ DomPt T j} (hR : IsRdgU h j hj n R e) {N : ℕ} {wL : WeightFamilies.Wt D j}
    (w : Fin N → (recB h.toLawsCore).Cusp j wL) (t : Idx D j N → ℂ) (i : Fin (WeightFamilies.dimY D j + 1)) (y : R.Y) :
    R.s w t i y = ∑ k, t (i, k) * rdR h j (w k) (e y).1 (e y).2.1 := by
  simp only [Rdg.s, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hR.2]

theorem mem_sp_of_rdOnto {D : D7} {T : Top D} {h : LawsP T} {j : ℕ} {hj : InR D j} {n : SecNorm (recB h.toLawsCore)}
    {R : Rdg (recPlusN h j hj n)} {e : R.Y ≃ DomPt T j} (hR : IsRdgU h j hj n R e) {u : WeightFamilies.Wt D j}
    (hO : RdOnto h j u) (f : ∀ k : (T.U j T.σ₀).Comp, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ)
    (hf : ∀ k, f k ∈ ((T.U j T.σ₀).X k).SS (laR T j u k)) :
    (fun y => f (e y).1 (e y).2.1) ∈ R.sp u Set.univ := by
  obtain ⟨m, a, F, -, hF⟩ := hO f hf
  have hfun : (fun y => f (e y).1 (e y).2.1) = ∑ i, a i • R.ev ((recPlusN h j hj n).inc u (F i)) := by
    funext y
    rw [hF _ _ (e y).2.2]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hR.2]
  rw [hfun]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨F i, Set.mem_univ _, rfl⟩)

theorem points_and_interp : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → (∀ k : ℕ, RdOnto h j (addL wF wL k)) → (∀ q, R.s w t 0 (xs q) ≠ 0 ∧ ∀ i : Fin (WeightFamilies.dimY D j), R.s w t i.succ (xs q) = 0) ∧ ∀ v : Fin δ → ℂ, ∃ f ∈ R.sp wF Set.univ, ∀ q, f (xs q) = v q := by
  intro D T h j hj n R e hR N wL wF w Tn c1 A t Fl δ xs en hxs hO

  have hvan : ∀ (k : (T.U j T.σ₀).Comp) (a : Fin (nd ((T.U j T.σ₀).X k))) (p : Fin (Fl.Fl k).δ),
      (Fl.Fl k).s a ((Fl.Fl k).xs p) = 0 := by
    intro k a p
    have hb : (fun _ => (1 : Matrix (Fin D.R.r) (Fin D.R.r) ℂ) : Frame ((T.U j T.σ₀).X k).Ψ D.R.r) ∈
        Bor ((T.U j T.σ₀).X k).Ψ D.R.r := by
      intro τ
      refine ⟨?_, fun a c hca => Matrix.one_apply_ne hca.ne'⟩
      show (1 : Matrix (Fin D.R.r) (Fin D.R.r) ℂ).det ≠ 0
      simp
    have hself : (Fl.Fl k).xs p = lact 1 (rmul ((Fl.Fl k).xs p)
        (fun _ => (1 : Matrix (Fin D.R.r) (Fin D.R.r) ℂ))) := by
      funext τ a c
      simp only [lact, rmul, mat, Units.val_one, Matrix.map_one _ (map_zero τ.1) (map_one τ.1), one_mul]
      have hm : (Matrix.of ((Fl.Fl k).xs p τ) : Matrix (Fin D.R.r) (Fin D.R.r) ℂ) * 1 =
          Matrix.of ((Fl.Fl k).xs p τ) := Matrix.mul_one _
      exact (congrFun (congrFun hm a) c).symm
    exact (((Fl.Fl k).S_eq _ ((Fl.Fl k).xs_mem p)).2
      ⟨p, 1, ((T.U j T.σ₀).X k).Γ.one_mem, _, hb, hself⟩) a
  refine ⟨fun q => ⟨?_, fun i => ?_⟩, fun v => ?_⟩
  · rw [rdg_s_apply hR, hxs q]
    dsimp only
    rw [← Fl.h0]
    exact (Fl.Fl _).w0_ne _
  · rw [rdg_s_apply hR, hxs q]
    dsimp only
    have hs := Fl.hs (en q).1 (Fin.cast (A.dim (en q).1).symm i) ((Fl.Fl (en q).1).xs (en q).2)
    have hi : Fin.cast (A.dim (en q).1) (Fin.cast (A.dim (en q).1).symm i) = i := Fin.ext rfl
    rw [hi] at hs
    rw [← hs]
    exact hvan _ _ _
  ·
    have hF : ∀ k : (T.U j T.σ₀).Comp, ∃ F ∈ ((T.U j T.σ₀).X k).SSgt (A.Xa k).Fp 0,
        ∀ p, F ((Fl.Fl k).xs p) = v (en.symm ⟨k, p⟩) := by
      intro k
      obtain ⟨bb, m, h1, h2, h3⟩ := (A.mar k).1
      exact interpStatement_holds _ _ (A.Xa k) (Fl.Fl k)
        (GlobalTheory.ClosedDiscontinuity.propDisc_closed _ _)
        ⟨bb, m, h1, h2, fun x0 hx0 z hz ξ => by simpa using h3 0 (Set.mem_insert _ _) x0 hx0 z hz ξ⟩
        (A.mar k).2.2.1 (fun P hP => by simpa using (A.mar k).2.2.2.2 0 P (by simpa using hP)) _
    choose F hFmem hFval using hF
    have hO0 : RdOnto h j wF := by
      have h0 := hO 0
      rwa [addL_zero_pts] at h0
    have hf : ∀ k, F k ∈ ((T.U j T.σ₀).X k).SS (laR T j wF k) := by
      intro k
      rw [← A.hF k]
      exact (hFmem k).1
    refine ⟨_, mem_sp_of_rdOnto hR hO0 F hf, fun q => ?_⟩
    show F (e (xs q)).1 (e (xs q)).2.1 = v q
    rw [hxs q]
    exact (hFval _ _).trans (by simp)

end GlobalTheory.Shares
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FieldBC

namespace GlobalTheory.FieldBC

theorem shortExpr_bc {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) (nab : NabV Xo c) {n : ℕ} (w : (Fin n → LevQ Dw l) → c.F)
    (β : c.F) (a b N : ℕ) (P : MvPolynomial (LtN Dw n) c.F) {S : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S]
    (h : AlgOver c c' hle S) (y : FrPt Xo c' S) {J : Type} [Fintype J] (k : ℤ)
    (F : (Fin n → LevQ Dw l) → J → Fin n → LB.Sec (Out.LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) :
    algebraMap c'.F S ((incF c c' hle β)⁻¹ * ((a : c'.F))⁻¹ * ((b : c'.F))⁻¹ *
        ((N : c'.F) ^ (MvPolynomial.map (incF c c' hle) P).totalDegree)⁻¹) *
      ∑ᶠ q : Fin n → LevQ Dw l, algebraMap c'.F S (incF c c' hle (w q)) *
        ∑ i, ∑ m ∈ (MvPolynomial.map (incF c c' hle) P).support,
          algebraMap c'.F S ((MvPolynomial.map (incF c c' hle) P).coeff m) *
          ∏ j, nabBC hle nab y k (F q i j) (colOf m j) =
    algebraMap c.F S (β⁻¹ * ((a : c.F))⁻¹ * ((b : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹) *
      ∑ᶠ q : Fin n → LevQ Dw l, algebraMap c.F S (w q) *
        ∑ i, ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) *
          ∏ j, nab (y.res hle h) k (F q i j) (colOf m j) := by
  have h' : ∀ x : c.F, algebraMap c'.F S (incF c c' hle x) = algebraMap c.F S x := h
  have hd : (MvPolynomial.map (incF c c' hle) P).totalDegree = P.totalDegree := by
    simp only [MvPolynomial.totalDegree, MvPolynomial.support_map_of_injective P (incF c c' hle).injective]
  congr 1
  · rw [hd, ← h']
    simp only [map_mul, map_inv₀, map_pow, map_natCast]
  · refine finsum_congr fun q => ?_
    rw [h']
    congr 1
    exact Finset.sum_congr rfl fun i _ => (GlobalTheory.T.connectionPolynomialExpression_coeffFieldExtension E H Dw l Xo c c' hle nab n P S h y k (F q i)).2

theorem shortValAt_bc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (nab : NabV Xo c) (n : ℕ) (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (β : c.F) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F) (S : Type) [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S) (y : FrPt Xo c' S) (v : S), ShortValAt Xo c' (nabBC hle nab) (fun q => incF c c' hle (w q)) Λ (incF c c' hle β) N (MvPolynomial.map (incF c c' hle) P) y v ↔ ShortValAt Xo c nab w Λ β N P (y.res hle h) v := by
  intro E _ _ _ H Dw l Xo c c' hle nab n w Λ β N P S _ _ _ h y v
  constructor
  · rintro ⟨S', i1, i2, φ, y', z, tp, F, hff, hfr, hz, hg, htp, hF, hv⟩
    letI i3 : Algebra c.F S' := resAlg hle S'
    have h' : AlgOver c c' hle S' := fun _ => rfl
    let φ₀ : S →ₐ[c.F] S' := { φ.toRingHom with commutes' := fun x => (congrArg φ (h x).symm).trans (φ.commutes _) }
    exact ⟨S', i1, i3, φ₀, y'.res hle h', z, tp, F, hff, hfr, hz, hg, htp, hF,
      hv.trans (shortExpr_bc hle nab w β _ _ N P h' y' _ F)⟩
  · rintro ⟨S', i1, i2, φ, y', z, tp, F, hff, hfr, hz, hg, htp, hF, hv⟩
    letI i3 : Algebra c'.F S' := (φ.toRingHom.comp (algebraMap c'.F S)).toAlgebra
    have h' : AlgOver c c' hle S' := fun x => (congrArg φ (h x)).trans (φ.commutes x)
    let φ₀ : S →ₐ[c'.F] S' := { φ.toRingHom with commutes' := fun _ => rfl }
    exact ⟨S', i1, i3, φ₀, y'.ext hle h', z, tp, F, hff, hfr, hz, hg, htp, hF,
      hv.trans (shortExpr_bc hle nab w β _ _ N P h' (y'.ext hle h') _ F).symm⟩

end GlobalTheory.FieldBC
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory.CanonConn

theorem exists_isNab : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∃ (_ : StarRing (𝓞 E)) (nab : NabV Xo c), IsNab Xo c nab := by
  intro hL E _ _ _ H Dw l Xo c
  classical
  letI : StarRing (𝓞 E) := H.starRing
  have hs : ∀ a : 𝓞 E, star a = H.bar a := fun _ => rfl
  have hC := GlobalTheory.T.exists_biextension_chart_with_germs_framed_point hL E H Dw l Xo c hs
  choose C _hT hg using hC
  choose g hg using hg
  let val : ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (k : ℤ),
      LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x)) → (Lt1 Dw →₀ ℕ) → S :=
    fun S _ _ _ y k => match k with
      | Int.ofNat k => fun F α =>
          (C S y).B.nabVal S (C S y).h H.w0 k (g S y k F) (C S y).uvec (MvPolynomial.monomial α 1)
      | Int.negSucc _ => fun _ _ => 0
  let nab : NabV Xo c := fun {S} _ _ y k F α =>
    if h : Nonempty (Algebra ℚ S) then @val S _ _ h.some y k F α else 0
  refine ⟨inferInstance, nab, hs, ?_⟩
  intro S _ _ iQ y
  refine ⟨C S y, fun k F => ⟨_, hg S y k F⟩, ?_⟩
  intro k F f hf α
  have hne : Nonempty (Algebra ℚ S) := ⟨iQ⟩
  have h1 : nab y k F α = @val S _ _ hne.some y k F α := dif_pos hne
  have h2 : hne.some = iQ := Subsingleton.elim _ _
  refine h1.trans ?_
  rw [h2, isGermFun_holds E H Dw l Xo c S y _ _ _ _ _ k F f _ hf (hg S y k F)]

end GlobalTheory.CanonConn
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaGroup_shift_halfTorsion_root : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (B : Type) [CommRing B] (x0 : Sp B ⟶ Xo.X) (N : ℕ), Odd N → ∀ (s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 (ptO Xo x0))) (t u z : ptO Xo x0 ⟶ Xo.univ.t.G) (e : Γ((ptO Xo x0).left, ⊤)ˣ), t ^ (N ^ 2) = 1 → u ^ (N ^ 2) = 1 → z ^ (N ^ 2) = 1 → WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) t u 1 → WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) u z e → ∀ F F', IsUUOver Xo.univ.t.G Xo.univ.t.PP N s z (t * u) F → IsUUOver Xo.univ.t.G Xo.univ.t.PP N s (u * z) t F' → ∃ r : B, (toΓ B r) ^ 2 = (e : Γ((ptO Xo x0).left, ⊤)) ∧ r ^ (N ^ 2) = 1 ∧ ∀ j, F.f j = liftFun Xo.univ.t.G _ (T := ptO Xo x0) (toΓ B r) * F'.f j := by
  first | exact @GlobalTheory.isUUOver_shift | exact GlobalTheory.isUUOver_shift | (intros; apply GlobalTheory.isUUOver_shift <;> assumption)
end
