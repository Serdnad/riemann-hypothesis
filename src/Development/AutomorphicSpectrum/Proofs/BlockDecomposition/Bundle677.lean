module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyExhaustion.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetSubLeftOfAdmissible
public import Development.WeilBound.ThetaLifts.Reductions.SiegelAbs
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import GroundTheory.AutomorphicForms.ReductionHeight
public import GroundTheory.AutomorphicForms.ReductionFinite
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle669
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
import Development.WeilBound.ThetaLifts.Reductions.SiegelHaar

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

theorem _root_.GlobalTheory.T.jacquet_sub_left_of_admissible : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → JacquetSubLeft k := by
  first | exact @GlobalTheory.CompanionTheory.JacquetLeft.jacquetSubLeft | exact GlobalTheory.CompanionTheory.JacquetLeft.jacquetSubLeft | (intros; apply GlobalTheory.CompanionTheory.JacquetLeft.jacquetSubLeft <;> assumption)
end

section

set_option linter.unusedSectionVars false

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.ParCocompact.UnipNormal

section Ring

variable {n r : ℕ} {R : Type} [CommRing R] {s : R →+* R} {Jm : Matrix (Fin n) (Fin n) R}
  {Xm Ym : Matrix (Fin n) (Fin r) R}

theorem coef_inv (hF : PFr s Jm Xm Ym) {M : Matrix (Fin n) (Fin n) R} (hM : cT s M * Jm * M = Jm)
    {d d' : Fin r → R} (e : M * Xm = Xm * diagonal d) (e' : M * Ym = Ym * diagonal d') (i : Fin r) :
    d i * s (d' i) = 1 := by
  have h := hF.inv_coef hM e
  rw [e', ← Matrix.mul_assoc, hF.xy, Matrix.one_mul] at h
  have h2 := congrFun (congrFun h i) i
  have e3 : cT s (diagonal d') = diagonal (fun i => s (d' i)) := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [cT]
    · simp [cT, Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ (Ne.symm hab)]
  rw [e3, Matrix.diagonal_mul_diagonal] at h2
  simpa [mul_comm] using h2

theorem inv_mul_frame {M Mi : Matrix (Fin n) (Fin n) R} (hMi : Mi * M = 1) {d c : Fin r → R}
    (hdc : ∀ i, d i * c i = 1) (e : M * Xm = Xm * diagonal d) : Mi * Xm = Xm * diagonal c := by
  have h1 : diagonal d * diagonal c = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg _ (funext hdc)
  calc Mi * Xm = Mi * (Xm * (diagonal d * diagonal c)) := by rw [h1, Matrix.mul_one]
    _ = Mi * M * Xm * diagonal c := by
      rw [← Matrix.mul_assoc Xm, ← e]
      simp only [Matrix.mul_assoc]
    _ = Xm * diagonal c := by rw [hMi, Matrix.one_mul]

theorem orth_mulVec {M : Matrix (Fin n) (Fin n) R} (hM : cT s M * Jm * M = Jm) {d c : Fin r → R}
    (hdc : ∀ i, d i * c i = 1) (e : M * Xm = Xm * diagonal d) {v : Fin n → R}
    (hv : (cT s Xm * Jm) *ᵥ v = 0) : (cT s Xm * Jm) *ᵥ (M *ᵥ v) = 0 := by
  have h1 : diagonal d * diagonal c = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg _ (funext hdc)
  have h := pgram_unitary hM (Xm * diagonal c) (1 : Matrix (Fin n) (Fin n) R)
  rw [← Matrix.mul_assoc M, e, Matrix.mul_assoc Xm, h1, Matrix.mul_one, Matrix.mul_one, Matrix.mul_one,
    Formalism.UG.cT_mul] at h
  rw [Matrix.mulVec_mulVec, h, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

theorem clause_extend (hF : PFr s Jm Xm Ym) {U : Matrix (Fin n) (Fin n) R} {B : Matrix (Fin r) (Fin r) R}
    (hU : U * Xm = Xm * B) {P : Matrix (Fin n) (Fin n) R}
    (hP : P = 1 - Xm * (cT s Ym * Jm) - Ym * (cT s Xm * Jm))
    (hc : ∀ k, ∃ a : Fin r → R, (U - 1) *ᵥ (fun i => P i k) = Xm *ᵥ a) {w : Fin n → R}
    (hw : (cT s Xm * Jm) *ᵥ w = 0) : ∃ a : Fin r → R, (U - 1) *ᵥ w = Xm *ᵥ a := by
  choose A hA using hc
  have hUP : (U - 1) * P = Xm * (Matrix.of fun j k => A k j) := by
    ext i k
    have := congrFun (hA k) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have hUX : (U - 1) * Xm = Xm * (B - 1) := by
    rw [Matrix.sub_mul, Matrix.one_mul, hU, Matrix.mul_sub, Matrix.mul_one]
  have hwd : w = P *ᵥ w + Xm *ᵥ ((cT s Ym * Jm) *ᵥ w) := by
    rw [hP, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec w Ym, hw,
      Matrix.mulVec_zero, ← Matrix.mulVec_mulVec]
    abel
  refine ⟨(Matrix.of fun j k => A k j) *ᵥ w + (B - 1) *ᵥ ((cT s Ym * Jm) *ᵥ w), ?_⟩
  conv_lhs => rw [hwd]
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hUP, hUX, Matrix.mulVec_add]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

end Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}

def orthProj (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E) :
    Matrix (Fin n) (Fin n) E :=
  1 - X * (cT (σ : E →+* E) Y * J) - Y * (cT (σ : E →+* E) X * J)

theorem orth_orthProj (hW : IsWittFrame σ J X Y) : (cT (σ : E →+* E) X * J) * orthProj σ J X Y = 0 := by
  have e1 : cT (σ : E →+* E) X * J * (X * (cT (σ : E →+* E) Y * J)) = 0 := by
    rw [← Matrix.mul_assoc, hW.xx, Matrix.zero_mul]
  have e2 : cT (σ : E →+* E) X * J * (Y * (cT (σ : E →+* E) X * J)) = cT (σ : E →+* E) X * J := by
    rw [← Matrix.mul_assoc, hW.xy, Matrix.one_mul]
  rw [orthProj, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, e1, e2]
  abel

theorem leviMin_normalises_unipMin (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E) (hW : IsWittFrame σ J X Y) (m : GAd σ J) (hm : m ∈ leviMin σ J X Y)
    (u : GAd σ J) (hu : u ∈ unipMin σ J X) : m⁻¹ * u * m ∈ unipMin σ J X := by
  have hF := pfrA h hJ hW
  obtain ⟨d, d', e, e'⟩ := hm
  obtain ⟨B, hB, hB1, eU, hz⟩ := hu
  have hM := unitaryA_matHom m
  set M := (matHom _ σ J m).1 with hMdef
  set U := (matHom _ σ J u).1 with hUdef
  set Mi := (matHom _ σ J m⁻¹).1 with hMidef
  have hMi : Mi * M = 1 := by
    rw [hMidef, hMdef, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  obtain ⟨c, hdc⟩ : ∃ c : Fin r → AF F ⊗[F] E, ∀ i, d i * c i = 1 := ⟨_, coef_inv hF hM e e'⟩
  have eMi := inv_mul_frame hMi hdc e
  have hV : (matHom _ σ J (m⁻¹ * u * m)).1 = Mi * U * M := by
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul]
  refine ⟨diagonal c * B * diagonal d, ((Matrix.blockTriangular_diagonal _).mul hB).mul
    (Matrix.blockTriangular_diagonal _), ?_, ?_, ?_⟩
  · intro i
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hB1, mul_one, mul_comm]
    exact hdc i
  · rw [hV, Matrix.mul_assoc, e, ← Matrix.mul_assoc, Matrix.mul_assoc Mi, eU, ← Matrix.mul_assoc Mi, eMi]
    simp only [Matrix.mul_assoc]
  · intro z hzz
    have hcol : ∀ k, ∃ a, (U - 1) *ᵥ (fun i => ((orthProj σ J X Y).map (inclR (F := F) (AF F))) i k) =
        adMat F X *ᵥ a := by
      intro k
      refine hz (fun i => orthProj σ J X Y i k) ?_
      funext i
      have := congrFun (congrFun (orth_orthProj hW) i) k
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    have hv : (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (adMat F X) * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF F) J) *ᵥ
        (fun i => inclR (F := F) (AF F) (z i)) = 0 := by
      have e1 : cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (adMat F X) * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF F) J =
          (cT (σ : E →+* E) X * J).map (inclR (F := F) (AF F)) := by
        unfold JR
        rw [← cT_map_inclR, Matrix.map_mul]
        rfl
      rw [e1]
      funext i
      have := congrArg (inclR (F := F) (AF F)) (congrFun hzz i)

      simpa [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul] using this
    obtain ⟨a, ha⟩ := clause_extend hF eU (by
      unfold JR
      rw [← cT_map_inclR, ← cT_map_inclR, orthProj, Matrix.map_sub _ (map_sub _), Matrix.map_sub _ (map_sub _),
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul]) hcol
      (orth_mulVec hM hdc e hv)
    refine ⟨diagonal c *ᵥ a, ?_⟩
    have e4 : Mi * U * M - 1 = Mi * (U - 1) * M := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hMi]
    rw [hV, e4, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_mulVec, eMi,
      Matrix.mulVec_mulVec]

end GlobalTheory.CompanionTheory.ParCocompact.UnipNormal

end
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.RedCov.Simple
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
open IsDedekindDomain

noncomputable section

namespace GlobalTheory.CompanionTheory.RedCov.Simple.NormBound

open GroundTheory.Automorphic.Reduction

theorem finprod_le_prod_of_le {α : Type*} {f b : α → ℝ} (S : Finset α) (h0 : ∀ a, 0 ≤ f a)
    (hS : ∀ a ∈ S, f a ≤ b a) (hb : ∀ a ∈ S, 1 ≤ b a) (h1 : ∀ a, a ∉ S → f a ≤ 1) :
    ∏ᶠ a, f a ≤ ∏ a ∈ S, b a := by
  classical
  have hone : (1 : ℝ) ≤ ∏ a ∈ S, b a := by
    have := Finset.prod_le_prod₀ (s := S) (f := fun _ => (1 : ℝ)) (g := b)
      (fun _ _ => zero_le_one) hb
    simpa using this
  by_cases hf : (Function.mulSupport f).Finite
  · set c : α → ℝ := fun a => if a ∈ S then b a else 1 with hc
    have hcs : Function.mulSupport c ⊆ (S : Set α) := fun a ha => by
      by_contra h
      exact ha (by simp only [hc]; exact if_neg fun h' => h (Finset.mem_coe.2 h'))
    have hcf : (Function.mulSupport c).Finite := S.finite_toSet.subset hcs
    have hle : ∏ᶠ a, f a ≤ ∏ᶠ a, c a :=
      finprod_le_finprod_of_nonneg hf hcf h0 fun a => by
        simp only [hc]
        split_ifs with h
        · exact hS a h
        · exact h1 a h
    rw [finprod_eq_prod_of_mulSupport_subset c hcs] at hle
    refine hle.trans (le_of_eq (Finset.prod_congr rfl fun a ha => ?_))
    simp only [hc]
    rw [if_pos ha]
  · rw [finprod_of_infinite_mulSupport hf]
    exact hone

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

def integralOutside (S : Finset (HeightOneSpectrum (𝓞 F))) : Set (Fin N → AF F) :=
  {y | ∀ i, ∀ v, v ∉ S → (y i).2 v ∈ v.adicCompletionIntegers F}

theorem isOpen_integralOutside (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsOpen (integralOutside (N := N) S) := by
  have h := RestrictedProduct.isOpen_forall_imp_mem
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun v => Valued.isOpen_valuationSubring _) (p := fun v => v ∉ S)
  have h2 : IsOpen {a : AF F | ∀ v, v ∉ S → a.2 v ∈ v.adicCompletionIntegers F} :=
    h.preimage continuous_snd
  have : integralOutside (N := N) S = ⋂ i : Fin N, (fun y : Fin N → AF F => y i) ⁻¹'
      {a : AF F | ∀ v, v ∉ S → a.2 v ∈ v.adicCompletionIntegers F} := by
    ext y
    simp only [integralOutside, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [this]
  exact isOpen_iInter_of_finite fun i => h2.preimage (continuous_apply i)

theorem exists_mem_integralOutside (y : Fin N → AF F) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), y ∈ integralOutside S := by
  have h : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ i, (y i).2 v ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun i => (y i).2.2
  have hfin := Filter.eventually_cofinite.1 h
  refine ⟨hfin.toFinset, fun i v hv => ?_⟩
  by_contra hc
  exact hv (hfin.mem_toFinset.2 fun h' => hc (h' i))

theorem exists_finset_subset_integralOutside {D : Set (Fin N → AF F)} (hD : IsCompact D) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), D ⊆ integralOutside S := by
  classical
  obtain ⟨T, hT⟩ := hD.elim_finite_subcover
    (fun S : Finset (HeightOneSpectrum (𝓞 F)) => integralOutside (N := N) S)
    isOpen_integralOutside (fun y _ => by
      obtain ⟨S, hS⟩ := exists_mem_integralOutside y
      exact Set.mem_iUnion.2 ⟨S, hS⟩)
  refine ⟨T.sup id, fun y hy i v hv => ?_⟩
  obtain ⟨S, hS, hyS⟩ := Set.mem_iUnion₂.1 (hT hy)
  exact hyS i v fun h => hv (Finset.mem_sup.2 ⟨S, hS, h⟩)

theorem norm_finComp_le_one {y : Fin N → AF F} {v : HeightOneSpectrum (𝓞 F)}
    (h : ∀ i, (y i).2 v ∈ v.adicCompletionIntegers F) : ‖finComp v y‖ ≤ 1 :=
  (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i =>
    (Valued.toNormedField.norm_le_one_iff).2
      ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (h i))

theorem continuous_euclidNorm_infComp (w : InfinitePlace F) :
    Continuous fun y : Fin N → AF F => euclidNorm (infComp w y) :=
  continuous_euclidNorm.comp (continuous_pi fun i =>
    (continuous_apply w).comp (continuous_fst.comp (continuous_apply i)))

theorem continuous_norm_finComp (v : HeightOneSpectrum (𝓞 F)) :
    Continuous fun y : Fin N → AF F => ‖finComp v y‖ :=
  (continuous_pi fun i => (RestrictedProduct.continuous_eval v).comp
    (continuous_snd.comp (continuous_apply i))).norm

end GlobalTheory.CompanionTheory.RedCov.Simple.NormBound

namespace GlobalTheory.CompanionTheory.RedCov.Simple


open GroundTheory.Automorphic.Reduction NormBound in
theorem exists_adelicNorm_le_of_isCompact :
    ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (D : Set (Fin N → AF F)), IsCompact D →
      ∃ P : ℝ, 0 < P ∧ ∀ y ∈ D, GroundTheory.Automorphic.Reduction.adelicNorm y ≤ P := by
  intro F _ _ N D hD
  classical
  obtain ⟨S, hS⟩ := exists_finset_subset_integralOutside hD
  choose a ha1 ha using fun w : InfinitePlace F =>
    exists_one_le_bound hD (continuous_euclidNorm_infComp (N := N) w)
  choose b hb1 hb using fun v : HeightOneSpectrum (𝓞 F) =>
    exists_one_le_bound hD (continuous_norm_finComp (N := N) v)
  have hA : (1 : ℝ) ≤ ∏ w, a w ^ w.mult := by
    have := Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ : InfinitePlace F => (1 : ℝ))
      (g := fun w => a w ^ w.mult) (fun _ _ => zero_le_one)
      (fun w _ => one_le_pow₀ (ha1 w))
    simpa using this
  have hB : (1 : ℝ) ≤ ∏ v ∈ S, b v := by
    have := Finset.prod_le_prod₀ (s := S) (f := fun _ => (1 : ℝ)) (g := b)
      (fun _ _ => zero_le_one) (fun v _ => hb1 v)
    simpa using this
  refine ⟨(∏ w, a w ^ w.mult) * ∏ v ∈ S, b v, by positivity, fun y hy => ?_⟩
  refine mul_le_mul ?_ ?_ (finprod_nonneg fun _ => norm_nonneg _) (by positivity)
  · exact Finset.prod_le_prod₀ (fun w _ => pow_nonneg (euclidNorm_nonneg _) _)
      fun w _ => pow_le_pow_left₀ (euclidNorm_nonneg _) (ha w y hy) _
  · exact finprod_le_prod_of_le S (fun _ => norm_nonneg _) (fun v _ => hb v y hy)
      (fun v _ => hb1 v) fun v hv => norm_finComp_le_one fun i => hS hy i v hv

end GlobalTheory.CompanionTheory.RedCov.Simple

end
end
