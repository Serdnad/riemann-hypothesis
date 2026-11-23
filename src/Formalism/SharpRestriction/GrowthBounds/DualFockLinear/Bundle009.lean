module

public import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.FockR
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.OneSidedLemma4Realisable
public import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.FockPairingRowAction
public import Formalism.PolynomialDimension.MultinomialDepth.FockGaussComparisonHolds
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.CloudBAtOfRho
public import Formalism.LocalToGlobal.GroupLattices.FockModels.Bundle001
public import Formalism.LocalToGlobal.GroupLattices.FockModels.MulMemRiemannRochSpaceAdd
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.SourcePrimitiveIntegrality
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.SubstSPtrue
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.Bundle001
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.Bundle005
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.Bundle002
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.Pf14
open Formalism.L2.G.Model (Lin Th0 Aa Lin_comp Lin_one Lin_Pol Th0_inj mem_tens_nabla mem_tens_dw map_Pol mem_Pol)
open Formalism.L2.G.Model.TS

section Contra

variable {S : Type} [Fintype S] [DecidableEq S] {R : Type} [CommRing R] {k : ℕ}

theorem fock_eq_fockR {τ : Type} (F G : MvPolynomial τ R) : fock F G = fockR F G := rfl

theorem Lin_X (N : S → Matrix (Fin k) (Fin k) R) (v : S × Fin k) :
    Lin N (X v) = ∑ b : Fin k, C (N v.1 v.2 b) * X (v.1, b) := by
  simp [Lin]

theorem Lin_coeff_zero (N : S → Matrix (Fin k) (Fin k) R) (h : MvPolynomial (S × Fin k) R) :
    AddMonoidAlgebra.coeff (Lin N h) 0 = AddMonoidAlgebra.coeff h 0 := by
  have h1 : (MvPolynomial.constantCoeff : MvPolynomial (S × Fin k) R →+* R).comp (Lin N).toRingHom =
      MvPolynomial.constantCoeff := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro v
      simp [Lin]
  exact congrArg (fun φ : MvPolynomial (S × Fin k) R →+* R => φ h) h1

theorem Lin_chain (N : S → Matrix (Fin k) (Fin k) R) (s : S) (b : Fin k) (h : MvPolynomial (S × Fin k) R) :
    pderiv (s, b) (Lin N h) = ∑ a : Fin k, N s a b • Lin N (pderiv (s, a) h) := by
  have hX : ∀ v : S × Fin k, pderiv (s, b) (Lin N (X v)) = ∑ a : Fin k, N s a b • Lin N (pderiv (s, a) (X v)) := by
    rintro ⟨t, c⟩
    rw [Lin_X]

    simp only [map_sum, Derivation.leibniz, MvPolynomial.pderiv_X, MvPolynomial.pderiv_C, smul_zero, add_zero,
    Pi.single_apply, Prod.mk.injEq, smul_eq_mul]
    by_cases ht : t = s
    · subst ht
      simp [Finset.sum_ite_eq', Finset.sum_ite_eq, MvPolynomial.smul_eq_C_mul]
    · simp [ht]
  induction h using MvPolynomial.induction_on with
  | C r =>
    have h1 : Lin N (C r) = C r := (Lin N).commutes r
    simp [h1]
  | add p q hp hq =>
    simp only [map_add (f := _), hp, hq, smul_add, Finset.sum_add_distrib]
  | mul_X p v hp =>
    rw [map_mul, Derivation.leibniz, hp, hX v]
    simp only [Derivation.leibniz, map_add (f := _), map_mul, smul_add, Finset.sum_add_distrib, smul_eq_mul,
      Finset.mul_sum, Finset.smul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun a _ => ?_
      simp only [MvPolynomial.smul_eq_C_mul]
      ring
    · refine Finset.sum_congr rfl fun a _ => ?_
      simp only [MvPolynomial.smul_eq_C_mul]
      ring

theorem fockR_Lin (N : S → Matrix (Fin k) (Fin k) R) (P : MvPolynomial (S × Fin k) R) :
    ∀ Q : MvPolynomial (S × Fin k) R, fockR (Lin N P) Q = fockR P (Lin (fun s => (N s).transpose) Q) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    intro Q
    have h1 : Lin N (C a : MvPolynomial (S × Fin k) R) = C a := by simp [Lin]
    rw [h1, C_apply, tsact_monomial_left, tsact_monomial_left, Lin_coeff_zero]
  | add p q hp hq =>
    intro Q
    rw [map_add (f := _), tsact_add_left, tsact_add_left, hp, hq]
  | mul_X p v hp =>
    intro Q
    rw [map_mul, Lin_X, Finset.mul_sum, tsact_sum_left, tsact_X_mul, Lin_chain, tsact_sum_right]
    refine Finset.sum_congr rfl fun b _ => ?_
    have e : Lin N p * (C (N v.1 v.2 b) * X (v.1, b)) = N v.1 v.2 b • (Lin N p * X (v.1, b)) := by
      rw [smul_eq_C_mul]; ring
    rw [e, tsact_smul_left, tsact_X_mul, hp, tsact_smul_right, Matrix.transpose_apply]

theorem fockR_Lin_dual (A B : S → Matrix (Fin k) (Fin k) R) (h : ∀ s, B s * (A s).transpose = 1)
    (P Q : MvPolynomial (S × Fin k) R) : fockR (Lin A P) (Lin B Q) = fockR P Q := by
  rw [fockR_Lin, Lin_comp]
  simp only [h]
  rw [Lin_one]

end Contra

theorem Aa_dual {K : Type} [Field K] {m : ℕ} (vec : Bool) (M : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (hM : IsUnit M.det) : Aa vec ((M⁻¹).transpose)⁻¹ * (Aa vec M⁻¹).transpose = 1 := by
  have h1 : IsUnit (M⁻¹).det := Matrix.isUnit_nonsing_inv_det M hM
  have h2 : IsUnit ((M⁻¹).transpose).det := by rwa [Matrix.det_transpose]
  cases vec
  · simp only [Aa, Bool.false_eq_true, if_false]
    rw [Matrix.nonsing_inv_nonsing_inv _ h2, Matrix.transpose_transpose, Matrix.transpose_transpose,
      Matrix.nonsing_inv_nonsing_inv _ hM, Matrix.nonsing_inv_mul _ hM]
  · simp only [Aa, if_true]
    exact Matrix.nonsing_inv_mul _ h2

theorem multDiv_kapFl (O : Type) [CommRing O] [IsLocalRing O] (p : ℕ) [hp : Fact p.Prime]
    (hpO : (p : O) ∈ IsLocalRing.maximalIdeal O) {n' k : ℕ} (d : Fin n' → ℕ) :
    MultDiv O p (kapFl p k d) (k := k) d := by
  intro α hα

  have h1 : ∀ s, (d s).factorial = Nat.multinomial Finset.univ (fun c : Fin k => α (s, c)) *
      ∏ c : Fin k, (α (s, c)).factorial := by
    intro s
    rw [mul_comm, Nat.multinomial_spec, ← hα s]
    rfl
  have h2 : expFact α = ∏ s : Fin n', ∏ c : Fin k, (α (s, c)).factorial := by
    unfold expFact
    rw [Finsupp.prod_fintype _ _ (fun _ => rfl), Fintype.prod_prod_type]
  set Mn : ℕ := ∏ s : Fin n', Nat.multinomial Finset.univ (fun c : Fin k => α (s, c)) with hMn
  have h3 : (∏ s, (d s).factorial) = Mn * expFact α := by
    rw [h2, hMn, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun s _ => h1 s
  have hMn0 : Mn ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => (Nat.multinomial_pos _ _).ne'
  have h4 : padicValNat p Mn ≤ kapFl p k d := by
    rw [hMn, Formalism.CountingSumsFrames.fock_val_prod p _ _ (fun s _ => (Nat.multinomial_pos _ _).ne')]
    unfold kapFl
    refine Finset.sum_le_sum fun s _ => ?_
    have := Formalism.CountingSumsFrames.fock_mult_val_le p (fun c : Fin k => α (s, c)) Finset.univ
    rw [Finset.card_univ, Fintype.card_fin] at this
    have e : ∑ c : Fin k, α (s, c) = d s := hα s
    rw [e] at this
    exact this

  have hdv : p ^ padicValNat p Mn ∣ Mn := (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
  have hnd : ¬ p ^ (padicValNat p Mn + 1) ∣ Mn := by
    rw [Nat.padicValNat_def]
    exact pow_succ_multiplicity_not_dvd hMn0
  generalize padicValNat p Mn = v at h4 hdv hnd
  obtain ⟨u, hu⟩ := hdv
  have hpu : ¬ p ∣ u := by
    intro hd
    apply hnd
    rw [hu, pow_succ]
    exact Nat.mul_dvd_mul_left _ hd
  have huO : IsUnit ((u : ℕ) : O) := by
    have hco : Nat.Coprime u p := ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hpu).symm
    by_contra hnu
    have hm : ((u : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hnu
    have hb := Nat.gcd_eq_gcd_ab u p
    rw [hco] at hb
    have h5 : (1 : O) = (u : O) * ((Nat.gcdA u p : ℤ) : O) + (p : O) * ((Nat.gcdB u p : ℤ) : O) := by
      have := congrArg (fun z : ℤ => (z : O)) hb
      push_cast at this
      exact this
    have h6 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      rw [h5]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hm) (Ideal.mul_mem_right _ _ hpO)
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h6)
  obtain ⟨uu, huu⟩ := huO
  refine ⟨(p : O) ^ (kapFl p k d - v) * (↑uu⁻¹ : O), ?_⟩
  rw [h3, hu]
  push_cast
  rw [← huu]
  have e1 : (p : O) ^ kapFl p k d = (p : O) ^ v * (p : O) ^ (kapFl p k d - v) := by
    rw [← pow_add]
    congr 1
    omega
  rw [e1]
  have e2 : (uu : O) * (↑uu⁻¹ : O) = 1 := Units.mul_inv uu
  linear_combination (-(p : O) ^ v * (p : O) ^ (kapFl p k d - v) * (expFact α : O)) * e2

end Formalism.MainNotions.TestSideCounting
end
end

section

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial

def RhoStep (C CK : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ),
    ∀ hSet : UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w,
    Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar →
    ∀ φ : WF p n' ≃+* W, IsWittIdent σ φ →
    ∀ e : Edge W Qq (m + 1), IsEdge p n' r e → e.tgt = colSpan W (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) →
    ∀ (hm : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')),
      IsUnit hm.det → IsGLW g → IsEdgeBasis p r e (hm * ((matQ φ g)⁻¹).transpose) →
      ∀ Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0))),
        IsTrueTheta hSet.1 (dT TT lam0) (flW (dT TT lam0)) (vecE n') hm Θ →
        RhoAt p n' ι σ w r TT lam0 c0 (r * TT.card * c0 + 2 * r * n' * cpp)
          (CK * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a) e Θ

def RestRho (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → ∃ CK C₁ : ℝ, 0 < CK ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → RhoStep C CK

theorem cloudBStep_of_rho (D : Formalism.BasicNotions.D7) (C CK CLa : ℝ) (hR : RhoStep C CK) : CloudBStep C CK CLa := by
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ K
    _ _ hk hrk F hF E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis
  let _ : Algebra (WF p n') O := algOfIdent j φ
  intro FsB hFsB Θ hΘ
  have hkr : orbitWindowCount r de h x + 2 * r ≤ (m + 1) - r := H.2.2.2.2.2.2.2.1
  have hr2 : 2 ≤ r := H.2.1
  have hdom : IsDominant lam0 := H.2.2.2.2.1.2.1
  have hw : algebraMap O Kf w ≠ 0 := w_ne_zero hSet.1
  obtain ⟨Θ', hΘ1, hΘ2⟩ := theta_exists p n' W Qq O Kf ι σ j w hSet.1 φ hφ m r (vecE n') (dT TT lam0) (flW (dT TT lam0))
    (by omega) (by omega) (isFlat_flW _) hm hhm
  have hΘeq : Θ = Θ' := LinearEquiv.ext fun G => Subtype.ext (by rw [hΘ G, hΘ2 G])
  have hFs : ∀ b, Θ (FsB b) ∈ Re p ι σ w r (flW (dT TT lam0)) e := by
    intro b
    have h1 : InWjRg p n' O w r (flatLetters (vecE n')) g (FsB b : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) 0 := by
      show InWj w (subst p n' O w n' r g (FsB b : MvPolynomial (TV n' (m + 1)) (KK O))) 0
      rw [hFsB b]
      unfold symB toK
      rw [subst_SPtrue w F hF.2.1 hSet.1.even (by omega) hrk hg, ← map_mul]
      intro mm
      exact ⟨AddMonoidAlgebra.coeff _ mm, by rw [coeff_map, pow_zero, one_mul]⟩
    have h2 := (hΘ1.2 g hg e hbasis (FsB b) 0).1 h1
    rw [hΘeq]
    obtain ⟨z, hz, hze⟩ := mem_scale.1 h2
    rw [← hze]
    simpa using hz
  refine cloudBAt_of_rho hSet.1 Formalism.L2.G.Model.bePerfect r TT lam0 hdom c0 _ _ e he FsB Θ ?_
    (hR p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ e he htgt hm g hhm hg hbasis
      Θ hΘ)
  intro b s u hs hu
  exact edge_lattice_mul_of_weight_sum D (Formalism.L2.G.Model.products_sections_integral D) p ι σ w hw r (lambda_zero_eq_product TT lam0) (flW_dom _)
    (restW_dom (by omega) TT lam0 hdom) e hu (hFs b) hs

theorem restCloudB_of_rho (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (h : RestRho D CLa Ck Crk Cdeg) :
    RestCloudB D CLa Ck Crk Cdeg := by
  intro hA
  obtain ⟨CK, C₁, h1, h2, h3⟩ := h hA
  exact ⟨CK, C₁, h1, h2, fun C hC => cloudBStep_of_rho D C CK CLa (h3 C hC)⟩

end Formalism.MainNotions.TestSideCounting
end
end

section

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.Pf14

theorem rest6a (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : SourcePrimitiveIntegrality D CLa Ck Crk Cdeg :=
  source_integrality_of_substitution transStep substPol 1 one_pos (fun C _ => spStep C) D CLa Ck Crk Cdeg

end Formalism.MainNotions.TestSideCounting
end
end
