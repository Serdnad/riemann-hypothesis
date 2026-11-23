module

public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle100
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryAdjoinLatticeImageEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle101
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle014
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle137
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle147
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle352
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle150
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle572
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle374
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle416
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle241
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle324
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle567
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle568
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle417
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle367
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle570
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
public import Mathlib.Data.Nat.Choose.Dvd
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnHeckeEisensteinFourierTerm

@[expose] public section

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

theorem _root_.GlobalTheory.T.powerSeriesLinearCoefficients_mvPowerSeriesFormalLog : ∀ (Q : Type) [CommRing Q] [Algebra ℚ Q] (d : ℕ) (g : MvPowerSeries (Fin d) Q), constantCoeff g = 1 → ∀ i, lin (formalLog g) i = lin g i := by
  first | exact @GlobalTheory.FormalCalc.lin_formalLog | exact GlobalTheory.FormalCalc.lin_formalLog | (intros; apply GlobalTheory.FormalCalc.lin_formalLog <;> assumption)
end

section

open Polynomial Matrix GlobalTheory.LatOrb

theorem _root_.GlobalTheory.T.exists_unitary_adjoin_lattice_image_eq : ∀ {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Field K] [Algebra O K] [IsFractionRing O K]
    (n : ℕ) (P₀ : O[X]), IsCoprime P₀ (derivative P₀) →
    ∀ γ : Matrix (Fin n) (Fin n) K, γ.charpoly = P₀.map (algebraMap O K) →
    ∀ σ : K →+* K, (∀ x, σ (σ x) = x) → (∀ a : O, ∃ b : O, σ (algebraMap O K a) = algebraMap O K b) →
    (γ.map σ)ᵀ * γ = 1 →
    ∀ M : Submodule O (Fin n → K), IsLatV O M → (∀ v ∈ M, γ *ᵥ v ∈ M) →
    ∀ p : K[X], IsUnit (aeval γ p) → matLat O (((aeval γ p).map σ)ᵀ * aeval γ p) M = M →
    ∃ t : Matrix (Fin n) (Fin n) K, (t.map σ)ᵀ * t = 1 ∧ t * γ = γ * t ∧ matLat O t M = matLat O (aeval γ p) M := by
  first | exact @GlobalTheory.LatOrb.exists_unitary_matLat_eq | exact GlobalTheory.LatOrb.exists_unitary_matLat_eq | (intros; apply GlobalTheory.LatOrb.exists_unitary_matLat_eq <;> assumption)
end

section

open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model

noncomputable section

namespace GlobalTheory.HTRho

theorem finrank_ksSub_map_cls_eq_homO {k O H : Type*} [Field k] [AddCommGroup H] [Module k H]
    [FiniteDimensional k H] [Ring O] (σ : O →+* Module.End k H) (G Z : Submodule k H)
    (hG : ∀ a, ∀ x ∈ G, σ a x ∈ G) (hZ : ∀ a, ∀ x ∈ Z, σ a x ∈ Z) (hZG : Z ≤ G) :
    finrank k ((ksSub σ 0 G Z).map (cls G)) =
      finrank k (homO (qAct (rAct σ G hG) (Z.comap G.subtype) (fun a x hx => hZ a x hx))
        (qAct σ G hG)) := by
  set Zc := Z.comap G.subtype
  set hom := homO (qAct (rAct σ G hG) Zc (fun a x hx => hZ a x hx)) (qAct σ G hG)
  let Ψ : hom →ₗ[k] (G →ₗ[k] H ⧸ G) := (LinearMap.lcomp k (H ⧸ G) Zc.mkQ) ∘ₗ hom.subtype
  have hΨ : ∀ S : hom, Ψ S = (S : (G ⧸ Zc) →ₗ[k] H ⧸ G) ∘ₗ Zc.mkQ := fun S => rfl
  have inj : Function.Injective Ψ := by
    intro S S' h
    rw [hΨ, hΨ] at h
    exact Subtype.ext (LinearMap.ext fun q => by
      obtain ⟨x, rfl⟩ := Zc.mkQ_surjective q
      exact LinearMap.congr_fun h x)
  have hr : LinearMap.range Ψ = (ksSub σ 0 G Z).map (cls G) := by
    apply le_antisymm
    · rintro _ ⟨S, rfl⟩
      obtain ⟨G', hG'⟩ := Submodule.exists_isCompl G
      obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective G.mkQ (Submodule.range_mkQ G)
      have hs' : ∀ q, G.mkQ (s q) = q := fun q => LinearMap.congr_fun hs q
      let T : G →ₗ[k] H ⧸ G := Ψ S
      let f : H →ₗ[k] H := s ∘ₗ T ∘ₗ Submodule.linearProjOfIsCompl G G' hG'
      have hf : ∀ x (hx : x ∈ G), G.mkQ (f x) = (S : (G ⧸ Zc) →ₗ[k] H ⧸ G) (Zc.mkQ ⟨x, hx⟩) := by
        intro x hx
        have hp : Submodule.linearProjOfIsCompl G G' hG' x = ⟨x, hx⟩ :=
          Submodule.linearProjOfIsCompl_apply_left hG' ⟨x, hx⟩
        simp only [f, LinearMap.comp_apply, hp, hs']
        rfl
      refine ⟨f, ⟨?_, ?_, ?_⟩, ?_⟩
      · intro a x hx
        rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, sub_eq_zero]
        change G.mkQ (f (σ a x)) = G.mkQ (σ a (f x))
        rw [hf _ (hG a x hx), ← qAct_mk σ G hG, hf x hx]
        rw [← (mem_homO _ _ _).1 S.2 a]
        rfl
      · intro x hx
        rw [← Submodule.Quotient.mk_eq_zero]
        change G.mkQ (f x) = 0
        rw [hf x (hZG hx)]
        have : Zc.mkQ ⟨x, hZG hx⟩ = 0 := (Submodule.Quotient.mk_eq_zero _).2 hx
        rw [this, map_zero]
      · intro x _ y _
        simp
      · apply LinearMap.ext
        rintro ⟨x, hx⟩
        exact hf x hx
    · rintro _ ⟨f, hf, rfl⟩
      have hker : Zc ≤ LinearMap.ker (cls G f) := by
        intro x hx
        rw [LinearMap.mem_ker]
        exact (Submodule.Quotient.mk_eq_zero _).2 (hf.2.1 x hx)
      let S0 := Zc.liftQ (cls G f) hker
      have hS0 : S0 ∈ hom := by
        rw [mem_homO]
        intro a q
        obtain ⟨x, rfl⟩ := Zc.mkQ_surjective q
        change S0 (Zc.mkQ (rAct σ G hG a x)) = qAct σ G hG a (S0 (Zc.mkQ x))
        simp only [S0, Submodule.liftQ_mkQ]
        change G.mkQ (f (σ a x)) = G.mkQ (σ a (f x))
        rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hf.1 a x x.2
      refine ⟨⟨S0, hS0⟩, ?_⟩
      rw [hΨ]
      exact Submodule.liftQ_mkQ _ _ _
  rw [← hr, LinearMap.finrank_range_of_inj inj]

end GlobalTheory.HTRho
end
end

section

set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

namespace GlobalTheory.LawDer

open MvPowerSeries in
set_option autoImplicit false in
private lemma iterate_mul_eq_sum_antidiagonal_choose {A : Type} [CommRing A] (D : A → A)
    (hadd : ∀ a b, D (a + b) = D a + D b) (hmul : ∀ a b, D (a * b) = D a * b + a * D b) (n : ℕ)
    (a b : A) :
    D^[n] (a * b) = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, n.choose ij.1 • (D^[ij.1] a * D^[ij.2] b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsum : ∀ (s : Finset (ℕ × ℕ)) (f : ℕ × ℕ → A), D (∑ x ∈ s, f x) = ∑ x ∈ s, D (f x) :=
      fun s f => map_sum (AddMonoidHom.mk' D hadd) f s
    have hns : ∀ (m : ℕ) (x : A), D (m • x) = m • D x :=
      fun m x => map_nsmul (AddMonoidHom.mk' D hadd) m x
    have hc := Finset.sum_antidiagonal_choose_succ_nsmul (fun i j => D^[i] a * D^[j] b) n
    beta_reduce at hc
    rw [Function.iterate_succ_apply', ih, hsum, hc, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ij hij => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    rw [← Nat.choose_symm_of_eq_add hij.symm, hns, hmul, ← smul_add]
    simp only [Function.iterate_succ_apply']
    rw [add_comm]


open MvPowerSeries in
set_option autoImplicit false in
theorem _root_.GlobalTheory.LawDer.constantCoeff_iterate_invDer_mul : ∀ (p : ℕ) [Fact p.Prime] (R : Type)
    [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R),
    (∀ i, constantCoeff (μ i) = 0) →
    _root_.GlobalTheory.Katz.op μ (fun i => (X i : MvPowerSeries (Fin d) R)) (fun _ => 0) =
      (fun i => X i) →
    ∀ (u : Fin d → R) (F G : MvPowerSeries (Fin d) R), constantCoeff F = 0 → constantCoeff G = 0 →
      ∃ r : R, constantCoeff ((_root_.GlobalTheory.LawDer.invDer μ u)^[p] (F * G)) = p * r := by
  intro p hp R _ d μ hμ hid u F G hF hG
  have hlin := _root_.GlobalTheory.LawDer.Linear.invDer_linear R d μ hμ u

  rw [iterate_mul_eq_sum_antidiagonal_choose _ hlin.1
  (_root_.GlobalTheory.LawDer.invDer_mul R d μ hμ hid u), map_sum]
  refine Finset.dvd_sum fun ij hij => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
  rw [map_nsmul, map_mul, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos ij.1 with h1 | h1
  · rw [h1, Function.iterate_zero, id, hF]; simp
  rcases Nat.eq_zero_or_pos ij.2 with h2 | h2
  · rw [h2, Function.iterate_zero, id, hG]; simp
  have hdvd : p ∣ p.choose ij.1 := hp.out.dvd_choose_self h1.ne' (by omega)
  exact Dvd.dvd.mul_right (Nat.cast_dvd_cast hdvd) _

end GlobalTheory.LawDer
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

theorem _root_.GlobalTheory.T.invariantDerivationFormalGroupLaw_leibniz : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → op μ (fun i => (X i : MvPowerSeries (Fin d) R)) (fun _ => 0) = (fun i => X i) → ∀ (u : Fin d → R) (F G : MvPowerSeries (Fin d) R), invDer μ u (F * G) = invDer μ u F * G + F * invDer μ u G := by
  first | exact @GlobalTheory.LawDer.invDer_mul | exact GlobalTheory.LawDer.invDer_mul | (intros; apply GlobalTheory.LawDer.invDer_mul <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

namespace GlobalTheory.HerbrandAlg

theorem kerId : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a → ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)), (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) → ∀ τ : S, KernelIdentity v a Fil τ := by
  intro C _ v S _ _ a ha N Fil hF τ
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : lin a τ • x = 0 := hx
    show lin a τ • (Submodule.Quotient.mk x : (Fin N → RS a) ⧸ Fil) = 0
    rw [← Submodule.Quotient.mk_smul, hx', Submodule.Quotient.mk_zero]
  · ext x
    constructor
    · rintro ⟨hx, hk⟩
      have hx' : lin a τ • x = 0 := hx
      have hxF : x ∈ Fil := (Submodule.Quotient.mk_eq_zero Fil).1 hk
      refine ⟨⟨x, hxF⟩, ?_, rfl⟩
      show lin a τ • (⟨x, hxF⟩ : Fil) = 0
      exact Subtype.ext hx'
    · rintro ⟨⟨y, hy⟩, hy', rfl⟩
      have hy'' : lin a τ • (⟨y, hy⟩ : Fil) = 0 := hy'
      refine ⟨?_, ?_⟩
      · show lin a τ • y = 0
        exact congrArg Subtype.val hy''
      · show (Submodule.Quotient.mk y : (Fin N → RS a) ⧸ Fil) = 0
        exact (Submodule.Quotient.mk_eq_zero Fil).2 hy

theorem core : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a → ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)), (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) → ∀ τ : S, ∃ r : ℝ, (r : WithTop ℝ) = yExp v a Fil τ ∧ RelLen v ((eigSub a τ (Fin N → RS a)).map (comp a N τ)) ((preEig a Fil τ).map (comp a N τ)) r := by
  intro C _ v S _ _ a ha N Fil hF τ
  obtain ⟨r, hr, hR⟩ := GlobalTheory.T.relLength_filtrationInterKerCofactor_linearFactor C v S a ha N Fil hF τ
  obtain ⟨hd, hcP, hkerc, hsat, hAX, hHc, hcH, hprojX, hHX, hFX, htf, g, hg⟩ :=
    GlobalTheory.T.adjoinRootProdLinearFactors_lattice_facts C v S a ha N Fil hF τ
  obtain ⟨fF, fX, fK, fH, -, -, -⟩ := GlobalTheory.T.finite_eigenFiltration_pieces_addValInt C v S a ha N Fil hF τ
  have tfO : ∀ (c : Int0 v) (x : Fin N → Int0 v), c ≠ 0 → c • x = 0 → x = 0 := by
    intro c x hc h
    funext i
    have := congrFun h i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_eq_zero] at this
    exact this.resolve_left hc
  have hKF : filKer a Fil τ ≤ Fil.restrictScalars (Int0 v) := inf_le_left
  have fKs : Module.Finite (Int0 v) ↥(eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ) := by
    rw [Module.Finite.iff_fg] at fH fK ⊢
    exact fH.sup fK
  have hle : eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ ≤ preEig a Fil τ :=
    sup_le hHX (hKF.trans hFX)
  have hA : preEig a Fil τ ⊓ LinearMap.ker (mulR a N (lin a τ)) ≤
      eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ := fun x hx =>
    Submodule.mem_sup_left (LinearMap.mem_ker.1 hx.2)
  have hmapH : (eigSub a τ (Fin N → RS a)).map (mulR a N (lin a τ)) = ⊥ :=
    eq_bot_iff.2 (by rintro _ ⟨x, hx, rfl⟩; exact (Submodule.mem_bot _).2 hx)
  have e1 : (eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ).map (mulR a N (lin a τ)) =
      (filKer a Fil τ).map (mulR a N (lin a τ)) := by
    rw [Submodule.map_sup, hmapH, bot_sup_eq]
  have s1 : RelLen v (eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ) (preEig a Fil τ) r :=
    (GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htf htf (mulR a N (lin a τ)) _ _ hle hA fX fKs r).2 (by rw [e1, hAX]; exact hR)
  have hC : preEig a Fil τ ⊓ LinearMap.ker (comp a N τ) ≤
      eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ := fun x hx =>
    Submodule.mem_sup_right ⟨hsat hx, LinearMap.mem_ker.2 ((hcP x).1 (LinearMap.mem_ker.1 hx.2))⟩
  have s2 := (GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htf tfO (comp a N τ) _ _ hle hC fX fKs r).1 s1
  have hK0 : (filKer a Fil τ).map (comp a N τ) = ⊥ :=
    eq_bot_iff.2 (by
      rintro _ ⟨x, hx, rfl⟩
      exact (Submodule.mem_bot _).2 ((hcP x).2 (LinearMap.mem_ker.1 hx.2)))
  have e2 : (eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ).map (comp a N τ) =
      (eigSub a τ (Fin N → RS a)).map (comp a N τ) := by
    rw [Submodule.map_sup, hK0, sup_bot_eq]
  exact ⟨r, hr, e2 ▸ s2⟩

theorem herbrandDet : HerbrandDet := by
  intro C _ v S _ _ a ha N Fil hF τ
  obtain ⟨r, hr, hR⟩ := core C v S a ha N Fil hF τ
  exact ⟨GlobalTheory.T.herbrand_determinant_identity_of_relativeLength C v S a ha N Fil hF τ r hr hR, kerId C v S a ha N Fil hF τ,
    GlobalTheory.T.herbrand_lengthIdentities_of_relativeLength C v S a ha N Fil hF τ r hr hR⟩

end GlobalTheory.HerbrandAlg
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

theorem _root_.GlobalTheory.T.heckeWeightTwoContinuation_eq_latticeSeries : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (Zb : ℂ → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta (ClassGroup.mk F 𝔟)⁻¹ Zb → ∀ σ : ℂ, 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 2 σ z) ∧ GlobalTheory.HeckeTwo.gFun Zb 𝔞 𝔟 σ z = GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisSum 𝔞 𝔟 2 σ z := by
  first | exact @GlobalTheory.HeckeTwoEq.gFun_eq_eisSum | exact GlobalTheory.HeckeTwoEq.gFun_eq_eisSum | (intros; apply GlobalTheory.HeckeTwoEq.gFun_eq_eisSum <;> assumption)
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwo.TermBound

theorem factorSmooth (σ : ℂ) (hσ : σ ∈ halfPlane) (ν β : ℝ) (hβ : β ≠ 0) :
    ContDiffOn ℝ ∞ (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * ((ν * β * w.re : ℝ) : ℂ)) *
      hTrans σ ν (β * w.im)) {w : ℂ | 0 < w.im} := by
  have hre : ContDiff ℝ ∞ (fun w : ℂ => ((ν * β * w.re : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.mul Complex.reCLM.contDiff)
  have h1 : ContDiff ℝ ∞ (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * ((ν * β * w.re : ℝ) : ℂ))) :=
    Complex.contDiff_exp.comp (contDiff_const.mul hre)
  have h2 : ContDiffOn ℝ ∞ (fun w : ℂ => hTrans σ ν (β * w.im)) {w : ℂ | 0 < w.im} := by
    refine (GlobalTheory.HeckeTwo.TermSmooth.contDiffOn_hTrans σ hσ ν).comp
      (contDiff_const.mul Complex.imCLM.contDiff : ContDiff ℝ ∞ fun w : ℂ => β * w.im).contDiffOn ?_
    intro w hw; exact mul_ne_zero hβ (ne_of_gt hw)
  exact h1.contDiffOn.mul h2

theorem fTerm_iteratedFDeriv_bound : ∀ (F : Type) [Field F] [NumberField F] (K : Set ℂ), IsCompact K → K ⊆ halfPlane →
    ∀ L : Set (Emb F → ℂ), IsCompact L → L ⊆ upperHalf F → ∀ n : ℕ, ∃ m : ℕ, ∀ N : ℕ, ∃ C : ℝ,
      ∀ σ ∈ K, ∀ z ∈ L, ∀ b ν : F, b ≠ 0 → ν ≠ 0 →
        ‖iteratedFDeriv ℝ n (fun z : Emb F → ℂ => fTerm σ z b ν) z‖ ≤
          C * ∏ τ : Emb F, (|τ b| + |τ b|⁻¹) ^ m / (1 + |τ ν * τ b|) ^ N := by
  intro F _ _ K hK hKH L hL hLH n
  obtain ⟨c, c', hc, hcc⟩ := GlobalTheory.T.exists_im_bounds_of_isCompact_upperHalfPlane (Emb F) L hL (fun z hz τ => hLH hz τ)
  have hfb := GlobalTheory.T.norm_iteratedFDeriv_heckeFourierFactor_le (GlobalTheory.T.iteratedDeriv_heckePhiFourierTransform_bound GlobalTheory.T.iteratedDeriv_heckePhiFourierTransform_repr GlobalTheory.T.heckeYDerivativeTermIntegral_polynomial_decay) K hK hKH c c' hc
  choose mk hmk using hfb
  refine ⟨(Finset.range (n + 1)).sup mk, fun N => ?_⟩
  choose Ck hCk using fun k => hmk k N
  refine ⟨n.factorial * (∑ k ∈ Finset.range (n + 1), max (Ck k) 0) ^ Fintype.card (Emb F), ?_⟩
  intro σ hσ z hz b ν hb hν
  have hσH : σ ∈ halfPlane := hKH hσ
  set m := (Finset.range (n + 1)).sup mk with hm
  set C0 := ∑ k ∈ Finset.range (n + 1), max (Ck k) 0 with hC0
  set g : Emb F → ℂ → ℂ := fun τ w => Complex.exp (2 * (Real.pi : ℂ) * I * ((τ ν * τ b * w.re : ℝ) : ℂ)) *
    hTrans σ (τ ν) (τ b * w.im) with hg
  have hfun : (fun z : Emb F → ℂ => fTerm σ z b ν) = fun z => ∏ τ, g τ (z τ) := rfl
  have hτb : ∀ τ : Emb F, τ b ≠ 0 := fun τ => (map_ne_zero τ).2 hb
  have hτν : ∀ τ : Emb F, τ ν ≠ 0 := fun τ => (map_ne_zero τ).2 hν
  have hsm : ∀ τ, ContDiffOn ℝ ∞ (g τ) {w : ℂ | 0 < w.im} := fun τ => factorSmooth σ hσH (τ ν) (τ b) (hτb τ)
  have hopen : ∀ τ : Emb F, IsOpen {w : ℂ | 0 < w.im} := fun _ => isOpen_lt continuous_const Complex.continuous_im
  rw [hfun]
  refine (GlobalTheory.T.norm_iteratedFDeriv_prod_coord_le_leibniz (Emb F) g (fun _ => {w : ℂ | 0 < w.im}) hopen hsm z (fun τ => hLH hz τ) n).trans ?_
  have hfac : ∀ τ, ∑ k ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ k (g τ) (z τ)‖ ≤
      C0 * ((|τ b| + |τ b|⁻¹) ^ m / (1 + |τ ν * τ b|) ^ N) := by
    intro τ
    rw [hC0, Finset.sum_mul]
    refine Finset.sum_le_sum fun k hk => ?_
    have h1 := hCk k σ hσ (τ ν) (τ b) (hτν τ) (hτb τ) (z τ) (hcc z hz τ).1 (hcc z hz τ).2
    have hB1 : (1 : ℝ) ≤ |τ b| + |τ b|⁻¹ := by
      have hp : 0 < |τ b| := abs_pos.2 (hτb τ)
      rcases le_total 1 |τ b| with h | h
      · linarith [inv_pos.2 hp]
      · have : 1 ≤ |τ b|⁻¹ := (one_le_inv₀ hp).2 h
        linarith
    have hmk' : mk k ≤ m := Finset.le_sup hk
    have hpow : (|τ b| + |τ b|⁻¹) ^ mk k ≤ (|τ b| + |τ b|⁻¹) ^ m := pow_le_pow_right₀ hB1 hmk'
    have hden : 0 < (1 + |τ ν * τ b|) ^ N := by positivity
    calc ‖iteratedFDeriv ℝ k (g τ) (z τ)‖ ≤ Ck k * (|τ b| + |τ b|⁻¹) ^ mk k / (1 + |τ ν * τ b|) ^ N := h1
      _ ≤ max (Ck k) 0 * ((|τ b| + |τ b|⁻¹) ^ m / (1 + |τ ν * τ b|) ^ N) := by
        rw [mul_div_assoc]
        exact mul_le_mul (le_max_left _ _) (div_le_div_of_nonneg_right hpow hden.le) (by positivity)
          (le_max_right _ _)
  calc (n.factorial : ℝ) * ∏ τ, ∑ k ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ k (g τ) (z τ)‖
      ≤ n.factorial * ∏ τ : Emb F, (C0 * ((|τ b| + |τ b|⁻¹) ^ m / (1 + |τ ν * τ b|) ^ N)) := by
        exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun τ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
          (fun τ _ => hfac τ)) (by positivity)
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]; ring

end GlobalTheory.HeckeTwo.TermBound
end
end

section

open GlobalTheory.UnitLemma Polynomial Matrix

theorem _root_.GlobalTheory.T.exists_isModel_of_unitary_charpoly_eq : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (γ : Matrix (Fin n) (Fin n) K.E), (γ.map K.c)ᵀ * γ = 1 → B.g * B.σ B.g = 1 → B.P.Separable → γ.charpoly = B.P → ∃ (x : B.Aˣ) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), GlobalTheory.InertUnitOrb.IsModel B γ x ψ := by
  first | exact @GlobalTheory.InertUnitOrb.exists_isModel_of_unitary | exact GlobalTheory.InertUnitOrb.exists_isModel_of_unitary | (intros; apply GlobalTheory.InertUnitOrb.exists_isModel_of_unitary <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SecGlue

theorem lifts_corrected_agree_on_overlaps : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (κ : Type) [Finite κ] (f : κ → R), Ideal.span (Set.range f) = ⊤ → ∀ V : κ → X.left.Opens, (∀ k, IsAffineOpen (V k)) →
    (∀ k, GlobalTheory.SecLift.LiftIn π X g₀ (f k) (V k)) →
    ∃ e : ∀ k, Sp (Localization.Away (f k)) ⟶ X.left,
      (∀ k, e k ≫ X.hom = spMap (algebraMap R (Localization.Away (f k)))) ∧
      (∀ k, spMap (Localization.awayMap π (f k)) ≫ e k = spMap (algebraMap R₀ (Localization.Away (π (f k)))) ≫ g₀) ∧
      ∀ j k, spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f k)) (f j) (f k)) ≫ e j =
        spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f k)) (f k) (f j)) ≫ e k := by
  intro R R₀ _ _ π hπ hI X hX g₀ hg₀ κ _ f hf V hV hL
  classical
  have : Fintype κ := Fintype.ofFinite κ
  choose e he1 he2 he3 using hL
  choose N₀ hN₀ using fun k j => GlobalTheory.T.exists_squareZeroLift_basicOpen_pair_agree R R₀ π hπ hI X hX g₀ hg₀ (f j) (f k) (V j) (hV j) (e j) (he1 j) (he2 j) (he3 j) (e k) (he1 k) (he2 k)
  have hN : ∀ k j, N₀ k j ≤ Finset.univ.sup (fun p : κ × κ => N₀ p.1 p.2) := fun k j =>
    Finset.le_sup (f := fun p : κ × κ => N₀ p.1 p.2) (Finset.mem_univ (k, j))
  choose t ht1 ht2 ht3 ht4 using fun k j => hN₀ k j _ (hN k j)
  choose n s W hs hW hWl using fun j l => GlobalTheory.T.exists_basicOpen_cover_affineOpen_spec _ _ (spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l)) ≫ e j)
  obtain ⟨M, t', h1, h2, h3, h4⟩ := GlobalTheory.T.exists_pow_cocycle_alt R R₀ π hπ hI X hX g₀ hg₀ κ f V hV e he1 he2 he3 _ t ht1 ht2 ht3 ht4 n s W hs hW hWl
  exact GlobalTheory.T.exists_lifts_agree_of_cocycle_alt R R₀ π hπ hI X g₀ hg₀ κ f hf V hV e he1 he2 he3 _ t' h1 h2 h3 n s W hs hW hWl h4

end GlobalTheory.SecGlue
end

section

open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc

theorem _root_.GlobalTheory.T.exists_end_lattice_trace_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), 1 ≤ r → SelfDualLat G Λ → ∃ Z ∈ endLat Λ, Z.trace = 1 := by
  first | exact @GlobalTheory.LieDisc.exists_endLat_trace_eq_one | exact GlobalTheory.LieDisc.exists_endLat_trace_eq_one | (intros; apply GlobalTheory.LieDisc.exists_endLat_trace_eq_one <;> assumption)
end

section

open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc

theorem _root_.GlobalTheory.T.hermitian_adjoint_mem_end_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Y : Matrix (Fin r) (Fin r) E), SelfDualLat G Λ → Y ∈ endLat Λ → hAdj G Y ∈ endLat Λ := by
  first | exact @GlobalTheory.LieDisc.hAdj_mem_endLat_main | exact GlobalTheory.LieDisc.hAdj_mem_endLat_main | (intros; apply GlobalTheory.LieDisc.hAdj_mem_endLat_main <;> assumption)
end
