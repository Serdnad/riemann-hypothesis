module

public import ReciprocityTheory.DualLattices.Bundle017
public import ReciprocityTheory.DualLattices.Bundle001
public import ReciprocityTheory.DualLattices.Bundle027
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.DualLattices.InvolutionPermApplyZero
import ReciprocityTheory.DualLattices.Bundle016
public import ReciprocityTheory.DualLattices.HasLenLeOfSurj
public import ReciprocityTheory.DualLattices.Bundle028

@[expose] public section

section

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}

theorem btP_facts (hS : HodgeTateSetting p v R O σ cp) (H : HodgeTateDatum p g v R O σ cp) {m : ℕ} (e : Fin m → O)
    (π : Equiv.Perm (Fin m)) (horth : ∀ i j, e i * e j = if i = j then e i else 0)
    (hσ : ∀ i, σ (e i) = e (π i)) (hsT : (∑ i, H.ρ (e i)) + H.P = 1)
    (hPT : ∀ i, H.ρ (e i) * H.P = 0) (hsL : (∑ i, H.ρL (e i)) + H.PL = 1)
    (hPL : ∀ i, H.ρL (e i) * H.PL = 0) :
    (btP H e)ᵀ * H.Ht - H.Htᵀ * btP H e = cp • H.E.map (algebraMap ℤ_[p] R) ∧
    (∀ i, btP H e * (H.ρ (e i)).map (algebraMap ℤ_[p] R) = H.ρL (e i) * btP H e) ∧
    btP H e * H.P.map (algebraMap ℤ_[p] R) = H.PL * btP H e := by
  classical
  set F := (algebraMap ℤ_[p] R).mapMatrix (m := Ix g) with hF
  have hFa : ∀ M : Matrix (Ix g) (Ix g) ℤ_[p], M.map (algebraMap ℤ_[p] R) = F M := fun M => rfl
  have hFt : ∀ M : Matrix (Ix g) (Ix g) ℤ_[p], (F M)ᵀ = F Mᵀ := fun M => rfl
  let π2 := pi2 e π hσ
  have hπ2 : ∀ k, π2 (π2 k) = k := involutionPerm_involutive e π hσ horth hS.invol
  let εT : Fin (m + 1) → Matrix (Ix g) (Ix g) R :=
    Fin.lastCases (F H.P) (fun i => F (H.ρ (e i)))
  let εL : Fin (m + 1) → Matrix (Fin g) (Fin g) R :=
    Fin.lastCases H.PL (fun i => H.ρL (e i))
  let π' : Equiv.Perm (Fin (m + 1)) := finSuccEquivLast.symm.permCongr (Equiv.optionCongr π2)
  have hTc : ∀ i : Fin m, εT i.castSucc = F (H.ρ (e i)) := fun i => by simp [εT]
  have hTl : εT (Fin.last m) = F H.P := by simp [εT]
  have hLc : ∀ i : Fin m, εL i.castSucc = H.ρL (e i) := fun i => by simp [εL]
  have hLl : εL (Fin.last m) = H.PL := by simp [εL]
  have hπc : ∀ i : Fin m, π' i.castSucc = (π2 i).castSucc := fun i => by
    simp [π', Equiv.permCongr_apply]
  have hπl : π' (Fin.last m) = Fin.last m := by simp [π', Equiv.permCongr_apply]
  have hPρ : ∀ i, H.P * H.ρ (e i) = 0 := fun i => by rw [H.projectors.2.2.2.1, hPT]
  have hPLρ : ∀ i, H.PL * H.ρL (e i) = 0 := fun i => by rw [H.projectors.2.2.2.2, hPL]
  have h1 : ∀ i, π' (π' i) = i := by
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [hπl, hπl]
    · rw [hπc, hπc, hπ2]
  have h2 : ∀ i j, εT i * εT j = if i = j then εT i else 0 := by
    intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [hTl, ← map_mul, H.projectors.1, if_pos rfl]
    · rw [hTl, hTc, ← map_mul, hPρ, map_zero, if_neg (Fin.castSucc_lt_last j).ne']
    · rw [hTl, hTc, ← map_mul, hPT, map_zero, if_neg (Fin.castSucc_lt_last i).ne]
    · rw [hTc, hTc, ← map_mul, ← map_mul, horth]
      by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg hij, if_neg (fun h => hij (Fin.castSucc_injective _ h)), map_zero, map_zero]
  have h3 : ∑ i, εT i = 1 := by
    rw [Fin.sum_univ_castSucc]
    simp only [hTc, hTl]

    rw [← map_sum F (fun i => H.ρ (e i)), ← map_add (f := _), hsT, map_one]
  have h4 : ∀ i j, εL i * εL j = if i = j then εL i else 0 := by
    intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [hLl, H.projectors.2.1, if_pos rfl]
    · rw [hLl, hLc, hPLρ, if_neg (Fin.castSucc_lt_last j).ne']
    · rw [hLl, hLc, hPL, if_neg (Fin.castSucc_lt_last i).ne]
    · rw [hLc, hLc, ← map_mul, horth]
      by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg hij, if_neg (fun h => hij (Fin.castSucc_injective _ h)), map_zero]
  have h5 : ∑ i, εL i = 1 := by
    rw [Fin.sum_univ_castSucc]
    simp only [hLc, hLl]
    exact hsL
  have h6 : ∀ i, H.Ht * εT i = (εL (π' i))ᵀ * H.Ht := by
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [hTl, hπl, hLl, ← hFa, H.Ht_equivariant.2]
    · rw [hTc, hπc, hLc, ← hFa, H.Ht_equivariant.1, involutionPerm_sigma e π hσ i]
  have h7 : ∀ i, (εT i)ᵀ * H.E.map (algebraMap ℤ_[p] R) =
      H.E.map (algebraMap ℤ_[p] R) * εT (π' i) := by
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [hTl, hπl, hTl, hFa, hFt, ← map_mul, ← map_mul, H.projectors.2.2.1]
    · rw [hTc, hπc, hTc, hFa, hFt, ← map_mul, ← map_mul, H.E_equivariant, involutionPerm_sigma e π hσ i]
  have hu := u1 R g (m + 1) H.Ht H.Bt (H.E.map (algebraMap ℤ_[p] R)) cp εT εL π' h1 h2 h3 h4 h5
    h6 h7 H.form_eq_alt
  have hB : (∑ i, εL i * H.Bt * εT i) = btP H e := by
    rw [Fin.sum_univ_castSucc]
    simp only [hLc, hLl, hTc, hTl, btP, hFa]
  obtain ⟨hA, hC, -⟩ := hu
  rw [hB] at hA hC
  refine ⟨hA, fun i => ?_, ?_⟩
  · have := hC i.castSucc
    rw [hTc, hLc, ← hFa] at this
    exact this
  · have := hC (Fin.last m)
    rw [hTl, hLl, ← hFa] at this
    exact this

private lemma stdJ_form4 {D : Type} [CommRing D] {g : ℕ}
    (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) D) (i j : Fin g ⊕ Fin g) :
    (Mᵀ * stdJ D g * M) i j =
      ∑ a, (M (Sum.inr a) i * M (Sum.inl a) j - M (Sum.inl a) i * M (Sum.inr a) j) := by
  rw [Matrix.mul_assoc, Matrix.mul_apply, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Matrix.mul_apply, stdJ, Fintype.sum_sum_type, Matrix.one_apply] <;> ring

theorem phiP_J (hS : HodgeTateSetting p v R O σ cp) (H : HodgeTateDatum p g v R O σ cp) {m : ℕ} (e : Fin m → O)
    (π : Equiv.Perm (Fin m)) (horth : ∀ i j, e i * e j = if i = j then e i else 0)
    (hσ : ∀ i, σ (e i) = e (π i)) (hsT : (∑ i, H.ρ (e i)) + H.P = 1)
    (hPT : ∀ i, H.ρ (e i) * H.P = 0) (hsL : (∑ i, H.ρL (e i)) + H.PL = 1)
    (hPL : ∀ i, H.ρL (e i) * H.PL = 0) :
    (phiP H e)ᵀ * stdJ R g * phiP H e = cp • H.E.map (algebraMap ℤ_[p] R) := by
  obtain ⟨h1, -, -⟩ := btP_facts hS H e π horth hσ hsT hPT hsL hPL
  ext i j
  rw [stdJ_form4, ← h1, Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply,
    ← Finset.sum_sub_distrib]
  rfl

end ReciprocityTheory.PGsh.Up
end
end

section

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

theorem u7F3 : FrobeniusLengthBoundStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hp2 hS H U X D hdet hbasis τ N z hN hNsq hz
  have hv : v.Integers R := hS.integers
  have hinj : Function.Injective (algebraMap R C) := hv.hom_inj

  have hsqle : sqIdeal (augIdeal H.AA.carrier) ≤ augIdeal H.AA.carrier := by
    refine Submodule.span_le.mpr ?_
    rintro h ⟨f, hf, f', hf', rfl⟩
    rw [SetLike.mem_coe]
    obtain ⟨hfA, hf0⟩ := Submodule.mem_inf.1 hf
    obtain ⟨hfA', -⟩ := Submodule.mem_inf.1 hf'
    refine Submodule.mem_inf.2 ⟨H.AA.mul_mem f f' hfA hfA', ?_⟩
    rw [LinearMap.mem_ker] at hf0 ⊢
    simp only [LinearMap.proj_apply, Pi.mul_apply] at hf0 ⊢
    rw [hf0, zero_mul]

  have hkill : ∀ k, D.κ k ≠ τ → thetaQ U τ (H.φ ⟨xL D k, D.x_mem k⟩) = 0 := by
    intro k hk
    obtain ⟨l, hl⟩ := Submodule.Quotient.mk_surjective _ (H.φ ⟨xL D k, D.x_mem k⟩)
    have hg := phi_x_grade hS D k τ (Ne.symm hk) l hl.symm
    obtain ⟨w', hw'⟩ := (mem_pP _).1 hg
    rw [← hl]
    change redP (U.r τ) (thetaL U τ l) = 0
    have hl_sum : ∑ i, (U.εL i)ᵀ *ᵥ l = l := by
      funext j
      simp only [Finset.sum_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul]
      have h1 : ∀ k', ∑ i, U.εL i k' j = (1 : Matrix (Fin g) (Fin g) R) k' j := fun k' => by
        rw [← U.εL_sum, Matrix.sum_apply]
      simp [h1, Matrix.one_apply]
    have hθ : thetaL U τ l = (p : R) • thetaL U τ w' := by

      rw [← hl_sum, map_sum,
      Finset.sum_eq_single τ (fun i _ hi => theta_kill U hi l) (by simp), hw', map_smul]
    rw [hθ]
    exact redP_pP ((mem_pP _).2 ⟨_, rfl⟩)
  have hsx : ∀ d : Ix g → R,
      sumX D d = ∑ k, d k • (⟨xL D k, D.x_mem k⟩ : augIdeal H.AA.carrier) := by
    intro d
    apply Subtype.ext
    simp [sumX]
  let π : (blockL D τ ⧸ N.comap (blockL D τ).subtype) →ₗ[R]
      (Fin (U.r τ) → R ⧸ Ideal.span {(p : R)}) :=
    (N.comap (blockL D τ).subtype).liftQ
      (thetaQ U τ ∘ₗ H.φ ∘ₗ sumX D ∘ₗ (blockL D τ).subtype) (by
        intro c hc
        rw [Submodule.mem_comap, Submodule.subtype_apply] at hc
        obtain ⟨f, hf, hfc⟩ := hNsq _ hc
        obtain ⟨c', hc', hsub⟩ := sub_lin_mem_sq hv D hdet hbasis (hsqle hf)
        have hcc : c' = (c : Ix g → R) := funext fun k => hinj ((hc' k).trans (hfc k).symm)
        rw [hcc] at hsub
        have hmem : sumX D (c : Ix g → R) ∈ LinearMap.ker H.φ := by
          rw [H.cotangent_ker_eq, Submodule.mem_comap, Submodule.subtype_apply]
          have h2 := Submodule.sub_mem _ hf hsub
          rw [sub_sub_cancel] at h2
          simpa [sumX] using h2
        rw [LinearMap.mem_ker] at hmem ⊢
        simp only [LinearMap.comp_apply, Submodule.subtype_apply, hmem, map_zero])
  have hsurj : Function.Surjective π := by
    intro w
    obtain ⟨y, rfl⟩ := thetaQ_surj U τ w
    obtain ⟨f, rfl⟩ := H.cotangent_surjective y
    obtain ⟨c0, -, hsub0⟩ := sub_lin_mem_sq hv D hdet hbasis f.2
    let c : blockL D τ :=
      ⟨fun k => if D.κ k = τ then c0 k else 0, fun k hk => by simp [hk]⟩
    refine ⟨Submodule.Quotient.mk c, ?_⟩
    change thetaQ U τ (H.φ (sumX D (c : Ix g → R))) = thetaQ U τ (H.φ f)
    have hf0 : H.φ f = H.φ (sumX D c0) := by
      rw [← sub_eq_zero, ← map_sub]
      apply LinearMap.mem_ker.1
      rw [H.cotangent_ker_eq, Submodule.mem_comap, Submodule.subtype_apply]
      simpa [sumX] using hsub0
    rw [hf0]
    have hzero : thetaQ U τ (H.φ (sumX D (c0 - (c : Ix g → R)))) = 0 := by

      rw [hsx, map_sum, map_sum]
      apply Finset.sum_eq_zero
      intro k _
      rw [map_smul, map_smul]
      by_cases hk : D.κ k = τ
      · have hck : (c0 - (c : Ix g → R)) k = 0 := by simp [c, hk]
        rw [hck, zero_smul]
      · rw [hkill k hk, smul_zero]
    rw [map_sub, map_sub, map_sub, sub_eq_zero] at hzero
    exact hzero.symm
  exact hasLen_le_of_surj hv hz (p : R) (U.r τ) π hsurj

end ReciprocityTheory.PGsh.Up
end
end
