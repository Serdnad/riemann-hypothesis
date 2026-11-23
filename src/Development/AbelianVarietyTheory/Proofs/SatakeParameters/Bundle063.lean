module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle014
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MapMulVecMemOfMemSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle236
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle003
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle002
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle252
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle059
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle060
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle061
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle025
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

section

open NumberField
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open scoped TensorProduct

namespace GlobalTheory.GoodPrime

theorem schur (tr nm : ℤ) (M : ℕ) (hM : 0 < M) :
    ∃ p : ℕ, p.Prime ∧ ¬ p ∣ M ∧ ∃ r : ℤ, (p : ℤ) ∣ r ^ 2 - tr * r + nm := by
  by_cases hnm : nm = 0
  · obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (n := M + 1) (by omega)
    refine ⟨p, hp, fun h => hp.one_lt.ne' ?_, 0, by simp [hnm]⟩
    exact Nat.dvd_one.1 ((Nat.dvd_add_right h).1 hpd)
  · set t : ℤ := |tr| + 3
    set g : ℤ := (M : ℤ) ^ 2 * nm * t ^ 2 - tr * M * t + 1
    have ht : 3 ≤ t := by have := abs_nonneg tr; omega
    have hMz : (1 : ℤ) ≤ M := by exact_mod_cast hM
    have hnm1 : 1 ≤ |nm| := Int.one_le_abs hnm
    have hg : 2 ≤ |g| := by
      have h1 : |(M : ℤ) ^ 2 * nm * t ^ 2| = (M : ℤ) ^ 2 * |nm| * t ^ 2 := by
        rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_of_pos (by omega : (0:ℤ) < M), abs_of_pos (by omega : (0:ℤ) < t)]
      have h2 : |tr * M * t| = |tr| * M * t := by
        rw [abs_mul, abs_mul, abs_of_pos (by omega : (0:ℤ) < M), abs_of_pos (by omega : (0:ℤ) < t)]
      have h3 : |(M : ℤ) ^ 2 * nm * t ^ 2| ≤ |g| + |tr * M * t| + 1 := by
        have : (M : ℤ) ^ 2 * nm * t ^ 2 = g + tr * M * t - 1 := by simp only [g]; ring
        rw [this]
        calc |g + tr * M * t - 1| ≤ |g + tr * M * t| + |(1:ℤ)| := abs_sub _ _
          _ ≤ |g| + |tr * M * t| + 1 := by simpa using abs_add_le g (tr * M * t)
      rw [h1, h2] at h3
      have hat : |tr| = t - 3 := by simp only [t]; ring
      rw [hat] at h3
      have hMt : 3 ≤ (M : ℤ) * t := by nlinarith
      have hk : (M : ℤ) ^ 2 * t ^ 2 ≤ (M : ℤ) ^ 2 * |nm| * t ^ 2 := by
        have := mul_le_mul_of_nonneg_right hnm1 (by positivity : (0:ℤ) ≤ (M : ℤ) ^ 2 * t ^ 2)
        linarith
      have hq : 3 ≤ t * ((M : ℤ) - 1) + 3 := by nlinarith
      have hr : 9 ≤ ((M : ℤ) * t) * (t * ((M : ℤ) - 1) + 3) := by nlinarith
      have e : ((M : ℤ) * t) * (t * ((M : ℤ) - 1) + 3) = (M : ℤ) ^ 2 * t ^ 2 - (t - 3) * M * t := by ring
      linarith
    have hg' : (2 : ℤ) ≤ (g.natAbs : ℤ) := by rw [← Int.abs_eq_natAbs]; exact hg
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (n := g.natAbs) (by omega)
    have hpg : (p : ℤ) ∣ g := Int.natCast_dvd.2 hpd
    refine ⟨p, hp, fun h => hp.one_lt.ne' ?_, M * nm * t, ?_⟩
    · have hpM : (p : ℤ) ∣ M := Int.natCast_dvd_natCast.2 h
      have : (p : ℤ) ∣ g - M * (M * nm * t ^ 2 - tr * t) := dvd_sub hpg (dvd_mul_of_dvd_left hpM _)
      have e : g - M * (M * nm * t ^ 2 - tr * t) = 1 := by simp only [g]; ring
      rw [e] at this
      exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this
    · have e : ((M : ℤ) * nm * t) ^ 2 - tr * (M * nm * t) + nm = nm * g := by simp only [g]; ring
      rw [e]; exact dvd_mul_of_dvd_right hpg _

theorem exists_datum (G : GDatum) (N : ℕ) (hN : 0 < N) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (D : Datum p), N.Coprime p ∧ D.toG = G := by
  haveI := G.freeLa; haveI := G.finLa
  obtain ⟨e, he, hperf⟩ := GlobalTheory.T.bilinForm_injective_exists_nsmul_mem_range G.La G.EF G.nondeg
  obtain ⟨M, hM, hsplit⟩ := GlobalTheory.T.harrisTaylorOrder_split_almost_all_primes G
  have hd : 0 < (G.tr ^ 2 - 4 * G.nm).natAbs := Int.natAbs_pos.2 (ne_of_lt G.disc_neg)
  obtain ⟨p, hp, hpM, r, hr⟩ := schur G.tr G.nm (N * e * M * (G.tr ^ 2 - 4 * G.nm).natAbs) (by positivity)
  haveI : Fact p.Prime := ⟨hp⟩
  have hN' : ¬ p ∣ N := fun h => hpM (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right h _) _) _)
  have he' : ¬ p ∣ e := fun h => hpM (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left h _) _) _)
  have hM' : ¬ p ∣ M := fun h => hpM (Dvd.dvd.mul_right (Dvd.dvd.mul_left h _) _)
  have hd' : ¬ (p : ℤ) ∣ G.tr ^ 2 - 4 * G.nm := fun h => hpM (Dvd.dvd.mul_left (Int.natCast_dvd.1 h) _)
  refine ⟨p, inferInstance,
    { F := G.F, fld := G.fld, nf := G.nf, cm := G.cm, bar := G.bar, bar_eq := G.bar_eq, ω := G.ω,
      tr := G.tr, nm := G.nm, tr_eq := G.tr_eq, nm_eq := G.nm_eq, disc_neg := G.disc_neg, disc_p := hd',
      split := ⟨r, hr⟩, O := G.O, rng := G.rng, alg := G.alg, freeO := G.freeO, finO := G.finO,
      m := G.m, m_pos := G.m_pos, rankO := G.rankO, central := G.central, star := G.star,
      star_star := G.star_star, star_F := G.star_F, splitP := hsplit p hM', La := G.La, acg := G.acg,
      modO := G.modO, freeLa := G.freeLa, finLa := G.finLa, n := G.n, n_pos := G.n_pos, rankLa := G.rankLa,
      EF := G.EF, alt := G.alt, nondeg := G.nondeg,
      perfP := ⟨e, Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).2 he'), hperf⟩,
      adj := G.adj, a := G.a, ρc := G.ρc, ρc_root := G.ρc_root, tau := G.tau, tau_ω := G.tau_ω,
      dom := G.dom },
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).2 hN'), rfl⟩

end GlobalTheory.GoodPrime
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ParahoricSph

open Matrix

section Contract

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

lemma rid_lTensor_map (φ : W →ₗ[ℂ] ℂ) (A : V →ₗ[ℂ] V) (B : W →ₗ[ℂ] W) (y : V ⊗[ℂ] W) :
    TensorProduct.rid ℂ V (φ.lTensor V (TensorProduct.map A B y)) =
      A (TensorProduct.rid ℂ V ((φ ∘ₗ B).lTensor V y)) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v w => simp
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

lemma lid_rTensor_map (ψ : V →ₗ[ℂ] ℂ) (A : V →ₗ[ℂ] V) (B : W →ₗ[ℂ] W) (y : V ⊗[ℂ] W) :
    TensorProduct.lid ℂ W (ψ.rTensor W (TensorProduct.map A B y)) =
      B (TensorProduct.lid ℂ W ((ψ ∘ₗ A).rTensor W y)) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v w => simp
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

lemma exists_rid_ne_zero {x : V ⊗[ℂ] W} (hx : x ≠ 0) :
    ∃ φ : W →ₗ[ℂ] ℂ, TensorProduct.rid ℂ V (φ.lTensor V x) ≠ 0 := by
  classical
  let b := Module.Free.chooseBasis ℂ W
  let e := TensorProduct.equivFinsuppOfBasisRight (M := V) b
  have he : e x ≠ 0 := by
    intro h; exact hx (e.injective (by rw [h, map_zero]))
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp he
  refine ⟨b.coord i, ?_⟩
  have key : ∀ w : V ⊗[ℂ] W, TensorProduct.rid ℂ V ((b.coord i).lTensor V w) = e w i := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul v y => simp [e, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
    | add y z hy hz => simp only [map_add (f := _), hy, hz, Finsupp.add_apply]
  rw [key]; simpa using hi

lemma exists_lid_ne_zero {x : V ⊗[ℂ] W} (hx : x ≠ 0) :
    ∃ ψ : V →ₗ[ℂ] ℂ, TensorProduct.lid ℂ W (ψ.rTensor W x) ≠ 0 := by
  have hc : TensorProduct.comm ℂ V W x ≠ 0 := fun h =>
    hx ((TensorProduct.comm ℂ V W).injective (by rw [h, map_zero]))
  obtain ⟨ψ, hψ⟩ := exists_rid_ne_zero hc
  refine ⟨ψ, ?_⟩
  have key : ∀ y : V ⊗[ℂ] W, TensorProduct.lid ℂ W (ψ.rTensor W y) =
      TensorProduct.rid ℂ W (ψ.lTensor W (TensorProduct.comm ℂ V W y)) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v w => simp
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  rw [key]; exact hψ

end Contract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valuation_det_of_mem_KO {n : Type} [Fintype n] [DecidableEq n] {g : GL n k}
    (hg : g ∈ KO k n) : valuation k ((GeneralLinearGroup.det g : kˣ) : k) = 1 := by
  obtain ⟨g, rfl⟩ := hg
  have h1 : ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap 𝒪[k] k) g) : kˣ) : k) =
      algebraMap 𝒪[k] k (GeneralLinearGroup.det g : 𝒪[k]ˣ) :=
    ((algebraMap 𝒪[k] k).map_det _).symm
  rw [h1]
  exact (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _)

theorem emb₂_mem_KO {r t : ℕ} {m₁ : GL (Fin r) k} {m₂ : GL (Fin t) k} (h₁ : m₁ ∈ KO k (Fin r))
    (h₂ : m₂ ∈ KO k (Fin t)) :
    emb₂ k (stdSum (rfl : r + t = r + t)) (m₁, m₂) ∈ KO k (Fin (r + t)) := by
  obtain ⟨g₁, rfl⟩ := h₁
  obtain ⟨g₂, rfl⟩ := h₂
  refine ⟨emb₂ 𝒪[k] (stdSum (rfl : r + t = r + t)) (g₁, g₂), ?_⟩
  ext i j
  obtain ⟨i, rfl⟩ := (stdSum (rfl : r + t = r + t)).surjective i
  obtain ⟨j, rfl⟩ := (stdSum (rfl : r + t = r + t)).surjective j
  have hv := val_emb₂ 𝒪[k] (stdSum (rfl : r + t = r + t)) (g₁, g₂)
  have hw := val_emb₂ k (stdSum (rfl : r + t = r + t)) (GeneralLinearGroup.map (algebraMap 𝒪[k] k) g₁, GeneralLinearGroup.map (algebraMap 𝒪[k] k) g₂)
  show algebraMap 𝒪[k] k ((emb₂ 𝒪[k] (stdSum (rfl : r + t = r + t)) (g₁, g₂)).val _ _) = _
  rw [hv, hw]
  rcases i with i | i <;> rcases j with j | j <;> simp [GeneralLinearGroup.map]

theorem extTensor_apply_eq {r t : ℕ} {χ : kˣ →* ℂˣ} {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {σ₁ : Representation ℂ (GL (Fin r) k) V}
    {σ₂ : Representation ℂ (GL (Fin t) k) W} {f : _} (hf : IsParahoricVec χ (prod₂ σ₁ σ₂) f)
    {m₁ : GL (Fin r) k} {m₂ : GL (Fin t) k} (h₁ : m₁ ∈ KO k (Fin r)) (h₂ : m₂ ∈ KO k (Fin t)) :
    extTensor σ₁ σ₂ (m₁, m₂) (f.1.1 1) = (χ (GeneralLinearGroup.det m₂) : ℂ) • f.1.1 1 := by
  have hmem := emb₂_mem_KO h₁ h₂
  have hv := val_emb₂ k (stdSum (rfl : r + t = r + t)) (m₁, m₂)
  have hll : ∀ (i : Fin t) (j : Fin r),
      valuation k ((emb₂ k (stdSum (rfl : r + t = r + t)) (m₁, m₂)).val (Fin.natAdd r i) (Fin.castAdd t j)) < 1 := by
    intro i j
    have h0 : (emb₂ k (stdSum (rfl : r + t = r + t)) (m₁, m₂)).val (Fin.natAdd r i) (Fin.castAdd t j) = 0 := by
      have hi : Fin.natAdd r i = (stdSum (rfl : r + t = r + t)) (Sum.inr i) := by ext; simp
      have hj : Fin.castAdd t j = (stdSum (rfl : r + t = r + t)) (Sum.inl j) := by ext; simp
      rw [hv, hi, hj]
      simp
    rw [h0, map_zero]
    exact zero_lt_one
  have hdet : ((GeneralLinearGroup.det m₂ : kˣ) : k) =
      ((emb₂ k (stdSum (rfl : r + t = r + t)) (m₁, m₂)).val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det := by
    have hs : (emb₂ k (stdSum (rfl : r + t = r + t)) (m₁, m₂)).val.submatrix (Fin.natAdd r) (Fin.natAdd r) = m₂.val := by
      ext i j
      have hi : Fin.natAdd r i = (stdSum (rfl : r + t = r + t)) (Sum.inr i) := by ext; simp
      have hj : Fin.natAdd r j = (stdSum (rfl : r + t = r + t)) (Sum.inr j) := by ext; simp
      rw [submatrix_apply, hv, hi, hj]
      simp
    rw [hs]
    rfl
  have H := congrArg (fun F => F.1.1 (1 : GL (Fin (r + t)) k)) (hf _ hmem hll _ hdet)
  let p : parab k (two (stdSum (rfl : r + t = r + t))) := ⟨leviEmb k (two (stdSum (rfl : r + t = r + t))) (leviTwo k (Fin r) (Fin t) (m₁, m₂)),
    leviEmb_mem_parab k (two (stdSum (rfl : r + t = r + t))) _⟩
  have H2 := parInd_law (two (stdSum (rfl : r + t = r + t)))
    ((extTensor σ₁ σ₂).comp (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) f p 1
  have hδ : (deltaHalf k (Two (Fin r) (Fin t)) (leviTwo k (Fin r) (Fin t) (m₁, m₂)) : ℂ) = 1 := by
    rw [deltaHalf_two, isUnram_absPow k _ _ (valuation_det_of_mem_KO h₁),
      isUnram_absPow k _ _ (valuation_det_of_mem_KO h₂), mul_one, Units.val_one]
  rw [leviProj_leviEmb, hδ, one_smul] at H2
  have E1 : f.1.1 ((p : GL (Fin (r + t)) k) * 1) = f.1.1 (1 * emb₂ k (stdSum (rfl : r + t = r + t)) (m₁, m₂)) := by
    rw [mul_one, one_mul]; rfl
  rw [E1] at H2
  change f.1.1 (1 * emb₂ k (stdSum (rfl : r + t = r + t)) (m₁, m₂)) = (χ _ : ℂ) • f.1.1 1 at H
  rw [H] at H2
  rw [H2]
  simp

theorem isSpherical_of_isParahoricVec : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (W : Type) [AddCommGroup W] [Module ℂ W] (σ₁ : Representation ℂ (GL (Fin r) k) V)
    (σ₂ : Representation ℂ (GL (Fin t) k) W) (f : _), IsParahoricVec χ (prod₂ σ₁ σ₂) f →
    f.1.1 1 ≠ 0 → IsSpherical σ₁ ∧ IsSpherical (twist σ₂ (detChar (Fin t) χ⁻¹)) := by
  intro k _ _ _ _ r t χ V _ _ W _ _ σ₁ σ₂ f hf h0
  constructor
  · obtain ⟨φ, hφ⟩ := exists_rid_ne_zero h0
    refine (Submodule.ne_bot_iff _).2 ⟨_, ?_, hφ⟩
    rintro ⟨m, hm⟩
    have H := extTensor_apply_eq hf hm (one_mem (KO k (Fin t)))
    change TensorProduct.map (σ₁ m) (σ₂ 1) (f.1.1 1) = _ at H
    show σ₁ m _ = ((1 : KO k (Fin r) →* ℂˣ) ⟨m, hm⟩ : ℂ) • _
    rw [MonoidHom.one_apply, Units.val_one, one_smul]
    have H' := congrArg (fun y => TensorProduct.rid ℂ V (φ.lTensor V y)) H
    rw [rid_lTensor_map] at H'
    simpa [Module.End.one_eq_id] using H'
  · obtain ⟨ψ, hψ⟩ := exists_lid_ne_zero h0
    refine (Submodule.ne_bot_iff _).2 ⟨_, ?_, hψ⟩
    rintro ⟨m, hm⟩
    have H := extTensor_apply_eq hf (one_mem (KO k (Fin r))) hm
    change TensorProduct.map (σ₁ 1) (σ₂ m) (f.1.1 1) = _ at H
    show twist σ₂ (detChar (Fin t) χ⁻¹) m _ = ((1 : KO k (Fin t) →* ℂˣ) ⟨m, hm⟩ : ℂ) • _
    rw [MonoidHom.one_apply, Units.val_one, one_smul, twist_apply]
    have H' := congrArg (fun y => TensorProduct.lid ℂ W (ψ.rTensor W y)) H
    rw [lid_rTensor_map] at H'
    simp [Module.End.one_eq_id] at H'
    rw [H', smul_smul, ← Units.val_mul]
    simp

end GlobalTheory.ParahoricSph
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.automorphicRep_eq_of_eq_at_almost_all_split_places : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (i : N.Loc), GlobalTheory.RowTie.BCEx N A i → GlobalTheory.RowTie.SplitBC N A i → GlobalTheory.RowTie.RepOfLoc N A i → ∀ P P' : A.AV i, (∀ᶠ w in Filter.cofinite, IsSplitPl H w → A.locV i P w = A.locV i P' w) → P = P' := by
  first | exact @GlobalTheory.RowTie.repDet_split | exact GlobalTheory.RowTie.repDet_split | (intros; apply GlobalTheory.RowTie.repDet_split <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.splitComponentsDeterminedByPoint_of_baseChange : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (i : N.Loc), GlobalTheory.RowTie.BCEx N A i → GlobalTheory.RowTie.SplitBC N A i → GlobalTheory.ThetaExh.LocOfPt N A i := by
  first | exact @GlobalTheory.RowTie.locOfPt_of_splitBC | exact GlobalTheory.RowTie.locOfPt_of_splitBC | (intros; apply GlobalTheory.RowTie.locOfPt_of_splitBC <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.tempered_of_rank_one_unitary : ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), GlobalTheory.RowTie.RankOneUnitary T → (∀ (a : ℕ) (π : D.naut.CG a), 2 ≤ a → D.naut.csd π → D.naut.ralg π → ∀ w, D.naut.tempered (D.naut.locG π w)) → GlobalTheory.RowCopy.TempCSD D ∧ GlobalTheory.ThetaExh.Tempered D.nd D.naut := by
  first | exact @GlobalTheory.RowTie.tempered_all_ranks | exact GlobalTheory.RowTie.tempered_all_ranks | (intros; apply GlobalTheory.RowTie.tempered_all_ranks <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.localParameterLaws_of_weilDeligneIdentification :
    ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N),
    GlobalTheory.RowTie.WDTie N A →
      GlobalTheory.ThetaExh.ParamLaws N A ∧ GlobalTheory.RowTie.CharLaws N A ∧
        GlobalTheory.RowTie.Cancel N A :=
  GlobalTheory.RowLaws.main
end

section

open Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.SplitField

namespace GlobalTheory.SplitField

theorem endSpanned_of_isIrrSub_of_isAlgClosed :
    ∀ {Γ E : Type} [Group Γ] [Field E] [IsAlgClosed E] {a : ℕ} (σ : Γ →* GL (Fin a) E)
      (U : Submodule E (Fin a → E)), IsIrrSub σ U → EndSpanned σ U := by
  intro Γ E _ _ _ a σ U h
  classical
  have hinv : ∀ g, ∀ v ∈ U, (Matrix.toLin' ((σ g : GL (Fin a) E) : Matrix (Fin a) (Fin a) E)) v ∈ U :=
    fun g v hv => by rw [Matrix.toLin'_apply]; exact h.2.1 g v hv
  let r : Representation E Γ U :=
    { toFun := fun g => (Matrix.toLin' ((σ g : GL (Fin a) E) : Matrix (Fin a) (Fin a) E)).restrict (hinv g)
      map_one' := by
        ext v i
        simp [LinearMap.restrict_apply]
      map_mul' := fun g g' => by
        ext v i
        simp [LinearMap.restrict_apply, Matrix.mulVec_mulVec] }
  have hr : ∀ g (v : U), ((r g v : U) : Fin a → E) = ((σ g : GL (Fin a) E) : Matrix (Fin a) (Fin a) E).mulVec v :=
    fun g v => by simp [r, LinearMap.restrict_apply]
  have hirr : r.IsIrreducible := by
    have hnt : Nontrivial (Subrepresentation r) := by
      refine ⟨⊥, ⊤, fun hbt => h.1 ?_⟩
      have h2 := congrArg Subrepresentation.toSubmodule hbt
      change (⊥ : Submodule E U) = ⊤ at h2
      rw [eq_bot_iff]
      intro v hv
      have : (⟨v, hv⟩ : U) ∈ (⊥ : Submodule E U) := by rw [h2]; trivial
      rw [Submodule.mem_bot] at this
      simpa using congrArg Subtype.val this
    refine ⟨fun W => ?_⟩
    have hle : W.toSubmodule.map U.subtype ≤ U := by
      rintro _ ⟨v, _, rfl⟩; exact v.2
    have hinvW : IsInv σ (W.toSubmodule.map U.subtype) := by
      rintro g _ ⟨v, hv, rfl⟩
      refine ⟨r g v, W.apply_mem_toSubmodule g hv, ?_⟩
      simp [hr]
    rcases h.2.2 _ hle hinvW with h1 | h1
    · left
      refine Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun v hv => ?_)
      have : (v : Fin a → E) ∈ W.toSubmodule.map U.subtype := ⟨v, hv, rfl⟩
      rw [h1, Submodule.mem_bot] at this
      show v ∈ (⊥ : Submodule E U)
      rw [Submodule.mem_bot]; exact Subtype.ext this
    · right
      refine Subrepresentation.toSubmodule_injective (eq_top_iff.2 fun v _ => ?_)
      have : (v : Fin a → E) ∈ W.toSubmodule.map U.subtype := by rw [h1]; exact v.2
      obtain ⟨w, hw, hwv⟩ := this
      rwa [show w = v from Subtype.ext hwv] at hw
  have hs := GlobalTheory.BurnsideField.span_range_eq_top_of_isAlgClosed r hirr
  intro φ
  have hφ : φ ∈ Submodule.span E (Set.range r) := by rw [hs]; trivial
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact ⟨_, Submodule.subset_span ⟨g, rfl⟩, fun w => (hr g w).symm⟩
  | zero => exact ⟨0, Submodule.zero_mem _, fun w => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨X, hX, hXw⟩ := hx
    obtain ⟨Y, hY, hYw⟩ := hy
    exact ⟨X + Y, Submodule.add_mem _ hX hY, fun w => by rw [Matrix.add_mulVec, hXw, hYw]; simp⟩
  | smul c x _ hx =>
    obtain ⟨X, hX, hXw⟩ := hx
    exact ⟨c • X, Submodule.smul_mem _ c hX, fun w => by rw [Matrix.smul_mulVec, hXw]; simp⟩

end GlobalTheory.SplitField
end

section

namespace GlobalTheory.ThLoc

theorem place_extends_to_iso : Formalism.L2.KerInert.LamExt :=
  fun p _ lam => GlobalTheory.PadicComplexIso.exists_ringEquiv_extending p lam

end GlobalTheory.ThLoc
end

section

open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.CoeffEmbedding

theorem continuous_iotaOQ_of_data : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R}
    (N : NData R H what₂) (A : NAut N) (i : N.Loc), Continuous (iotaOQ N A i) :=
  fun {R H what₂} N A i => continuous_iotaOQ R H what₂ N A i

end GlobalTheory.CoeffEmbedding
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

theorem _root_.GlobalTheory.T.localFieldDegree_eq_ramification_mul_inertia : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (nbr : Br.NBr N) (i : N.Loc) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i)), Br.DegW nbr i w hw := by
  first | exact @GlobalTheory.bridge_degW | exact GlobalTheory.bridge_degW | (intros; apply GlobalTheory.bridge_degW <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

namespace GlobalTheory.RowTie

theorem split_theta_correspondence_of_local_pairings : ∀ D : D7, (∀ i, PairLift D.nd D.naut i) → Formalism.MainNotions.SumRepresentations.adm3 D := by
  intro D h i σ P hθ w hw
  exact GlobalTheory.RowTie.splitLift_of_pairLift _ _ _ D.nd D.naut i (h i) σ P hθ w hw

end GlobalTheory.RowTie
end

section

open Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.exists_conj_double_block_of_iso_subspaces : ∀ {k Γ : Type} [Field k] [Group Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W₁ W₂ : Submodule k (Fin a → k)), IsSSRep ρ → IsInv ρ W₁ → IsInv ρ W₂ → W₁ ≠ ⊥ → W₁ ⊓ W₂ = ⊥ → IsoSub ρ W₁ W₂ → ∃ (d u : ℕ) (σ : Γ →* GL (Fin d) k) (υ : Γ →* GL (Fin u) k) (h : d + d + u = a) (Pm : GL (Fin a) k), 0 < d ∧ ∀ g, ((Pm⁻¹ * ρ g * Pm : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) = Matrix.reindex (finCongr h) (finCongr h) ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g : GL (Fin (d + d + u)) k) : Matrix (Fin (d + d + u)) (Fin (d + d + u)) k) := by
  first | exact @GlobalTheory.DoubleBlock.exists_conj_double | exact GlobalTheory.DoubleBlock.exists_conj_double | (intros; apply GlobalTheory.DoubleBlock.exists_conj_double <;> assumption)
end
