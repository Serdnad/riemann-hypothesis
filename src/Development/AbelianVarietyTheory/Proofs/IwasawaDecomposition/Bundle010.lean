module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.IsDiag
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
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Group.Ultra
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace GlobalTheory.EntrySumMulBound

theorem entrySum_mul_le :
    (let d1 : {n : Type} → [Fintype n] → Matrix n n ℂ → ℝ := @(fun {n : Type} [Fintype n] (M : Matrix n n ℂ) ↦ ∑ i : n, ∑ j : n, ‖M i j‖); ∀ {n : Type} [inst : Fintype n] (A B : Matrix n n ℂ), d1 (A * B) ≤ d1 A * d1 B) := by
  intro d1 n inst A B
  show ∑ i : n, ∑ j : n, ‖(A * B) i j‖ ≤ (∑ i : n, ∑ k : n, ‖A i k‖) * (∑ l : n, ∑ j : n, ‖B l j‖)
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ∑ j : n, ‖(A * B) i j‖ ≤ ∑ j : n, ∑ k : n, ‖A i k‖ * ‖B k j‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [Matrix.mul_apply]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => norm_mul_le _ _)
    _ = ∑ k : n, ‖A i k‖ * ∑ j : n, ‖B k j‖ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ k : n, ‖A i k‖ * ∑ l : n, ∑ j : n, ‖B l j‖ := by
        refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact Finset.single_le_sum (f := fun l => ∑ j : n, ‖B l j‖)
          (fun l _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ k)
    _ = (∑ k : n, ‖A i k‖) * ∑ l : n, ∑ j : n, ‖B l j‖ := (Finset.sum_mul _ _ _).symm

end GlobalTheory.EntrySumMulBound
end

section

universe u_1

namespace GlobalTheory.RootNormPowerBound

open Polynomial

theorem pow_card_le_norm_eval_prod {K : Type u_1} [NormedField K] (x : K) (c : ℝ) (hc : 0 ≤ c)
    (s : Multiset K) (hs : ∀ a ∈ s, c ≤ ‖a - x‖) :
    c ^ Multiset.card s ≤ ‖Polynomial.eval x (s.map fun a => X - C a).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.card_cons, pow_succ, Multiset.map_cons, Multiset.prod_cons, eval_mul, norm_mul, mul_comm]
    have ha : c ≤ ‖eval x (X - C a)‖ := by
      rw [eval_sub, eval_X, eval_C, norm_sub_rev]
      exact hs a (Multiset.mem_cons_self a s)
    exact mul_le_mul ha (ih fun t ht => hs t (Multiset.mem_cons_of_mem ht)) (pow_nonneg hc _)
      (norm_nonneg _)

theorem exists_root_norm_sub_pow_le {K : Type u_1} [inst : NormedField K] [IsAlgClosed K]
    (p : Polynomial K) (hp : (0 : ℕ) < Polynomial.natDegree p) (x : K) :
    ∃ b ∈ Polynomial.roots p,
      ‖Polynomial.leadingCoeff p‖ * ‖b - x‖ ^ Polynomial.natDegree p ≤ ‖Polynomial.eval x p‖ := by
  have hsp : p.Splits := IsAlgClosed.splits p
  have hcard := hsp.natDegree_eq_card_roots
  have hne : p.roots ≠ 0 := by
    intro h
    rw [h, Multiset.card_zero] at hcard
    omega
  obtain ⟨b, hb, hmin⟩ := Multiset.exists_min_image (fun a => ‖a - x‖) hne
  refine ⟨b, hb, ?_⟩
  conv_rhs => rw [hsp.eq_prod_roots]
  rw [eval_mul, eval_C, norm_mul, hcard]
  exact mul_le_mul_of_nonneg_left (pow_card_le_norm_eval_prod x _ (norm_nonneg _) _ hmin) (norm_nonneg _)

end GlobalTheory.RootNormPowerBound
end

section

universe u_1

namespace GlobalTheory.NormPowSubOne

theorem norm_pow_sub_one_le {K : Type u_1} [NormedField K] [IsUltrametricDist K] {ζ : K}
    (hζ : ‖ζ‖ = (1 : ℝ)) (a : ℕ) : ‖ζ ^ a - (1 : K)‖ ≤ ‖ζ - (1 : K)‖ := by
  induction a with
  | zero => simp
  | succ n ih =>
    have h : ζ ^ (n + 1) - 1 = ζ * (ζ ^ n - 1) + (ζ - 1) := by ring
    rw [h]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ le_rfl)
    rw [norm_mul, hζ, one_mul]
    exact ih

theorem main : ∀ {K : Type u_1} [inst : NormedField K] [IsUltrametricDist K] {ζ : K},
    ‖ζ‖ = (1 : ℝ) → ∀ (a : ℕ), ‖ζ ^ a - (1 : K)‖ ≤ ‖ζ - (1 : K)‖ :=
  fun hζ a => norm_pow_sub_one_le hζ a

end GlobalTheory.NormPowSubOne
end

section

noncomputable section

namespace GlobalTheory.Mem.NrmCompl

open NumberField IsDedekindDomain

variable {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L))

def nrmAbs : AbsoluteValue (P.adicCompletion L) ℝ := NormedField.toAbsoluteValue (P.adicCompletion L)

theorem nrmAbs_eq_toNNReal (x : P.adicCompletion L) :
    nrmAbs P x = WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero P) (Valued.v x) :=
  FinitePlace.norm_def (v := P) x

theorem nrmAbs_eq_zpow {x : P.adicCompletion L} (hx : x ≠ 0) :
    nrmAbs P x = (Ideal.absNorm P.asIdeal : ℝ) ^ (WithZero.log (Valued.v x)) := by
  have hv : Valued.v x ≠ 0 := by simpa using hx
  rw [nrmAbs_eq_toNNReal, WithZeroMulInt.toNNReal_neg_apply _ hv]
  obtain ⟨n, hn⟩ : ∃ n : ℤ, Valued.v x = WithZero.exp n := ⟨_, (WithZero.exp_log hv).symm⟩
  simp only [hn, WithZero.log_exp]
  push_cast
  rfl

theorem nrmAbs_of_valuation_eq_exp {x : P.adicCompletion L} {n : ℤ} (h : Valued.v x = WithZero.exp n) :
    nrmAbs P x = (Ideal.absNorm P.asIdeal : ℝ) ^ n := by
  have hx : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at h
    exact WithZero.exp_ne_zero h.symm
  rw [nrmAbs_eq_zpow P hx, h, WithZero.log_exp]

theorem nrmAbs_eq_one_iff (x : P.adicCompletion L) : nrmAbs P x = 1 ↔ Valued.v x = 1 := by
  rw [nrmAbs_eq_toNNReal, ← NNReal.coe_one, NNReal.coe_inj]
  exact WithZeroMulInt.toNNReal_eq_one_iff _ _ (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal P).ne'

end GlobalTheory.Mem.NrmCompl
end
end

section

noncomputable section

open MvPolynomial TensorProduct

namespace GlobalTheory.GrassModel

variable (n : ℕ)

abbrev Ext : Type := ExteriorAlgebra ℂ (Fin n → ℂ)

abbrev Big : Type := Ext n ⊗[ℂ] Ext n

def vec (a : Fin n) : Ext n := ExteriorAlgebra.ι ℂ (Pi.single a 1 : Fin n → ℂ)

def gen (x : Fin n × Fin n) : Big n := vec n x.1 ⊗ₜ vec n x.2

theorem vec_mul_vec_comm (a b : Fin n) : vec n a * vec n b = -(vec n b * vec n a) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)

theorem gen_comm : ∀ u ∈ Set.range (gen n), ∀ v ∈ Set.range (gen n), u * v = v * u := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  simp only [gen, Algebra.TensorProduct.tmul_mul_tmul, vec_mul_vec_comm n x.1, vec_mul_vec_comm n x.2,
    TensorProduct.neg_tmul, TensorProduct.tmul_neg, neg_neg]

abbrev EvenPart : Subalgebra ℂ (Big n) := Algebra.adjoin ℂ (Set.range (gen n))

open scoped IsMulCommutative in
instance : CommRing (EvenPart n) :=
  have := Algebra.isMulCommutative_adjoin ℂ (s := Set.range (gen n))
    (fun u hu v hv _ => gen_comm n u hu v hv)
  inferInstance

def toEven : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] EvenPart n :=
  aeval fun x => ⟨gen n x, Algebra.subset_adjoin ⟨x, rfl⟩⟩


open Classical in
def topForm (i : ℕ) : (Fin n → ℂ) [⋀^Fin i]→ₗ[ℂ] ℂ :=
  if h : i = n then (Pi.basisFun ℂ (Fin n)).det.domDomCongr (finCongr h.symm) else 0

def topExt : Ext n →ₗ[ℂ] ℂ := ExteriorAlgebra.liftAlternating (topForm n)

def topBig : Big n →ₗ[ℂ] ℂ := TensorProduct.lift ((LinearMap.mul ℂ ℂ).compl₂ (topExt n) ∘ₗ topExt n)

theorem topBig_tmul (x y : Ext n) : topBig n (x ⊗ₜ y) = topExt n x * topExt n y := rfl

variable {n} {p q : ℕ}

def blockPoly (e : Fin p × Fin q → Fin n) : Matrix (Fin p) (Fin p) (MvPolynomial (Fin n × Fin n) ℂ) :=
  Matrix.of fun i j => ∑ b, X (e (i, b), e (j, b))

def blockPolyBar (e : Fin p × Fin q → Fin n) : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n × Fin n) ℂ) :=
  Matrix.of fun b b' => ∑ i, X (e (i, b), e (i, b'))

end GlobalTheory.GrassModel
end
end

section

namespace GlobalTheory

open Module

theorem descent_joint_eigen : ∀ {K V W ι κ : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W] (f : K →+* ℂ) (e : V →ₛₗ[f] W) (G : Submodule K V), (∀ v ∈ G, e v = 0 → v = 0) → ∀ (T : κ → Module.End K V) (T' : κ → Module.End ℂ W) (I : Set κ), (∀ k ∈ I, ∀ v, e (T k v) = T' k (e v)) → ∀ (Part : ι → Submodule ℂ W) (s : Set ι) (lam : ι → κ → K), (∀ σ ∈ s, ∀ k ∈ I, ∀ w ∈ Part σ, T' k w = f (lam σ k) • w) → (∀ v, e v ∈ ⨆ σ ∈ s, Part σ → v ∈ G) → ∀ v, e v ∈ ⨆ σ ∈ s, Part σ → v ∈ ⨆ σ ∈ s, G ⊓ ⨅ k ∈ I, Module.End.eigenspace (T k) (lam σ k) := by
  classical
  intro K V W ι κ _ _ _ _ _ f e G hinj T T' I hT Part s lam hPart hG v hv
  set M := ⨆ σ ∈ s, G ⊓ ⨅ k ∈ I, Module.End.eigenspace (T k) (lam σ k) with hM
  have mono : ∀ S : Finset ι, (↑S : Set ι) ⊆ s → (⨆ σ ∈ S, Part σ) ≤ ⨆ σ ∈ s, Part σ := by
    intro S hS
    exact iSup₂_le fun σ hσ => le_iSup₂_of_le (f := fun σ (_ : σ ∈ s) => Part σ) σ (hS hσ) le_rfl
  have key : ∀ (S S'' : Finset ι), (↑S : Set ι) ⊆ s → ∀ k ∈ I, ∀ c : K,
      (∀ σ ∈ S, σ ∉ S'' → lam σ k = c) → ∀ v, e v ∈ ⨆ σ ∈ S, Part σ →
      e (T k v - c • v) ∈ ⨆ σ ∈ S'', Part σ := by
    intro S S'' hS k hk c hc v hv
    have hrw : e (T k v - c • v) = (T' k - f c • (1 : Module.End ℂ W)) (e v) := by
      simp [map_sub, hT k hk, LinearMap.map_smulₛₗ]
    rw [hrw]
    suffices h : (⨆ σ ∈ S, Part σ) ≤ (⨆ σ ∈ S'', Part σ).comap (T' k - f c • (1 : Module.End ℂ W)) from h hv
    refine iSup₂_le fun σ hσ w hw => ?_
    rw [Submodule.mem_comap, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      hPart σ (hS hσ) k hk w hw, ← sub_smul]
    by_cases h : σ ∈ S''
    · exact Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem σ (Submodule.mem_iSup_of_mem h hw))
    · rw [hc σ hσ h, sub_self, zero_smul]; exact Submodule.zero_mem _
  have main : ∀ n : ℕ, ∀ S : Finset ι, S.card ≤ n → (↑S : Set ι) ⊆ s → ∀ v, e v ∈ ⨆ σ ∈ S, Part σ → v ∈ M := by
    intro n
    induction n with
    | zero =>
      intro S hS hSs v hv
      have hS0 : S = ∅ := Finset.card_eq_zero.mp (by omega)
      subst hS0
      simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at hv
      have hvG : v ∈ G := hG v (by rw [hv]; exact Submodule.zero_mem _)
      rw [hinj v hvG hv]; exact Submodule.zero_mem _
    | succ n ih =>
      intro S hS hSs v hv
      rcases S.eq_empty_or_nonempty with hS0 | ⟨a, ha⟩
      · exact ih S (by simp [hS0]) hSs v hv
      by_cases hall : ∀ b ∈ S, ∀ k ∈ I, lam b k = lam a k
      · have hvG : v ∈ G := hG v (mono S hSs hv)
        have heig : v ∈ ⨅ k ∈ I, Module.End.eigenspace (T k) (lam a k) := by
          refine Submodule.mem_iInf _ |>.mpr fun k => Submodule.mem_iInf _ |>.mpr fun hk => ?_
          have h0 := key S ∅ hSs k hk (lam a k) (fun σ hσ _ => hall σ hσ k hk) v hv
          simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at h0
          have hmG : T k v - lam a k • v ∈ G := hG _ (by rw [h0]; exact Submodule.zero_mem _)
          have := hinj _ hmG h0
          rw [Module.End.mem_eigenspace_iff]
          exact sub_eq_zero.mp this
        exact Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem (hSs ha) (Submodule.mem_inf.mpr ⟨hvG, heig⟩))
      · push_neg at hall
        obtain ⟨b, hb, k, hk, hne⟩ := hall
        have hcb := Finset.card_erase_of_mem hb
        have hca := Finset.card_erase_of_mem ha
        have hsub : ∀ x, (↑(S.erase x) : Set ι) ⊆ s := fun x y hy => hSs (Finset.mem_of_mem_erase hy)
        have h1 := ih (S.erase b) (by omega) (hsub b) _
          (key S (S.erase b) hSs k hk (lam b k) (fun σ hσ hn => by
            by_contra hc; exact hn (Finset.mem_erase.mpr ⟨fun h => hc (h ▸ rfl), hσ⟩)) v hv)
        have h2 := ih (S.erase a) (by omega) (hsub a) _
          (key S (S.erase a) hSs k hk (lam a k) (fun σ hσ hn => by
            by_contra hc; exact hn (Finset.mem_erase.mpr ⟨fun h => hc (h ▸ rfl), hσ⟩)) v hv)
        have hv' : v = (lam a k - lam b k)⁻¹ • ((T k v - lam b k • v) - (T k v - lam a k • v)) := by
          rw [sub_sub_sub_cancel_left, ← sub_smul, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne.symm), one_smul]
        rw [hv']; exact M.smul_mem _ (M.sub_mem h1 h2)

  have hv2 : e v ∈ ⨆ σ, ⨆ (_ : σ ∈ s), Part σ := hv
  obtain ⟨S, hS⟩ := Submodule.mem_iSup_iff_exists_finset.mp hv2
  have hle : (⨆ σ ∈ S, ⨆ (_ : σ ∈ s), Part σ) ≤ ⨆ σ ∈ S.filter (· ∈ s), Part σ :=
    iSup₂_le fun σ hσ => iSup_le fun hs =>
      le_iSup₂_of_le (f := fun σ (_ : σ ∈ S.filter (· ∈ s)) => Part σ) σ (Finset.mem_filter.mpr ⟨hσ, hs⟩) le_rfl
  exact main _ _ le_rfl (fun x hx => (Finset.mem_filter.mp hx).2) v (hle hS)

end GlobalTheory
end

section

open Matrix

namespace GlobalTheory

theorem mul_transvection_apply' {n : ℕ} (a b : Fin n) (c : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n) :
    (M * transvection a b c) x y = M x y + if y = b then M x a * c else 0 := by
  rw [transvection, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  congr 1
  by_cases hy : y = b
  · subst hy; simp [Matrix.mul_apply, single_apply]
  · simp [Matrix.mul_apply, single_apply, hy, Ne.symm hy]

theorem unitriangular_induction_transvection :
    ∀ (n : ℕ) (P : GL (Fin n) ℂ → Prop), P 1 → (∀ A B, P A → P B → P (A * B)) →
      (∀ (i j : Fin n), i < j → ∀ (s : ℂ) (B : GL (Fin n) ℂ), B.val = transvection i j s → P B) →
      ∀ U : GL (Fin n) ℂ, U.val.BlockTriangular id → (∀ i, U.val i i = 1) → P U := by
  intro n P h1 hmul htr
  let S : GL (Fin n) ℂ → Finset (Fin n × Fin n) := fun U =>
    Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ U.val p.1 p.2 ≠ 0)
  suffices H : ∀ k, ∀ U : GL (Fin n) ℂ, U.val.BlockTriangular id → (∀ i, U.val i i = 1) →
      (S U).card = k → P U from fun U hU hd => H _ U hU hd rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro U hU hd hk
  rcases (S U).eq_empty_or_nonempty with hS | hne
  · have : U = 1 := by
      apply Units.ext
      ext i j
      simp only [Units.val_one, Matrix.one_apply]
      rcases lt_trichotomy i j with hij | hij | hij
      · rw [if_neg hij.ne]
        by_contra h
        have : (i, j) ∈ S U := by simp [S, hij, h]
        rw [hS] at this; simp at this
      · subst hij; simp [hd]
      · rw [if_neg hij.ne']
        exact hU hij
    rw [this]; exact h1
  · obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image (S U) (fun p => p.2) hne
    obtain ⟨a, b⟩ := p
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨hab, hs⟩ := hp
    set s := U.val a b with hsdef
    have col : ∀ x, U.val x a = if x = a then 1 else 0 := by
      intro x
      split_ifs with hx
      · subst hx; exact hd x
      · rcases lt_trichotomy x a with hxa | hxa | hxa
        · by_contra h
          have hm := hmin (x, a) (by simp [S, hxa, h])
          simp at hm
          exact absurd (lt_of_le_of_lt hm hab) (lt_irrefl _)
        · exact absurd hxa hx
        · exact hU hxa
    let T : ℂ → GL (Fin n) ℂ := fun c =>
      ⟨transvection a b c, transvection a b (-c),
        by rw [transvection_mul_transvection_same _ _ hab.ne]; simp,
        by rw [transvection_mul_transvection_same _ _ hab.ne]; simp⟩
    let U' := U * T (-s)
    have ent : ∀ x y, U'.val x y = U.val x y + if y = b ∧ x = a then -s else 0 := by
      intro x y
      show (U.val * transvection a b (-s)) x y = _
      rw [mul_transvection_apply', col]
      by_cases hy : y = b <;> by_cases hx : x = a <;> simp [hy, hx]
    have hU' : U'.val.BlockTriangular id := by
      intro x y hxy
      rw [ent, hU hxy]
      simp only [id] at hxy
      rw [if_neg]; · simp
      rintro ⟨rfl, rfl⟩
      exact absurd (hab.trans hxy) (lt_irrefl _)
    have hd' : ∀ i, U'.val i i = 1 := by
      intro i
      rw [ent, hd]
      rw [if_neg]; · simp
      rintro ⟨rfl, h⟩
      exact hab.ne h.symm
    have hlt : (S U').card < k := by
      rw [← hk]
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨(a, b), ?_, ?_⟩
        · simpa [S, hab] using hs
        · simp [S, ent, hsdef]
      · intro q hq
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
        refine ⟨hq.1, ?_⟩
        by_cases hqe : q.2 = b ∧ q.1 = a
        · obtain ⟨q1, q2⟩ := q
          simp only at hqe
          obtain ⟨rfl, rfl⟩ := hqe
          exact hs
        · have := hq.2
          rw [ent, if_neg hqe, add_zero] at this
          exact this
    have PU' : P U' := ih _ hlt U' hU' hd' rfl
    have PT : P (T s) := htr a b hab s (T s) rfl
    have hUeq : U = U' * T s := by
      apply Units.ext
      show U.val = U.val * transvection a b (-s) * transvection a b s
      rw [mul_assoc, transvection_mul_transvection_same _ _ hab.ne]
      simp
    rw [hUeq]
    exact hmul _ _ PU' PT

end GlobalTheory
end

section

open Matrix

namespace GlobalTheory

theorem GL_upperTriangular_eq_diagonal_mul_unitriangular :
    ∀ (n : ℕ) (B : GL (Fin n) ℂ), B.val.BlockTriangular id → ∃ D U : GL (Fin n) ℂ,
      B = D * U ∧ D.val.IsDiag ∧ (∀ i, D.val i i = B.val i i) ∧
      U.val.BlockTriangular id ∧ ∀ i, U.val i i = 1 := by
  intro n B hB
  have hdet : B.val.det = ∏ i, B.val i i := Matrix.det_of_upperTriangular hB
  have hdet0 : B.val.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp B.isUnit).ne_zero
  have hne : ∀ i, B.val i i ≠ 0 := by
    intro i h
    apply hdet0
    rw [hdet]
    exact Finset.prod_eq_zero (Finset.mem_univ i) h
  let D : GL (Fin n) ℂ :=
    ⟨diagonal (fun i => B.val i i), diagonal (fun i => (B.val i i)⁻¹),
      by
        rw [diagonal_mul_diagonal, ← diagonal_one]
        congr 1; funext i; exact mul_inv_cancel₀ (hne i),
      by
        rw [diagonal_mul_diagonal, ← diagonal_one]
        congr 1; funext i; exact inv_mul_cancel₀ (hne i)⟩
  have hU : ∀ i j, (D⁻¹ * B).val i j = (B.val i i)⁻¹ * B.val i j := by
    intro i j
    change (diagonal (fun i => (B.val i i)⁻¹) * B.val) i j = _
    rw [diagonal_mul]
  refine ⟨D, D⁻¹ * B, by simp, isDiag_diagonal _, fun i => diagonal_apply_eq _ _, ?_, ?_⟩
  · intro i j hij
    rw [hU, hB hij, mul_zero]
  · intro i
    rw [hU, inv_mul_cancel₀ (hne i)]

end GlobalTheory
end
