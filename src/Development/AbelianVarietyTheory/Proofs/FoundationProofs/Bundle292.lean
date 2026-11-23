module

public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle007
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.CartanCoshPower
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle275
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle172
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle203
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle282
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightTensor
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StarMulOfMemKc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle172
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle173
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle283
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
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod pOf)
open GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower Matrix

namespace GlobalTheory.CoshSqInt

variable {p q : ℕ}

theorem pOf_mem_pR (B : Matrix (Fin p) (Fin q) ℂ) : pOf B ∈ pR p q := by
  refine ⟨?_, ?_⟩
  · change (pOf B)ᴴ * Jm p q + Jm p q * pOf B = 0
    rw [(pOf_herm B).eq]
    simp [pOf, Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
  · rintro (a | a) (b | b) h <;> simp [sameBlock] at h <;> simp [pOf]

theorem exists_cartan (T : GrpData p q) (g : T.G) :
    ∃ k ∈ T.Kset, g = k * T.expt (pOf (cartanB (T.covU g))) := by
  set B := cartanB (T.covU g) with hB
  refine ⟨g * (T.expt (pOf B))⁻¹, ?_, by simp⟩
  obtain ⟨k₁, -, k₂, -, h⟩ := isCartan_cartanB (T.covU g)
  have h1 : ((T.cov g : GL (Ix p q) ℂ) : Mat p q) =
      Matrix.fromBlocks k₁ 0 0 k₂ * ((T.cov (T.expt (pOf B)) : GL (Ix p q) ℂ) : Mat p q) := by
    rw [T.expt_cov _ (pOf_mem_pR B).1]; exact h
  have h2 : ((T.cov (g * (T.expt (pOf B))⁻¹) : GL (Ix p q) ℂ) : Mat p q) = Matrix.fromBlocks k₁ 0 0 k₂ := by
    rw [map_mul, map_inv, Units.val_mul, h1, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  change IsKC _
  rw [h2]
  rintro (a | a) (b | b) h <;> simp [sameBlock] at h <;> simp

theorem decay_sq (n : ℕ) (g : Formalism.BasicNotions.UpqT p q) :
    decay n (pOf (cartanB g)) ^ 2 = coshPow (2 * (n : ℝ)) g := by
  unfold decay coshPow singVal
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  have : (pOf (cartanB g)).toBlocks₁₂ = cartanB g := by simp [pOf]
  rw [this, Real.rpow_neg (Real.cosh_pos _).le, inv_pow, ← pow_mul, mul_comm n 2]
  congr 1
  rw [← Real.rpow_natCast]; push_cast; rfl

theorem memLp_two_of_decay : GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower.CoshIntegral → ∀ (p q n : ℕ), p + q < n →
    ∀ (T : GrpData p q) (f : T.G → ℂ) (C : ℝ), Continuous f →
    (∀ k ∈ T.Kset, ∀ X ∈ pR p q, ‖f (k * T.expt X)‖ ≤ C * decay n X) → MemLp f 2 T.haar := by
  intro hI p q n hn T f C hf hd
  obtain ⟨m, hm⟩ := GlobalTheory.MinfMeasure.exists_isMinf p q
  have hc : 2 * (((p + q : ℕ) : ℝ) - 1) < 2 * (n : ℝ) := by
    have : ((p + q : ℕ) : ℝ) < n := by exact_mod_cast hn
    linarith
  have h1 := hI.1 p q m hm _ hc
  haveI := hm.1
  haveI := GlobalTheory.DetSqrtCover.isHaarMeasure_map_covU T
  haveI : BorelSpace (Formalism.BasicNotions.UpqT p q) := ⟨rfl⟩
  obtain ⟨t, ht⟩ := GlobalTheory.CompactDualUnique.exists_eq_smul (T.haar.map T.covU) m
  have h2 : Integrable (coshPow (2 * (n : ℝ))) (T.haar.map T.covU) := by
    rw [ht]; exact h1.smul_measure_nnreal
  have h3 : Integrable (coshPow (2 * (n : ℝ)) ∘ T.covU) T.haar :=
    h2.comp_measurable (GlobalTheory.DetSqrtCover.continuous_covU T).measurable
  have hfm : AEStronglyMeasurable f T.haar := hf.measurable.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hfm]
  refine (h3.const_mul (C ^ 2)).mono' (hfm.norm.pow 2) (Filter.Eventually.of_forall fun g => ?_)
  obtain ⟨k, hk, hg⟩ := exists_cartan T g
  have h4 := hd k hk _ (pOf_mem_pR (cartanB (T.covU g)))
  rw [← hg] at h4
  rw [Real.norm_of_nonneg (by positivity), Function.comp_apply, ← decay_sq, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h4 2

end GlobalTheory.CoshSqInt
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.LowestType

open GlobalTheory.TensorHW

variable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

noncomputable def zc (p q : ℕ) : Mat p q :=
  Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => 0))

lemma zc_eq : zc p q = ∑ i : Fin p, Eab (Sum.inl i) (Sum.inl i) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [zc, Eab, Matrix.sum_apply, Matrix.single_apply, Matrix.diagonal_apply]
  by_cases h : a = b
  · subst h; simp [Finset.filter_eq']
  · rw [if_neg h, eq_comm]
    simp only [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro x - ⟨rfl, rfl⟩
    exact h rfl

lemma act_zc (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (x : V) :
    act (zc p q) x = ∑ i : Fin p, act (Eab (Sum.inl i) (Sum.inl i)) x := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [zc_eq, map_sum, LinearMap.sum_apply]

lemma zc_comm {X : Mat p q} (hX : IsKC X) : zc p q * X = X * zc p q := by
  ext a b
  rw [zc, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rcases a with a | a <;> rcases b with b | b
  · simp
  · simp [hX (.inl a) (.inr b) (by simp [sameBlock])]
  · simp [hX (.inr a) (.inl b) (by simp [sameBlock])]
  · simp

lemma kstable_eig {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (hL : IsLieAct act) (t : ℂ) :
    KStable act (Module.End.eigenspace (act (zc p q)) t) := by
  intro X hX w hw
  rw [Module.End.mem_eigenspace_iff] at hw ⊢
  have h := hL (zc p q) X
  rw [zc_comm hX, sub_self, map_zero, eq_comm, sub_eq_zero] at h
  have h2 := LinearMap.congr_fun h w
  simp only [Module.End.mul_apply] at h2
  rw [h2, hw, map_smul]

lemma kstable_inf {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {A B : Submodule ℂ V}
    (hA : KStable act A) (hB : KStable act B) : KStable act (A ⊓ B) :=
  fun X hX w hw => ⟨hA X hX w hw.1, hB X hX w hw.2⟩

lemma wt_eig {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {μ : Ix p q → ℚ} {x : V}
    (hx : x ∈ wtSub act μ) :
    x ∈ Module.End.eigenspace (act (zc p q)) ((∑ i : Fin p, μ (Sum.inl i) : ℚ) : ℂ) := by
  rw [Module.End.mem_eigenspace_iff, act_zc]
  simp only [mem_wt.1 hx]
  rw [← Finset.sum_smul]
  push_cast
  rfl

lemma eig_le (f : Module.End ℂ V) (c : ℂ) (N : ℕ → Submodule ℂ V) (hN : (⨆ m, N m) = ⊤)
    (h : ∀ m : ℕ, N m ≤ f.eigenspace (c + m)) (t : ℂ) :
    f.eigenspace t ≤ ⨆ m : ℕ, ⨆ _ : c + m = t, N m := by
  intro x hx
  have h1 : (⊤ : Submodule ℂ V) ≤ (⨆ m : ℕ, ⨆ _ : c + m = t, N m) ⊔ ⨆ s, ⨆ _ : s ≠ t, f.eigenspace s := by
    rw [← hN]
    refine iSup_le fun m => ?_
    by_cases hm : c + m = t
    · exact le_sup_of_le_left (le_iSup₂_of_le m hm le_rfl)
    · exact le_sup_of_le_right (le_iSup₂_of_le (c + m) hm (h m))
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (h1 (Submodule.mem_top : x ∈ ⊤))
  have ha' : a ∈ f.eigenspace t := by
    refine (iSup₂_le fun m hm => ?_ : (⨆ m : ℕ, ⨆ _ : c + m = t, N m) ≤ f.eigenspace t) ha
    rw [← hm]; exact h m
  have hb' : b ∈ f.eigenspace t := by
    simpa using Submodule.sub_mem _ hx ha'
  have hd := Module.End.eigenspaces_iSupIndep f t
  have : b = 0 := (Submodule.disjoint_def.1 hd) b hb' hb
  simpa [this] using ha

lemma eig_mem (f : Module.End ℂ V) (c : ℂ) (N : ℕ → Submodule ℂ V) (hN : (⨆ m, N m) = ⊤)
    (h : ∀ m : ℕ, N m ≤ f.eigenspace (c + m)) (t : ℂ) {x : V} (hx : x ∈ f.eigenspace t) (h0 : x ≠ 0) :
    ∃ m : ℕ, t = c + m ∧ x ∈ N m := by
  have h1 := eig_le f c N hN h t hx
  by_cases hm : ∃ m : ℕ, c + m = t
  · obtain ⟨m, rfl⟩ := hm
    refine ⟨m, rfl, (iSup₂_le fun k hk => ?_ : (⨆ k : ℕ, ⨆ _ : c + k = c + m, N k) ≤ N m) h1⟩
    have : k = m := by exact_mod_cast add_left_cancel hk
    rw [this]
  · refine absurd ?_ h0
    exact (iSup₂_le fun k hk => absurd ⟨k, hk⟩ hm : (⨆ k : ℕ, ⨆ _ : c + k = t, N k) ≤ ⊥) h1

lemma eig_unique {f : Module.End ℂ V} {s t : ℂ} {x : V} (hs : x ∈ f.eigenspace s)
    (ht : x ∈ f.eigenspace t) (h0 : x ≠ 0) : s = t := by
  rw [Module.End.mem_eigenspace_iff] at hs ht
  exact smul_left_injective ℂ h0 (hs.symm.trans ht)

def rk : Ix p q → ℕ := Sum.elim (fun i => i.1) (fun j => p + j.1)

lemma rk_inj : Function.Injective (rk : Ix p q → ℕ) := by
  rintro (a | a) (b | b) h <;> simp only [rk, Sum.elim_inl, Sum.elim_inr] at h
  · rw [Fin.ext h]
  · have := a.2; omega
  · have := b.2; omega
  · rw [Fin.ext (add_left_cancel h)]

lemma same_equiv : Equivalence (sameBlock : Ix p q → Ix p q → Prop) := by
  refine ⟨same_refl, ?_, ?_⟩
  · rintro (a | a) (b | b) h <;> simp_all [sameBlock]
  · rintro (a | a) (b | b) (c | c) h h' <;> simp_all [sameBlock]

lemma pos_of_rk {a b : Ix p q} (h : sameBlock a b) (hr : rk a < rk b) : posC a b := by
  rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock, rk, posC]

lemma hw_irr {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (hL : IsLieAct act) {W : Submodule ℂ V}
    (hW : KStable act W) (hirr : ∀ N : Submodule ℂ V, N ≤ W → KStable act N → N = ⊥ ∨ N = W)
    {μ : Ix p q → ℚ} {v : V} (hv : v ∈ W) (hh : IsHW act μ v) :
    (∀ x ∈ W, x ∈ wtSub act μ → ∃ c : ℂ, x = c • v) ∧
    ∀ (ν : Ix p q → ℚ), ∀ x ∈ W, x ≠ 0 → x ∈ wtSub act ν →
      ν = μ ∨ ∑ a, (rk a : ℚ) * μ a < ∑ a, (rk a : ℚ) * ν a := by
  obtain ⟨U, hvU, hS, hmin, h1, h2⟩ := GlobalTheory.ExtremalGen.exists_generated p q V act hL sameBlock same_equiv rk rk_inj μ v hh.2.1
    (fun a b hab hr => by
      have := hh.2.2
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, SetLike.mem_coe] at this
      exact this a b (pos_of_rk hab hr))
  have hUW : U ≤ W := hmin W hv fun a b hab _ x hx => hW _ (isKC_Eab (same_equiv.symm hab)) x hx
  have hU : U = W := by
    refine (hirr U hUW fun X hX w hw => kc_ind act U w (fun a b hab => hS a b hab w hw) hX).resolve_left ?_
    rintro rfl
    exact hh.1 (by simpa using hvU)
  subst hU
  exact ⟨h1, h2⟩

theorem lowest : ∀ (p q : ℕ) (M : GKMod p q) (Λ : Ix p q → ℚ) (W : Submodule ℂ M.V), IrrGK M → FiniteDimensional ℂ W → KStable M.act W → (∀ N : Submodule ℂ M.V, N ≤ W → KStable M.act N → N = ⊥ ∨ N = W) → (∃ e ∈ W, IsHW M.act Λ e) → (∀ e ∈ W, KilledByLower M.act e) → genSub M.act (W : Set M.V) = ⊤ → IsLowestType M Λ W ∧ Module.finrank ℂ ↥(hwSub M.act Λ) = 1 ∧ ∃ N : ℕ → Submodule ℂ M.V, (∀ m, FiniteDimensional ℂ (N m)) ∧ (⨆ m, N m) = ⊤ ∧ ∀ m : ℕ, ∀ x ∈ N m, ∑ i : Fin p, M.act (Eab (Sum.inl i) (Sum.inl i)) x = (((∑ i : Fin p, Λ (Sum.inl i) : ℚ) : ℂ) + m) • x := by
  intro p q M Λ W hM hfd hW hirr hex hlow hgen
  obtain ⟨e, heW, he⟩ := hex
  set c : ℂ := ((∑ i : Fin p, Λ (Sum.inl i) : ℚ) : ℂ) with hc
  have hWc : W ≤ Module.End.eigenspace (M.act (zc p q)) c := by
    rcases hirr _ inf_le_left (kstable_inf hW (kstable_eig M.lie c)) with h | h
    · exact absurd ((Submodule.eq_bot_iff _).1 h e ⟨heW, wt_eig he.2.1⟩) he.1
    · exact h.ge.trans inf_le_right
  obtain ⟨N, hN0, hNfd, hNtop, hN⟩ := GlobalTheory.FockGrade.exists_grading p q M.V M.act M.lie W c hfd hW hlow
    (fun x hx => by rw [← act_zc]; exact Module.End.mem_eigenspace_iff.1 (hWc hx))
  rw [hgen] at hNtop
  have hNe : ∀ m : ℕ, N m ≤ Module.End.eigenspace (M.act (zc p q)) (c + m) := fun m x hx => by
    rw [Module.End.mem_eigenspace_iff, act_zc]; exact hN m x hx
  have hcW : Module.End.eigenspace (M.act (zc p q)) c ≤ W := by
    intro x hx
    by_cases h0 : x = 0
    · rw [h0]; exact W.zero_mem
    obtain ⟨m, hm, hxm⟩ := eig_mem _ c N hNtop hNe c hx h0
    have : m = 0 := by exact_mod_cast left_eq_add.1 hm
    rwa [this, hN0] at hxm
  have hline := hw_irr M.lie hW hirr heW he
  refine ⟨⟨hM, hfd, hW, hirr, ⟨e, heW, he⟩, fun x => ⟨fun hx => ⟨W, hfd, hx, hW, ?_⟩, ?_⟩, hlow, hgen, ?_⟩, ?_,
    N, hNfd, hNtop, hN⟩
  · intro ν w hw hh
    rcases hline.2 ν w hw hh.1 hh.2.1 with h | h
    · exact h
    rcases (hw_irr M.lie hW hirr hw hh).2 Λ e heW he.1 he.2.1 with h' | h'
    · exact h'.symm
    · exact absurd h (not_lt.2 h'.le)
  · rintro ⟨W', hfd', hx, hW', hall⟩
    have h1 := GlobalTheory.WeightDecomp.mem_iSup_inf_wtSub p q M.V M.act W' (fun a y hy => hW' _ (isKC_Eab (same_refl a)) y hy) x hx (M.wts x)
    refine (iSup_le fun μ y hy => ?_ : (⨆ μ : Ix p q → ℚ, W' ⊓ wtSub M.act μ) ≤ W) h1
    by_cases h0 : y = 0
    · rw [h0]; exact W.zero_mem
    have hy2 := wt_eig hy.2
    have := hfd'
    obtain ⟨ν, v, hv, hh⟩ := GlobalTheory.ExistsHW.exists_highestWeight p q M _
      (Submodule.finiteDimensional_of_le inf_le_left) (kstable_inf hW' (kstable_eig M.lie
        ((∑ i : Fin p, μ (Sum.inl i) : ℚ) : ℂ)))
      (fun h => h0 ((Submodule.eq_bot_iff _).1 h y ⟨hy.1, hy2⟩))
    obtain rfl := hall ν v hv.1 hh
    have := eig_unique hv.2 (wt_eig hh.2.1) hh.1
    rw [this] at hy2
    exact hcW hy2
  · intro μ x h0 hx
    obtain ⟨m, hm, hxm⟩ := eig_mem _ c N hNtop hNe _ (wt_eig hx) h0
    refine ⟨m, by rw [hc] at hm; exact_mod_cast hm, ?_, fun hxW => ?_⟩
    · rintro rfl
      rwa [hN0] at hxm
    · have := eig_unique (hWc hxW) (hNe m hxm) h0
      exact_mod_cast left_eq_add.1 this
  · have : hwSub M.act Λ = Submodule.span ℂ {e} := by
      refine le_antisymm (fun x hx => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 he.2)
      obtain ⟨a, rfl⟩ := hline.1 x (hcW (wt_eig hx.1)) hx.1
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e)
    rw [this]
    exact finrank_span_singleton he.1

end GlobalTheory.LowestType
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.kTypes_unitary_lowestWeight_in_cone : ∀ (p q : ℕ) (M : GKMod p q) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (E : M.V →ₗ[ℂ] H), Function.Injective E → (∀ Z x y, inner ℂ (E (M.act Z x)) (E y) = inner ℂ (E x) (E (M.act (adjZ Z) y))) → ∀ (Λ : Ix p q → ℚ) (e : M.V), e ∈ hwSub M.act Λ → KilledByLower M.act e → genSub M.act {e} = ⊤ → ∀ (μ : Ix p q → ℚ) (v : M.V), IsHW M.act μ v → ∃ m : Ix p q → Ix p q → ℕ, (∀ a b, m a b ≠ 0 → ∃ i j, a = Sum.inl i ∧ b = Sum.inr j) ∧ μ = fun c => Λ c + ∑ a, ∑ b, (m a b : ℚ) * ((if c = a then 1 else 0) - (if c = b then 1 else 0)) := by
  first | exact @GlobalTheory.LowestCone.cone | exact GlobalTheory.LowestCone.cone | (intros; apply GlobalTheory.LowestCone.cone <;> assumption)
end

section

namespace GlobalTheory.CartanInt.Frob
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory

theorem sq_col_le {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (a : Fin n) : (∑ i, ‖U i a‖) ^ 2 ≤ n := by
  have h1 : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have h2 := congrFun (congrFun h1 a) a
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.star_def,
    Complex.conj_mul'] at h2
  have h3 : ∑ i, ‖U i a‖ ^ 2 = 1 := by exact_mod_cast h2
  have h4 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖U i a‖)
  simpa [h3] using h4

theorem sum_diag (p q : ℕ) (s : ℕ → ℝ) :
    ∑ a : Fin p, ∑ b : Fin q, (if (a : ℕ) = (b : ℕ) then s a else 0) =
      ∑ i ∈ Finset.range (min p q), s i := by
  rw [Fin.sum_univ_eq_sum_range (fun a => ∑ b : Fin q, (if a = (b : ℕ) then s a else 0)) p]
  have h : ∀ a : ℕ, ∑ b : Fin q, (if a = (b : ℕ) then s a else 0) =
      if a ∈ Finset.range q then s a else 0 := fun a => by
    rw [Fin.sum_univ_eq_sum_range (fun b => if a = b then s a else 0) q, Finset.sum_ite_eq]
  simp only [h]
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

theorem sum_norm_le_sum_singVal : ∀ (p q : ℕ) (B : Matrix (Fin p) (Fin q) ℂ),
    ∑ i, ∑ j, ‖B i j‖ ≤
      (((p + q : ℕ) : ℝ) + 1) / 2 * ∑ i ∈ Finset.range (min p q), singVal B i := by
  intro p q B
  obtain ⟨U, hU, V, hV, hB⟩ := GlobalTheory.RectSVD.exists_svd_singularValues p q B
  set d : Fin p → Fin q → ℝ := fun a b => if (a : ℕ) = (b : ℕ) then singVal B a else 0 with hd
  have hd0 : ∀ a b, 0 ≤ d a b := fun a b => by
    simp only [hd]; split_ifs
    · exact singVal_nonneg _ _
    · exact le_rfl
  have h1 : ∀ i j, ‖B i j‖ ≤ ∑ b, ∑ a, ‖U i a‖ * d a b * ‖V j b‖ := by
    intro i j
    have e := congrFun (congrFun hB i) j
    rw [e, Matrix.mul_apply]
    refine norm_sum_le_of_le _ fun b _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine norm_sum_le_of_le _ fun a _ => le_of_eq ?_
    rw [norm_mul, norm_mul, Matrix.conjTranspose_apply, norm_star, Matrix.of_apply]
    congr 2
    simp only [hd]
    split_ifs
    · rw [Complex.norm_real]; exact Real.norm_of_nonneg (singVal_nonneg B a)
    · simp
  calc ∑ i, ∑ j, ‖B i j‖ ≤ ∑ i, ∑ j, ∑ b, ∑ a, ‖U i a‖ * d a b * ‖V j b‖ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 i j
    _ = ∑ b, ∑ a, ((∑ i, ‖U i a‖) * ∑ j, ‖V j b‖) * d a b := by
        simp only [Finset.sum_mul_sum, Finset.sum_mul]
        simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin q))) (t := (Finset.univ : Finset (Fin q))) (f := fun j b => ∑ a, ‖U _ a‖ * d a b * ‖V j b‖)]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin q))) (t := (Finset.univ : Finset (Fin p))) (f := fun j a => ‖U _ a‖ * d a b * ‖V j b‖)]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.mul_sum]; ring
    _ ≤ ∑ b, ∑ a, (((p + q : ℕ) : ℝ) + 1) / 2 * d a b := by
        refine Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_right ?_ (hd0 a b)
        have := sq_col_le hU a
        have := sq_col_le hV b
        push_cast
        nlinarith [sq_nonneg ((∑ i, ‖U i a‖) - ∑ j, ‖V j b‖)]
    _ = _ := by
        rw [← sum_diag, Finset.sum_comm]
        simp only [Finset.mul_sum, hd]

end GlobalTheory.CartanInt.Frob
end

section

open GlobalTheory.NeedB Polynomial

theorem _root_.GlobalTheory.T.kummerCupProduct_coboundary_theorem : GlobalTheory.NeedB.ThmA := by
  first | exact @GlobalTheory.KummerCob.thmA | exact GlobalTheory.KummerCob.thmA | (intros; apply GlobalTheory.KummerCob.thmA <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.exists_ringEquiv_fn_ring_coeff_eq_apply : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (s : Ω ≃+* Ω), ∃ σ : GlobalTheory.FN.ring ε.range ≃+* GlobalTheory.FN.ring ε.range, ∀ (a : GlobalTheory.FN.ring ε.range) (h h' : HahnSeries ℚ Ω), IsExp ε a h → IsExp ε (σ a : GlobalTheory.FN.ring ε.range) h' → ∀ r, h'.coeff r = s (h.coeff r) := by
  first | exact @GlobalTheory.FN.exists_ringEquiv_coeff_conj | exact GlobalTheory.FN.exists_ringEquiv_coeff_conj | (intros; apply GlobalTheory.FN.exists_ringEquiv_coeff_conj <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.exists_level_gal_sl_commute : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (f : T.K), ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, 0 < N → N₀ ∣ N → ∀ (s : Ω ≃ₐ[ℚ] Ω) (d : ℤ), s (eOm ε (1 / N)) = eOm ε (1 / N) ^ d → ∀ γ γ' : SL(2, ℤ), Cong N d γ γ' → T.gal s (T.sl (ofSL γ) f) = T.sl (ofSL γ') (T.gal s f) := by
  first | exact @GlobalTheory.FN.reciprocity_large_level | exact GlobalTheory.FN.reciprocity_large_level | (intros; apply GlobalTheory.FN.reciprocity_large_level <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.eq_zero_of_mem_twistedJacquetKernel_upperUnitriangular : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → (∀ i, IsSmoothChar (ψ i)) → Ordered ψ → ∀ v ∈ twKer π (unipB k (Fin n)) 1, IsEig π (grp ψ) (theta ψ) v → v = 0 := by
  first | exact @GlobalTheory.PsType.eq_zero_of_mem_twKer_unipB | exact GlobalTheory.PsType.eq_zero_of_mem_twKer_unipB | (intros; apply GlobalTheory.PsType.eq_zero_of_mem_twKer_unipB <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem GlobalTheory.KZ.H3.exists_kum_of_mem_A : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ)
    [Fact l.Prime], JHol X → ∀ (n : ℕ), ∀ x ∈ X.A l, ∃ χ : SL(2, ℤ) → ZMod (l ^ n), Kum X l n x χ := by
  intro Ω _ _ ε X l _ hJ n x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨f, hf, he⟩ := hy n
    have hm : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
    obtain ⟨a, b, hab⟩ := GlobalTheory.T.exists_isRoot_of_mem_Un_of_jHol Ω ε X hJ (l ^ n) hm f hf
    exact GlobalTheory.T.exists_kummerCharacter_of_upperHalfPlane_root Ω ε X l n y f a b he hab
  | zero => exact ⟨0, (GlobalTheory.T.isKummerCharacterAtLevel_add_zero_congr Ω ε X l n).2.1⟩
  | add y z _ _ hy hz =>
    obtain ⟨χ, hχ⟩ := hy
    obtain ⟨χ', hχ'⟩ := hz
    exact ⟨χ + χ', (GlobalTheory.T.isKummerCharacterAtLevel_add_zero_congr Ω ε X l n).1 y z χ χ' hχ hχ'⟩
  | smul c y _ hy =>
    obtain ⟨χ, hχ⟩ := hy
    exact ⟨_, GlobalTheory.T.isKummerCharacterAtLevel_padicInt_smul Ω ε X l n c y χ hχ⟩
end
