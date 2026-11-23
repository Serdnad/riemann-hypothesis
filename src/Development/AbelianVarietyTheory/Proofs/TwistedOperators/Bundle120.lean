module

public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle009
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BlockTriangularOfSubOne
public import Mathlib.RepresentationTheory.Character
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle923
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle119
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspValueComparison
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Formalism.CyclotomicNorms.Bundle001
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass

@[expose] public section

section

open Matrix

namespace GlobalTheory.OneParamUnitary

open scoped ContDiff

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem oneParam_eq_exp_lieU {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (u : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (hc : Continuous u) (h0 : u 0 = 1) (hadd : ∀ s t, u (s + t) = u s * u t)
    (hU : ∀ t, u t ∈ Formalism.QuantumDeterminants.UH G) :
    ∃ Y ∈ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU G, ∀ t : ℝ, u t = NormedSpace.exp (t • Y) := by
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  have hsm : ContDiff ℝ ∞ u :=
    GlobalTheory.contDiff_of_continuous_oneParameter (Matrix (Fin n) (Fin n) ℂ) u hc h0 hadd
  have hdiff : Differentiable ℝ u := hsm.differentiable (by simp)
  set Y := deriv u 0 with hY
  have hY0 : HasDerivAt u Y 0 := (hdiff 0).hasDerivAt
  have hder : ∀ t, HasDerivAt u (u t * Y) t := by
    intro t
    have h1 : HasDerivAt (fun s => u (s - t)) Y t :=
      (show HasDerivAt u Y (t - t) by simpa using hY0).comp_sub_const t t
    have h2 := h1.const_mul (u t)
    have h3 : (fun s => u t * u (s - t)) = u := by
      funext s
      rw [← hadd]; congr 1; ring
    rwa [h3] at h2

  have hexp : ∀ t : ℝ, u t = NormedSpace.exp (t • Y) := by
    set v : ℝ → Matrix (Fin n) (Fin n) ℂ := fun t => u t * NormedSpace.exp (t • (-Y)) with hv
    have hvd : ∀ t, HasDerivAt v 0 t := by
      intro t
      have hE := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-Y) t
      have := (hder t).mul hE
      rw [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, add_neg_cancel] at this
      exact this
    have hvc : ∀ t, v t = v 0 := fun t =>
      is_const_of_deriv_eq_zero (fun s => (hvd s).differentiableAt) (fun s => (hvd s).deriv) t 0
    have hv0 : v 0 = 1 := by simp [hv, h0]
    intro t
    have hcomm : Commute (t • (-Y)) (t • Y) :=
      ((Commute.refl Y).neg_left.smul_left t).smul_right t
    have hinv : NormedSpace.exp (t • (-Y)) * NormedSpace.exp (t • Y) = 1 := by
      rw [← Matrix.exp_add_of_commute _ _ hcomm, smul_neg, neg_add_cancel, NormedSpace.exp_zero]
    calc u t = u t * (NormedSpace.exp (t • (-Y)) * NormedSpace.exp (t • Y)) := by rw [hinv, Matrix.mul_one]
      _ = v t * NormedSpace.exp (t • Y) := by rw [hv, Matrix.mul_assoc]
      _ = NormedSpace.exp (t • Y) := by rw [hvc t, hv0, Matrix.one_mul]
  refine ⟨Y, ?_, hexp⟩

  show Yᴴ * G + G * Y = 0
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun A => star A
      map_add' := fun A B => star_add A B
      map_smul' := fun c A => by simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul] }
  have hst : HasDerivAt (fun t => star (u t)) (star Y) 0 :=
    (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt 0 hY0
  have hw := (hst.mul_const G).mul hY0
  have hconst : ((fun t => star (u t) * G) * u) = fun _ => G := by
    funext t; exact hU t
  rw [hconst] at hw
  have := (hasDerivAt_const (0 : ℝ) G).unique hw
  rw [h0, star_one, Matrix.one_mul, Matrix.mul_one, ← Matrix.star_eq_conjTranspose] at *
  exact this.symm

end GlobalTheory.OneParamUnitary
end

section

noncomputable section

open Polynomial NumberField Formalism.CyclotomicNorms Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors GlobalTheory.Parabolic GlobalTheory.FiniteGL

namespace GlobalTheory.GoodNoFixed

theorem mem_radical_iff {k : Type} [Field k] {r a : ℕ} {u : GL (Fin r) k} :
    u ∈ radical k r a ↔ u ∈ unipRadical k (blk2 a) := by
  rw [GlobalTheory.FiniteGL.mem_unipRadical]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.radical, Set.mem_ofPred_eq]
  constructor
  · intro h i j hij
    rw [Matrix.sub_apply, sub_eq_zero]
    by_contra hne
    obtain ⟨h1, h2⟩ := h i j hne
    simp only [Formalism.L2.DIV.blk2] at hij
    split_ifs at hij <;> omega
  · intro h i j hne
    by_contra hc
    apply hne
    rw [← sub_eq_zero, ← Matrix.sub_apply]
    apply h
    simp only [Formalism.L2.DIV.blk2]
    by_cases hi : (i : ℕ) < a
    · have hj : (j : ℕ) < a := by
        by_contra hj
        exact hc ⟨hi, by omega⟩
      split_ifs <;> omega
    · split_ifs <;> omega

theorem monotone_twoBlockIndicator {r : ℕ} (a : ℕ) : Monotone (blk2 (n := r) a) := by
  intro i j hij
  rw [Fin.le_iff_val_le_val] at hij
  simp only [Formalism.L2.DIV.blk2]
  split_ifs <;> omega

private theorem mem_map_castLEEmb_trans_perm_iff {r a : ℕ} (ha : a ≤ r) (w : Equiv.Perm (Fin r)) (i : Fin r) :
    i ∈ Finset.univ.map ((Fin.castLEEmb ha).trans w.toEmbedding) ↔ (w.symm i : ℕ) < a := by
  simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.trans_apply,
    Fin.castLEEmb_apply, Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨t, rfl⟩
    simp
  · intro h
    refine ⟨⟨_, h⟩, ?_⟩
    rw [show Fin.castLE ha ⟨(w.symm i : ℕ), h⟩ = w.symm i from Fin.ext rfl]
    simp

theorem exists_union_of_blocks {k : Type} [Field k] {r : ℕ} {b : Fin r → ℕ} (hb : Monotone b) {Y : Type} [Zero Y]
    (ρ : blockTri (κ := k) b → Y → Y) (hρ : ∀ q, ρ q 0 = 0)
    (cusp : ∀ S : Finset (Fin r), (∃ i j, b i = b j ∧ i ∈ S ∧ j ∉ S) → ∀ y : Y,
      (∀ u : blockTri (κ := k) b, (∀ i j, ((u : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) i j ≠
        (1 : Matrix (Fin r) (Fin r) k) i j → b i = b j ∧ i ∈ S ∧ j ∉ S) → ρ u y = y) → y = 0)
    {a : ℕ} (ha : a ≤ r) (φ : GL (Fin r) k → Y)
    (hl : ∀ (q : blockTri (κ := k) b) (x : GL (Fin r) k), φ (q * x) = ρ q (φ x))
    (hr : ∀ x, ∀ n ∈ radical k r a, φ (x * n) = φ x) (x : GL (Fin r) k) (hx : φ x ≠ 0) :
    ∃ S : Finset (Fin r), S.card = a ∧ ∀ i j, b i = b j → i ∈ S → j ∈ S := by
  obtain ⟨w, p', p, hxe⟩ := GlobalTheory.FinGL.Bruhat.exists_perm_rep_blockTri k r (blk2 a) b (monotone_twoBlockIndicator a) hb x
  have hy : φ (GlobalTheory.Parabolic.permGL k w * (p : GL (Fin r) k)) ≠ 0 := by
    intro h0
    apply hx
    rw [hxe, mul_assoc, hl p', h0, hρ]
  have hS := mem_map_castLEEmb_trans_perm_iff ha w
  refine ⟨Finset.univ.map ((Fin.castLEEmb ha).trans w.toEmbedding), by simp, fun i j hij hi => ?_⟩
  by_contra hj
  apply hy
  refine cusp _ ⟨i, j, hij, hi, hj⟩ _ fun u hu => ?_
  have hm : (GlobalTheory.Parabolic.permGL k w)⁻¹ * (u : GL (Fin r) k) * GlobalTheory.Parabolic.permGL k w ∈ radical k r a := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.radical, Set.mem_ofPred_eq]
    intro i' j' hne
    have he := GlobalTheory.Parabolic.conj_permGL_apply (k := k) w⁻¹ (u : GL (Fin r) k) (w i') (w j')
    rw [map_inv, inv_inv] at he
    simp only [Equiv.Perm.inv_def, Equiv.symm_apply_apply] at he
    rw [he] at hne
    have h1 : (1 : Matrix (Fin r) (Fin r) k) (w i') (w j') = (1 : Matrix (Fin r) (Fin r) k) i' j' := by
      by_cases h : i' = j'
      · subst h; simp
      · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne (fun e => h (w.injective e))]
    rw [← h1] at hne
    obtain ⟨-, hi', hj'⟩ := hu _ _ hne
    rw [hS] at hi' hj'
    simp only [Equiv.symm_apply_apply] at hi' hj'
    exact ⟨hi', not_lt.1 hj'⟩
  have hm' : (p : GL (Fin r) k)⁻¹ * ((GlobalTheory.Parabolic.permGL k w)⁻¹ * (u : GL (Fin r) k) *
      GlobalTheory.Parabolic.permGL k w) * (p : GL (Fin r) k) ∈ radical k r a := by
    rw [mem_radical_iff] at hm ⊢
    have hn := GlobalTheory.Parabolic.blockTri_le_normalizer (k := k) (blk2 (n := r) a) (Subgroup.inv_mem _ p.2)
    have := (Subgroup.mem_normalizer_iff.1 hn _).1 hm
    simpa only [inv_inv, SetLike.mem_coe] using this
  calc ρ u (φ (GlobalTheory.Parabolic.permGL k w * (p : GL (Fin r) k)))
      = φ ((u : GL (Fin r) k) * (GlobalTheory.Parabolic.permGL k w * (p : GL (Fin r) k))) := (hl u _).symm
    _ = φ ((GlobalTheory.Parabolic.permGL k w * (p : GL (Fin r) k)) * ((p : GL (Fin r) k)⁻¹ *
        ((GlobalTheory.Parabolic.permGL k w)⁻¹ * (u : GL (Fin r) k) * GlobalTheory.Parabolic.permGL k w) *
        (p : GL (Fin r) k))) := by congr 1; group
    _ = φ (GlobalTheory.Parabolic.permGL k w * (p : GL (Fin r) k)) := hr _ _ hm'

theorem card_eq_sum_blocks {r : ℕ} {ι : Type} [DecidableEq ι] (b : Fin r → ι) (S : Finset (Fin r))
    (hS : ∀ i j, b i = b j → i ∈ S → j ∈ S) :
    S.card = ∑ c ∈ S.image b, (Finset.univ.filter fun i => b i = c).card := by
  rw [Finset.card_eq_sum_card_image b S]
  refine Finset.sum_congr rfl fun c hc => ?_
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hc
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
  intro hj
  exact hS i j hj.symm hi

theorem fixedVectorBlocks : FixedVectorBlocks := by
  intro k _ _ r b W _ _ ρ hc V _ _ τ hsub a ha0 har hnf
  obtain ⟨T, hTi, hT⟩ := hsub
  unfold NoFixed at hnf
  push Not at hnf
  obtain ⟨v, hv, hv0⟩ := hnf
  have hTv : T v ≠ 0 := fun h => hv0 (hTi (h.trans (map_zero T).symm))
  obtain ⟨y, hy⟩ : ∃ y, ((T v : _) : GL (Fin r) k → W) y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hTv (Subtype.ext (funext hcon))
  have hl : ∀ (q : blockTri (κ := k) b) (z : GL (Fin r) k),
      ((T v : _) : GL (Fin r) k → W) (q * z) = ρ q (((T v : _) : GL (Fin r) k → W) z) :=
    fun q z => (T v).2 q z
  have hr : ∀ z, ∀ n ∈ radical k r a, ((T v : _) : GL (Fin r) k → W) (z * n) = ((T v : _) : GL (Fin r) k → W) z := by
    intro z n hn
    have h1 := LinearMap.congr_fun (hT n) v
    simp only [LinearMap.comp_apply] at h1
    rw [hv n hn] at h1
    have h2 := congrFun (congrArg Subtype.val h1) z
    exact h2.symm
  obtain ⟨S, hS, hU⟩ := exists_union_of_blocks (k := k) hc.mono (Y := W) (fun q w => ρ q w)
    (fun q => map_zero _) hc.cusp (le_of_lt har) _ hl hr y hy
  refine ⟨S.image b, Finset.image_subset_image (Finset.subset_univ _), ?_⟩
  rw [← hS, card_eq_sum_blocks b S hU]
  simp only [Fintype.card_subtype]

theorem map_mem_radical {k k' : Type} [CommRing k] [CommRing k'] (e : k →+* k') {r a : ℕ} {u : GL (Fin r) k}
    (hu : u ∈ radical k r a) : Matrix.GeneralLinearGroup.map e u ∈ radical k' r a := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.radical, Set.mem_ofPred_eq] at hu ⊢
  intro i j hij
  apply hu i j
  intro heq
  apply hij
  rw [Matrix.GeneralLinearGroup.map_apply]
  rw [heq]
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

theorem sum_character_eq_zero_iff {H V : Type} [Group H] [Fintype H] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (τ : Representation ℂ H V) : ∑ h, τ.character h = 0 ↔ ∀ x : V, (∀ h, τ h x = x) → x = 0 := by
  have hcard : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.card_pos (α := H)).ne'
  haveI : Invertible (Nat.card H : ℂ) := invertibleOfNonzero hcard
  have h := τ.card_inv_mul_sum_char_eq_finrank
  constructor
  · intro hs x hx
    rw [hs, mul_zero] at h
    have h0 : Module.finrank ℂ τ.invariants = 0 := by exact_mod_cast h.symm
    have hb : τ.invariants = ⊥ := Submodule.finrank_eq_zero.1 h0
    have hxm : x ∈ τ.invariants := (τ.mem_invariants x).2 hx
    rw [hb] at hxm
    exact (Submodule.mem_bot ℂ).1 hxm
  · intro hx
    have hb : τ.invariants = ⊥ :=
      (Submodule.eq_bot_iff _).2 fun x hxm => hx x ((τ.mem_invariants x).1 hxm)
    rw [hb, finrank_bot, Nat.cast_zero] at h
    exact (mul_eq_zero.1 h).resolve_left (inv_ne_zero hcard)

theorem noFixed_iff_sum {k : Type} [Field k] {r a : ℕ} [Fintype (unipRadical k (blk2 (n := r) a))] {G V : Type} [Group G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (τ : Representation ℂ G V) (ι : GL (Fin r) k →* G) :
    NoFixed τ (ι '' radical k r a) ↔ ∑ u : unipRadical k (blk2 (n := r) a), τ.character (ι u) = 0 := by
  refine Iff.trans ?_ (sum_character_eq_zero_iff (τ.comp (ι.comp (unipRadical k (blk2 (n := r) a)).subtype))).symm
  unfold NoFixed
  refine forall_congr' fun x => imp_congr_left ⟨fun hx h => hx _ ⟨h, mem_radical_iff.2 h.2, rfl⟩, ?_⟩
  rintro hx _ ⟨u, hu, rfl⟩
  exact hx ⟨u, mem_radical_iff.1 hu⟩

end GlobalTheory.GoodNoFixed
end
end

section

open MeasureTheory NumberField Matrix Formalism.MainNotions.S GlobalTheory.Count Formalism.REAL Formalism.HN

theorem _root_.GlobalTheory.T.leastSize_pow_mul_sqrt_absNorm_le_prod_norms : ∀ (I : AutInst) (x : I.GA) (𝔪 : Ideal (𝓞 I.E)), 𝔪 ≠ ⊥ → ∀ w ∈ 𝔪 • lamX I x, w ≠ 0 → least I x ^ I.f * Real.sqrt (Ideal.absNorm 𝔪) ≤ ∏ v, Real.sqrt (∑ i, ‖(uMat (x.1 v)⁻¹ *ᵥ ((I.P v)⁻¹ *ᵥ fun j => I.φ v (w j))) i‖ ^ 2) := by
  first | exact @GlobalTheory.LineBound.least_pow_mul_sqrt_absNorm_le_prod | exact GlobalTheory.LineBound.least_pow_mul_sqrt_absNorm_le_prod | (intros; apply GlobalTheory.LineBound.least_pow_mul_sqrt_absNorm_le_prod <;> assumption)
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL

namespace GlobalTheory.SmGL.Exponents

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def leviChar {R β : Type} [CommRing R] [Fintype β] (c : β → Type) [∀ j, Fintype (c j)]
    [∀ j, DecidableEq (c j)] (χ : β → Rˣ →* ℂˣ) : Levi R c →* ℂˣ :=
  ∏ j, (detChar (c j) (χ j)).comp (Pi.evalMonoidHom (fun j => GL (c j) R) j)

theorem leviChar_apply {R β : Type} [CommRing R] [Fintype β] (c : β → Type) [∀ j, Fintype (c j)]
    [∀ j, DecidableEq (c j)] (χ : β → Rˣ →* ℂˣ) (g : Levi R c) :
    leviChar c χ g = ∏ j, χ j (Matrix.GeneralLinearGroup.det (g j)) := by
  simp [leviChar]

def wordMult {n : ℕ} (π : Representation ℂ (GL (Fin n) k) V) (w : List ℂˣ) : ℕ∞ :=
  if w.length = n then jhMult (ofChar (torusChar fun i : Fin n => unrChar k (w.getD i 1))) (jacB π)
  else 0

theorem wordMult_ofFn {n : ℕ} (π : Representation ℂ (GL (Fin n) k) V) (z : Fin n → ℂˣ) :
    wordMult π (List.ofFn z) = jhMult (ofChar (torusChar fun i => unrChar k (z i))) (jacB π) := by
  simp [wordMult]

theorem wordMult_of_ne {n : ℕ} (π : Representation ℂ (GL (Fin n) k) V) {w : List ℂˣ}
    (h : w.length ≠ n) : wordMult π w = 0 := by
  rw [wordMult, if_neg h]

def jacEquiv {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
    {π : Representation ℂ (GL n k) V} {τ : Representation ℂ (GL n k) W} (φ : π.Equiv τ) :
    (jac e π).Equiv (jac e τ) :=
  LocGL.equivOfBijective (jacMap e φ.toIntertwiningMap) (Function.bijective_iff_has_inverse.2
    ⟨jacMap e φ.symm.toIntertwiningMap, fun x => by
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      exact congrArg Submodule.Quotient.mk (φ.symm_apply_apply v), fun x => by
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      exact congrArg Submodule.Quotient.mk (φ.apply_symm_apply v)⟩)

theorem wordMult_congr {n : ℕ} {π : Representation ℂ (GL (Fin n) k) V}
    {τ : Representation ℂ (GL (Fin n) k) W} (φ : π.Equiv τ) (w : List ℂˣ) :
    wordMult π w = wordMult τ w := by
  unfold wordMult
  split_ifs
  · exact jhMult_congr_right _ (Representation.Equiv.mk (jacEquiv (points (Fin n)) φ).toLinearEquiv
      fun t => (jacEquiv (points (Fin n)) φ).isIntertwining' _)
  · rfl

instance instAddCommGroupTwo : ∀ x, AddCommGroup (Two V W x)
  | false => inferInstanceAs (AddCommGroup V)
  | true => inferInstanceAs (AddCommGroup W)

instance instModuleTwo : ∀ x, Module ℂ (Two V W x)
  | false => inferInstanceAs (Module ℂ V)
  | true => inferInstanceAs (Module ℂ W)

def twoRep {R a b : Type} [CommRing R] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (π₁ : Representation ℂ (GL a R) V) (π₂ : Representation ℂ (GL b R) W) :
    ∀ x, Representation ℂ (GL (Two a b x) R) (Two V W x)
  | false => π₁
  | true => π₂

end GlobalTheory.SmGL.Exponents
end
end

section

open Formalism.L2.Ker MvPolynomial

noncomputable section

namespace GlobalTheory.CoefScale

lemma weight_colW_apply {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) (t : Fin n) :
    Finsupp.weight (Formalism.GradedWeylDivisibility.colW r n) m t = ∑ a : Fin r, m (a, t) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
    Fintype.sum_prod_type_right]
  rw [Finset.sum_eq_single t]
  · refine Finset.sum_congr rfl fun a _ => ?_
    simp [Formalism.GradedWeylDivisibility.colW]
  · intro s _ hs
    refine Finset.sum_eq_zero fun a _ => ?_
    simp [Formalism.GradedWeylDivisibility.colW, Pi.single_apply, Ne.symm hs]
  · simp

theorem rowAct_scalar_dualWeyl {r n : ℕ} (ν : Fin n → ℕ) (c : ℂ) (F : MvPolynomial (Fin r × Fin n) ℂ)
    (hF : F ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ r n ν) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (Matrix.diagonal fun _ : Fin r => c) F = c ^ (∑ t, ν t) • F := by
  have hw : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW r n) F ν :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).1 (Submodule.mem_inf.1 hF).1
  ext m
  rw [Formalism.GradedWeylDivisibility.ldrow_coeff_rowAct_diag, MvPolynomial.coeff_smul, smul_eq_mul]
  by_cases h : AddMonoidAlgebra.coeff F m = 0
  · simp [h]
  · have hm := hw h
    rw [Finset.prod_pow_eq_pow_sum, mul_comm]
    congr 2
    simp only [Formalism.GradedWeylDivisibility.rowDeg]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← weight_colW_apply, hm]

end GlobalTheory.CoefScale

namespace GlobalTheory

theorem blockAct_diag_mem_VV {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → Formalism.BasicNotions.DomWeight n) (c : ι → ℂ)
    (Q : Formalism.L2.DIV.Pol ℂ ι n) (hQ : Q ∈ Formalism.L2.DIV.VV ℂ lam) :
    Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => Matrix.diagonal fun _ : Fin n => c τ) Q =
      (∏ τ, c τ ^ ∑ a, (lam τ).natW a) • Q := by
  unfold Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat at hQ
  induction hQ using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨F, hF, rfl⟩ := hP
    have h1 := (Formalism.GradedWeylDivisibility.blockActTensor ℂ ℂ ι n n (fun τ => Matrix.diagonal fun _ : Fin n => c τ)).1
    rw [map_prod]
    simp_rw [h1]
    have h2 : ∀ τ, Formalism.GradedWeylDivisibility.rowAct ℂ (Matrix.diagonal fun _ : Fin n => c τ) (F τ) =
        c τ ^ (∑ a, (lam τ).natW a) • F τ := fun τ =>
      GlobalTheory.CoefScale.rowAct_scalar_dualWeyl _ _ _ (hF τ)
    simp_rw [h2, map_smul, Algebra.smul_def, Finset.prod_mul_distrib, map_prod]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, smul_add]
  | smul a x _ hx => rw [map_smul, hx, smul_comm]

end GlobalTheory
end
end
