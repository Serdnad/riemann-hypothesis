module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle003
public import Mathlib.Algebra.Module.ZLattice.Basic
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplBoxVolume

theorem set_eq_preimage {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (a : ι → ℝ) :
    {x : ι → ℝ | ∀ i, |(A *ᵥ x) i| < a i} =
      (Matrix.toLin' A) ⁻¹' (Set.pi Set.univ fun i => Set.Ioo (-a i) (a i)) := by
  ext x
  simp [abs_lt]

end PSymplBoxVolume


open PSymplBoxVolume in
theorem SymplBoxVolume.proof : SymplBoxVolume.Statement := by
  intro ι _ _ A a hA ha
  rw [set_eq_preimage, MeasureTheory.Measure.addHaar_preimage_linearMap _ (by rwa [LinearMap.det_toLin'])
    , Real.volume_pi_Ioo, LinearMap.det_toLin',
    ← ENNReal.ofReal_prod_of_nonneg (fun i _ => by linarith [ha i]),
    ← ENNReal.ofReal_mul (abs_nonneg _), abs_inv, div_eq_mul_inv, mul_comm]
  congr 2
  refine Finset.prod_congr rfl fun i _ => ?_
  ring

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplGramMem

lemma det_map_cast {n : ℕ} {P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ}
    (hP : P ∈ symplecticGroup (Fin n) ℤ) : (P.map (Int.cast : ℤ → ℝ)).det = 1 := by
  have h := SymplecticGroup.det_eq_one (SymplecticGroup.map_mem hP (Int.castRingHom ℝ))
  simpa using h

lemma gram_diag {l : Type*} [Fintype l] (P : Matrix l l ℤ) (G : Matrix l l ℝ) (x : l) :
    symplGram P G x x = qf G (intVec (P x)) := by
  unfold symplGram qf intVec
  rw [Matrix.mul_mul_apply]
  rfl

end PSymplGramMem


open PSymplGramMem in
theorem SymplGramMem.proof : SymplGramMem.Statement := by
  intro n P G hP hG hGpd
  set P' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ := P.map (Int.cast : ℤ → ℝ) with hP'
  have hP'mem : P' ∈ symplecticGroup (Fin n) ℝ := SymplecticGroup.map_mem hP (Int.castRingHom ℝ)
  refine ⟨?_, ?_, ?_, fun x => gram_diag P G x⟩
  · exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hP'mem hG) (SymplecticGroup.transpose_mem hP'mem)
  · have hdet : IsUnit P'.det := by rw [det_map_cast hP]; exact isUnit_one
    have hinj : Function.Injective P'.vecMul :=
      vecMul_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hdet)
    have h := hGpd.mul_mul_conjTranspose_same hinj
    rwa [conjTranspose_eq_transpose_of_trivial] at h
  · intro Q
    unfold symplGram
    have hmap : (Q * P).map (Int.cast : ℤ → ℝ) = Q.map (Int.cast : ℤ → ℝ) * P.map (Int.cast : ℤ → ℝ) :=
      Matrix.map_mul (f := Int.castRingHom ℝ)
    rw [hmap, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplFirstRow

theorem intVec_ne_zero {ι : Type*} {v : ι → ℤ} (hv : v ≠ 0) : intVec v ≠ 0 := by
  intro h
  apply hv
  funext i
  have := congrFun h i
  simpa [intVec] using this

end PSymplFirstRow

theorem SymplFirstRow.proof (h1 : SymplMinExists.Statement) (h2 : SymplMinBound.Statement)
    (h3 : SymplOrbit.Statement) (h4 : SymplShortPrim.Statement) (h5 : SymplGramMem.Statement) :
    SymplFirstRow.Statement := by
  intro n G hG hpd
  obtain ⟨ρsq, hleast⟩ := h1 (Fin (n + 1) ⊕ Fin (n + 1)) G hpd
  have hdet : G.det = 1 := SymplecticGroup.det_eq_one hG
  have hbound := h2 (Fin (n + 1) ⊕ Fin (n + 1)) G hpd hdet ρsq hleast
  obtain ⟨v, hv0, hvρ⟩ := hleast.1
  refine ⟨ρsq, hleast, ?_, ?_, ?_⟩
  · rw [hvρ]
    have := hpd.dotProduct_mulVec_pos (PSymplFirstRow.intVec_ne_zero hv0)
    simpa [qf] using this
  · simp only [Fintype.card_sum, Fintype.card_fin] at hbound
    push_cast at hbound
    linarith
  · have hmin : ∀ u : Fin (n + 1) ⊕ Fin (n + 1) → ℤ, u ≠ 0 →
        qf G (intVec v) ≤ qf G (intVec u) := by
      intro u hu
      rw [← hvρ]
      exact hleast.2 ⟨u, hu, rfl⟩
    obtain ⟨P, hP, m, hm⟩ := h3 n v
    have hrow : ∃ P' ∈ symplecticGroup (Fin (n + 1)) ℤ, P' (Sum.inl 0) = v := by
      rcases h4 _ G hpd v (P (Sum.inl 0)) m hm hv0 hmin with h | h
      · exact ⟨P, hP, by rw [hm, h, one_smul]⟩
      · refine ⟨-P, SymplecticGroup.neg_mem hP, ?_⟩
        rw [hm, h, neg_one_smul]
        rfl
    obtain ⟨P', hP', hP'v⟩ := hrow
    refine ⟨P', hP', ?_⟩
    rw [(h5 (n + 1) P' G hP' hG hpd).2.2.2 (Sum.inl 0), hP'v, hvρ]

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplOmegaMem

theorem mul_J_mul_transpose_apply {R : Type*} [CommRing R] {l : Type*} [Fintype l]
    [DecidableEq l] (M : Matrix (l ⊕ l) (l ⊕ l) R) (x y : l ⊕ l) :
    (M * J l R * Mᵀ) x y = symplOmega (M x) (M y) := by
  rw [symplOmega, dotProduct_mulVec, Matrix.mul_apply]
  rfl

end PSymplOmegaMem

theorem SymplOmegaMem.proof : SymplOmegaMem.Statement := by
  intro R _ l _ _ M
  rw [SymplecticGroup.mem_iff]
  constructor
  · intro h x y
    rw [← PSymplOmegaMem.mul_J_mul_transpose_apply, h]
  · intro h
    ext x y
    rw [PSymplOmegaMem.mul_J_mul_transpose_apply, h]

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace PSymplGcd

theorem of_gcd_ne_zero (a b : ℤ) (hc : (Int.gcd a b : ℤ) ≠ 0) :
    ∃ c a' b' x y : ℤ, a = c * a' ∧ b = c * b' ∧ x * a' + y * b' = 1 := by
  obtain ⟨a', ha'⟩ := Int.gcd_dvd_left a b
  obtain ⟨b', hb'⟩ := Int.gcd_dvd_right a b
  refine ⟨(Int.gcd a b : ℤ), a', b', Int.gcdA a b, Int.gcdB a b, ha', hb', ?_⟩
  have h := Int.gcd_eq_gcd_ab a b
  apply mul_left_cancel₀ hc
  linear_combination (-Int.gcdA a b) * ha' - Int.gcdB a b * hb' - h

end PSymplGcd

theorem SymplGcd.proof : SymplGcd.Statement := by
  intro a b
  by_cases hc : (Int.gcd a b : ℤ) = 0
  · have h0 : Int.gcd a b = 0 := by exact_mod_cast hc
    obtain ⟨rfl, rfl⟩ := Int.gcd_eq_zero_iff.mp h0
    exact ⟨0, 1, 0, 1, 0, by ring, by ring, by ring⟩
  · exact PSymplGcd.of_gcd_ne_zero a b hc

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace PSymplReduceStep

theorem symplExt_map {n : ℕ} (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) :
    (symplExt (1 : ℤ) 0 0 1 Q).map (Int.cast : ℤ → ℝ) =
      symplExt 1 0 0 1 (Q.map (Int.cast : ℤ → ℝ)) := by
  ext x y
  rcases x with i | i <;> rcases y with j | j <;>
    cases i using Fin.cases <;> cases j using Fin.cases <;> simp [symplExt, symplCons]

theorem schur_toBlocks {n : ℕ} (K : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ) :
    (Matrix.of fun i j : Fin n => K.toBlocks₁₁ i.succ j.succ -
        K.toBlocks₁₁ i.succ 0 * K.toBlocks₁₁ 0 j.succ / K.toBlocks₁₁ 0 0) =
      (symplReduce K).toBlocks₁₁ := by
  ext i j
  simp [symplReduce, Matrix.toBlocks₁₁]

end PSymplReduceStep

theorem SymplReduceStep.proof (h1 : SymplExtMem.Statement) (h2 : SymplReduceConj.Statement)
    (h3 : SymplDetSchur.Statement) : SymplReduceStep.Statement := by
  intro n H Q hH hQ
  refine ⟨symplExt 1 0 0 1 Q, h1 ℤ n 1 0 0 1 Q (by norm_num) hQ, ?_⟩
  obtain ⟨he, hred⟩ := h2 n H (Q.map (Int.cast : ℤ → ℝ))
  rw [symplGram, PSymplReduceStep.symplExt_map]
  generalize symplExt 1 0 0 1 (Q.map (Int.cast : ℤ → ℝ)) * H *
    (symplExt 1 0 0 1 (Q.map (Int.cast : ℤ → ℝ)))ᵀ = K at he hred ⊢
  refine ⟨he, ?_⟩
  have hk0 : K.toBlocks₁₁ 0 0 = H (Sum.inl 0) (Sum.inl 0) := he
  rw [h3 n K.toBlocks₁₁ (hk0 ▸ hH), PSymplReduceStep.schur_toBlocks, hred, hk0]
  rfl

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

theorem SymplStep.proof (h1 : SymplFirstRow.Statement) (h2 : SymplGramMem.Statement)
    (h3 : SymplReduceMem.Statement) (h4 : SymplReducePosDef.Statement)
    (h5 : SymplReduceStep.Statement) : SymplStep.Statement := by
  intro n B G hG hGpd hind
  obtain ⟨ρsq, hleast, hpos, hle, P₁, hP₁, hP₁e⟩ := h1 n G hG hGpd
  obtain ⟨hHmem, hHpd, hcomp, -⟩ := h2 (n + 1) P₁ G hP₁ hG hGpd
  have hHe : symplGram P₁ G (Sum.inl 0) (Sum.inl 0) ≠ 0 := by
    rw [hP₁e]; exact hpos.ne'
  obtain ⟨Q, hQ, hQB⟩ :=
    hind (symplReduce (symplGram P₁ G)) (h3 n _ hHmem hHe) (h4 n _ hHpd)
  obtain ⟨Q', hQ', hQ'e, hQ'det⟩ := h5 n (symplGram P₁ G) Q hHe hQ
  refine ⟨ρsq, hleast, hpos, hle, Q' * P₁, Submonoid.mul_mem _ hQ' hP₁, ?_, ?_⟩
  · rw [hcomp Q', hQ'e, hP₁e]
  · rw [hcomp Q', hQ'det, hP₁e]
    exact mul_le_mul_of_nonneg_left hQB hpos.le

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

theorem SymplecticReduction.proof (hStep : SymplStep.Statement) (hDet : SymplDetBound.Statement) :
    SymplecticReduction.Statement := by
  intro g _ G hG hpos
  obtain ⟨n, rfl⟩ : ∃ n, g = n + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne g)
  obtain ⟨ρsq, hleast, hρ, hle, P, hP, hent, hdet⟩ :=
    hStep n ((2 * (n : ℝ)) ^ n) G hG hpos (fun H hH hHpos => hDet n H hH hHpos)
  refine ⟨ρsq, hleast, ?_, P, hP, hent, ?_⟩
  · push_cast; linarith
  · calc (symplGram P G).toBlocks₁₁.det ≤ ρsq * (2 * (n : ℝ)) ^ n := hdet
      _ ≤ ρsq * (2 * ((n + 1 : ℕ) : ℝ)) ^ (n + 1 - 1) := by
        rw [Nat.add_sub_cancel]
        apply mul_le_mul_of_nonneg_left _ hρ.le
        apply pow_le_pow_left₀ (by positivity)
        push_cast; linarith

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix MeasureTheory

namespace PSymplMinkowskiBox

theorem box_neg {ι : Type} [Fintype ι] (A : Matrix ι ι ℝ) (a : ι → ℝ) (x : ι → ℝ)
    (hx : ∀ i, |(A *ᵥ x) i| < a i) : ∀ i, |(A *ᵥ (-x)) i| < a i := by
  intro i
  rw [mulVec_neg, Pi.neg_apply, abs_neg]
  exact hx i

theorem box_convex {ι : Type} [Fintype ι] (A : Matrix ι ι ℝ) (a : ι → ℝ) :
    Convex ℝ {x : ι → ℝ | ∀ i, |(A *ᵥ x) i| < a i} := by
  intro x hx y hy s t hs ht hst i
  have hlt : s • |(A *ᵥ x) i| + t • |(A *ᵥ y) i| ∈ Set.Iio (a i) :=
    convex_Iio (a i) (hx i) (hy i) hs ht hst
  rw [Set.mem_Iio, smul_eq_mul, smul_eq_mul] at hlt
  rw [mulVec_add, mulVec_smul, mulVec_smul, Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
    smul_eq_mul, smul_eq_mul]
  calc |s * (A *ᵥ x) i + t * (A *ᵥ y) i| ≤ |s * (A *ᵥ x) i| + |t * (A *ᵥ y) i| := abs_add_le _ _
    _ = s * |(A *ᵥ x) i| + t * |(A *ᵥ y) i| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]
    _ < a i := hlt

theorem volume_fundamentalDomain_basisFun (ι : Type) [Fintype ι] :
    volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ ι)) = 1 := by
  rw [ZSpan.fundamentalDomain_pi_basisFun, volume_pi, Measure.pi_pi]
  simp [Real.volume_Ico]

end PSymplMinkowskiBox


open PSymplMinkowskiBox in
theorem SymplMinkowskiBox.proof (h1 : SymplBoxVolume.Statement) : SymplMinkowskiBox.Statement := by
  intro ι _ _ A a hdet ha hprod
  have hdet0 : A.det ≠ 0 := by
    intro h
    rw [h, abs_zero] at hdet
    exact zero_ne_one hdet
  set s : Set (ι → ℝ) := {x | ∀ i, |(A *ᵥ x) i| < a i} with hs
  have hvol : volume s = ENNReal.ofReal (2 ^ Fintype.card ι * ∏ i, a i) := by
    rw [hs, h1 ι A a hdet0 ha, hdet, div_one, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ]
  have hP : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  have hbig : volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ ι)) * 2 ^ Module.finrank ℝ (ι → ℝ) <
      volume s := by
    rw [volume_fundamentalDomain_basisFun, one_mul, Module.finrank_fintype_fun_eq_card, hvol,
      ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    exact lt_mul_of_one_lt_right hP hprod
  have : Countable (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))).toAddSubgroup := by
    change Countable (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι)))
    infer_instance
  obtain ⟨x, hx0, hxs⟩ := MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (L := (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))).toAddSubgroup)
    (ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ ι) volume)
    (fun y hy => box_neg A a y hy) (box_convex A a) hbig
  have hint : ∀ i, ∃ z : ℤ, (z : ℝ) = (x : ι → ℝ) i := by
    intro i
    obtain ⟨z, hz⟩ := ((Pi.basisFun ℝ ι).mem_span_iff_repr_mem ℤ (x : ι → ℝ)).mp x.2 i
    exact ⟨z, by simpa using hz⟩
  choose v hv using hint
  have hxv : intVec v = (x : ι → ℝ) := funext hv
  refine ⟨v, ?_, fun i => ?_⟩
  · rintro rfl
    apply hx0
    ext i
    rw [← hv i]
    simp
  · rw [hxv]
    exact hxs i

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real

noncomputable section

namespace PGaussPoissonDual

theorem qf_smul {g : ℕ} (c : ℝ) (Y : Matrix (Fin g) (Fin g) ℝ) (w : Fin g → ℝ) :
    qf (c • Y) w = c * qf Y w := by
  rw [qf, qf, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem dot_mulVec_self {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (w : Fin g → ℝ) :
    (B *ᵥ w) ⬝ᵥ (B *ᵥ w) = qf (Bᵀ * B) w := by
  rw [qf, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec w Bᵀ, Matrix.vecMul_transpose]

end PGaussPoissonDual


open PGaussPoissonDual in
theorem GaussPoissonDual.proof (hS : GaussSqrt.Statement) (hP : GaussPoissonBound.Statement)
    (hM : GaussDualMin.Statement) (hD : GaussDetFactor.Statement) :
    GaussPoissonDual.Statement := by
  intro g Y ρ hY hρ hmin u
  have hY2 : ((1 / 2 : ℝ) • Y).PosDef := hY.smul (by norm_num)
  obtain ⟨B, hB⟩ := hS g _ hY2
  have hdetB : B.det ≠ 0 := by
    intro h0
    have h1 : (Bᵀ * B).det = 0 := by rw [det_mul, det_transpose, h0, mul_zero]
    rw [hB] at h1
    exact hY2.det_pos.ne' h1
  have hterm : ∀ k : Fin g → ℤ, Real.exp (-(π / 2) * qf Y (intVec k + u)) =
      Real.exp (-π * ((B *ᵥ (intVec k + u)) ⬝ᵥ (B *ᵥ (intVec k + u)))) := by
    intro k
    rw [dot_mulVec_self, hB, qf_smul]
    ring_nf
  obtain ⟨hsum, -, hle⟩ := hP g B hdetB u
  refine ⟨(summable_congr hterm).2 hsum, GroundTheory.Global.dualLattice (gaussLattice B), ?_, ?_⟩
  · intro v hv hv0
    obtain ⟨l, hl0, hl⟩ := hM g B hdetB v hv hv0
    have hYdet : IsUnit Y.det := isUnit_iff_ne_zero.2 hY.det_pos.ne'
    have hinv : (Bᵀ * B)⁻¹ = (2 : ℝ) • Y⁻¹ := by
      rw [hB]
      apply Matrix.inv_eq_left_inv
      rw [smul_mul_smul_comm, Y.nonsing_inv_mul hYdet]
      norm_num
    rw [hinv, qf_smul] at hl
    have h2 := hmin l hl0
    have hq : 0 ≤ qf Y⁻¹ (intVec l) := le_trans (sq_nonneg ρ) h2
    have h3 : ρ ^ 2 ≤ ‖v‖ ^ 2 := by linarith
    nlinarith [norm_nonneg v]
  · rw [tsum_congr hterm, ← hD g Y B hY hB]
    exact hle

end

end GroundTheory.Heights₂.Heights
end
