module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle003
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Pi.Interval
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace PSymplQuadDiag

theorem abs_det_eq_one_of_mul_transpose {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : Matrix ι ι ℝ) (h : Oᵀ * O = 1) : |O.det| = 1 := by
  have h1 : O.det * O.det = 1 := by
    have := congrArg Matrix.det h
    rwa [det_mul, det_transpose, det_one] at this
  have h2 : |O.det| * |O.det| = 1 := by rw [← abs_mul, h1, abs_one]
  nlinarith [abs_nonneg O.det]

end PSymplQuadDiag

theorem SymplQuadDiag.proof : SymplQuadDiag.Statement := by
  intro ι _ _ G hG
  have hH := hG.isHermitian
  set U : Matrix ι ι ℝ := (hH.eigenvectorUnitary : Matrix ι ι ℝ) with hUdef
  have hstar : star U = Uᵀ := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have hspec : G = U * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star U := by
    conv_lhs => rw [hH.spectral_theorem]
    simp [hUdef]
  refine ⟨star U, hH.eigenvalues, fun i => hG.eigenvalues_pos i, ?_, ?_, ?_⟩
  · rw [hstar]
    apply PSymplQuadDiag.abs_det_eq_one_of_mul_transpose
    rw [transpose_transpose, ← hstar]
    exact Unitary.coe_mul_star_self hH.eigenvectorUnitary
  · rw [hH.det_eq_prod_eigenvalues]
    simp
  · intro x
    have hx : x ᵥ* U = star U *ᵥ x := by rw [hstar, mulVec_transpose]
    calc qf G x = x ⬝ᵥ (U *ᵥ (diagonal (RCLike.ofReal ∘ hH.eigenvalues) *ᵥ (star U *ᵥ x))) := by
          have hG' : G *ᵥ x = U *ᵥ (diagonal (RCLike.ofReal ∘ hH.eigenvalues) *ᵥ (star U *ᵥ x)) := by
            rw [mulVec_mulVec, mulVec_mulVec, ← hspec]
          rw [qf, hG']
      _ = (star U *ᵥ x) ⬝ᵥ (diagonal (RCLike.ofReal ∘ hH.eigenvalues) *ᵥ (star U *ᵥ x)) := by
          rw [dotProduct_mulVec, hx]
      _ = ∑ i, hH.eigenvalues i * (star U *ᵥ x) i ^ 2 := by
          simp only [dotProduct, mulVec_diagonal, Function.comp_apply, RCLike.ofReal_real_eq_id,
            id]
          exact Finset.sum_congr rfl fun i _ => by ring

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplOrbit

theorem smul_symplCons {R : Type*} [CommRing R] {n : ℕ} (m p q : R) (w : Fin n ⊕ Fin n → R) :
    m • symplCons p q w = symplCons (m * p) (m * q) (m • w) := by
  funext x
  rcases x with i | i <;> refine Fin.cases ?_ (fun j => ?_) i <;> simp [symplCons]

theorem symplCons_one_zero {R : Type*} [CommRing R] {n : ℕ} :
    symplCons (1 : R) 0 (0 : Fin n ⊕ Fin n → R) = Pi.single (Sum.inl 0) 1 := by
  funext x
  rcases x with i | i <;> refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [symplCons, Fin.succ_ne_zero]

end PSymplOrbit


open PSymplOrbit in
theorem SymplOrbit.proof (h1 : SymplExtMem.Statement) (h2 : SymplExtVecMul.Statement)
    (h3 : SymplTwoRow.Statement) (h4 : SymplGcd.Statement) (h5 : SymplCons.Statement) :
    SymplOrbit.Statement := by
  intro n
  induction n with
  | zero =>
    intro v
    obtain ⟨c, a', b', x, y, ha, hb, hxy⟩ := h4 (v (Sum.inl 0)) (v (Sum.inr 0))
    have hE := h1 ℤ 0 a' b' (-y) x 1 (by linarith) (Submonoid.one_mem _)
    refine ⟨_, hE, c, ?_⟩
    have htail : symplTail v = 0 := funext fun z => z.elim (fun i => i.elim0) (fun i => i.elim0)
    have hrow : symplExt a' b' (-y) x (1 : Matrix (Fin 0 ⊕ Fin 0) (Fin 0 ⊕ Fin 0) ℤ) (Sum.inl 0) =
        symplCons a' b' 0 :=
      rfl
    rw [hrow, smul_symplCons, ← ha, ← hb, smul_zero, ← htail]
    exact ((h5 ℤ 0).1 v).symm
  | succ n ih =>
    intro v
    obtain ⟨Q, hQ, m', hw⟩ := ih (symplTail v)
    obtain ⟨c, a', b', x, y, ha, hb, hxy⟩ := h4 (v (Sum.inl 0)) (v (Sum.inr 0))
    obtain ⟨k, c'', d'', x', y', hc, hm, hxy'⟩ := h4 c m'
    obtain ⟨P₂, hP₂, hrow₂⟩ := h3 n c'' d'' x' y' hxy'
    have hE₁ := h1 ℤ (n + 1) a' b' (-y) x 1 (by linarith) (Submonoid.one_mem _)
    have hE₂ := h1 ℤ (n + 1) 1 0 0 1 Q (by ring) hQ
    refine ⟨P₂ * symplExt 1 0 0 1 Q * symplExt a' b' (-y) x 1,
      Submonoid.mul_mem _ (Submonoid.mul_mem _ hP₂ hE₂) hE₁, k, ?_⟩
    have e1 : symplCons c 0 (symplTail v) ᵥ* symplExt a' b' (-y) x 1 = v := by
      rw [h2, vecMul_one]
      simp only [zero_mul, add_zero]
      rw [← ha, ← hb]
      exact (h5 ℤ (n + 1)).1 v
    have e2 : symplCons c 0 (symplCons m' 0 0) ᵥ* symplExt 1 0 0 1 Q = symplCons c 0 (symplTail v) := by
      rw [h2]
      simp only [mul_one, mul_zero, add_zero]
      congr 1
      have hs : symplCons m' 0 (0 : Fin n ⊕ Fin n → ℤ) = m' • symplCons 1 0 0 := by
        rw [smul_symplCons]; simp
      rw [hs, smul_vecMul, symplCons_one_zero, single_one_vecMul, hw]
      rfl
    have e3 : k • P₂ (Sum.inl 0) = symplCons c 0 (symplCons m' 0 0) := by
      rw [hrow₂, hc, hm, smul_symplCons, smul_symplCons]
      simp
    rw [mul_apply_eq_vecMul, mul_apply_eq_vecMul, ← smul_vecMul, ← smul_vecMul, e3, e2, e1]

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplTwoRow

def twoBlock (n : ℕ) (a b r s : ℤ) : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℤ :=
  Matrix.of (vecCons (vecCons a (vecCons b 0))
    (vecCons (vecCons (-s) (vecCons r 0)) fun k => vecCons 0 (vecCons 0 (Pi.single k 1))))

theorem twoBlock_mul_transpose {n : ℕ} {c d x y : ℤ} (h : x * c + y * d = 1) :
    twoBlock n c d x y * (twoBlock n x y c d)ᵀ = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j <;>
  simp [twoBlock, Fin.sum_univ_succ, Matrix.one_apply, Pi.single_apply] <;>
  first | linarith | (split_ifs <;> simp_all [Fin.ext_iff]) | simp [Fin.ext_iff]

end PSymplTwoRow


open PSymplTwoRow in
theorem SymplTwoRow.proof : SymplTwoRow.Statement := by
  intro n c d x y h
  refine ⟨fromBlocks (twoBlock n c d x y) 0 0 (twoBlock n x y c d), ?_, ?_⟩
  · rw [SymplecticGroup.mem_iff]
    have h1 := twoBlock_mul_transpose (n := n) h
    have h2 : twoBlock n x y c d * (twoBlock n c d x y)ᵀ = 1 := by
      rw [← transpose_transpose (twoBlock n x y c d), ← transpose_mul, h1, transpose_one]
    simp [J, fromBlocks_transpose, fromBlocks_multiply, h1, h2]
  · funext z
    rcases z with i | i
    · refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
        simp [symplCons, twoBlock]
    · refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
        simp [symplCons]

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplMinExists

variable {ι : Type} [Fintype ι]

theorem qf_smul (G : Matrix ι ι ℝ) (c : ℝ) (x : ι → ℝ) : qf G (c • x) = c ^ 2 * qf G x := by
  simp only [qf, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

theorem continuous_qf (G : Matrix ι ι ℝ) : Continuous (qf G) :=
  continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)

theorem exists_lower [DecidableEq ι] [Nonempty ι] (G : Matrix ι ι ℝ) (hG : G.PosDef) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ x : ι → ℝ, μ * ‖x‖ ^ 2 ≤ qf G x := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hpos : ∀ x : ι → ℝ, x ≠ 0 → 0 < qf G x := fun x hx => by
    simpa [qf] using hG.dotProduct_mulVec_pos hx
  have hK : IsCompact (Metric.sphere (0 : ι → ℝ) 1) := isCompact_sphere 0 1
  have hne : (Metric.sphere (0 : ι → ℝ) 1).Nonempty :=
    ⟨Pi.single i₀ 1, by simp [Pi.norm_single]⟩
  obtain ⟨u, hu, hmin⟩ := hK.exists_isMinOn hne (continuous_qf G).continuousOn
  refine ⟨qf G u, hpos u ?_, fun x => ?_⟩
  · rintro rfl
    simp at hu
  · by_cases hx : x = 0
    · subst hx
      simp [qf]
    · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hy : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : ι → ℝ) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
      have h1 : qf G u ≤ qf G (‖x‖⁻¹ • x) := isMinOn_iff.mp hmin _ hy
      calc qf G u * ‖x‖ ^ 2 ≤ qf G (‖x‖⁻¹ • x) * ‖x‖ ^ 2 := by gcongr
        _ = qf G x := by
          rw [qf_smul]
          field_simp

end PSymplMinExists

theorem SymplMinExists.proof (h1 : SymplQuadDiag.Statement) : SymplMinExists.Statement := by
  intro ι _ _ _ G hG
  obtain ⟨μ, hμ, hlow⟩ := PSymplMinExists.exists_lower G hG
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  set v₀ : ι → ℤ := Pi.single i₀ 1 with hv₀def
  set M₀ : ℝ := qf G (intVec v₀) with hM₀
  set R : ℤ := ⌈M₀ / μ⌉ with hR
  set S : Set (ι → ℤ) := {v | v ≠ 0 ∧ qf G (intVec v) ≤ M₀} with hS
  have hbox : S ⊆ Set.Icc (fun _ => -R) (fun _ => R) := by
    rintro v ⟨-, hq⟩
    have hb : ∀ i, |(v i : ℝ)| ≤ M₀ / μ := by
      intro i
      have hi : |(v i : ℝ)| ≤ ‖intVec v‖ := by
        have := norm_le_pi_norm (intVec v) i
        simpa [intVec, Real.norm_eq_abs] using this
      have hsq : |(v i : ℝ)| ≤ |(v i : ℝ)| ^ 2 := by
        rcases eq_or_ne (v i) 0 with h | h
        · simp [h]
        · have h' : (1 : ℝ) ≤ |(v i : ℝ)| := by
            rw [← Int.cast_abs]
            exact_mod_cast Int.one_le_abs h
          nlinarith
      have hsq2 : |(v i : ℝ)| ^ 2 ≤ ‖intVec v‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hi 2
      rw [le_div_iff₀ hμ]
      calc |(v i : ℝ)| * μ ≤ μ * ‖intVec v‖ ^ 2 := by nlinarith
        _ ≤ qf G (intVec v) := hlow _
        _ ≤ M₀ := hq
    have hc : ∀ i, |v i| ≤ R := by
      intro i
      have : ((|v i| : ℤ) : ℝ) ≤ (R : ℝ) := by
        rw [Int.cast_abs]
        exact (hb i).trans (Int.le_ceil _)
      exact_mod_cast this
    refine ⟨fun i => ?_, fun i => ?_⟩
    · exact (abs_le.mp (hc i)).1
    · exact (abs_le.mp (hc i)).2
  have hfin : S.Finite := (Set.finite_Icc _ _).subset hbox
  have hv₀ : v₀ ∈ S := by
    refine ⟨fun h => ?_, le_rfl⟩
    have := congrFun h i₀
    simp [v₀] at this
  obtain ⟨w, hwS, hwmin⟩ := Set.exists_min_image S (fun v => qf G (intVec v)) hfin ⟨v₀, hv₀⟩
  refine ⟨qf G (intVec w), ⟨w, hwS.1, rfl⟩, ?_⟩
  rintro t ⟨v, hv, rfl⟩
  by_cases hvS : qf G (intVec v) ≤ M₀
  · exact hwmin v ⟨hv, hvS⟩
  · exact hwS.2.trans (le_of_lt (not_le.mp hvS))

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplMinBound

theorem prod_sqrt_eq_one {ι : Type} [Fintype ι] (lam : ι → ℝ) (hlam : ∀ i, 0 < lam i)
    (hprod : ∏ i, lam i = 1) : ∏ i, Real.sqrt (lam i) = 1 := by
  have hnn : 0 ≤ ∏ i, Real.sqrt (lam i) := Finset.prod_nonneg fun i _ => Real.sqrt_nonneg _
  have hsq : (∏ i, Real.sqrt (lam i)) ^ 2 = 1 := by
    rw [← Finset.prod_pow]
    simp_rw [Real.sq_sqrt (hlam _).le]
    exact hprod
  nlinarith [hsq, hnn]

theorem exists_lt (h2 : SymplMinkowskiBox.Statement) {ι : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (O : Matrix ι ι ℝ) (lam : ι → ℝ) (hlam : ∀ i, 0 < lam i) (hO : |O.det| = 1)
    (hprod : ∏ i, lam i = 1) (c : ℝ) (hc : 1 < c) :
    ∃ v : ι → ℤ, v ≠ 0 ∧
      ∑ i, lam i * (O *ᵥ intVec v) i ^ 2 < (Fintype.card ι : ℝ) * c ^ 2 := by
  have hc0 : 0 < c := by linarith
  have ha : ∀ i, 0 < c / Real.sqrt (lam i) := fun i => div_pos hc0 (Real.sqrt_pos.2 (hlam i))
  have hpa : 1 < ∏ i, c / Real.sqrt (lam i) := by
    rw [Finset.prod_div_distrib, prod_sqrt_eq_one lam hlam hprod, div_one, Finset.prod_const,
      Finset.card_univ]
    exact one_lt_pow₀ hc Fintype.card_ne_zero
  obtain ⟨v, hv, hbox⟩ := h2 ι O (fun i => c / Real.sqrt (lam i)) hO ha hpa
  refine ⟨v, hv, ?_⟩
  have hlt : ∀ i ∈ (Finset.univ : Finset ι), lam i * (O *ᵥ intVec v) i ^ 2 < c ^ 2 := by
    intro i _
    have hs := Real.sqrt_pos.2 (hlam i)
    have h1 : |(O *ᵥ intVec v) i| * Real.sqrt (lam i) < c := (lt_div_iff₀ hs).1 (hbox i)
    have h2' : (|(O *ᵥ intVec v) i| * Real.sqrt (lam i)) ^ 2 < c ^ 2 :=
      pow_lt_pow_left₀ h1 (mul_nonneg (abs_nonneg _) hs.le) two_ne_zero
    rw [mul_pow, sq_abs, Real.sq_sqrt (hlam i).le] at h2'
    linarith
  calc ∑ i, lam i * (O *ᵥ intVec v) i ^ 2 < ∑ _i : ι, c ^ 2 :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty hlt
    _ = (Fintype.card ι : ℝ) * c ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end PSymplMinBound

theorem SymplMinBound.proof (h1 : SymplQuadDiag.Statement) (h2 : SymplMinkowskiBox.Statement) :
    SymplMinBound.Statement := by
  intro ι _ _ G hG hdet m hm
  obtain ⟨w, hw, -⟩ := hm.1
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hw (funext fun i => (IsEmpty.false i).elim)
  obtain ⟨O, lam, hlam, hO, hprod, hq⟩ := h1 ι G hG
  rw [hdet] at hprod
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have key : ∀ c : ℝ, 1 < c → m < (Fintype.card ι : ℝ) * c ^ 2 := by
    intro c hc
    obtain ⟨v, hv, hlt⟩ := PSymplMinBound.exists_lt h2 O lam hlam hO hprod c hc
    have hmv : m ≤ qf G (intVec v) := hm.2 ⟨v, hv, rfl⟩
    rw [hq] at hmv
    linarith
  by_contra hcon
  rw [not_le] at hcon
  set N : ℝ := (Fintype.card ι : ℝ) with hNdef
  set t : ℝ := (m / N + 1) / 2 with htdef
  have hmN : 1 < m / N := by rw [lt_div_iff₀ hN]; linarith
  have ht : 1 < t := by rw [htdef]; linarith
  have hsqrt : 1 < Real.sqrt t := by
    rw [Real.lt_sqrt zero_le_one]; linarith
  have hk := key (Real.sqrt t) hsqrt
  rw [Real.sq_sqrt (by linarith)] at hk
  have : N * t = (m + N) / 2 := by
    rw [htdef]; field_simp
  linarith

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplShortPrim

lemma intVec_smul {ι : Type} (m : ℤ) (w : ι → ℤ) : intVec (m • w) = (m : ℝ) • intVec w := by
  funext i
  simp [intVec]

lemma qf_smul {ι : Type} [Fintype ι] (Y : Matrix ι ι ℝ) (c : ℝ) (x : ι → ℝ) :
    qf Y (c • x) = c ^ 2 * qf Y x := by
  simp only [qf, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

end PSymplShortPrim


open PSymplShortPrim in
theorem SymplShortPrim.proof : SymplShortPrim.Statement := by
  intro ι _ _ G hG v w m hvw hv hmin
  have hm : m ≠ 0 := by
    rintro rfl
    exact hv (by simp [hvw])
  have hw : w ≠ 0 := by
    rintro rfl
    exact hv (by simp [hvw])
  have hwR : intVec w ≠ 0 := by
    intro h
    apply hw
    funext i
    have := congrFun h i
    simpa [intVec] using this
  have hq : 0 < qf G (intVec w) := by
    have := hG.dotProduct_mulVec_pos hwR
    simpa [qf] using this
  have hle := hmin w hw
  rw [hvw, intVec_smul, qf_smul] at hle
  have hm2 : ((m : ℝ)) ^ 2 ≤ 1 := by
    by_contra h
    rw [not_le] at h
    nlinarith
  have hm2' : m ^ 2 ≤ 1 := by exact_mod_cast hm2
  have habs : |m| ≤ 1 := (sq_le_one_iff_abs_le_one m).mp hm2'
  rw [abs_le] at habs
  omega

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

theorem SymplExtVecMul.proof : SymplExtVecMul.Statement := by
  intro R _ n α β γ δ p q Q w
  funext y
  rcases y with y | y <;> refine Fin.cases ?_ (fun j => ?_) y <;>
    simp [vecMul, dotProduct, symplCons, symplExt, Fintype.sum_sum_type, Fin.sum_univ_succ]

end GroundTheory.Heights₂.Heights
end
