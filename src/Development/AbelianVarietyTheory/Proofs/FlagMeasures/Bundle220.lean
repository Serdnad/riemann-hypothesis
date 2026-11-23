module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicLeviEmbeddingHomomorphismProperties
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantFlagLengthsInvarianceTorusPositivity
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedDualVectorPairingBoundedMajorant
public import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe
import Formalism.FormalDegreeBessel.FinalG
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle170
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle183
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle012
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle206
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Real.Pi.Bounds
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle013
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle204

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Amp.NfComp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.NfOff

lemma exists_blockEnd {r : ℕ} {β : Fin r → ℕ} (hβ : Monotone β) (c : Fin r) :
    ∃ l, l ≤ r ∧ ∀ i : Fin r, i.val < l ↔ β i ≤ β c := by
  obtain ⟨d, hd, hmax⟩ := Finset.exists_max_image (Finset.univ.filter fun i : Fin r => β i ≤ β c) id
    ⟨c, by simp⟩
  refine ⟨d.val + 1, d.2, fun i => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact (hβ (show i ≤ d from Nat.le_of_lt_succ h)).trans (Finset.mem_filter.1 hd).2
  · exact Nat.lt_succ_of_le (hmax i (by simpa using h))

lemma minor_ne_zero {r l : ℕ} (hl : l ≤ r) (Z : Matrix (Fin r) (Fin r) ℂ) (hZ : Z.det ≠ 0)
    (h : ∀ i : Fin r, ¬ i.val < l → ∀ j : Fin r, j.val < l → Z i j = 0) :
    (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det ≠ 0 := by
  rw [Matrix.twoBlockTriangular_det Z (fun i => i.val < l) h] at hZ
  have h1 := left_ne_zero_of_mul hZ
  let e : Fin l ≃ {i : Fin r // i.val < l} :=
    ⟨fun i => ⟨Fin.castLE hl i, i.2⟩, fun i => ⟨i.1.val, i.2⟩, fun _ => rfl, fun _ => rfl⟩
  rw [← Matrix.det_submatrix_equiv_self e] at h1
  exact h1

lemma Zr_mul_uEmb {k r : ℕ} (g : Mat k r) (u : Matrix (Fin r) (Fin r) ℂ) (hu : IsUnit u.det) :
    Zr k r (g * uEmb k r u) = Zr k r g * u := by
  ext a b
  have h := ((GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.1 u hu).2.2.1 b
  have h2 : Zr k r (g * uEmb k r u) a b = (g *ᵥ (uEmb k r u *ᵥ bvec (eI k r b))) (esI k r a) := by
    rw [Matrix.mulVec_mulVec]; simp [bvec, Zr]
  rw [h2, h, Matrix.mulVec_sum, Finset.sum_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp [bvec, Zr, Matrix.mulVec_smul, mul_comm]

lemma N_sub_S {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) {n : Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, ⟨(uHGroup _ _ (Hunit k r)).1, by simp, by simp⟩, _, hn, (one_mul _).symm⟩

theorem offBlock_le : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g₀ : Mat k r) (β : Fin r → ℕ) (De R₀ : ℝ), TwoFl k r z z' g₀ → IsNormal k r β g₀ → DeOK k r z z' g₀ De → 1 ≤ R₀ → ∀ m ∈ UH (Hb k), ∀ (y : UToff β → ℂ) (q : PPar k r) (a : Fin r → ℝ), (∀ b, 0 < a b) → Sg k r z' (uEmb k r (upperOff β y) * pOf k r q * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) ≤ R₀ → Sg k r z (g₀ * (uEmb k r (upperOff β y) * pOf k r q * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) ≤ R₀ → ∀ p, ‖y p‖ ≤ R₀ ^ (2 * r) * De := by
  intro k r z z' g₀ β De R₀ hT hN hDe hR m hm y q a ha hS' hS p
  obtain ⟨hz, hz', -⟩ := hT
  obtain ⟨hg, -, hβ, hdet, hblk, -⟩ := hN
  obtain ⟨⟨⟨c, b⟩, hcb⟩, hβcb⟩ := p
  simp only at hcb hβcb
  obtain ⟨hg1, he⟩ := levi_diag_middle_mem_bessel_unitary_eucl (r := r) hm a ha
  have hU1 : (upperOff β y).det = 1 := ((GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.2 _).1
  have hUu : IsUnit (upperOff β y).det := by rw [hU1]; exact isUnit_one
  have hUN : uEmb k r (upperOff β y) ∈ Nset k r := ((GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.2 _).2
  have hPN : pOf k r q ∈ Nset k r :=
    (((GlobalTheory.Amp.Rad.radical k r).1 _ _).2.2.2 ((GlobalTheory.Amp.Rad.radical k r).2.1 _ _)).1
  have hPe : ∀ d : Fin r, pOf k r q *ᵥ bvec (eI k r d) = bvec (eI k r d) := ((GlobalTheory.Amp.Rad.radical k r).1 _ _).1
  have hs : uEmb k r (upperOff β y) * pOf k r q ∈ Nset k r := (nSubgroup k r).2.1 _ hUN _ hPN
  rw [Matrix.mul_assoc (uEmb k r (upperOff β y) * pOf k r q)] at hS hS'
  have hlen : ∀ d : Fin r, (a d)⁻¹ ≤ R₀ := by
    intro d
    have h1 := (((GlobalTheory.Amp.LInv.lengths_basic k r z' hz').1 _ hg1 _ (N_sub_S z' hs) 1
      ⟨(uHGroup _ _ (Hunit k r)).1, one_mem _⟩).1 d.castSucc)
    rw [mul_one, (GlobalTheory.Amp.LInv.lengths_basic k r z' hz').2.1 a ha m hm] at h1
    rw [← h1]
    exact ((((GlobalTheory.Amp.LInv.lengths_basic k r z' hz').2.2 _).2.1 _).2).trans hS'
  set g₁ := uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m with hg₁
  set U := upperOff β y with hU
  obtain ⟨l, hl, hlβ⟩ := exists_blockEnd hβ c
  have hcl : c.val < l := (hlβ c).2 le_rfl
  have hZ0 : ∀ i j : Fin r, (i.val < l ↔ ¬ j.val < l) → Zr k r g₀ i j = 0 := by
    intro i j hij
    by_contra h
    have := hblk i j h
    rw [hlβ, hlβ, this] at hij
    tauto
  have hcr := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.cramerUpper ℂ r l hl 1 (Zr k r g₀) U (by simp)
    (fun i j h => Matrix.one_apply_ne h.ne) (fun i => by simp [hU, upperOff, upper])
    (fun i j h => by
      simp only [hU, upperOff, upper]
      rw [dite_eq_right (not_lt.2 h.le), if_neg h.ne'])
    (fun i j hi hj => hZ0 i j ⟨fun _ => not_lt.2 hj, fun _ => hi⟩) ⟨c.val, hcl⟩ b
    (fun c' hc' => by
      by_contra h
      rcases upperOff_ne hβ y _ _ h with h' | h'
      · exact hc'.ne (Fin.castLE_injective hl h')
      · exact absurd ((hlβ (Fin.castLE hl c')).1 c'.2) (not_le.2 h'))
  have hUcb : U (Fin.castLE hl ⟨c.val, hcl⟩) b = y ⟨⟨(c, b), hcb⟩, hβcb⟩ := by
    show upperOff β y c b = _
    simp only [upperOff, upper]
    rw [dite_eq_left hcb, dite_eq_left hβcb]
  rw [Matrix.one_mul, hUcb, ← Zr_mul_uEmb g₀ U hUu] at hcr
  have hD1 : ((Zr k r (g₀ * uEmb k r U)).submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      Dmin k r z z' g₀ ⟨l, by omega⟩ := by
    have h1 := dInv k r z z' hz hz' 1 (N_sub_S z (nSubgroup k r).1) _ (N_sub_S z' hUN) g₀ ⟨l, by omega⟩
    rw [Matrix.one_mul] at h1
    rw [← h1, Dmin_eq le_rfl z z' _ l hl]
    rfl
  have hD0 : Dmin k r z z' g₀ ⟨l, by omega⟩ ≠ 0 := by
    rw [Dmin_eq le_rfl z z' _ l hl]
    exact minor_ne_zero hl _ hdet fun i hi j hj => hZ0 i j ⟨fun h => absurd h hi, fun h => absurd hj h⟩
  have hDb := hDe.2 ⟨l, by omega⟩ hl hD0
  rw [hD1] at hcr
  set σ : Fin l → Fin r := fun j => if j = ⟨c.val, hcl⟩ then b else Fin.castLE hl j with hσ
  have hx := G_mul hg (G_mul hs.1 hg1)
  have hp := pluck_flag hl z hz _ hx R₀ hS (fun i => g₁⁻¹ *ᵥ bvec (eI k r (σ i))) (fun i => by
    rw [he]; exact hlen _)
  have hmat : (Matrix.of fun i i' : Fin l =>
      herm (Hpk k r) ((g₀ * (uEmb k r U * pOf k r q * g₁))⁻¹ *ᵥ bvec (eI k r (Fin.castLE hl i')))
        (g₁⁻¹ *ᵥ bvec (eI k r (σ i)))) = ((Zr k r (g₀ * uEmb k r U)).submatrix (Fin.castLE hl) σ)ᴴ := by
    ext i i'
    rw [Matrix.of_apply, herm_inv_left hx, herm_symm, herm_e, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (G_unit hg1), Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mulVec_mulVec, hPe]
    simp [bvec, Zr]
  rw [hmat, Matrix.det_conjTranspose, norm_star, hcr, norm_mul] at hp
  have hP0 : 0 < ‖Dmin k r z z' g₀ ⟨l, by omega⟩‖ := norm_pos_iff.2 hD0
  have hpow : R₀ ^ l * R₀ ^ l ≤ R₀ ^ (2 * r) := by
    rw [← pow_add]; exact pow_le_pow_right₀ hR (by omega)
  calc _ ≤ R₀ ^ (2 * r) * ‖Dmin k r z z' g₀ ⟨l, by omega⟩‖⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀' hP0]; exact hp.trans hpow
    _ ≤ _ := mul_le_mul_of_nonneg_left hDb (by positivity)

end GlobalTheory.Amp.NfOff
end
end

section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal Pointwise

noncomputable section

namespace GlobalTheory.TwoSidedMoments

open GlobalTheory.AmpMoments

theorem size_bound_inv {b v g x Cg Cu CT : ℝ} {r : ℕ} (hb : Real.exp 1 < b) (hv : 1 ≤ v) (hvb : 2 * v ≤ b)
    (hg : 1 ≤ g) (hgb : g ≤ b ^ (2 * Cg)) (hCg : 8 ≤ Cg) (hx0 : 0 ≤ x)
    (hx : x ≤ max (Real.pi / v / g) (Real.pi / v / g)⁻¹ ^ r) :
    x * (b ^ max 2 Cu) ^ (2 * r) ≤ b ^ ((2 * Cg + 2 + |CT| + 10 * max 2 Cu) * (2 * r + 2 : ℝ)) := by
  have hb2 : 2 < b := lt_trans (by have := Real.exp_one_gt_d9; linarith) hb
  have hb1 : 1 ≤ b := by linarith
  have hb0 : 0 < b := by linarith
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hB : (2 : ℝ) ≤ max 2 Cu := le_max_left _ _
  have hp := Real.pi_gt_three
  have hg2 : 1 ≤ b ^ (2 * Cg) := hg.trans hgb
  have hM : max (Real.pi / v / g) (Real.pi / v / g)⁻¹ ≤ b ^ (2 * Cg + 2) := by
    rw [Real.rpow_add hb0, Real.rpow_two]
    refine max_le ?_ ?_
    · have : Real.pi / v / g ≤ Real.pi :=
        (div_le_self (by positivity) hg).trans (div_le_self (by positivity) hv)
      have := Real.pi_le_four
      nlinarith
    · rw [div_div, inv_div, div_le_iff₀ (by positivity)]
      have h1 : v * g ≤ b ^ 2 * b ^ (2 * Cg) := mul_le_mul (by nlinarith) hgb (by linarith) (by positivity)
      have : 0 ≤ b ^ (2 * Cg) * b ^ 2 := by positivity
      nlinarith
  have h1 : x ≤ b ^ ((2 * Cg + 2) * r) := by
    rw [Real.rpow_mul_natCast hb0.le]
    exact hx.trans (pow_le_pow_left₀ (le_max_of_le_left (by positivity)) hM r)
  calc x * (b ^ max 2 Cu) ^ (2 * r) ≤ b ^ ((2 * Cg + 2) * r) * (b ^ max 2 Cu) ^ (2 * r) := by gcongr
    _ = b ^ ((2 * Cg + 2) * r + max 2 Cu * ((2 * r : ℕ) : ℝ)) := by
        rw [Real.rpow_add hb0, Real.rpow_mul_natCast hb0.le (max 2 Cu)]
    _ ≤ _ := by
        refine Real.rpow_le_rpow_of_exponent_le hb1 ?_
        push_cast
        have := abs_nonneg CT
        nlinarith [mul_nonneg this hr, mul_nonneg (by linarith : 0 ≤ Cg) hr, mul_nonneg (by linarith : 0 ≤ max 2 Cu) hr]

theorem rpow_bridge {b C x : ℝ} {q : ℕ} (hb : 0 ≤ b) : b ^ (2 * C * x * q) = (b ^ (C * x)) ^ (2 * q) := by
  rw [← Real.rpow_mul_natCast hb]; congr 1; push_cast; ring

end GlobalTheory.TwoSidedMoments

namespace GlobalTheory.TwoSidedMoments

open GlobalTheory.AmpMoments

theorem hypTT_self (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) (hZ : HypZ D large₂ C' Cl Cg cb Cu cT CT C0)
    (w : D.what₂.Word) : HypTT D w w := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, hg1, -, hg2, -, -, -, -, -, -, -, -, -, -, -⟩, hDat, -⟩ := hZ
  obtain ⟨-, -, -, -, -, -, -, -, hmod, -⟩ := hDat
  have hk : (1 : ℝ) ≤ D.R.k := by have := D.R.m_add_three_le_k; exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hL : 1 < large₂.sc.L := Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
  have hbe : Real.exp 1 < large₂.sc.b := Real.exp_lt_exp.2 hL
  have hb2 : 2 < large₂.sc.b := lt_trans (by have := Real.exp_one_gt_d9; linarith) hbe
  have hkb : 2 < (D.R.k : ℝ) * large₂.sc.b := by nlinarith
  have hg : (2 : ℝ) < D.host.g 0 := lt_of_lt_of_le hkb ((le_self_pow₀ (by linarith) (by norm_num)).trans hg1)
  have hg' : 2 < D.host.g 0 := by exact_mod_cast hg
  have hgg : (2 : ℝ) < D.host.g 1 := lt_of_lt_of_le hkb ((le_self_pow₀ (by linarith) (by norm_num)).trans hg2)
  have hgg' : 2 < D.host.g 1 := by exact_mod_cast hgg
  have hp := (D.mem w).A.T_prime
  have h3 : 3 ≤ (D.mem w).A.T := by
    rcases (D.mem w).A.T_prime.two_le.eq_or_lt with h | h
    · exfalso
      have hm := (hmod w).2
      rw [← h] at hm
      have hN : 4 < (D.host.g 0 * D.host.g 1) ^ 2 := by
        have h9 : 9 ≤ D.host.g 0 * D.host.g 1 := Nat.mul_le_mul (show 3 ≤ D.host.g 0 from hg') (show 3 ≤ D.host.g 1 from hgg')
        nlinarith
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hm
      omega
    · omega
  exact ⟨hp, hp, h3, h3, Int.ModEq.refl _⟩

end GlobalTheory.TwoSidedMoments

namespace GlobalTheory.TwoSidedMoments

open GlobalTheory.AmpMoments

theorem rd_le_b (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) (hCl : 1000 ≤ Cl)
    (hZ : HypZ D large₂ C' Cl Cg cb Cu cT CT C0) : D.host.rdE ≤ large₂.sc.b := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, hrdL, -, -, -, -, -, -, -, hv, -⟩, -, -⟩ := hZ
  have hL : 1 < large₂.sc.L := Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
  have hrd : D.host.rdE = 2 * D.host.v := by unfold Host.v; ring
  have h0 : 0 < D.host.rdE := by rw [hrd]; linarith
  have h1 : large₂.sc.L / Cl ≤ large₂.sc.L := div_le_self (by linarith) (by linarith)
  show D.host.rdE ≤ Real.exp large₂.sc.L
  exact (Real.log_le_iff_le_exp h0).1 (hrdL.trans h1)

end GlobalTheory.TwoSidedMoments
end
end

section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.Amp.TailTwo

theorem cheb_le {X : Type*} [MeasurableSpace X] (ν : Measure X) (l : X → ℝ) (f : X → ℝ≥0∞) (E : Set X)
    (hE : MeasurableSet E) (T : ℝ) (hT : 0 < T) (hl : ∀ x ∈ E, T ≤ l x) (n : ℕ) :
    ∫⁻ x in E, f x ∂ν ≤ ENNReal.ofReal ((T ^ n)⁻¹) * ∫⁻ x, ENNReal.ofReal (l x ^ n) * f x ∂ν := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine le_trans (setLIntegral_mono' hE fun x hx => ?_) (setLIntegral_le_lintegral E _)
  have hTn : 0 < T ^ n := pow_pos hT n
  rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hTn.le)]
  refine le_mul_of_one_le_left' ?_
  rw [ENNReal.one_le_ofReal, inv_mul_eq_div, one_le_div hTn]
  exact pow_le_pow_left₀ hT.le (hl x hx) n

theorem meas_closed (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℝ) (hg : ContinuousOn g (GG k r)) (t : Set ℝ) (ht : IsClosed t) :
    MeasurableSet {x : Mt k r | Matrix.of x ∈ GG k r ∧ g (Matrix.of x) ∈ t} := by
  obtain ⟨u, hu, h⟩ := (continuousOn_iff_isClosed.1 hg) t ht
  have h1 : MeasurableSet (α := Mt k r) u := IsClosed.measurableSet (α := Mt k r) hu
  have h2 : MeasurableSet (α := Mt k r) (GG k r) := IsClosed.measurableSet (α := Mt k r) (Cheb.isClosed_GG k r)
  have h3 : {x : Mt k r | Matrix.of x ∈ GG k r ∧ g (Matrix.of x) ∈ t} = u ∩ GG k r := by
    rw [← h]
    ext x
    exact ⟨fun hx => ⟨hx.2, hx.1⟩, fun hx => ⟨hx.2, hx.1⟩⟩
  rw [h3]
  exact h1.inter h2

theorem meas_open (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℝ) (hg : ContinuousOn g (GG k r)) (t : Set ℝ) (ht : IsOpen t) :
    MeasurableSet {x : Mt k r | Matrix.of x ∈ GG k r ∧ g (Matrix.of x) ∈ t} := by
  obtain ⟨u, hu, h⟩ := continuousOn_iff'.1 hg t ht
  have h1 : MeasurableSet (α := Mt k r) u := IsOpen.measurableSet (α := Mt k r) hu
  have h2 : MeasurableSet (α := Mt k r) (GG k r) := IsClosed.measurableSet (α := Mt k r) (Cheb.isClosed_GG k r)
  have h3 : {x : Mt k r | Matrix.of x ∈ GG k r ∧ g (Matrix.of x) ∈ t} = u ∩ GG k r := by
    rw [← h]
    ext x
    exact ⟨fun hx => ⟨hx.2, hx.1⟩, fun hx => ⟨hx.2, hx.1⟩⟩
  rw [h3]
  exact h1.inter h2

end GlobalTheory.Amp.TailTwo

namespace GlobalTheory.Amp.TailTwo

theorem tailBd_of_moments : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (νS : Measure (Mt k r)) (Φ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Wp) (q : ℕ) (H₁ : ℝ), inWb k r z → 0 < H₁ → νS {x | Matrix.of x ∉ GG k r} = 0 → ContinuousOn Φ (GG k r) → MomBd z νS Φ q H₁ → (∀ a : Fin (r + 1), ∫⁻ x, ENNReal.ofReal ((lA k r z (Matrix.of x) a)⁻¹ ^ (2 * q)) * (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂νS ≤ ENNReal.ofReal (H₁ ^ (2 * q)) * l2SG νS Φ) → TailBd z νS Φ q H₁ := by
  intro k r Wp _ _ _ z νS Φ q H₁ _ hH hG _ hM hI la hla
  set T : ℝ := la * H₁ with hTdef
  have hT : 0 < T := mul_pos hla hH
  set f : Mt k r → ℝ≥0∞ := fun x => (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 with hf
  set A : Fin (r + 1) → Set (Mt k r) := fun a =>
    {x : Mt k r | Matrix.of x ∈ GG k r ∧ (fun g => lA k r z g a) (Matrix.of x) ∈ Set.Ici T} with hA
  set B : Fin (r + 1) → Set (Mt k r) := fun a =>
    {x : Mt k r | Matrix.of x ∈ GG k r ∧ (fun g => lA k r z g a) (Matrix.of x) ∈ Set.Ioi 0} ∩
    {x : Mt k r | Matrix.of x ∈ GG k r ∧ (fun g => lA k r z g a) (Matrix.of x) ∈ Set.Iic T⁻¹} with hB
  set N : Set (Mt k r) := {x | Matrix.of x ∉ GG k r} with hN
  have hGc : MeasurableSet (α := Mt k r) (GG k r) := IsClosed.measurableSet (α := Mt k r) (Cheb.isClosed_GG k r)
  have hNm : MeasurableSet N := hGc.compl
  have hAm : ∀ a, MeasurableSet (A a) := fun a =>
    meas_closed k r _ ((LenCont.lA_Sg_continuousOn k r z).1 a) _ isClosed_Ici
  have hBm : ∀ a, MeasurableSet (B a) := fun a =>
    (meas_open k r _ ((LenCont.lA_Sg_continuousOn k r z).1 a) _ isOpen_Ioi).inter
      (meas_closed k r _ ((LenCont.lA_Sg_continuousOn k r z).1 a) _ isClosed_Iic)
  set U : Set (Mt k r) := N ∪ ⋃ a, (A a ∪ B a) with hU
  have hUm : MeasurableSet U := hNm.union (MeasurableSet.iUnion fun a => (hAm a).union (hBm a))
  have hsub : {x : Mt k r | ∃ a : Fin (r + 1), la * H₁ ≤ max (lA k r z (Matrix.of x) a) (lA k r z (Matrix.of x) a)⁻¹} ⊆ U := by
    rintro x ⟨a, ha⟩
    by_cases hx : Matrix.of x ∈ GG k r
    · refine Or.inr (Set.mem_iUnion.2 ⟨a, ?_⟩)
      rcases le_max_iff.1 ha with h | h
      · exact Or.inl ⟨hx, h⟩
      · have hpos : 0 < lA k r z (Matrix.of x) a := inv_pos.1 (lt_of_lt_of_le hT h)
        refine Or.inr ⟨⟨hx, hpos⟩, hx, ?_⟩
        show lA k r z (Matrix.of x) a ≤ T⁻¹
        exact (le_inv_comm₀ hT hpos).1 h
    · exact Or.inl hx
  have hc : ∀ a, ∫⁻ x in A a ∪ B a, f x ∂νS ≤ 2 * (ENNReal.ofReal (la ^ (-(2 * (q : ℝ)))) * l2SG νS Φ) := by
    intro a
    have key : ENNReal.ofReal ((T ^ (2 * q))⁻¹) * (ENNReal.ofReal (H₁ ^ (2 * q)) * l2SG νS Φ) =
        ENNReal.ofReal (la ^ (-(2 * (q : ℝ)))) * l2SG νS Φ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      rw [Real.rpow_neg hla.le, hTdef, mul_pow]
      have : la ^ (2 * (q : ℝ)) = la ^ (2 * q) := by
        rw [← Real.rpow_natCast]; push_cast; ring_nf
      rw [this]
      have h1 : H₁ ^ (2 * q) ≠ 0 := pow_ne_zero _ hH.ne'
      field_simp
    have hA' : ∫⁻ x in A a, f x ∂νS ≤ ENNReal.ofReal (la ^ (-(2 * (q : ℝ)))) * l2SG νS Φ := by
      refine (cheb_le νS (fun x => lA k r z (Matrix.of x) a) f (A a) (hAm a) T hT (fun x hx => hx.2) (2 * q)).trans ?_
      rw [← key]
      gcongr
      exact hM a
    have hB' : ∫⁻ x in B a, f x ∂νS ≤ ENNReal.ofReal (la ^ (-(2 * (q : ℝ)))) * l2SG νS Φ := by
      refine (cheb_le νS (fun x => (lA k r z (Matrix.of x) a)⁻¹) f (B a) (hBm a) T hT (fun x hx => ?_) (2 * q)).trans ?_
      · have hpos : 0 < lA k r z (Matrix.of x) a := hx.1.2
        exact (le_inv_comm₀ hT hpos).2 hx.2.2
      · rw [← key]
        gcongr
        exact hI a
    refine (lintegral_union_le _ _ _).trans ?_
    exact (add_le_add hA' hB').trans (le_of_eq (two_mul _).symm)
  calc ∫⁻ x, Set.indicator {x : Mt k r | ∃ a : Fin (r + 1), la * H₁ ≤ max (lA k r z (Matrix.of x) a) (lA k r z (Matrix.of x) a)⁻¹}
          (fun x => (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2) x ∂νS
        ≤ ∫⁻ x, U.indicator f x ∂νS := lintegral_mono fun x => Set.indicator_le_indicator_of_subset hsub (fun _ => by simp) x
    _ = ∫⁻ x in U, f x ∂νS := lintegral_indicator hUm _
    _ ≤ ∫⁻ x in N, f x ∂νS + ∫⁻ x in ⋃ a, (A a ∪ B a), f x ∂νS := lintegral_union_le _ _ _
    _ ≤ 0 + ∑ a : Fin (r + 1), ∫⁻ x in A a ∪ B a, f x ∂νS := by
        gcongr
        · exact (setLIntegral_measure_zero _ _ hG).le
        · exact (lintegral_iUnion_le _ _).trans (le_of_eq (tsum_fintype _))
    _ ≤ ∑ _a : Fin (r + 1), 2 * (ENNReal.ofReal (la ^ (-(2 * (q : ℝ)))) * l2SG νS Φ) := by
        rw [zero_add]; exact Finset.sum_le_sum fun a _ => hc a
    _ ≤ ENNReal.ofReal (2 * (2 * r + 2 : ℝ) * la ^ (-(2 * (q : ℝ)))) * l2SG νS Φ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, ← mul_assoc,
          ENNReal.ofReal_mul (by positivity)]
        gcongr ?_ * _ * _
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        push_cast
        have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
        nlinarith

end GlobalTheory.Amp.TailTwo
end
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.moved_dual_vector_pairing_bounded_majorant : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ), inWb k r z → inWb k r z' → 0 < Tz k r z → IsNormal0 k r hj β c z z' g₀ → ∀ De R₀ : ℝ, DeOK k r z z' g₀ De → 1 ≤ R₀ → ∀ m ∈ UH (Hb k), ∀ (q : PSec k r j × (UToff β → ℂ)) (a : Fin r → ℝ), (∀ b, 0 < a b) → Sg2 k r z' (sEl k r j β q * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) ≤ R₀ → Sg k r z (g₀ * (sEl k r j β q * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m))) ≤ R₀ → ∀ b : Fin r, b.val < j → ∀ u : (Fin (2 * r + k + 1) → ℂ), eucl ((uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)⁻¹ *ᵥ u) ≤ R₀ → ‖herm (Hpk k r) ((sEl k r j β q)⁻¹ *ᵥ bvec (esI k r b)) u‖ ≤ R₀ ^ (2 * r) * De := by
  first | exact @GlobalTheory.Amp.NfComp.herm_sEl_inv_le | exact GlobalTheory.Amp.NfComp.herm_sEl_inv_le | (intros; apply GlobalTheory.Amp.NfComp.herm_sEl_inv_le <;> assumption)
end

section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.TypeAsm

def swapW {k r : ℕ} (W : LocW k r) : LocW k r where
  Wp := W.Wq
  Wq := W.Wp
  π := W.π'
  π' := W.π
  z := W.z'
  z' := W.z
  μG := W.μG
  μW := W.μW'
  μW' := W.μW
  μN := W.μN
  νS := W.νS'
  νS' := W.νS

def swapS {k r : ℕ} {W : LocW k r} (A : LocS W) : LocS (swapW W) where
  H := A.H
  σ := A.σ
  B := A.B'
  B' := A.B
  v0 := A.v0
  cN := A.cN
  deg := A.deg

theorem goodW_swap {D : D7} {τ : D.what₂.Tau} {w w' : D.what₂.Word} {θ : ℝ} {W : LocW D.R.k D.R.rS}
    (h : GoodW D τ w w' θ W) : GoodW D τ w' w θ (swapW W) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h2, h1, h4, h3, h6, h5, h7, h10, h11, h8, h9, h12, h14, h13⟩

theorem goodS_swap {D : D7} {W : LocW D.R.k D.R.rS} {lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ} {A : LocS W}
    (h : GoodS D lam A) : GoodS D lam (swapS A) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h4, h3, h5, h6, h7, h8, h10, h9, h11⟩

theorem tailBd_primed_of_unprimed : ∀ (D : D7) (τ : D.what₂.Tau) (w : D.what₂.Word) (θ : ℝ) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (q : ℕ) (H₁ : ℝ), (∀ (W : LocW D.R.k D.R.rS), GoodW D τ w w θ W → ∀ A : LocS W, GoodS D lam A → TailBd W.z W.νS A.Φ q H₁) → ∀ (W : LocW D.R.k D.R.rS), GoodW D τ w w θ W → ∀ A : LocS W, GoodS D lam A → TailBd W.z' W.νS' A.Φ' q H₁ := by
  intro D τ w θ lam q H₁ h W hW A hA
  exact h (swapW W) (goodW_swap hW) (swapS A) (goodS_swap hA)

end GlobalTheory.TypeAsm
end
end

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.definiteLattice_discriminantModule_card_det_sq : ∀ (D : D7) (M : LatW D), M.FG → IsPosDef (D.sp.X 0).hT → Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT M → 1 ≤ idxW D (dualInH (D.sp.X 0).hT M) M ∧ (idxW D (dualInH (D.sp.X 0).hT M) M : ℝ) = detW D M ^ 2 ∧ ∀ P : LatW D, P ≤ M → rkW D P = rkW D M → 1 ≤ idxW D M P ∧ detW D P = detW D M * idxW D M P := by
  first | exact @GlobalTheory.LoopC.DetCard.main | exact GlobalTheory.LoopC.DetCard.main | (intros; apply GlobalTheory.LoopC.DetCard.main <;> assumption)
end
