module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle007
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle008
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle018
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle017
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle014
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.SphU
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.VacuumNonvanishingOfFacts
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle016
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Hermitian
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
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle003

@[expose] public section

section

noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.HSt.HolTPf

open PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

theorem upper_left_block_mul (M N : M2 n) : (M * N).toBlocks₁₁ = M.toBlocks₁₁ * N.toBlocks₁₁ + M.toBlocks₁₂ * N.toBlocks₂₁ := by
  ext i j
  simp [Matrix.toBlocks₂₁, Matrix.toBlocks₁₂, Matrix.toBlocks₁₁, Matrix.mul_apply, Fintype.sum_sum_type]

theorem upper_right_block_mul (M N : M2 n) : (M * N).toBlocks₁₂ = M.toBlocks₁₁ * N.toBlocks₁₂ + M.toBlocks₁₂ * N.toBlocks₂₂ := by
  ext i j
  simp [Matrix.toBlocks₂₂, Matrix.toBlocks₁₂, Matrix.toBlocks₁₁, Matrix.mul_apply, Fintype.sum_sum_type]

theorem det_mR_ne (y : GR n) : (mR y).det ≠ 0 := by
  have h : IsUnit (mR y) := (y.1).isUnit
  exact (Matrix.isUnit_iff_isUnit_det _).mp h |>.ne_zero

theorem isUnit_first_cayley_block (y : GR n) : IsUnit (u1 (mR y)) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (detU1 n y).1)

theorem spherical_section_ne_zero_group (p q : ℕ) (e : ℤ) (y : GR n) : F0 p q e y ≠ 0 := by
  have h1 := det_mR_ne y
  obtain ⟨h2, h3⟩ := detU1 n y
  simp only [F0, f0]
  exact mul_ne_zero (zpow_ne_zero _ h1) (mul_ne_zero (zpow_ne_zero _ h2) (zpow_ne_zero _ h3))

theorem zOf_nU' (h : Matrix (Fin n) (Fin n) ℂ) (x y : GR n) (hx : mR x = nU h) : zOf (x * y) = zOf y + h := by
  have hm : mR (x * y) = nU h * mR y := by rw [mR_mul, hx]
  have hu : u1 (mR (x * y)) = u1 (mR y) := by
    simp only [u1, hm, projected_block_lower_sum, lowerDiagonalBlockAsGL, nU, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add,
      Matrix.one_mul]
  have hU := isUnit_first_cayley_block y
  unfold zOf
  rw [hu, hm, upper_left_block_mul, upper_right_block_mul]
  simp only [nU, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, Matrix.one_mul]
  have key : (Complex.I • ((mR y).toBlocks₁₁ + h * (mR y).toBlocks₂₁) + ((mR y).toBlocks₁₂ + h * (mR y).toBlocks₂₂)) =
      (Complex.I • (mR y).toBlocks₁₁ + (mR y).toBlocks₁₂) + h * u1 (mR y) := by
    simp only [u1, Matrix.mul_add, Matrix.mul_smul, smul_add]
    abel
  rw [key, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hU),
    Matrix.mul_one]

theorem spherical_section_unipotent_invariant (p q : ℕ) (e : ℤ) (h : Matrix (Fin n) (Fin n) ℂ) (x y : GR n) (hx : mR x = nU h) :
    F0 p q e (x * y) = F0 p q e y := by
  have hm : mR (x * y) = nU h * mR y := by rw [mR_mul, hx]
  have hu1 : u1 (mR (x * y)) = u1 (mR y) := by
    simp only [u1, hm, projected_block_lower_sum, lowerDiagonalBlockAsGL, nU, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add,
      Matrix.one_mul]
  have hu2 : u2 (mR (x * y)) = u2 (mR y) := by
    simp only [u2, hm, projected_block_lower_sum, lowerDiagonalBlockAsGL, nU, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add,
      Matrix.one_mul]
  have hd : (mR (x * y)).det = (mR y).det := by
    rw [hm, Matrix.det_mul, nU, Matrix.det_fromBlocks_zero₂₁]
    simp
  simp only [F0, f0, hu1, hu2, hd]

theorem levi_inv (a a' : Matrix (Fin n) (Fin n) ℂ) (x : GR n) (hx : mR x = fromBlocks a 0 0 a') : aᴴ * a' = 1 := by
  obtain ⟨-, E2, -⟩ := IwaPf.inG_blocks (mR x) x.2
  rw [hx] at E2
  simpa using E2

theorem zOf_levi' (a a' : Matrix (Fin n) (Fin n) ℂ) (x y : GR n) (hx : mR x = fromBlocks a 0 0 a') :
    zOf (x * y) = a * zOf y * aᴴ := by
  have hinv := levi_inv a a' x hx
  have ha' : a'⁻¹ = aᴴ := Matrix.inv_eq_left_inv hinv
  have hm : mR (x * y) = fromBlocks a 0 0 a' * mR y := by rw [mR_mul, hx]
  have hu : u1 (mR (x * y)) = a' * u1 (mR y) := by
    simp only [u1, hm, projected_block_lower_sum, lowerDiagonalBlockAsGL, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add,
      Matrix.mul_add, Matrix.mul_smul]
  unfold zOf
  rw [hu, hm, upper_left_block_mul, upper_right_block_mul]
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, Matrix.zero_mul, add_zero]
  rw [Matrix.mul_inv_rev, ha']
  simp only [← Matrix.mul_smul, ← Matrix.mul_add, Matrix.mul_assoc]

theorem spherical_section_levi_mul (p q : ℕ) (e : ℤ) (a a' : Matrix (Fin n) (Fin n) ℂ) (x y : GR n) (hx : mR x = fromBlocks a 0 0 a') :
    F0 p q e (x * y) = F0 p q e x * F0 p q e y := by
  have hm : mR (x * y) = fromBlocks a 0 0 a' * mR y := by rw [mR_mul, hx]
  have hu1 : u1 (mR (x * y)) = a' * u1 (mR y) := by
    simp only [u1, hm, projected_block_lower_sum, lowerDiagonalBlockAsGL, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add,
      Matrix.mul_add, Matrix.mul_smul]
  have hu2 : u2 (mR (x * y)) = a' * u2 (mR y) := by
    simp only [u2, hm, projected_block_lower_sum, lowerDiagonalBlockAsGL, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add,
      Matrix.mul_add, Matrix.mul_smul, Matrix.mul_neg]
  have hx1 : u1 (mR x) = a' := by simp [u1, hx]
  have hx2 : u2 (mR x) = a' := by simp [u2, hx]
  have hd : (mR (x * y)).det = (mR x).det * (mR y).det := by rw [mR_mul, Matrix.det_mul]
  simp only [F0, f0, hu1, hu2, hx1, hx2, hd, Matrix.det_mul, mul_zpow]
  ring

end PositivityTheory.Rg.Sw.HSt.HolTPf
end
end

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal ContDiff

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.SiegelWeilFormula

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def HolLeadHol : Prop :=
  ∀ (m n : ℕ) (e : ℤ), 1 ≤ m → m < n →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] (Pp Γ : Subgroup G) (ι : GR n →* G) (s₀ : ℂ) (Ht : G → ℝ≥0) (f : G → ℂ), Continuous ι →
      (∀ g, ∃ (x : G) (y : GR n) (S : ℂ) (r : ℝ), 0 < r ∧ g = x * ι y ∧
        ∀ y' : GR n, (Ht (x * ι y') : ℝ) = r * hLoc y' ∧ f (x * ι y') = S * F0 m 0 e y') →
      ∀ (U : Set ℂ) (d : Polynomial ℂ) (Ê : ℂ → G → ℂ) (t : ℝ), IsOpen U → GlobalTheory.Cont.IsRightDomain U → s₀ ∈ U →
        (∀ g, DifferentiableOn ℂ (Ê · g) U) → ContinuousOn (fun y : ℂ × G => Ê y.1 y.2) (U ×ˢ Set.univ) →
        (∀ z : ℂ, t < z.re → (∀ C : Set G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets Pp Γ → ℝ, Summable u ∧ ∀ g ∈ C, ∀ c,
            ‖GlobalTheory.Eis.term Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * f x) g c‖ ≤ u c) ∧
          ∀ g, Ê z g = d.eval z * GlobalTheory.Eis.cosetSum Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * f x) g) →
        ∀ j : ℕ, (∀ i < j, ∀ g, iteratedDeriv i (Ê · g) s₀ = 0) →
          (∀ ψ, IsSingTest ψ → ∀ nb : (Fin n → Fin n → ℝ) → GR n, (∀ x, mR (nb x) = nU (herm x)) →
            ∀ (g : G) (a b : GR n), ∫ x, iteratedDeriv j (Ê · (g * ι (a * nb x * b))) s₀ * ψ x = 0) →
          ∀ g, IsHolW m 0 e fun y => iteratedDeriv j (Ê · (g * ι y)) s₀

def Conj : Prop := HolLeadHol → HolLead

def SecFz : Prop :=
  ∀ (n m : ℕ) (e : ℤ) (w : ℂ) (y : GR n), fz m e w (mR y) = F0 m 0 e y * ((hLoc y : ℝ) : ℂ) ^ w


open Classical in
def lift (φ : GR n → ℂ) (x : M2 n) : ℂ := if h : IsUnit x ∧ InG x then φ ⟨h.1.unit, h.2⟩ else 0

def CRLem : Prop :=
  ∀ (n m : ℕ) (e : ℤ) (φ : GR n → ℂ) (Φ : M2 n → ℂ) (Ω : Set (M2 n)), IsOpen Ω → GSet n ⊆ Ω → ContDiffOn ℝ ∞ Φ Ω →
    (∀ y, Φ (mR y) = φ y) → (∀ y k : GR n, InK (mR k) → φ (y * k) = φ y * F0 m 0 e k) →
    (∀ (y : GR n) (Q : Matrix (Fin n) (Fin n) ℂ), rC (lowQ Q) Φ (mR y) = 0) → IsHolW m 0 e φ

def AsmH : Prop := LocTau → SecFz → CRLem → HolLeadHol

end PositivityTheory.Rg.Sw.HSt
end
end

section

namespace PositivityTheory.Rg.Sw.HSt

theorem crux : Crux := eRed (vacuum_nonvanishing_of_facts fdProps djFd kSplit sphU fzHol)

end PositivityTheory.Rg.Sw.HSt
end

section

noncomputable section

open Matrix Filter Topology
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.HSt.HolTPf

open PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

def imM (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (-(Complex.I / 2)) • (Z - Zᴴ)

theorem star_c : star (-(Complex.I / 2)) = -(-(Complex.I / 2)) := by
  apply Complex.ext <;> simp <;> norm_num

theorem imM_herm (Z : Matrix (Fin n) (Fin n) ℂ) : (imM Z).IsHermitian := by
  unfold imM
  rw [IsHermitian, conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose, star_c, neg_smul,
    ← smul_neg, neg_sub]

theorem mem_dom_iff (Z : Fin n → Fin n → ℂ) : Z ∈ Dom n ↔ (imM (Matrix.of Z)).PosDef := Iff.rfl

theorem posdef_iff_re {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) :
    M.PosDef ↔ ∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ (M *ᵥ x)).re := by
  rw [posDef_iff_dotProduct_mulVec]
  constructor
  · rintro ⟨-, h⟩ x hx
    exact (Complex.lt_def.1 (h hx)).1
  · intro h
    refine ⟨hM, fun x hx => ?_⟩
    have him : (star x ⬝ᵥ (M *ᵥ x)).im = 0 := hM.im_star_dotProduct_mulVec_self x
    exact Complex.lt_def.2 ⟨h x hx, by simpa using him.symm⟩

theorem re_smul_quad (M : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) (c : ℝ) :
    (star ((c : ℂ) • x) ⬝ᵥ (M *ᵥ ((c : ℂ) • x))).re = c ^ 2 * (star x ⬝ᵥ (M *ᵥ x)).re := by
  rw [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
  rw [← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  ring

theorem continuous_quad : Continuous fun p : (Fin n → Fin n → ℂ) × (Fin n → ℂ) =>
    (star p.2 ⬝ᵥ (imM (Matrix.of p.1) *ᵥ p.2)).re := by
  have h1 : Continuous fun p : (Fin n → Fin n → ℂ) × (Fin n → ℂ) => (Matrix.of p.1 : Matrix (Fin n) (Fin n) ℂ) :=
    continuous_fst
  have h2 : Continuous fun p : (Fin n → Fin n → ℂ) × (Fin n → ℂ) => imM (Matrix.of p.1) := by
    unfold imM
    exact (h1.sub h1.matrix_conjTranspose).const_smul (-(Complex.I / 2) : ℂ)
  exact Complex.continuous_re.comp (continuous_snd.star.dotProduct (h2.matrix_mulVec continuous_snd))

theorem isOpen_dom' : IsOpen (Dom n) := by
  rw [isOpen_iff_mem_nhds]
  intro Z hZ
  have hsph : IsCompact (Metric.sphere (0 : Fin n → ℂ) 1) := isCompact_sphere 0 1
  have key : ∀ᶠ W in 𝓝 Z, ∀ y ∈ Metric.sphere (0 : Fin n → ℂ) 1,
      0 < (star y ⬝ᵥ (imM (Matrix.of W) *ᵥ y)).re := by
    apply hsph.eventually_forall_of_forall_eventually
    intro y hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      simp at hy
    have hpos : 0 < (star y ⬝ᵥ (imM (Matrix.of Z) *ᵥ y)).re :=
      (posdef_iff_re (imM_herm _)).1 ((mem_dom_iff Z).1 hZ) y hy0
    exact (continuous_quad.tendsto (Z, y)).eventually (lt_mem_nhds hpos)
  filter_upwards [key] with W hW
  rw [mem_dom_iff, posdef_iff_re (imM_herm _)]
  intro x hx
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hy : (((‖x‖⁻¹ : ℝ) : ℂ) • x) ∈ Metric.sphere (0 : Fin n → ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul]
    simp [hn.ne']
  have hxe : x = ((‖x‖ : ℝ) : ℂ) • (((‖x‖⁻¹ : ℝ) : ℂ) • x) := by
    rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne', Complex.ofReal_one, one_smul]
  rw [hxe, re_smul_quad]
  exact mul_pos (pow_pos hn 2) (hW _ hy)

theorem convex_dom' : Convex ℝ (Dom n) := by
  intro Z hZ W hW a b ha hb hab
  rw [mem_dom_iff, posdef_iff_re (imM_herm _)] at hZ hW ⊢
  intro x hx
  have hm : imM (Matrix.of (a • Z + b • W)) = (a : ℂ) • imM (Matrix.of Z) + (b : ℂ) • imM (Matrix.of W) := by
    ext i j
    simp [imM, Complex.real_smul]
    ring
  have hq : (star x ⬝ᵥ (imM (Matrix.of (a • Z + b • W)) *ᵥ x)).re
      = a * (star x ⬝ᵥ (imM (Matrix.of Z) *ᵥ x)).re + b * (star x ⬝ᵥ (imM (Matrix.of W) *ᵥ x)).re := by
    rw [hm, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, dotProduct_add,
      dotProduct_smul, dotProduct_smul, Complex.add_re, smul_eq_mul, smul_eq_mul, Complex.re_ofReal_mul,
      Complex.re_ofReal_mul]
  rw [hq]
  have hp := hZ x hx
  have hq' := hW x hx
  rcases ha.eq_or_lt with rfl | ha'
  · have hb1 : b = 1 := by linarith
    subst hb1
    simpa using hq'
  · linarith [mul_pos ha' hp, mul_nonneg hb hq'.le]

private theorem conjTranspose_I_smul_add_sub_eq_neg_two_I (A B C D : Matrix (Fin n) (Fin n) ℂ)
    (h1 : -(Cᴴ * A) + Aᴴ * C = 0) (h2 : -(Cᴴ * B) + Aᴴ * D = 1)
    (h3 : -(Dᴴ * A) + Bᴴ * C = -1) (h4 : -(Dᴴ * B) + Bᴴ * D = 0) :
    (Complex.I • A + B)ᴴ * (Complex.I • C + D) - (Complex.I • C + D)ᴴ * (Complex.I • A + B)
      = (-(2 * Complex.I)) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  simp only [conjTranspose_add, conjTranspose_smul, Complex.star_def, Complex.conj_I, Matrix.add_mul,
    Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  linear_combination (norm := skip) h1 + h4 + (-Complex.I) • h2 + Complex.I • h3
  match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

private theorem posDef_imM_mul_inv_of_skew_relation (X U : Matrix (Fin n) (Fin n) ℂ)
    (hk : Xᴴ * U - Uᴴ * X = (-(2 * Complex.I)) • (1 : Matrix (Fin n) (Fin n) ℂ)) :
    (imM (X * U⁻¹)).PosDef := by
  have hker : ∀ v, U *ᵥ v = 0 → v = 0 := by
    intro v hv
    have e : star v ⬝ᵥ ((Xᴴ * U - Uᴴ * X) *ᵥ v)
        = star v ⬝ᵥ (((-(2 * Complex.I)) • (1 : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) := by
      rw [hk]
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero,
      zero_sub, dotProduct_neg, dotProduct_mulVec, ← star_mulVec, hv, star_zero, zero_dotProduct,
      neg_zero, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul] at e
    have h2I : -(2 * Complex.I) ≠ 0 := by simp
    have hvv : star v ⬝ᵥ v = 0 := (mul_eq_zero.1 e.symm).resolve_left h2I
    exact dotProduct_star_self_eq_zero.1 hvv
  have hinj : Function.Injective U.mulVec := by
    intro v w hvw
    have h0 : U *ᵥ (v - w) = 0 := by
      rw [Matrix.mulVec_sub, sub_eq_zero]
      exact hvw
    exact sub_eq_zero.1 (hker _ h0)
  have hU : IsUnit U := mulVec_injective_iff_isUnit.1 hinj
  have hUU : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U ((Matrix.isUnit_iff_isUnit_det U).1 hU)
  have hc : (U⁻¹)ᴴ * Uᴴ = 1 := by
    rw [← conjTranspose_mul, hUU, conjTranspose_one]
  have e1 : X * U⁻¹ - (X * U⁻¹)ᴴ = (U⁻¹)ᴴ * (Uᴴ * X - Xᴴ * U) * U⁻¹ := by
    rw [conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc (U⁻¹)ᴴ Uᴴ X, hc,
      Matrix.one_mul, ← Matrix.mul_assoc (U⁻¹)ᴴ Xᴴ U, Matrix.mul_assoc _ U U⁻¹, hUU, Matrix.mul_one]
  have e2 : Uᴴ * X - Xᴴ * U = (2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← neg_sub, hk, neg_smul, neg_neg]
  have e3 : imM (X * U⁻¹) = (U⁻¹)ᴴ * 1 * U⁻¹ := by
    unfold imM
    rw [e1, e2, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    have hs : -(Complex.I / 2) * (2 * Complex.I) = 1 := by
      ring_nf
      simp [Complex.I_sq]
    rw [hs, one_smul]
  have hinv : Function.Injective (U⁻¹).mulVec := by
    intro v w hvw
    have := congrArg (fun z => U *ᵥ z) hvw
    simpa [Matrix.mulVec_mulVec, hUU] using this
  rw [e3]
  exact Matrix.PosDef.one.conjTranspose_mul_mul_same hinv

theorem zOf_mem' (y : GR n) : zOf y ∈ Dom n := by
  have hM : (mR y)ᴴ * JJ n * mR y = JJ n := y.2
  have hblk : mR y = fromBlocks (toBlocks₁₁ (mR y)) (toBlocks₁₂ (mR y)) (toBlocks₂₁ (mR y))
      (toBlocks₂₂ (mR y)) :=
    (fromBlocks_toBlocks _).symm
  rw [hblk, JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply] at hM
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg,
    Matrix.neg_mul, add_zero, zero_add] at hM
  obtain ⟨h1, h2, h3, h4⟩ := Matrix.fromBlocks_inj.1 hM
  have hk := conjTranspose_I_smul_add_sub_eq_neg_two_I _ _ _ _ h1 h2 h3 h4
  refine (mem_dom_iff (n := n) (zOf y)).2 ?_
  exact posDef_imM_mul_inv_of_skew_relation _ _ hk

theorem neg_conj_mem' {W : Fin n → Fin n → ℂ} (hW : W ∈ Dom n) :
    (-(Matrix.of W)ᴴ : Matrix (Fin n) (Fin n) ℂ) ∈ Dom n := by
  have h : imM (Matrix.of (-(Matrix.of W)ᴴ : Matrix (Fin n) (Fin n) ℂ)) = imM (Matrix.of W) := by
    change imM (-(Matrix.of W)ᴴ) = imM (Matrix.of W)
    ext i j
    simp [imM]
    ring
  refine (mem_dom_iff (n := n) (-(Matrix.of W)ᴴ : Matrix (Fin n) (Fin n) ℂ)).2 ?_
  rw [h]
  exact (mem_dom_iff W).1 hW

end PositivityTheory.Rg.Sw.HSt.HolTPf
end
end
