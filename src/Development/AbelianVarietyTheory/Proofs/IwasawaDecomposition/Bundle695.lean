module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle212
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle540
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle012
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle683
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle684
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle686
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle682
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle690
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

theorem GlobalTheory.FlagBundle.exists_isHom_base_of_lifts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : C.Y.X ⟶ X.X), f ≫ j = C.π → (∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ j ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x ∧ C.Carries p g) → ∃ φ : X.Fn →ₐ[F] C.Y.Fn, (ratOf X).IsHom (ratOf C.Y) φ f := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C X j _ hj f hf hl
  have hs : f ≫ X.str = C.Y.str := by
    rw [← hj, ← C.π_str, ← hf, Category.assoc]

  let K : Type := AlgebraicClosure X.Fn
  let a : X.Fn →+* K := algebraMap X.Fn K
  let x : Sp K ⟶ X.X := spMap a ≫ genericPt X
  have h1 : genericPt X ≫ X.str = spMap (algebraMap F X.Fn) := (ratOf X).pt_s
  have h2 : spMap e.toRingHom ≫ spMap e.symm.toRingHom = 𝟙 _ := by
    rw [← Spec.map_comp]
    exact (congrArg Spec.map (CommRingCat.hom_ext (RingEquiv.toRingHom_comp_symm_toRingHom e))).trans (Spec.map_id _)
  have hg0 : (genericPt X ≫ j) ≫ genStr Z = spMap (constF e X) := by
    have : spMap (constF e X) = spMap (algebraMap F X.Fn) ≫ spMap e.symm.toRingHom := by
      rw [constF, ← Spec.map_comp]; rfl
    rw [this, ← h1, ← hj]
    simp only [Category.assoc, h2, Category.comp_id]
  let χ : c.F →+* K := a.comp (constF e X)
  have hx : (x ≫ j) ≫ genStr Z = spMap χ := by
    have : spMap χ = spMap a ≫ spMap (constF e X) := by rw [← Spec.map_comp]; rfl
    rw [this, ← hg0]
    simp only [x, Category.assoc]
  obtain ⟨g⟩ := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c O β Z K χ (x ≫ j) hx
  rw [Category.assoc] at g hx
  obtain ⟨p, ⟨hp, -⟩, -⟩ := hl K χ x hx g

  have hpt : f (p (IsLocalRing.closedPoint K)) = genericPoint X.X := by
    have hc : (p ≫ f) (IsLocalRing.closedPoint K) = f (p (IsLocalRing.closedPoint K)) := Scheme.Hom.comp_apply _ _ _
    rw [← hc, hp]
    show (ratOf X).pt (spMap a (IsLocalRing.closedPoint K)) = _
    exact (ratOf X).pt_apply _
  have hsp : f (genericPoint C.Y.X) ⤳ genericPoint X.X :=
    hpt ▸ (genericPoint_specializes (p (IsLocalRing.closedPoint K))).map f.continuous
  exact exists_isHom_of_generic (ratOf X) (ratOf C.Y) f hs (hsp.antisymm (genericPoint_specializes _)).eq
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegChart

theorem isAdmissibleBase_of_completeNormalLocalCharZero {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A] (hA : IsCN A) : LN.admitted A (maximalIdeal A) :=
  ⟨admissibleBase_of_completeNormalLocalCharZero hA, hA.2.2.1, hA.2.2.2, inferInstance, inferInstanceAs (IsIntegrallyClosed (ResidueField A))⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l}

end GlobalTheory.SiegChart
end
end

section

noncomputable section

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RedTh

theorem term_le_double_sum {n : ℕ} (f : Fin n → Fin n → ℝ) (hf : ∀ p q, 0 ≤ f p q) (p q : Fin n) :
    f p q ≤ ∑ p, ∑ q, f p q := by
  calc f p q ≤ ∑ q, f p q := Finset.single_le_sum (fun q _ => hf p q) (Finset.mem_univ q)
    _ ≤ ∑ p, ∑ q, f p q := Finset.single_le_sum (f := fun p => ∑ q, f p q)
        (fun p _ => Finset.sum_nonneg fun q _ => hf p q) (Finset.mem_univ p)

theorem step_chain {n : ℕ} {d : Fin n → ℝ} (hs : ∀ p q : Fin n, (q : ℕ) = p + 1 → d p ≤ 4 * d q)
    (q : Fin n) : ∀ m (hm : (q : ℕ) + m < n), d q ≤ 4 ^ m * d ⟨q + m, hm⟩ := by
  intro m
  induction m with
  | zero => intro hm; simp
  | succ m ih =>
    intro hm
    have h1 := ih (by omega)
    have h2 := hs ⟨q + m, by omega⟩ ⟨q + (m + 1), hm⟩ (by simp; omega)
    calc d q ≤ 4 ^ m * d ⟨q + m, by omega⟩ := h1
      _ ≤ 4 ^ m * (4 * d ⟨q + (m + 1), hm⟩) := by gcongr
      _ = 4 ^ (m + 1) * d ⟨q + (m + 1), hm⟩ := by ring

theorem gap_chain {n : ℕ} {d : Fin n → ℝ} {R : ℝ} (hR : 0 ≤ R) (p : Fin n) :
    ∀ m (hm : (p : ℕ) + m < n),
      (∀ k k' : Fin n, (k' : ℕ) = k + 1 → p ≤ k → (k' : ℕ) ≤ p + m → d k' ≤ R * d k) →
      d ⟨p + m, hm⟩ ≤ R ^ m * d p := by
  intro m
  induction m with
  | zero => intro hm _; simp
  | succ m ih =>
    intro hm h
    have h1 := ih (by omega) (fun k k' hk hpk hk' => h k k' hk hpk (by omega))
    have h2 := h ⟨p + m, by omega⟩ ⟨p + (m + 1), hm⟩ (by simp; omega)
      (by simp [Fin.le_def]) (by simp)
    calc d ⟨p + (m + 1), hm⟩ ≤ R * d ⟨p + m, by omega⟩ := h2
      _ ≤ R * (R ^ m * d p) := by gcongr
      _ = R ^ (m + 1) * d p := by ring

theorem balanced_entries_bounded : ∀ (n : ℕ) (K : ℝ), ∃ C : ℝ, ∀ (A A' : Matrix (Fin n) (Fin n) ℤ) (d : Fin n → ℝ)
    (u : Matrix (Fin n) (Fin n) ℝ), IsSiegel d u → (∀ i, 0 < d i) →
    (A.map (Int.cast : ℤ → ℝ))ᵀ * gram d u = gram d u * A'.map (Int.cast : ℤ → ℝ) →
    (((A' * A).trace : ℤ) : ℝ) ≤ K → ∀ i j, ((|A i j| : ℤ) : ℝ) ≤ C := by
  intro n K
  obtain ⟨c, hc⟩ := GlobalTheory.T.siegelUnipotent_inverse_entries_bounded n
  obtain ⟨R, hR1, hR⟩ := GlobalTheory.T.siegelDomain_lowerBlock_eq_zero_of_large_gap n K c
  have hK0 : 0 ≤ max K 0 := le_max_right _ _
  have h4 : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
  have hRn : (1 : ℝ) ≤ R ^ n := one_le_pow₀ hR1
  have hB : 0 ≤ 4 ^ n * R ^ n * max K 0 := by
    apply mul_nonneg (mul_nonneg (by linarith) (by linarith)) hK0
  refine ⟨(n : ℝ) ^ 2 * |c| * (1 + 4 ^ n * R ^ n * max K 0), ?_⟩
  intro A A' d u hS hd hbal htr i j
  obtain ⟨v, hvu, huv, hvl, hvc⟩ := hc u hS.diag hS.lower hS.upper
  obtain ⟨hsym, hsum, hsum'⟩ := GlobalTheory.T.balancedIntMatrix_triangularGram_adjoint_weighted_sq_trace n A A' d u v hd hvu huv hbal
  have hK' : ∑ p, ∑ q, d p / d q * (u * A'.map (Int.cast : ℤ → ℝ) * v) p q ^ 2 ≤ K := by
    rw [hsum']; exact htr
  have hK : ∑ p, ∑ q, d p / d q * (u * A.map (Int.cast : ℤ → ℝ) * v) p q ^ 2 ≤ K := by
    rw [hsum]; exact htr
  set Ar := A.map (Int.cast : ℤ → ℝ) with hAr
  set W := u * Ar * v with hWdef
  set B := 4 ^ n * R ^ n * max K 0 with hBdef
  have hterm : ∀ p q, d p / d q * W p q ^ 2 ≤ max K 0 := fun p q =>
    (term_le_double_sum (fun p q => d p / d q * W p q ^ 2)
      (fun p q => mul_nonneg (div_nonneg (hd p).le (hd q).le) (sq_nonneg _)) p q).trans
      (hK.trans (le_max_left _ _))
  have hsq : ∀ p q, W p q ^ 2 ≤ d q / d p * max K 0 := by
    intro p q
    have hp := (hd p).ne'
    have hq := (hd q).ne'
    have e : W p q ^ 2 = d q / d p * (d p / d q * W p q ^ 2) := by field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left (hterm p q) (div_nonneg (hd q).le (hd p).le)
  have hW : ∀ p q, W p q ^ 2 ≤ B := by
    intro p q
    rcases le_or_gt q p with hqp | hpq
    · have hqp' : (q : ℕ) ≤ p := hqp
      have hm : (q : ℕ) + ((p : ℕ) - q) < n := by omega
      have h1 := step_chain hS.step q ((p : ℕ) - q) hm
      have hpe : (⟨(q : ℕ) + ((p : ℕ) - q), hm⟩ : Fin n) = p := by ext; simp; omega
      rw [hpe] at h1
      have h2 : (4 : ℝ) ^ ((p : ℕ) - q) ≤ 4 ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
      have h3 : d q ≤ 4 ^ n * d p := h1.trans (mul_le_mul_of_nonneg_right h2 (hd p).le)
      have h5 : d q / d p ≤ 4 ^ n := by rw [div_le_iff₀ (hd p)]; exact h3
      calc W p q ^ 2 ≤ d q / d p * max K 0 := hsq p q
        _ ≤ 4 ^ n * max K 0 := mul_le_mul_of_nonneg_right h5 hK0
        _ ≤ 4 ^ n * max K 0 * R ^ n := le_mul_of_one_le_right (by positivity) hRn
        _ = B := by rw [hBdef]; ring
    · have hpq' : (p : ℕ) < q := hpq
      by_cases hgap : ∃ k k' : Fin n, (k' : ℕ) = k + 1 ∧ p ≤ k ∧ k' ≤ q ∧ R * d k < d k'
      · obtain ⟨k, k', hk, hpk, hkq, hlt⟩ := hgap
        have h0 : (u * A'.map (Int.cast : ℤ → ℝ) * v) q p = 0 :=
          hR A' d u v hS hd hvu huv hvl hvc hK' k k' hk hlt q p hpk hkq
        have h1 := hsym p q
        rw [h0, mul_zero] at h1
        have hz : W p q = 0 := by
          rcases mul_eq_zero.mp h1 with h | h
          · exact absurd h (hd p).ne'
          · exact h
        rw [hz]
        simpa using hB
      · push_neg at hgap
        have hm : (p : ℕ) + ((q : ℕ) - p) < n := by omega
        have h1 := gap_chain (d := d) (by linarith) p ((q : ℕ) - p) hm
          (fun k k' hk hpk hk' => hgap k k' hk hpk (by rw [Fin.le_def]; omega))
        have hqe : (⟨(p : ℕ) + ((q : ℕ) - p), hm⟩ : Fin n) = q := by ext; simp; omega
        rw [hqe] at h1
        have h2 : R ^ ((q : ℕ) - p) ≤ R ^ n := pow_le_pow_right₀ hR1 (by omega)
        have h3 : d q ≤ R ^ n * d p := h1.trans (mul_le_mul_of_nonneg_right h2 (hd p).le)
        have h5 : d q / d p ≤ R ^ n := by rw [div_le_iff₀ (hd p)]; exact h3
        calc W p q ^ 2 ≤ d q / d p * max K 0 := hsq p q
          _ ≤ R ^ n * max K 0 := mul_le_mul_of_nonneg_right h5 hK0
          _ ≤ 4 ^ n * (R ^ n * max K 0) := le_mul_of_one_le_left (by positivity) h4
          _ = B := by rw [hBdef]; ring
  have hA : Ar = v * W * u := by
    calc Ar = (v * u) * Ar * (v * u) := by rw [hvu, Matrix.one_mul, Matrix.mul_one]
      _ = v * W * u := by rw [hWdef]; simp only [Matrix.mul_assoc]
  have hu1 : ∀ l j, |u l j| ≤ 1 := by
    intro l j
    rcases lt_trichotomy l j with h | h | h
    · exact (hS.upper l j h).trans (by norm_num)
    · subst h; rw [hS.diag]; simp
    · rw [hS.lower l j h]; simp
  have hWb : ∀ k l, |W k l| ≤ 1 + B := fun k l => by
    nlinarith [hW k l, abs_nonneg (W k l), sq_abs (W k l)]
  have hc0 : 0 ≤ |c| := abs_nonneg c
  have hentry : |Ar i j| ≤ (n : ℝ) ^ 2 * |c| * (1 + B) := by
    rw [hA, Matrix.mul_apply]
    calc |∑ l, (v * W) i l * u l j| ≤ ∑ l, |(v * W) i l * u l j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ l : Fin n, (n : ℝ) * (|c| * (1 + B)) := by
        apply Finset.sum_le_sum; intro l _
        rw [abs_mul, Matrix.mul_apply]
        have hin : |∑ k, v i k * W k l| ≤ (n : ℝ) * (|c| * (1 + B)) := by
          calc |∑ k, v i k * W k l| ≤ ∑ k, |v i k * W k l| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ k : Fin n, |c| * (1 + B) := by
              apply Finset.sum_le_sum; intro k _
              rw [abs_mul]
              exact mul_le_mul ((hvc i k).trans (le_abs_self c)) (hWb k l) (abs_nonneg _) hc0
            _ = (n : ℝ) * (|c| * (1 + B)) := by simp
        calc |∑ k, v i k * W k l| * |u l j| ≤ (n : ℝ) * (|c| * (1 + B)) * 1 :=
              mul_le_mul hin (hu1 l j) (abs_nonneg _) (by positivity)
          _ = (n : ℝ) * (|c| * (1 + B)) := by ring
      _ = (n : ℝ) ^ 2 * |c| * (1 + B) := by simp; ring
  have hcast : ((|A i j| : ℤ) : ℝ) = |Ar i j| := by simp [hAr, Int.cast_abs]
  rw [hcast]
  exact hentry

end GlobalTheory.RedTh
end
end

section

open Matrix GlobalTheory.RedTh

noncomputable section

namespace GlobalTheory.SiegelCone

abbrev Tail {n : ℕ} (k : Fin n) : Type := {i : Fin n // k ≤ i}

def unip (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  Set.pi Set.univ fun i => Set.pi Set.univ fun j =>
    if i = j then {1} else if j < i then {0} else Set.Icc (-(1 / 2)) (1 / 2)

theorem isCompact_unip (n : ℕ) : IsCompact (unip n) := by
  refine isCompact_univ_pi fun i => isCompact_univ_pi fun j => ?_
  split_ifs
  · exact isCompact_singleton
  · exact isCompact_singleton
  · exact isCompact_Icc

theorem mem_unip {n : ℕ} {d : Fin n → ℝ} {u : Matrix (Fin n) (Fin n) ℝ} (h : GlobalTheory.RedTh.IsSiegel d u) :
    u ∈ unip n := by
  intro i _ j _
  simp only
  split_ifs with h1 h2
  · subst h1; simp [h.diag]
  · simp [h.lower i j h2]
  · have : i < j := lt_of_le_of_ne (not_lt.1 h2) h1
    exact abs_le.1 (h.upper i j this)

def tailForm {n : ℕ} (k : Fin n) (u : Matrix (Fin n) (Fin n) ℝ) : Matrix (Tail k) (Tail k) ℝ :=
  (u.submatrix Subtype.val Subtype.val)ᵀ * diagonal (fun a : Tail k => ((4 : ℝ) ^ (a.1 : ℕ))⁻¹) *
    u.submatrix Subtype.val Subtype.val

theorem continuous_tailForm {n : ℕ} (k : Fin n) : Continuous (tailForm k) := by
  unfold tailForm
  exact ((continuous_id.matrix_submatrix _ _).matrix_transpose.matrix_mul continuous_const).matrix_mul
    (continuous_id.matrix_submatrix _ _)

theorem tailForm_posDef {n : ℕ} (k : Fin n) {u : Matrix (Fin n) (Fin n) ℝ} (hu : u ∈ unip n) :
    (tailForm k u).PosDef := by
  have hu' : ∀ i j, u i j ∈ (if i = j then ({1} : Set ℝ) else if j < i then {0} else Set.Icc (-(1 / 2)) (1 / 2)) :=
    fun i j => hu i trivial j trivial
  set v := u.submatrix (Subtype.val : Tail k → Fin n) Subtype.val
  have htri : v.BlockTriangular id := by
    intro a b hab
    have := hu' a.1 b.1
    have hne : a.1 ≠ b.1 := fun h => (ne_of_lt hab) (Subtype.ext h).symm
    simp only [hne, if_false, show b.1 < a.1 from hab, if_true, Set.mem_singleton_iff] at this
    exact this
  have hdet : v.det = 1 := by
    rw [det_of_upperTriangular htri]
    refine Finset.prod_eq_one fun a _ => ?_
    have := hu' a.1 a.1
    simpa [v] using this
  have hunit : IsUnit v := (isUnit_iff_isUnit_det v).2 (by rw [hdet]; exact isUnit_one)
  have hD : (diagonal fun a : Tail k => ((4 : ℝ) ^ (a.1 : ℕ))⁻¹).PosDef :=
    posDef_diagonal_iff.2 fun a => by positivity
  have := hD.conjTranspose_mul_mul_same (mulVec_injective_of_isUnit hunit)
  rw [conjTranspose_eq_transpose_of_trivial] at this
  exact this

theorem tailForm_apply {n : ℕ} (k : Fin n) (u : Matrix (Fin n) (Fin n) ℝ) (a b : Tail k) :
    tailForm k u a b = ∑ m : Fin n, if k ≤ m then ((4 : ℝ) ^ (m : ℕ))⁻¹ * u m a.1 * u m b.1 else 0 := by
  rw [tailForm, Matrix.mul_apply]
  simp only [mul_diagonal, transpose_apply, submatrix_apply]
  rw [← Finset.sum_filter, Finset.sum_subtype (Finset.univ.filter (k ≤ ·)) (p := (k ≤ ·)) (by simp)]
  refine Finset.sum_congr rfl fun c _ => by ring

end GlobalTheory.SiegelCone

namespace GlobalTheory.SiegelCone

def extZ {n : ℕ} (k : Fin n) (l : Tail k → ℤ) : Fin n → ℤ := fun i => if h : k ≤ i then l ⟨i, h⟩ else 0

theorem exists_increments {n : ℕ} {d : Fin n → ℝ} {u : Matrix (Fin n) (Fin n) ℝ} (hs : GlobalTheory.RedTh.IsSiegel d u) :
    ∃ G : Fin n → ℝ, (∀ k, 0 ≤ G k) ∧ ∀ m, d m = ((4 : ℝ) ^ (m : ℕ))⁻¹ * ∑ k, if k ≤ m then G k else 0 := by
  let F : ℕ → ℝ := fun m => if h : m < n then d ⟨m, h⟩ * 4 ^ m else 0
  let G : ℕ → ℝ := fun k => if k = 0 then F 0 else F k - F (k - 1)
  have htel : ∀ m : ℕ, ∑ k ∈ Finset.range (m + 1), G k = F m := by
    intro m
    induction m with
    | zero => simp [G]
    | succ m ih => rw [Finset.sum_range_succ, ih]; simp only [G, if_neg (Nat.succ_ne_zero m), Nat.add_sub_cancel]; ring
  refine ⟨fun k => G k, fun k => ?_, fun m => ?_⟩
  · by_cases h0 : (k : ℕ) = 0
    · have := hs.nonneg k
      simp only [G, h0, if_true, F, dif_pos (show 0 < n from lt_of_le_of_lt (Nat.zero_le _) k.2)]
      have e : (⟨0, lt_of_le_of_lt (Nat.zero_le _) k.2⟩ : Fin n) = k := Fin.ext h0.symm
      rw [e]; positivity
    · obtain ⟨j, hj⟩ : ∃ j, (k : ℕ) = j + 1 := ⟨(k : ℕ) - 1, by omega⟩
      have hjn : j < n := by omega
      have hstep := hs.step ⟨j, hjn⟩ k (by simp [hj])
      have hnn := hs.nonneg ⟨j, hjn⟩
      have hdk : ∀ h, d ⟨j + 1, h⟩ = d k := fun h => congrArg d (Fin.ext hj.symm)
      have hFk : F (j + 1) = d k * 4 ^ (j + 1) := by
        simp only [F, dif_pos (show j + 1 < n by omega), hdk]
      have hFj : F j = d ⟨j, hjn⟩ * 4 ^ j := by simp only [F, dif_pos hjn]
      show 0 ≤ G (k : ℕ)
      rw [hj]
      simp only [G, if_neg (Nat.succ_ne_zero j), Nat.add_sub_cancel, hFk, hFj, pow_succ]
      have : (0 : ℝ) ≤ 4 ^ j := by positivity
      nlinarith
  · have hsum : ∑ k : Fin n, (if k ≤ m then G k else 0) = F m := by
      have h1 : ∀ k : Fin n, (if k ≤ m then G k else 0) = (fun x : ℕ => if x ≤ (m : ℕ) then G x else 0) k :=
        fun k => by simp only [Fin.le_iff_val_le_val]
      rw [Finset.sum_congr rfl (fun k _ => h1 k), Fin.sum_univ_eq_sum_range (fun x => if x ≤ (m : ℕ) then G x else 0) n,
        ← Finset.sum_filter]
      have h2 : (Finset.range n).filter (· ≤ (m : ℕ)) = Finset.range ((m : ℕ) + 1) := by
        ext x; simp; omega
      rw [h2, htel]
    rw [hsum]
    simp only [F, dif_pos m.2, Fin.eta]
    field_simp

theorem tail_sum {n : ℕ} (k : Fin n) {u : Matrix (Fin n) (Fin n) ℝ} (hu : u ∈ unip n) (T : Finset (Tail k → ℤ))
    (C : (Tail k → ℤ) → ℝ)
    (hC : tailForm k u = ∑ l ∈ T, C l • vecMulVec (fun i => (l i : ℝ)) (fun i => (l i : ℝ))) (i j : Fin n) :
    ∑ l ∈ T, C l * ((extZ k l i : ℝ) * (extZ k l j : ℝ)) =
      ∑ m : Fin n, if k ≤ m then ((4 : ℝ) ^ (m : ℕ))⁻¹ * u m i * u m j else 0 := by
  have hlow : ∀ m i, k ≤ m → ¬ k ≤ i → u m i = 0 := by
    intro m i hm hi
    have := hu m trivial i trivial
    have hlt : i < m := lt_of_lt_of_le (not_le.1 hi) hm
    simpa [hlt.ne', hlt] using this
  by_cases hi : k ≤ i
  · by_cases hj : k ≤ j
    · have := congrFun (congrFun hC ⟨i, hi⟩) ⟨j, hj⟩
      rw [tailForm_apply] at this
      rw [this]
      simp [Matrix.sum_apply, vecMulVec_apply, extZ, hi, hj]
    · simp only [extZ, dif_neg hj, Int.cast_zero, mul_zero]
      simp only [Finset.sum_const_zero]
      refine (Finset.sum_eq_zero fun m _ => ?_).symm
      split_ifs with hm
      · rw [hlow m j hm hj, mul_zero]
      · rfl
  · simp only [extZ, dif_neg hi, Int.cast_zero, zero_mul, mul_zero, Finset.sum_const_zero]
    refine (Finset.sum_eq_zero fun m _ => ?_).symm
    split_ifs with hm
    · rw [hlow m i hm hi, mul_zero, zero_mul]
    · rfl

theorem gram_mem_cone : ∀ n : ℕ, ∃ S : Finset (Fin n → ℤ), ∀ (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ),
    GlobalTheory.RedTh.IsSiegel d u → ∃ c : (Fin n → ℤ) → ℝ, (∀ l, 0 ≤ c l) ∧
      GlobalTheory.RedTh.gram d u = ∑ l ∈ S, c l • vecMulVec (fun i => (l i : ℝ)) (fun i => (l i : ℝ)) := by
  intro n
  have hK : ∀ k : Fin n, ∃ T : Finset (Tail k → ℤ), ∀ P ∈ tailForm k '' unip n, ∃ c : (Tail k → ℤ) → ℝ,
      (∀ l, 0 ≤ c l) ∧ P = ∑ l ∈ T, c l • vecMulVec (fun i => (l i : ℝ)) (fun i => (l i : ℝ)) := fun k =>
    GlobalTheory.T.exists_finset_squares_cone_of_compact_posDef (Tail k) (tailForm k '' unip n) ((isCompact_unip n).image (continuous_tailForm k))
      (by rintro _ ⟨u, hu, rfl⟩; exact tailForm_posDef k hu)
  choose T hT using hK
  refine ⟨Finset.univ.biUnion fun k => (T k).image (extZ k), ?_⟩
  intro d u hs
  have hu := mem_unip hs
  choose C hC0 hC using fun k => hT k _ ⟨u, hu, rfl⟩
  obtain ⟨G, hG0, hd⟩ := exists_increments hs
  refine ⟨fun l => ∑ k : Fin n, G k * ∑ l' ∈ T k, if extZ k l' = l then C k l' else 0, fun l => ?_, ?_⟩
  · refine Finset.sum_nonneg fun k _ => mul_nonneg (hG0 k) (Finset.sum_nonneg fun l' _ => ?_)
    split_ifs
    · exact hC0 k l'
    · exact le_rfl
  ext i j
  have hL : GlobalTheory.RedTh.gram d u i j = ∑ k, G k * ∑ m : Fin n, if k ≤ m then ((4 : ℝ) ^ (m : ℕ))⁻¹ * u m i * u m j else 0 := by
    calc GlobalTheory.RedTh.gram d u i j = ∑ m, u m i * d m * u m j := by
          rw [GlobalTheory.RedTh.gram, Matrix.mul_apply]; simp only [mul_diagonal, transpose_apply]
      _ = ∑ m : Fin n, ∑ k : Fin n, if k ≤ m then G k * (((4 : ℝ) ^ (m : ℕ))⁻¹ * u m i * u m j) else 0 := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [hd m, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          split_ifs <;> ring
      _ = _ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          split_ifs <;> ring
  rw [hL]
  simp only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  simp_rw [← tail_sum _ hu _ _ (hC _)]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l' hl' => ?_
  have hmem : extZ k l' ∈ Finset.univ.biUnion fun k => (T k).image (extZ k) :=
    Finset.mem_biUnion.2 ⟨k, Finset.mem_univ _, Finset.mem_image_of_mem _ hl'⟩
  simp_rw [mul_ite, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq, if_pos hmem]
  ring

end GlobalTheory.SiegelCone
end
end
