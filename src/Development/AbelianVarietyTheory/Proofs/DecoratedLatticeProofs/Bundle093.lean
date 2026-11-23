module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle077
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle173
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle294
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle008
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle085
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle001
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle099
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle090
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalConjUnipotentRadicalIsotropic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle065
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord

@[expose] public section

section

noncomputable section

open scoped NNReal TensorProduct
open NumberField Matrix Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory.Eis.Conv GlobalTheory.MixModel GlobalTheory.RegSW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GodementSectionReduction


open GlobalTheory.SummCount in
theorem summable_of_count (ι : Type) (n N : ℕ) (b C t : ℝ) (k : ι → Fin n → ℕ)
    (h : ι → ℝ) (hb : 1 < b) (ht : (N : ℝ) < t)
    (hh : ∀ q, 0 ≤ h q ∧ h q ≤ C * ∏ i, (b ^ k q i)⁻¹)
    (hT : ∀ (m : Fin n → ℕ) (T : Finset ι), (∀ q ∈ T, k q = m) →
      (T.card : ℝ) ≤ C * ∏ i, b ^ (N * m i)) :
    Summable fun q => h q ^ t := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  have ht0 : 0 ≤ t := le_trans (Nat.cast_nonneg N) ht.le
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨q0⟩⟩
  · exact .of_finite
  have hP : ∀ m : Fin n → ℕ, 0 < ∏ i, (b ^ m i)⁻¹ := fun m => by positivity
  have hC : 0 ≤ C := (mul_nonneg_iff_of_pos_right (hP (k q0))).1 ((hh q0).1.trans (hh q0).2)
  set r := b ^ ((N : ℝ) - t) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg hb0.le _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hb (by linarith)
  set g : (Fin n → ℕ) → ℝ := fun m => C * C ^ t * ∏ i, r ^ m i with hg_def
  have hg0 : ∀ m, 0 ≤ g m := fun m => by
    simp only [hg_def]; positivity
  have hg : Summable g :=
    (summable_prod_fin_tuple (summable_geometric_of_lt_one hr0 hr1) (fun _ => pow_nonneg hr0 _)
      n).mul_left _
  have key : ∀ q, h q ^ t ≤ C ^ t * ∏ i, ((b ^ k q i)⁻¹) ^ t := fun q => by
    rw [Real.finsetProd_rpow _ _ (fun i _ => by positivity), ← Real.mul_rpow hC (hP _).le]
    exact Real.rpow_le_rpow (hh q).1 (hh q).2 ht0
  refine summable_of_sum_le (c := ∑' m, g m) (fun q => Real.rpow_nonneg (hh q).1 _) fun T => ?_
  rw [← Finset.sum_fiberwise_of_maps_to (g := k) (t := T.image k)
    (fun q hq => Finset.mem_image_of_mem k hq)]
  refine le_trans (Finset.sum_le_sum fun m _ => ?_) (hg.sum_le_tsum _ (fun m _ => hg0 m))
  calc ∑ q ∈ T with k q = m, h q ^ t
      ≤ ∑ q ∈ T with k q = m, C ^ t * ∏ i, ((b ^ m i)⁻¹) ^ t :=
        Finset.sum_le_sum fun q hq => by
          have := key q
          rwa [(Finset.mem_filter.1 hq).2] at this
    _ = ((T.filter (k · = m)).card : ℝ) * (C ^ t * ∏ i, ((b ^ m i)⁻¹) ^ t) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (C * ∏ i, b ^ (N * m i)) * (C ^ t * ∏ i, ((b ^ m i)⁻¹) ^ t) :=
        mul_le_mul_of_nonneg_right (hT m _ fun q hq => (Finset.mem_filter.1 hq).2)
          (mul_nonneg (Real.rpow_nonneg hC _)
            (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (by positivity) _))
    _ = g m := by
        simp only [hg_def, hr, ← pow_mul_inv_rpow_eq hb0 N, Finset.prod_mul_distrib]
        ring


open GlobalTheory.Eis.Conv.CovSkew in
theorem cover_adele (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : IsCMExt F E σ) : ∃ (Ω : Set (AF F ⊗[F] E)) (C : ℝ), IsCompact Ω ∧ ∀ m : ℕ, ∃ Y : Finset (AF F ⊗[F] E),
      (Y.card : ℝ) ≤ C * ((4 : ℝ) ^ Fintype.card (InfinitePlace F)) ^ m ∧ ∀ z : AF F ⊗[F] E, ∃ x : E, ∃ y ∈ Y, ∃ ω ∈ Ω,
        z = inclR (F := F) (AF F) x + y + (halfE F E).1 ^ m * ω := by
  classical
  haveI := hσ.1
  obtain ⟨Ω₀, C₀, hΩ₀, hcov⟩ := GlobalTheory.T.exists_adele_cover_mod_field_shrunk_compact F
  obtain ⟨δ, -, hsp⟩ := exists_delta F E σ hσ
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := isTopologicalRing_tens
  have hcont : Continuous fun p : AF F × AF F => psi (F := F) δ p.1 p.2 := by
    unfold psi
    fun_prop
  refine ⟨_, C₀ ^ 2, (hΩ₀.prod hΩ₀).image hcont, fun m => ?_⟩
  obtain ⟨Y, hY, hYc⟩ := hcov m
  refine ⟨(Y ×ˢ Y).image fun y => psi δ y.1 y.2, ?_, fun z => ?_⟩
  · refine (Nat.cast_le.mpr Finset.card_image_le).trans ?_
    rw [Finset.card_product, Nat.cast_mul]
    refine (mul_self_le_mul_self (Nat.cast_nonneg _) hY).trans (le_of_eq ?_)
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow, mul_pow]
    ring
  · obtain ⟨u, v, rfl⟩ := exists_coords δ hsp z
    set c : AF F := algebraMap F (AF F) 2⁻¹ with hc
    have h2 : 2 * c = 1 := by
      rw [hc, ← map_ofNat (algebraMap F (AF F)) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
    obtain ⟨x, y, hy, ω, hω, e⟩ := hYc (c * (u + v))
    obtain ⟨x', y', hy', ω', hω', e'⟩ := hYc (c * (v - u))
    refine ⟨(x - x') • (1 : E) + (x + x') • δ, _, Finset.mem_image.mpr ⟨(y, y'), Finset.mem_product.2 ⟨hy, hy'⟩, rfl⟩,
      _, ⟨(ω, ω'), ⟨hω, hω'⟩, rfl⟩, ?_⟩
    have : (halfE F E).1 = algebraMap (AF F) (AF F ⊗[F] E) (halfInf F).1 := rfl
    rw [this, ← map_pow, ← psi_split, ← e, ← e', psi_eq]
    congr 2
    · linear_combination (-u) * h2
    · linear_combination (-v) * h2

variable {D : D7} {T T₀ : HSp D} {r : ℕ}

end GlobalTheory.GodementSectionReduction

end
end

section

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.Gen
open GlobalTheory.StdUnn.Model
variable {D : D7} {n : ℕ}

theorem mat_mul (g h : G D n) : mat (g * h) = mat g * mat h := rfl

theorem exists_blockMatrixTwoByTwoFin_eq {R : Type} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : ∃ a b c d, M = blk4 a b c d := by
  refine ⟨(M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁, (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂,
    (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁, (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂, ?_⟩
  rw [blk4, Matrix.fromBlocks_toBlocks]
  ext i j
  simp

theorem rel {g : G D n} {a b c d : Mx D n n} (hg : mat g = blk4 a b c d) :
    -(adj c * a) + adj a * c = 0 ∧ -(adj c * b) + adj a * d = 1 ∧ -(adj d * b) + adj b * d = 0 := by
  have h : adj (mat g) * JR (AF D.host.F) (Jst D n) * mat g = JR (AF D.host.F) (Jst D n) := g.2
  rw [JR_Jst, hg] at h
  simp only [adelicConjTranspose_blockMatrixTwoByTwoFin, submatrix_fromBlocks_mul, mul_zero, mul_one, add_zero, zero_add, mul_neg, neg_mul] at h
  exact ⟨(blockMatrixTwoByTwoFin_injective h).1, (blockMatrixTwoByTwoFin_injective h).2.1, (blockMatrixTwoByTwoFin_injective h).2.2.2⟩

variable {S : Subgroup (G D n)}
  (hm : ∀ (g : G D n) (a : GL (Fin n) (AE D)), mat g = blk4 a.1 0 0 (adj (a⁻¹).1) → g ∈ S)
  (hn : ∀ (g : G D n) (b : Mx D n n), mat g = blk4 1 b 0 1 → g ∈ S)
  (hw : ∀ g : G D n, mat g = blk4 0 1 (-1) 0 → g ∈ S)

include hm hn in
theorem mem_of_upper {g : G D n} {a b d : Mx D n n} (hg : mat g = blk4 a b 0 d) (ha : IsUnit a) : g ∈ S := by
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨m, hmm⟩ := exists_levi (D := D) (n := n) u⁻¹
  have h1 : (adj u.1 : Mx D n n) * d = 1 := by simpa using (rel hg).2.1
  rw [← S.mul_mem_cancel_left (hm m _ hmm)]
  refine hn _ ((u⁻¹).1 * b) ?_
  rw [mat_mul, hmm, hg, submatrix_fromBlocks_mul]
  simp only [inv_inv, Units.inv_mul, mul_zero, zero_mul, add_zero, zero_add, h1]

include hm hn hw in
theorem mem_of_lower {g : G D n} {a c d : Mx D n n} (hg : mat g = blk4 a 0 c d) (hd : IsUnit d) : g ∈ S := by
  obtain ⟨w, hww⟩ := exists_weyl (D := D) (n := n)
  rw [← S.mul_mem_cancel_left (hw w hww), ← S.mul_mem_cancel_right (hw w hww)]
  refine mem_of_upper hm hn (a := -d) (b := c) (d := -a) ?_ hd.neg
  rw [mat_mul, mat_mul, hww, hg, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp

include hm hn hw in
theorem mem_of_isUnit {g : G D n} {a b c d : Mx D n n} (hg : mat g = blk4 a b c d) (hd : IsUnit d) : g ∈ S := by
  obtain ⟨u, rfl⟩ := hd
  have adj_mul_local {l m n : ℕ} (x : Mx D l m) (y : Mx D m n) :
      adj (x * y) = adj y * adj x := by
    unfold adj
    rw [Matrix.map_mul, Matrix.transpose_mul]
  have h1 : (adj u.1 : Mx D n n) * b = adj b * u.1 := neg_add_eq_zero.1 (rel hg).2.2
  have h2 : (adj (u⁻¹).1 : Mx D n n) * adj u.1 = 1 := by rw [← adj_mul_local, Units.mul_inv, adj_one]
  have h3 : (adj (-(b * (u⁻¹).1)) : Mx D n n) = -(b * (u⁻¹).1) := by
    rw [adj_neg, adj_mul_local]
    congr 1
    calc (adj (u⁻¹).1 : Mx D n n) * adj b = adj (u⁻¹).1 * (adj b * u.1) * (u⁻¹).1 := by
          rw [mul_assoc, mul_assoc, Units.mul_inv, mul_one]
      _ = b * (u⁻¹).1 := by rw [← h1, ← mul_assoc, h2, one_mul]
  obtain ⟨x, hx⟩ := (exists_unip _).2 h3
  rw [← S.mul_mem_cancel_left (hn x _ hx)]
  refine mem_of_lower hm hn hw (a := a + -(b * (u⁻¹).1) * c) (c := c) (d := u.1) ?_ u.isUnit
  rw [mat_mul, hx, hg, submatrix_fromBlocks_mul]
  simp only [one_mul, zero_mul, zero_add, neg_mul, mul_assoc, Units.inv_mul, mul_one, add_neg_cancel]

end GlobalTheory.StdUnn.Gen

namespace GlobalTheory.StdUnn

theorem eq_top_of_levi_unip_weyl : ∀ (D : D7) (n : ℕ) (S : Subgroup (GlobalTheory.StdUnn.G D n)), (∀ (g : GlobalTheory.StdUnn.G D n) (a : GL (Fin n) (AE D)), GlobalTheory.StdUnn.mat g = GlobalTheory.StdUnn.blk4 a.1 0 0 (GlobalTheory.MixModel.adj (a⁻¹).1) → g ∈ S) → (∀ (g : GlobalTheory.StdUnn.G D n) (b : Mx D n n), GlobalTheory.StdUnn.mat g = GlobalTheory.StdUnn.blk4 1 b 0 1 → g ∈ S) → (∀ g : GlobalTheory.StdUnn.G D n, GlobalTheory.StdUnn.mat g = GlobalTheory.StdUnn.blk4 0 1 (-1) 0 → g ∈ S) → S = ⊤ := by
  intro D n S hm hn hw
  rw [eq_top_iff]
  intro g _
  obtain ⟨a, b, c, d, hg⟩ := Gen.exists_blockMatrixTwoByTwoFin_eq (mat g)
  obtain ⟨p', p, q', q, hi⟩ := Gen.exists_blockMatrixTwoByTwoFin_eq (mat g⁻¹)
  have h1 : mat g * mat g⁻¹ = 1 := by rw [← Gen.mat_mul, mul_inv_cancel]; rfl
  rw [hg, hi, Model.submatrix_fromBlocks_mul, ← Model.block_matrix_one] at h1
  obtain ⟨x, hx, hu⟩ := GlobalTheory.HermTransversal.exists_herm_isUnit D n c d p q (Model.blockMatrixTwoByTwoFin_injective h1).2.2.2
  obtain ⟨y, hy⟩ := (Model.exists_unip x).2 hx
  rw [← S.mul_mem_cancel_right (hn y _ hy)]
  refine Gen.mem_of_isUnit hm hn hw (a := a) (b := a * x + b) (c := c) (d := c * x + d) ?_ hu
  rw [Gen.mat_mul, hg, hy, Model.submatrix_fromBlocks_mul]
  simp only [mul_one, mul_zero, add_zero]

end GlobalTheory.StdUnn

end
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.LeftInvSect
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model
variable {D : D7} {n : ℕ}

theorem rat_mat {γ : G D n} (h : γ ∈ GF D n) :
    ∃ x : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E, mat γ = x.map (incA D) := by
  obtain ⟨x, -, hx⟩ := h
  exact ⟨x.1, (congrArg Units.val hx).symm⟩

theorem det_rat {γ : G D n} (h : γ ∈ GF D n) (a : GL (Fin n) (AE D)) (ha : blkA (mat γ) = a.1) :
    ∃ u : D.host.Eˣ, Matrix.GeneralLinearGroup.det a = Units.map (incA D).toMonoidHom u := by
  haveI : Nontrivial (AF D.host.F) := inferInstanceAs (Nontrivial (Ainf D.host.F × Af D.host.F))
  haveI : Nontrivial (AE D) := inferInstance
  obtain ⟨x, hx⟩ := rat_mat h
  have e : ((Matrix.GeneralLinearGroup.det a : (AE D)ˣ) : AE D) = incA D (blkA x).det := by
    rw [RingHom.map_det]
    change a.1.det = _
    rw [← ha, hx]; rfl
  have h0 : (blkA x).det ≠ 0 := fun h0 => Units.ne_zero _ (e.trans (by rw [h0, map_zero]))
  exact ⟨Units.mk0 _ h0, Units.ext e⟩

theorem siegelParabolicUnn_matrix_blockUpperTriangular {p : G D n} (hp : p ∈ P D n) : ∃ b d, mat p = blk4 (blkA (mat p)) b 0 d := by
  refine ⟨((mat p).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂,
    ((mat p).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂, ?_⟩
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j
  · rfl
  · rfl
  · exact lower_eq_zero hp i j
  · rfl

theorem mat_inj {g h : G D n} (e : mat g = mat h) : g = h := Subtype.ext (Units.ext e)

theorem mat_mul (g h : G D n) : mat (g * h) = mat g * mat h := rfl

theorem mat_one : mat (1 : G D n) = 1 := rfl

theorem levi_mul_inv (a : GL (Fin n) (AE D)) :
    (blk4 a.1 0 0 (adj (a⁻¹).1) : Mx D (n + n) (n + n)) * blk4 (a⁻¹).1 0 0 (adj a.1) = 1 := by
  have h2 : (adj (a⁻¹).1 : Mx D n n) * adj a.1 = 1 := by rw [← adj_mul]; simp [adj_one]
  simp [submatrix_fromBlocks_mul, h2, block_matrix_one, -Matrix.coe_units_inv]

theorem exists_levi_unip {p : G D n} (hp : p ∈ P D n) (a : GL (Fin n) (AE D)) (ha' : blkA (mat p) = a.1) :
    ∃ (m u : G D n) (b : Mx D n n), p = m * u ∧ mat m = blk4 a.1 0 0 (adj (a⁻¹).1) ∧ mat u = blk4 1 b 0 1 := by
  obtain ⟨m, hm⟩ := exists_levi a
  obtain ⟨m', hm'⟩ := exists_levi a⁻¹
  obtain ⟨b, d, hb⟩ := siegelParabolicUnn_matrix_blockUpperTriangular hp
  rw [ha'] at hb
  rw [inv_inv] at hm'
  have hu : mat (m' * p) = blk4 1 ((a⁻¹).1 * b) 0 (adj a.1 * d) := by
    rw [mat_mul, hm', hb, submatrix_fromBlocks_mul]
    simp [-Matrix.coe_units_inv]
  have hd : (adj a.1 : Mx D n n) * d = 1 := by
    have h : adj (mat (m' * p)) * JR (AF D.host.F) (Jst D n) * mat (m' * p) = JR (AF D.host.F) (Jst D n) := (m' * p).2
    rw [JR_Jst, hu] at h
    generalize (adj a.1 : Mx D n n) * d = d' at h ⊢
    generalize (a⁻¹).1 * b = b' at h
    simp only [adelicConjTranspose_blockMatrixTwoByTwoFin, submatrix_fromBlocks_mul, adj_one, adj_zero, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, mul_neg,
      neg_mul, neg_zero] at h
    exact (blockMatrixTwoByTwoFin_injective h).2.1
  have hmm : m * m' = 1 := mat_inj (by rw [mat_mul, mat_one, hm, hm', levi_mul_inv])
  refine ⟨m, m' * p, (a⁻¹).1 * b, by rw [← mul_assoc, hmm, one_mul], hm, by rw [hu, hd]⟩

theorem exists_blkA {p : G D n} (hp : p ∈ P D n) : ∃ a : GL (Fin n) (AE D), blkA (mat p) = a.1 :=
  ⟨levi (D := D) (n := n) ⟨p, hp⟩, rfl⟩

theorem height_inv (hI : ∀ g : G D n, ∃ p ∈ P D n, ∃ k ∈ K D n, g = p * k) {H : G D n → ℝ≥0} (hH : IsHeight H)
    {γ : G D n} (hp : γ ∈ P D n) (a : GL (Fin n) (AE D)) (ha : blkA (mat γ) = a.1)
    (h1 : absA D (Matrix.GeneralLinearGroup.det a) = 1) (g : G D n) : H (γ * g) = H g := by
  obtain ⟨p, hp', k, hk, rfl⟩ := hI g
  obtain ⟨c, hc⟩ := exists_blkA hp'
  have e : blkA (mat (γ * p)) = (a * c).1 := by rw [blkA_mul hp', ha, hc, Units.val_mul]
  rw [← mul_assoc, hH _ ((P D n).mul_mem hp hp') (a * c) e k hk, hH p hp' c hc k hk, map_mul, map_mul, h1, one_mul]

theorem leftInv_sect : ∀ (D : D7) (n : ℕ), (∀ g : GlobalTheory.StdUnn.G D n, ∃ p ∈ GlobalTheory.StdUnn.P D n, ∃ k ∈ GlobalTheory.StdUnn.K D n, g = p * k) → ∀ (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D) (μ : Measure (Mx D V.rank n)) (ω : GlobalTheory.StdUnn.G D n →* Module.End ℂ (GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ V.rank n)), IsHeckeChar D χ → GlobalTheory.StdUnn.IsWeilSch ψ χ θ V μ ω → ∀ H : GlobalTheory.StdUnn.G D n → ℝ≥0, GlobalTheory.StdUnn.IsHeight H → ∀ (Φ : GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ V.rank n) (z : ℂ), GlobalTheory.AutomorphicL2Unitary.LeftInv (GlobalTheory.StdUnn.P D n ⊓ GlobalTheory.StdUnn.GF D n) (GlobalTheory.StdUnn.sect ω H Φ z) := by
  intro D n hI V ψ χ θ μ ω hχ hω H hH Φ z γ hγ g
  obtain ⟨hp, hr⟩ := Subgroup.mem_inf.1 hγ
  obtain ⟨a, ha⟩ := exists_blkA hp
  obtain ⟨u, hu⟩ := det_rat hr a ha
  have h1 : absA D (Matrix.GeneralLinearGroup.det a) = 1 := by
    rw [hu]; exact absE_inclR u
  have h2 : χ (Matrix.GeneralLinearGroup.det a) = 1 := by
    rw [hu]; exact hχ.2 u
  have hHe : H (γ * g) = H g := height_inv hI hH hp a ha h1 g
  have hW : (ω (γ * g) Φ).1 0 = (ω g Φ).1 0 := by
    obtain ⟨m, v, b, e, hm, hv⟩ := exists_levi_unip hp a ha
    have e' : ω (γ * g) Φ = ω m (ω v (ω g Φ)) := by
      rw [e, map_mul, map_mul]; rfl
    have z1 : ∀ a : Mx D n n, ((0 : Mx D V.rank n) ⬝ a : Mx D V.rank n) = 0 := fun a => Matrix.zero_mul a
    have z2 : StdUnn.inner V (0 : Mx D V.rank n) 0 = 0 := by rw [StdUnn.inner, adj_zero, Matrix.zero_mul]
    rw [e', hω.levi m _ hm, h1, h2, z1, hω.unip v b hv, z2]
    simp [halfTr, npow]
  simp only [sect, hHe, hW]

end GlobalTheory.StdUnn.LeftInvSect
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypePrimeUnif

theorem mul_not_mem_sq {R : Type*} [CommRing R] [IsDedekindDomain R] (Q : HeightOneSpectrum R) {a b : R}
    (hab : IsCoprime a b) (ha : a ∈ Q.asIdeal → a ∉ Q.asIdeal ^ 2) (hb : b ∈ Q.asIdeal → b ∉ Q.asIdeal ^ 2) :
    a * b ∉ Q.asIdeal ^ 2 := by
  intro h
  have := Q.isPrime
  have hle : Q.asIdeal ^ 2 ≤ Q.asIdeal := Ideal.pow_le_self two_ne_zero
  rcases Ideal.IsPrime.mul_mem_pow Q.asIdeal h with h1 | h1
  · rcases Ideal.IsPrime.mul_mem_pow Q.asIdeal (mul_comm a b ▸ h) with h2 | h2
    · obtain ⟨u, v, huv⟩ := hab
      exact Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
        (huv ▸ Q.asIdeal.add_mem (Q.asIdeal.mul_mem_left u h1) (Q.asIdeal.mul_mem_left v h2)))
    · exact ha h1 h2
  · exact hb (hle h1) h1

theorem prod_not_mem_sq : ∀ (D : D7) (Q : Pl D.host.E), ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal ^ 2 := by
  intro D Q _
  have key : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal →
      ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal ^ 2 := fun k hk =>
    (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) Q hk).2.1
  have hc : Nat.Coprime (D.host.g 0) (D.host.g 1) :=
    (Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne
  rw [Nat.cast_mul]
  exact mul_not_mem_sq Q (Nat.Coprime.cast hc) (key 0) (key 1)

end GlobalTheory.TypePrimeUnif
end

section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

theorem _root_.GlobalTheory.T.exists_compact_integral_unitary_finitePart : ∀ I : AutInst, ∃ K : Set I.Gf, IsCompact K ∧ ∀ γ : GL (Fin I.n) I.E, γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J → (∀ i j, IsIntegral ℤ ((γ : Matrix (Fin I.n) (Fin I.n) I.E) i j)) → (∀ i j, IsIntegral ℤ (((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) i j)) → ∃ x ∈ I.GFset, x.2 ∈ K ∧ ∀ v, uMat (x.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v := by
  first | exact @GlobalTheory.IntUnitCpt.intUnit_compact | exact GlobalTheory.IntUnitCpt.intUnit_compact | (intros; apply GlobalTheory.IntUnitCpt.intUnit_compact <;> assumption)
end

section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

theorem _root_.GlobalTheory.T.rational_conj_unipotentRadical_isotropic : ∀ (I : AutInst), ∀ γ ∈ I.GFset, ∀ W, I.IsIsot W → ∃ W', I.IsIsot W' ∧ ∀ m ∈ I.NA W', γ⁻¹ * m * γ ∈ I.NA W := by
  first | exact @GlobalTheory.CuspGeo.naconj | exact GlobalTheory.CuspGeo.naconj | (intros; apply GlobalTheory.CuspGeo.naconj <;> assumption)
end
