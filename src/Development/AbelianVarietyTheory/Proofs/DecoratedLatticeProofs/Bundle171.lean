module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle145
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle147
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientHeightLowerBoundShortIsotropicVector
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle157
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.LineAct

theorem neg_wRow_half_rd : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n'' : Type) [Fintype n] [DecidableEq n] [Fintype n''] [DecidableEq n''] (S₀ A L W₀ : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) (β : Frame p W₀ n) (γ : Frame p A n'') (γ₀ : Frame p S₀ (n'' ⊕ Fin 1)), IsSumFrame o ζ γ γ₀ → ∀ t : n → k, IsHalf p.e ((o.resT W₀).symm (0, -GlobalTheory.FinPl.LineAct.wRow p ζ β t)) ∧ ∀ i j, rd β γ₀ ((o.resT W₀).symm (0, -GlobalTheory.FinPl.LineAct.wRow p ζ β t)) i j = Sum.elim (fun _ => 0) (fun _ => -t j) i := by
  intro D k _ _ _ _ p n n'' _ _ _ _ S₀ A L W₀ o ζ β γ γ₀ hsum t
  have hes : ∀ a, p.e * p.sec a = p.sec a := fun a => by rw [← p.sec_pr, p.pr_sec]
  rw [OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.neg_apply, wRow, Matrix.of_apply, mul_left_comm, mul_neg, hes, mul_neg]
  · set c : Fin S₀.rank → k := fun i => p.pr (ratV (vecB o ζ) i) with hc
    have hmap : Matrix.map (o.jB * -wRow p ζ β t : Mx D S₀.rank W₀.rank) p.pr = -vecMulVec c (t ᵥ* β.b') := by
      refine Matrix.ext fun a b => ?_

      rw [Matrix.map_apply, Matrix.mul_apply, map_sum, Matrix.neg_apply, vecMulVec_apply, hc]

      simp only [ratV, vecB, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Matrix.neg_apply, wRow, Matrix.of_apply, map_neg, p.pr_sec, mul_neg, mul_assoc]
      rfl
    have hcol : (γ₀.b' *ᵥ c) i = Sum.elim (fun _ => 0) (fun _ => 1) i := by
      have h := congrFun (congrFun γ₀.b'b i) (Sum.inr 0)
      rw [hsum, Matrix.mul_apply] at h
      simp only [fromCols_apply_inr, replicateCol_apply] at h
      refine h.trans ?_
      rcases i with i | i
      · simp
      · obtain rfl := Subsingleton.elim i 0
        simp
    rw [rd, hmap, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_vecMul, β.b'b,
      Matrix.vecMul_one, Matrix.neg_apply, vecMulVec_apply, hcol]
    rcases i with i | i <;> simp

end GlobalTheory.FinPl.LineAct

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
open scoped TensorProduct

namespace GlobalTheory.IwaPlace.DualIso

variable {D : D7}

theorem intAE_mul_mem' {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem intAt_mul_mem {v : Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_left _ _ hb.1, by rw [map_mul]; exact intAE_mul_mem' ha.2 hb.2⟩

theorem hermAt_smul_left (S : HSp D) (o : AE D) (y x : Fin S.rank → AE D) :
    hermAt S (o • y) x = o * hermAt S y x := by
  simp only [hermAt, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem smul_mem_of_isSDAt {S : HSp D} {v : Pl D} {M : AddSubgroup (Fin S.rank → AE D)} (hM : IsSDAt S v M)
    {o : AE D} (ho : o ∈ intAt D (· = v)) {y : Fin S.rank → AE D} (hy : y ∈ M) : o • y ∈ M := by
  refine (hM.2.2 _ fun i => ?_).2 fun x hx => ?_
  · simp only [Pi.smul_apply, smul_eq_mul]; exact Ideal.mul_mem_left _ _ (hM.1 y hy i)
  · rw [hermAt_smul_left]; exact intAt_mul_mem ho ((hM.2.2 y (hM.1 y hy)).1 hy x hx)

theorem col_mul_mem {S : HSp D} {v : Pl D} {M : AddSubgroup (Fin S.rank → AE D)} (hM : IsSDAt S v M) {ρ : ℕ}
    (A : Mx D S.rank ρ) (B : Mx D ρ ρ) (hA : ∀ i, (fun k => A k i) ∈ M) (hB : ∀ m i, B m i ∈ intAt D (· = v))
    (i : Fin ρ) : (fun k => (A ⬝ B) k i) ∈ M := by
  have e : (fun k => (A ⬝ B) k i) = ∑ m, B m i • (fun k => A k m) := by
    funext k; simp [Matrix.mul_apply, Finset.sum_apply, mul_comm]
  rw [e]; exact AddSubgroup.sum_mem _ fun m _ => smul_mem_of_isSDAt hM (hB m i) (hA m)

theorem gram_entry (S : HSp D) {ρ : ℕ} (c' : Mx D S.rank ρ) (i j : Fin ρ) :
    (adj c' ⬝ (gA S ⬝ c')) i j = hermAt S (fun k => c' k j) (fun k => c' k i) := by
  simp only [hermAt, adj, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, mul_assoc]

theorem smul_mul_smul_one {ρ : ℕ} (ε w : AE D) (H : Mx D ρ ρ) : (ε • (1 : Mx D ρ ρ)) ⬝ (w • H) = (ε * w) • H := by
  rw [smul_mul_assoc, one_mul, smul_smul]

theorem smul_mul_smul_one' {ρ : ℕ} (ε w : AE D) (H : Mx D ρ ρ) : (w • H) ⬝ (ε • (1 : Mx D ρ ρ)) = (ε * w) • H := by
  rw [mul_smul_comm, mul_one, smul_smul]

theorem adj_gram_self (S : HSp D) {ρ : ℕ} (c' : Mx D S.rank ρ) : adj (adj c' ⬝ (gA S ⬝ c')) = adj c' ⬝ (gA S ⬝ c') := by
  rw [adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc]

theorem gram_swap_smul (S : HSp D) {ρ : ℕ} {ε : AE D} (hεc : cA D ε = ε) (c c' : Mx D S.rank ρ)
    (hcc : adj c' ⬝ (gA S ⬝ c) = ε • (1 : Mx D ρ ρ)) : adj c ⬝ (gA S ⬝ c') = ε • (1 : Mx D ρ ρ) := by
  have := congrArg adj hcc
  rwa [adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc, adj_smul, hεc, adj_one] at this

theorem pair_sub (S : HSp D) {ρ : ℕ} {ε : AE D} (c c' : Mx D S.rank ρ) (K : Mx D ρ ρ)
    (hcc0 : adj c ⬝ (gA S ⬝ c) = 0) (hcc : adj c' ⬝ (gA S ⬝ c) = ε • (1 : Mx D ρ ρ)) :
    adj (c' - c ⬝ K) ⬝ (gA S ⬝ c) = ε • (1 : Mx D ρ ρ) := by
  rw [adj_sub, adj_mul, Matrix.sub_mul, Matrix.mul_assoc, hcc0, Matrix.mul_zero, sub_zero, hcc]

theorem pair_sub' (S : HSp D) {ρ : ℕ} {ε : AE D} (c c' : Mx D S.rank ρ) (K : Mx D ρ ρ)
    (hcc' : adj c ⬝ (gA S ⬝ c') = ε • (1 : Mx D ρ ρ)) :
    adj (c' - c ⬝ K) ⬝ (gA S ⬝ c') = adj c' ⬝ (gA S ⬝ c') - adj K ⬝ (ε • (1 : Mx D ρ ρ)) := by
  rw [adj_sub, adj_mul, Matrix.sub_mul, Matrix.mul_assoc, hcc']

theorem self_sub (S : HSp D) {ρ : ℕ} (c'' c c' : Mx D S.rank ρ) (K : Mx D ρ ρ) (h : c'' = c' - c ⬝ K) :
    adj c'' ⬝ (gA S ⬝ c'') = adj c'' ⬝ (gA S ⬝ c') - adj c'' ⬝ (gA S ⬝ c) ⬝ K := by
  rw [h, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc (gA S) c K,
    ← Matrix.mul_assoc (adj (c' - c ⬝ K)) (gA S ⬝ c) K]

theorem isotropic_core {S : HSp D} {v : Pl D} {ε : AE D} (hεε : ε * ε = ε) (hεc : cA D ε = ε)
    (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) {M : AddSubgroup (Fin S.rank → AE D)} (hM : IsSDAt S v M)
    {w : AE D} (hw : w ∈ intAt D (· = v)) (hwc : w + cA D w = ε) {ρ : ℕ} (c c' : Mx D S.rank ρ)
    (hc : ∀ i, (fun k => c k i) ∈ M) (hc' : ∀ i, (fun k => c' k i) ∈ M) (hcc0 : adj c ⬝ (gA S ⬝ c) = 0)
    (hcc : adj c' ⬝ (gA S ⬝ c) = ε • (1 : Mx D ρ ρ)) :
    ∃ c'' : Mx D S.rank ρ, (∀ i, (fun k => c'' k i) ∈ M) ∧ adj c'' ⬝ (gA S ⬝ c) = ε • (1 : Mx D ρ ρ) ∧
      adj c'' ⬝ (gA S ⬝ c'') = 0 := by
  obtain ⟨H, hH⟩ : ∃ H : Mx D ρ ρ, H = adj c' ⬝ (gA S ⬝ c') := ⟨_, rfl⟩
  have hHint : ∀ i j, H i j ∈ intAt D (· = v) := fun i j => by
    rw [hH, gram_entry]; exact (hM.2.2 _ (hM.1 _ (hc' j))).1 (hc' j) _ (hc' i)
  have hεH : ε • H = H := by
    funext i j; rw [Matrix.smul_apply, smul_eq_mul]; exact (hε _).1 (hHint i j).1
  have hadjH : adj H = H := by rw [hH]; exact adj_gram_self S c'
  have hcc' := gram_swap_smul S hεc c c' hcc
  have hKint : ∀ m i, (w • H) m i ∈ intAt D (· = v) := fun m i => by
    rw [Matrix.smul_apply, smul_eq_mul]; exact intAt_mul_mem hw (hHint m i)
  have e3 : ε * cA D w + ε * w = ε := by rw [← mul_add, add_comm, hwc, hεε]
  have f3 : H - (ε * cA D w) • H - (ε * w) • H = 0 := by
    rw [sub_sub, ← add_smul, e3, hεH, sub_self]
  have e1 := pair_sub S (ε := ε) c c' (w • H) hcc0 hcc
  have e2 := pair_sub' S c c' (w • H) hcc'
  rw [← hH, adj_smul, hadjH, smul_mul_smul_one'] at e2
  refine ⟨c' - c ⬝ (w • H), fun i => ?_, e1, ?_⟩
  · have e : (fun k => (c' - c ⬝ (w • H)) k i) = (fun k => c' k i) - fun k => (c ⬝ (w • H)) k i := rfl
    rw [e]; exact sub_mem (hc' i) (col_mul_mem hM c _ hc hKint i)
  · rw [self_sub S _ c c' (w • H) rfl, e1, e2, smul_mul_smul_one, f3]
theorem dual_isotropic : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) (M : AddSubgroup (Fin S.rank → AE D)), IsSDAt S v M → ∀ w ∈ intAt D (· = v), w + cA D w = ε → ∀ (b : Mx D ρ ρ) (c' : Mx D S.rank ρ), (∀ i j, b i j ∈ idAt D (· = v)) → (∀ i, (fun k => (d.jX ⬝ b) k i) ∈ M) → (∀ i, (fun k => c' k i) ∈ M) → adj c' ⬝ (gA S ⬝ (d.jX ⬝ b)) = ε • (1 : Mx D ρ ρ) → ∃ c'' : Mx D S.rank ρ, (∀ i, (fun k => c'' k i) ∈ M) ∧ adj c'' ⬝ (gA S ⬝ (d.jX ⬝ b)) = ε • (1 : Mx D ρ ρ) ∧ adj c'' ⬝ (gA S ⬝ c'') = 0 := by
  intro D S S₀ ρ d v ε hεε hεc hεI hε M hM w hw hwc b c' hb hc hc' hcc
  have hcc0 : adj (d.jX ⬝ b) ⬝ (gA S ⬝ (d.jX ⬝ b)) = 0 := by
    rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S) d.jX b, ← Matrix.mul_assoc (adj d.jX),
      d.gram_XX, Matrix.zero_mul, Matrix.mul_zero]
  exact isotropic_core hεε hεc hε hM hw hwc (d.jX ⬝ b) c' hc hc' hcc0 hcc

end GlobalTheory.IwaPlace.DualIso

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
open scoped TensorProduct

namespace GlobalTheory.IwaPlace.SdComap



variable {D : D7}

theorem exists_nat_mul_isIntegral' (e : D.host.E) : ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : D.host.E) * e) := by
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := D.host.E) {e}
  have h := hy e (Finset.mem_singleton_self e)
  have hpos : 0 < y.natAbs := Int.natAbs_pos.2 hy0
  refine ⟨y.natAbs * y.natAbs, Nat.mul_pos hpos hpos, ?_⟩
  have e1 : ((y.natAbs * y.natAbs : ℕ) : D.host.E) * e = (y : D.host.E) * ((y : D.host.E) * e) := by
    have h2 := Int.natAbs_mul_self' y
    rw [← mul_assoc, ← Int.cast_natCast, Nat.cast_mul, h2, Int.cast_mul]
  rw [e1]
  rw [zsmul_eq_mul] at h
  refine IsIntegral.mul ?_ h
  simpa using (isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := y))

theorem mul_mem_intAE' {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem natCast_mem_intAE (n : ℕ) : (n : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D := by
  rw [Algebra.TensorProduct.natCast_def]
  refine AddSubgroup.subset_closure ⟨(n : Af D.host.F), fun v => ?_, 1, ?_⟩
  · rw [map_natCast]; exact natCast_mem _ n
  · simp

theorem exists_natCast_mul_mem_intAE (z : Af D.host.F ⊗[D.host.F] D.host.E) :
    ∃ n : ℕ, 0 < n ∧ (n : Af D.host.F ⊗[D.host.F] D.host.E) * z ∈ intAE D := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, by rw [mul_zero]; exact zero_mem _⟩
  | tmul a e =>
    obtain ⟨n, hn, he⟩ := exists_nat_mul_isIntegral' (D := D) e
    obtain ⟨d, hd, ha⟩ := GlobalTheory.HolDict.ShortVec.exists_denom_adele (F := D.host.F) a
    refine ⟨d * n, Nat.mul_pos hd hn, ?_⟩
    have e1 : ((d * n : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * (a ⊗ₜ[D.host.F] e) =
        ((d : Af D.host.F) * a) ⊗ₜ[D.host.F] ((n : D.host.E) * e) := by
      rw [Nat.cast_mul, Algebra.TensorProduct.natCast_def, Algebra.TensorProduct.natCast_def',
        Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [e1]
    exact AddSubgroup.subset_closure ⟨_, fun v => Subring.mem_iInf.1 ha v, ⟨_, he⟩, rfl⟩
  | add x y hx hy =>
    obtain ⟨n₁, h₁, hx⟩ := hx
    obtain ⟨n₂, h₂, hy⟩ := hy
    refine ⟨n₁ * n₂, Nat.mul_pos h₁ h₂, ?_⟩
    have e1 : ((n₁ * n₂ : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * (x + y) =
        (n₂ : Af D.host.F ⊗[D.host.F] D.host.E) * ((n₁ : Af D.host.F ⊗[D.host.F] D.host.E) * x) +
          (n₁ : Af D.host.F ⊗[D.host.F] D.host.E) * ((n₂ : Af D.host.F ⊗[D.host.F] D.host.E) * y) := by
      push_cast; ring
    rw [e1]
    exact add_mem (mul_mem_intAE' (natCast_mem_intAE n₂) hx) (mul_mem_intAE' (natCast_mem_intAE n₁) hy)

theorem exists_natCast_mul_mem_intAt {P : Pl D → Prop} {a : AE D} (ha : a ∈ idAt D P) :
    ∃ n : ℕ, 0 < n ∧ (n : AE D) * a ∈ intAt D P := by
  obtain ⟨n, hn, h⟩ := exists_natCast_mul_mem_intAE (D := D) (finPart D a)
  refine ⟨n, hn, Ideal.mul_mem_left _ _ ha, ?_⟩
  rw [map_mul, map_natCast]; exact h

theorem intAt_add {P : Pl D → Prop} {a b : AE D} (ha : a ∈ intAt D P) (hb : b ∈ intAt D P) : a + b ∈ intAt D P :=
  ⟨add_mem ha.1 hb.1, by rw [map_add]; exact add_mem ha.2 hb.2⟩

theorem intAt_mul {P : Pl D → Prop} {a b : AE D} (ha : a ∈ intAt D P) (hb : b ∈ intAt D P) : a * b ∈ intAt D P :=
  ⟨Ideal.mul_mem_left _ _ hb.1, by rw [map_mul]; exact mul_mem_intAE' ha.2 hb.2⟩

theorem intAt_natCast_mul {P : Pl D → Prop} {a : AE D} (n : ℕ) (ha : a ∈ intAt D P) : (n : AE D) * a ∈ intAt D P :=
  ⟨Ideal.mul_mem_left _ _ ha.1, by rw [map_mul, map_natCast]; exact mul_mem_intAE' (natCast_mem_intAE n) ha.2⟩

theorem intAt_sum {P : Pl D → Prop} {ι : Type} (s : Finset ι) (f : ι → AE D) (h : ∀ i ∈ s, f i ∈ intAt D P) :
    ∑ i ∈ s, f i ∈ intAt D P := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩
  | insert a s has ih =>
    rw [Finset.sum_insert has]
    exact intAt_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem cA_mulVec {n : ℕ} (M : Mx D n n) (y : Fin n → AE D) :
    (fun i => cA D ((M *ᵥ y) i)) = Matrix.vecMul (fun i => cA D (y i)) (adj M) := by
  funext i

  simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, adj, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem hermAt_eq (S : HSp D) (x y : Fin S.rank → AE D) :
    hermAt S x y = Matrix.vecMul (fun i => cA D (y i)) (gA S) ⬝ᵥ x := by
  simp only [hermAt, Matrix.vecMul, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem hermAt_mt (S : HSp D) (g : GA D S) (x y : Fin S.rank → AE D) :
    hermAt S (mt S g *ᵥ x) (mt S g *ᵥ y) = hermAt S x y := by
  rw [hermAt_eq, hermAt_eq, cA_mulVec (mt S g) y, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul,
    mt_unitary]

theorem mulVec_eq_add {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (y : Fin n → R) (i : Fin n) :
    (M *ᵥ y) i = y i + ∑ j, (M i j - (1 : Matrix (Fin n) (Fin n) R) i j) * y j := by
  have h : M *ᵥ y = y + (M - 1) *ᵥ y := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  rw [h]; rfl

theorem eq_mulVec_sub {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (y : Fin n → R) (i : Fin n) :
    y i = (M *ᵥ y) i - ∑ j, (M i j - (1 : Matrix (Fin n) (Fin n) R) i j) * y j := by
  rw [mulVec_eq_add, add_sub_cancel_right]

theorem smul_mulVec_apply {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (y : Fin n → R) (c : R)
    (i : Fin n) : (c • (M *ᵥ y)) i = c * y i + ∑ j, (c * (M i j - (1 : Matrix (Fin n) (Fin n) R) i j)) * y j := by
  rw [Pi.smul_apply, smul_eq_mul, mulVec_eq_add, mul_add, Finset.mul_sum]
  simp only [mul_assoc]

theorem mulVec_natCast_smul {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (y : Fin n → R) (m K : ℕ) :
    M *ᵥ (((m * K : ℕ) : R) • y) = (m : R) • ((K : R) • (M *ᵥ y)) := by
  rw [Matrix.mulVec_smul, Nat.cast_mul, mul_smul]

theorem mulVec_mulVec_of_mul_eq_one {R : Type} [CommRing R] {n : ℕ} {M N : Matrix (Fin n) (Fin n) R} (h : M * N = 1)
    (x : Fin n → R) : M *ᵥ (N *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

theorem exists_common_natCast_mul_mem_intAt {P : Pl D → Prop} {ι : Type} [Fintype ι] (a : ι → AE D)
    (ha : ∀ i, a i ∈ idAt D P) : ∃ K : ℕ, 0 < K ∧ ∀ i, (K : AE D) * a i ∈ intAt D P := by
  classical
  choose n hn hx using fun i => exists_natCast_mul_mem_intAt (ha i)
  refine ⟨∏ p, n p, Finset.prod_pos fun p _ => hn p, fun i => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Nat.cast_mul, mul_assoc]
  exact intAt_natCast_mul _ (hx i)

theorem isSDAt_comap_of (S : HSp D) (v : Pl D) (M N : Mx D S.rank S.rank) (hMN : M * N = 1)
    (hM1 : ∀ i j, M i j - (1 : Mx D S.rank S.rank) i j ∈ idAt D (· = v))
    (hherm : ∀ x y, hermAt S (M *ᵥ x) (M *ᵥ y) = hermAt S x y)
    (Λ : AddSubgroup (Fin S.rank → AE D)) (hΛ : IsSDAt S v Λ) :
    IsSDAt S v (Λ.comap (Matrix.mulVecLin M).toAddMonoidHom) := by
  obtain ⟨hsupp, ⟨m, hm, hmint⟩, hsd⟩ := hΛ
  have hmem : ∀ y, y ∈ Λ.comap (Matrix.mulVecLin M).toAddMonoidHom ↔ M *ᵥ y ∈ Λ := fun y => Iff.rfl
  refine ⟨fun y hy i => ?_, ?_, ?_⟩
  · rw [eq_mulVec_sub M y i]
    exact sub_mem (hsupp _ ((hmem y).1 hy) i) (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hM1 i j))
  · obtain ⟨K, hK, hKint⟩ := exists_common_natCast_mul_mem_intAt
      (fun p : Fin S.rank × Fin S.rank => M p.1 p.2 - (1 : Mx D S.rank S.rank) p.1 p.2) fun p => hM1 p.1 p.2
    refine ⟨m * K, Nat.mul_pos hm hK, fun y hy => (hmem _).2 ?_⟩
    rw [mulVec_natCast_smul M y m K]
    refine hmint _ fun i => ?_
    rw [smul_mulVec_apply M y (K : AE D) i]
    exact intAt_add (intAt_natCast_mul K (hy i)) (intAt_sum _ _ fun j _ => intAt_mul (hKint (i, j)) (hy j))
  · intro y hy
    have key := hsd _ (mulVec_mem_idAt M hy)
    refine ⟨fun h x hx => ?_, fun h => (hmem y).2 (key.2 fun x hx => ?_)⟩
    · rw [← hherm y x]; exact key.1 ((hmem y).1 h) _ ((hmem x).1 hx)
    · have hx' : M *ᵥ (N *ᵥ x) = x := mulVec_mulVec_of_mul_eq_one hMN x
      have h3 := h (N *ᵥ x) ((hmem _).2 (by rw [hx']; exact hx))
      rwa [← hherm, hx'] at h3

theorem isSDAt_comap (D : D7) (S : HSp D) (v : Pl D) (g : GA D S) (hg : g ∈ grpAt S (· = v))
    (Λ : AddSubgroup (Fin S.rank → AE D)) (hΛ : IsSDAt S v Λ) :
    IsSDAt S v (Λ.comap (Matrix.mulVecLin (mt S g)).toAddMonoidHom) :=
  isSDAt_comap_of S v (mt S g) (mt S g⁻¹) (mt_mul_inv S g) ((mem_congGrp_iff S (idAt D (· = v)) g).1 hg)
    (hermAt_mt S g) Λ hΛ

end GlobalTheory.IwaPlace.SdComap

end
end

section

open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd mainDatum)
open GlobalTheory.FinPl.Comm (fpair)

noncomputable section

namespace GlobalTheory.FinPl.Comm

theorem fpair_charInd_dualInd : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n]
    (q : Unif k) (χ : AddChar k Circle) (hχ : HasConductor χ 1) (e : k), (e = 1 ∨ e = -1) →
    ∀ (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (Q : Pair k n),
      fpair χ e μ (charInd (resChar χ hχ q) Q) (dualInd Q.lat) = 0 := by
  intro k _ _ _ _ _ _ n _ _ q χ hχ e he μ _ Q
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  haveI := secondCountable k
  set r := resChar χ hχ q with hr
  obtain ⟨a, ha⟩ : ∃ a, r a ≠ 1 := by
    by_contra h
    push_neg at h
    exact resChar_ne_one hχ q (by ext x; simpa using h x)
  obtain ⟨e₁, he₁⟩ := Q.exists_hasVal_one
  obtain ⟨s, hs⟩ := residue_surjective (R := 𝒪[k]) (-a)
  have hy₀ : Q.HasVal (s • e₁) (-a) := by simpa [hs] using he₁.smul s
  have hI : ∫ y, charInd r Q y ∂μ = 0 := by
    have h1 := integral_add_right_eq_self (μ := μ) (charInd r Q) (s • e₁)
    have h2 : ∀ y, charInd r Q (y + s • e₁) = r a * charInd r Q y := fun y => by
      by_cases hy : y ∈ Q.lat
      · have hyy : y + s • e₁ ∈ Q.lat := add_mem hy hy₀.mem
        rw [charInd, charInd, vecInd, vecInd, if_pos hy, if_pos hyy, ((Pair.hasVal_ev hy).add hy₀).ev_eq,
          neg_add, neg_neg, AddChar.map_add_eq_mul]
        ring
      · have hyy : y + s • e₁ ∉ Q.lat := fun h => hy (by simpa using sub_mem h hy₀.mem)
        rw [charInd, charInd, vecInd, vecInd, if_neg hy, if_neg hyy]
        simp
    simp only [h2] at h1
    rw [integral_const_mul] at h1
    by_contra h0
    exact ha ((mul_eq_right₀ h0).1 h1)
  unfold fpair
  have hF : ∀ η, (∫ y, charInd r Q y * (χ (e * (η ⬝ᵥ y)) : ℂ) ∂μ) * dualInd Q.lat η = 0 := fun η => by
    by_cases hη : GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.InDual Q.lat η
    · rw [dualInd, if_pos hη, mul_one]
      have : (fun y => charInd r Q y * (χ (e * (η ⬝ᵥ y)) : ℂ)) = fun y => charInd r Q y := by
        funext y
        by_cases hy : y ∈ Q.lat
        · have hm : e * (η ⬝ᵥ y) ∈ 𝒪[k] := by
            rcases he with rfl | rfl
            · simpa using hη y hy
            · simpa using hη y hy
          rw [show χ (e * (η ⬝ᵥ y)) = 1 from apply_int_eq_one hχ ⟨_, hm⟩]
          simp
        · rw [charInd, vecInd, if_neg hy]
          simp
      rw [this, hI]
    · rw [dualInd, if_neg hη, mul_zero]
  simp only [hF, integral_zero]

end GlobalTheory.FinPl.Comm

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct

namespace GlobalTheory.FixedUnitNorm

theorem integral_of_trace_norm_integral : ∀ (D : D7) (w : D.host.E) (t n : 𝓞 D.host.F),
    w + D.sp.cm.sig w = algebraMap D.host.F D.host.E t →
    w * D.sp.cm.sig w = algebraMap D.host.F D.host.E n → ∃ x : 𝓞 D.host.E, (x : D.host.E) = w := by
  intro D w t n ht hn
  have hint : ∀ s : 𝓞 D.host.F, IsIntegral ℤ (algebraMap D.host.F D.host.E s) := fun s =>
    (NumberField.RingOfIntegers.isIntegral_coe s).map (IsScalarTower.toAlgHom ℤ D.host.F D.host.E)
  let t' : 𝓞 D.host.E := ⟨algebraMap D.host.F D.host.E t, hint t⟩
  let n' : 𝓞 D.host.E := ⟨algebraMap D.host.F D.host.E n, hint n⟩
  have hw : IsIntegral (𝓞 D.host.E) w := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C t' * Polynomial.X + Polynomial.C n', ?_, ?_⟩
    · monicity!
    · have h1 : algebraMap (𝓞 D.host.E) D.host.E t' = w + D.sp.cm.sig w := ht.symm
      have h2 : algebraMap (𝓞 D.host.E) D.host.E n' = w * D.sp.cm.sig w := hn.symm
      simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
        Polynomial.eval₂_X, Polynomial.eval₂_C, h1, h2]
      ring
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := 𝓞 D.host.E) (K := D.host.E)).mp hw
  exact ⟨y, hy⟩

end GlobalTheory.FixedUnitNorm
end
