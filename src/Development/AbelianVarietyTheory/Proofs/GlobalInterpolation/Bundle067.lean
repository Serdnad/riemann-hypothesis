module

public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle060
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle044
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle027
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle019
public import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.RecursiveLatticeMembership.MemLamOfIff
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValuedAlgebraMapLtOneIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle010

@[expose] public section

section

noncomputable section

namespace GlobalTheory.MomDelta

section Scale

open GlobalTheory.MomOne

def scalePair (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) : PeriodPair :=
  ⟨c * L.ω₁, c * L.ω₂, LinearIndependent.pair_iff.2 fun s t h => by
    have h' : s • L.ω₁ + t • L.ω₂ = 0 := by
      apply mul_left_cancel₀ hc
      simp only [Complex.real_smul] at h ⊢
      linear_combination h
    exact LinearIndependent.pair_iff.1 L.indep s t h'⟩

theorem mem_scalePair (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    c * z ∈ (scalePair L c hc).lattice ↔ z ∈ L.lattice := by
  rw [PeriodPair.mem_lattice, PeriodPair.mem_lattice]
  constructor
  · rintro ⟨m, n, h⟩
    refine ⟨m, n, mul_left_cancel₀ hc ?_⟩
    simp only [scalePair] at h
    linear_combination h
  · rintro ⟨m, n, rfl⟩
    exact ⟨m, n, by simp only [scalePair]; ring⟩

theorem G_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (k : ℕ) :
    L.G k = c ^ k * (scalePair L c hc).G k := by
  let e : (L.lattice : Set ℂ) ≃ ((scalePair L c hc).lattice : Set ℂ) :=
    (Equiv.mulLeft₀ c hc).subtypeEquiv fun w => by
      simpa using (mem_scalePair L c hc w).symm
  have h2 : ∀ P : PeriodPair, P.G k = ∑' w : (P.lattice : Set ℂ), ((w : ℂ) ^ k)⁻¹ := fun _ => rfl
  rw [h2, h2, ← e.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun w => ?_
  have : ((e w : ((scalePair L c hc).lattice : Set ℂ)) : ℂ) = c * w := rfl
  rw [this, mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hc), one_mul]

theorem g₂_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) : (scalePair L c hc).g₂ = L.g₂ / c ^ 4 := by
  simp only [PeriodPair.g₂, G_scale L c hc 4]
  field_simp

theorem g₃_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) : (scalePair L c hc).g₃ = L.g₃ / c ^ 6 := by
  simp only [PeriodPair.g₃, G_scale L c hc 6]
  field_simp

variable {q : ℕ} [Fact q.Prime]

theorem ok_scale (M : Mdl q) (hM : M.Ok) (c : ℂ) (hc : c ≠ 0) :
    (Mdl.mk M.ι (scalePair M.L c hc) (M.c / c) M.W).Ok := by
  obtain ⟨h0, h1, h2, h3, h4, h6, hΔ, hg2, hg3⟩ := hM
  refine ⟨div_ne_zero h0 hc, h1, h2, h3, h4, h6, hΔ, ?_, ?_⟩
  · have : (scalePair M.L c hc).g₂ / (M.c / c) ^ 4 = M.L.g₂ / M.c ^ 4 := by
      rw [g₂_scale]; field_simp
    show M.W.c₄ / 12 = M.ι _
    rw [this]; exact hg2
  · have : (scalePair M.L c hc).g₃ / (M.c / c) ^ 6 = M.L.g₃ / M.c ^ 6 := by
      rw [g₃_scale]; field_simp
    show M.W.c₆ / 216 = M.ι _
    rw [this]; exact hg3

theorem norm_disc_ring (ι : ℂ ≃+* ℂ_[q]) {d : ℕ} (hd : d.Prime) (h16 : d % 16 = 7) (L' : PeriodPair) (N : ℕ)
    (hq : q ≠ 2) (hN : Nat.Coprime N (2 * q)) (hN0 : N ≠ 0)
    (h1 : ∀ z, InOK d z → (N : ℂ) * z ∈ L'.lattice) (h2 : ∀ x ∈ L'.lattice, InOK d x) :
    ‖ι (L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2)‖ = ‖ι (discr d)‖ := by
  have hc : (N : ℂ) ≠ 0 := by exact_mod_cast hN0
  have hL := Basic.isOK_okPair d hd.pos
  obtain ⟨M, hMι, hML, hOk, -⟩ := exists_model d q ι _ hd h16 hL
  have hIs : IsOK d M.L := hML ▸ hL
  subst hMι
  have hk := GlobalTheory.T.norm_discriminant_superlattice_odd_index_eq q (Mdl.mk M.ι (scalePair M.L N hc) (M.c / N) M.W) L' N hq (ok_scale M hOk N hc) hN
    (fun z hz => by
      have e : z = (N : ℂ) * (z / N) := by field_simp
      have hz' : (N : ℂ) * (z / N) ∈ (scalePair M.L N hc).lattice := by rw [← e]; exact hz
      rw [e]
      exact h1 _ ((hIs _).1 ((mem_scalePair M.L N hc _).1 hz')))
    (fun x hx => (mem_scalePair M.L N hc x).2 ((hIs x).2 (h2 x hx)))
  have e : (scalePair M.L N hc).g₂ ^ 3 - 27 * (scalePair M.L N hc).g₃ ^ 2
      = (M.L.g₂ ^ 3 - 27 * M.L.g₃ ^ 2) / (N : ℂ) ^ 12 := by
    rw [g₂_scale, g₃_scale]; field_simp
  have hnorm : ‖M.ι (N : ℂ)‖ = 1 := by
    rw [map_natCast]
    exact Basic.norm_nat_eq_one (Nat.Coprime.symm (Nat.coprime_mul_iff_right.1 hN).2)
  refine hk.trans ?_
  show ‖M.ι ((scalePair M.L N hc).g₂ ^ 3 - 27 * (scalePair M.L N hc).g₃ ^ 2)‖ = _
  rw [e, map_div₀, norm_div, map_pow, norm_pow, hnorm, one_pow, div_one, (Basic.discr_eq hIs).1]

end Scale

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

theorem delta_ratio : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ δ₀ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    δ₀ ^ 12 = GlobalTheory.MomOne.discr D.host.d → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → Nat.Coprime (Ideal.absNorm cc) q →
    δ / δ₀ ∈ Qbar ∧ ∀ ι : ℂ ≃+* ℂ_[q], ‖ι (δ / δ₀)‖ = 1 := by
  intro D cc δ δ₀ hcc hδ hδ₀ q _ hq hNq
  obtain ⟨hdp, h16, hOK, -, hlam⟩ := GlobalTheory.T.cmBaseField_integers_and_curveIdeal_facts D
  obtain ⟨hne, hcop⟩ := hcc
  have hN0 : Ideal.absNorm cc ≠ 0 := fun h => hne (Ideal.absNorm_eq_zero_iff.1 h)
  have hN2 : Nat.Coprime (Ideal.absNorm cc) (2 * q) :=
    Nat.coprime_mul_iff_right.2 ⟨(Nat.coprime_mul_iff_right.1 hcop).1, hNq⟩
  obtain ⟨L', hL'⟩ := Formalism.L2.PairingIndexBounds.Rec.exists_pp D cc hne
  have hmem : ((Ideal.absNorm cc : ℕ) : 𝓞 D.host.K) ∈ cc := Ideal.absNorm_mem cc
  have hΔ : Formalism.MainNotions.TaylorLogMetric.discr (Formalism.MainNotions.TaylorLogMetric.lamOf D cc 1) = L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2 := by
    have h4 := Formalism.L2.PairingIndexBounds.Rec.eisG_eq_G _ L' hL' 2 (by norm_num)
    have h6 := Formalism.L2.PairingIndexBounds.Rec.eisG_eq_G _ L' hL' 3 (by norm_num)
    unfold Formalism.MainNotions.TaylorLogMetric.discr Formalism.MainNotions.TaylorLogMetric.g2 Formalism.MainNotions.TaylorLogMetric.g3
    rw [h4, h6]
    simp [PeriodPair.g₂, PeriodPair.g₃]
  have h1 : ∀ z, GlobalTheory.MomOne.InOK D.host.d z → ((Ideal.absNorm cc : ℕ) : ℂ) * z ∈ L'.lattice := by
    intro z hz
    obtain ⟨x, rfl⟩ := (hOK z).1 hz
    refine (hL' _).1 ((hlam cc 1 hne).2 _ |>.2 ⟨((Ideal.absNorm cc : ℕ) : 𝓞 D.host.K) * x, cc.mul_mem_right x hmem, ?_⟩)
    simp
  have h2 : ∀ x ∈ L'.lattice, GlobalTheory.MomOne.InOK D.host.d x := by
    intro x hx
    obtain ⟨c, -, rfl⟩ := ((hlam cc 1 hne).2 x).1 ((hL' x).2 hx)
    exact (hOK _).2 ⟨c, by simp⟩
  have hne₀ : GlobalTheory.MomOne.discr D.host.d ≠ 0 :=
    (GlobalTheory.MomOne.Basic.discr_eq (GlobalTheory.MomOne.Basic.isOK_okPair _ hdp.pos)).2
  have hδ₀0 : δ₀ ≠ 0 := by
    rintro rfl
    exact hne₀ (by rw [← hδ₀]; simp)
  have key : ∀ ι : ℂ ≃+* ℂ_[q], ‖ι (δ / δ₀)‖ = 1 := by
    intro ι
    have h := norm_disc_ring ι hdp h16 L' _ hq hN2 hN0 h1 h2
    have hδ' : δ ^ 12 = L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2 := by rw [← hΔ]; exact hδ
    rw [← hδ', ← hδ₀, map_pow, map_pow, norm_pow, norm_pow] at h
    have hι₀ : ‖ι δ₀‖ ≠ 0 := by simpa using hδ₀0
    have h12 : ‖ι (δ / δ₀)‖ ^ 12 = 1 := by
      rw [map_div₀, norm_div, div_pow, h, div_self (pow_ne_zero _ hι₀)]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h12
  obtain ⟨ι⟩ := GlobalTheory.MomOne.Basic.nonempty_iso q
  exact ⟨GlobalTheory.MomOne.mem_algebraicClosure_of_norm_le q ι _ 1 fun ι' _ => (key ι').le, key⟩

end GlobalTheory.MomDelta
end
end

section

open MvPolynomial NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance GlobalTheory.BranchFormula

noncomputable section

namespace GlobalTheory.XiTopCoef

section Top

variable {σ A : Type} [CommRing A] (w : σ → ℕ)

def TopTerm (f : MvPolynomial σ A) (d : σ →₀ ℕ) (c : A) : Prop :=
  AddMonoidAlgebra.coeff f d = c ∧ ∀ m ∈ f.support, m = d ∨ Finsupp.weight w m < Finsupp.weight w d

variable {w}

theorem TopTerm.C (c : A) : TopTerm w (C c : MvPolynomial σ A) 0 c := by
  classical
  refine ⟨by simp, fun m hm => Or.inl ?_⟩
  by_contra h
  rw [mem_support_iff, coeff_C, if_neg (Ne.symm h)] at hm
  exact hm rfl

theorem TopTerm.mul {f g : MvPolynomial σ A} {d e : σ →₀ ℕ} {c c' : A} (hf : TopTerm w f d c) (hg : TopTerm w g e c') :
    TopTerm w (f * g) (d + e) (c * c') := by
  classical
  constructor
  · rw [coeff_mul, Finset.sum_eq_single (d, e), hf.1, hg.1]
    · rintro ⟨x, y⟩ hxy hne
      by_contra h0
      have hx := hf.2 x (mem_support_iff.2 (left_ne_zero_of_mul h0))
      have hy := hg.2 y (mem_support_iff.2 (right_ne_zero_of_mul h0))
      have hs : x + y = d + e := by simpa using hxy
      have hw := congrArg (Finsupp.weight w) hs
      rw [map_add (f := _), map_add (f := _)] at hw
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact hne rfl
      all_goals omega
    · intro h
      exact absurd (by simp) h
  · intro m hm
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.1 (support_mul f g hm)
    rw [map_add (f := _), map_add (f := _)]
    rcases hf.2 x hx with rfl | hx <;> rcases hg.2 y hy with rfl | hy
    · exact Or.inl rfl
    all_goals right; omega

theorem TopTerm.pow {f : MvPolynomial σ A} {d : σ →₀ ℕ} {c : A} (hf : TopTerm w f d c) (k : ℕ) :
    TopTerm w (f ^ k) (k • d) (c ^ k) := by
  induction k with
  | zero => simpa using TopTerm.C (w := w) (1 : A)
  | succ k ih => rw [pow_succ, pow_succ, succ_nsmul]; exact ih.mul hf

theorem TopTerm.prod {ι : Type} (s : Finset ι) {f : ι → MvPolynomial σ A} {d : ι → σ →₀ ℕ} {c : ι → A}
    (h : ∀ i, TopTerm w (f i) (d i) (c i)) : TopTerm w (∏ i ∈ s, f i) (∑ i ∈ s, d i) (∏ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using TopTerm.C (w := w) (1 : A)
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]; exact (h a).mul ih

theorem TopTerm.linear {k : ℕ} (v : Fin (k + 1) → σ) (c : Fin (k + 1) → A)
    (hv : ∀ q : Fin k, w (v q.castSucc) < w (v (Fin.last k))) :
    TopTerm w (∑ q, X (v q) * MvPolynomial.C (c q)) (Finsupp.single (v (Fin.last k)) 1) (c (Fin.last k)) := by
  classical
  have e : ∀ q, (X (v q) * MvPolynomial.C (c q) : MvPolynomial σ A) = monomial (Finsupp.single (v q) 1) (c q) := by
    intro q
    rw [mul_comm, C_mul_X_eq_monomial]
  simp only [e]
  constructor
  · rw [coeff_sum, Fin.sum_univ_castSucc, Finset.sum_eq_zero, zero_add, coeff_monomial, if_pos rfl]
    intro q _
    rw [coeff_monomial, if_neg]
    intro h
    have h1 := Finsupp.single_left_injective one_ne_zero h
    have := hv q
    rw [h1] at this
    exact lt_irrefl _ this
  · intro m hm
    obtain ⟨q, -, hq⟩ := Finset.mem_biUnion.1 (support_sum hm)
    have hq' := Finset.mem_singleton.1 (support_monomial_subset hq)
    subst hq'
    induction q using Fin.lastCases with
    | last => exact Or.inl rfl
    | cast q => right; simpa [Finsupp.weight_single] using hv q

end Top

variable (K : Type) [Field K] {N n : ℕ} (hN : N = n + 1)

def lp (n k : ℕ) : Pol K Unit n :=
  if h : k ≤ n then rename (fun v : Fin n × Fin n => (((), v) : Unit × Fin n × Fin n)) (Formalism.GradedWeylDivisibility.lpMinor K k h h) else 1

theorem lp_eq {k : ℕ} (h : k ≤ n) :
    lp K n k = (Matrix.of fun p q : Fin k => (X ((), Fin.castLE h p, Fin.castLE h q) : Pol K Unit n)).det := by
  rw [lp, dif_pos h, Formalism.GradedWeylDivisibility.lpMinor, AlgHom.map_det]
  congr 1
  ext p q
  simp

theorem lp_zero : lp K n 0 = 1 := by
  rw [lp_eq K (Nat.zero_le n), Matrix.det_isEmpty]

theorem split_lp {k : ℕ} (h : k ≤ n) (h' h'' : k ≤ N) :
    splitLast K Unit hN (rename (fun v : Fin N × Fin N => (((), v) : Unit × Fin N × Fin N)) (Formalism.GradedWeylDivisibility.lpMinor K k h' h'')) =
      C (lp K n k) := by
  rw [lp_eq K h, Formalism.GradedWeylDivisibility.lpMinor, AlgHom.map_det, AlgHom.map_det, RingHom.map_det]
  congr 1
  ext1 p q
  simp only [AlgHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rename_X]
  exact splitLast_X_up K Unit hN () (Fin.castLE h p) (Fin.castLE h q)

theorem weightedLeadingTerm_split_zMinor (i : Fin n) :
    TopTerm (fun p : Unit × Fin n => p.2.val)
      (splitLast K Unit hN (rename (fun v : Fin N × Fin N => (((), v) : Unit × Fin N × Fin N)) (Br.zMinor K hN i)))
      (Finsupp.single ((), i) 1) (lp K n i) := by
  have hi : i.val + 1 ≤ n := i.2
  have hi' : i.val ≤ n := i.2.le
  have key := TopTerm.linear (w := fun p : Unit × Fin n => p.2.val) (k := i.val) (fun q => ((), Fin.castLE hi q))
    (fun q => (-1) ^ (i.val + q.val) * (Matrix.of fun p r : Fin i.val =>
      (X ((), Fin.castLE hi' p, Fin.castLE hi (q.succAbove r)) : Pol K Unit n)).det) (fun q => by simp)
  convert key using 1
  · rw [Br.zMinor, Formalism.GradedWeylDivisibility.initMinor, AlgHom.map_det, AlgHom.map_det, Matrix.det_succ_row _ (Fin.last i.val)]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [map_mul, RingHom.map_det, map_pow, map_neg, map_one, mul_left_comm, ← mul_assoc]
    congr 2
    · simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rename_X, Fin.val_last, lt_irrefl, dif_neg,
        not_false_eq_true]
      exact splitLast_X_lastRow K Unit hN () (Fin.castLE hi q)
    · ext1 p r
      simp only [AlgHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rename_X,
        Matrix.submatrix_apply, Fin.succAbove_last, Fin.val_castSucc, p.2, dif_pos]
      exact splitLast_X_up K Unit hN () (Fin.castLE hi' p) (Fin.castLE hi (q.succAbove r))
  · rfl
  · rw [lp_eq K hi', Fin.val_last, ← two_mul, pow_mul]
    simp only [Fin.succAbove_last, even_two, Even.neg_pow, one_pow, one_mul]
    rfl

theorem prod_shift {M : Type} [CommMonoid M] (P : ℕ → M) (h0 : P 0 = 1) (b : Fin n → ℕ) :
    ∏ i : Fin n, P i ^ b i = ∏ i : Fin n, P (i + 1) ^ Formalism.GradedWeylDivisibility.nuNext b i := by
  cases n with
  | zero => simp
  | succ m =>
    rw [Fin.prod_univ_succ, Fin.prod_univ_castSucc]
    simp [h0, Formalism.GradedWeylDivisibility.nuNext]
    rfl

theorem exp_eq (lam : DomWeight N) (sg : DomWeight n) (hI : Br.Interlace hN lam sg) (hS : Br.SameShift lam sg) (i : Fin n) :
    (Br.aBr hN lam sg i).toNat + Formalism.GradedWeylDivisibility.nuNext (fun s => (Br.bBr hN lam sg s).toNat) i =
      sg.natW i - Formalism.GradedWeylDivisibility.nuNext sg.natW i := by
  subst hN
  have hn : 0 < n := i.pos
  have h1 := (hI i).1
  have e1 : sg.detShift = sg.w ⟨n - 1, by omega⟩ := dif_pos hn
  have e2 : lam.detShift = lam.w ⟨n, by omega⟩ := dif_pos (Nat.succ_pos n)
  unfold Br.SameShift at hS
  unfold Formalism.GradedWeylDivisibility.nuNext
  split_ifs with h
  · have h2 := (hI ⟨i.val + 1, h⟩).2
    have h3 : sg.w ⟨n - 1, by omega⟩ ≤ sg.w ⟨i.val + 1, h⟩ := sg.anti (by simp only [Fin.le_def]; omega)
    simp only [Br.aBr, Br.bBr, Br.iS, Br.iC, DomWeight.natW] at *
    omega
  · have hi : i = ⟨n - 1, by omega⟩ := Fin.ext (by have := i.2; simp only; omega)
    have e3 : lam.w (Br.iS rfl i) = lam.w ⟨n, by omega⟩ := by
      congr 1
      exact Fin.ext (by have := i.2; simp only [Br.iS]; omega)
    rw [← hi] at e1
    simp only [Br.aBr, DomWeight.natW] at *
    omega

theorem coefLast_xi : ∀ (K : Type) [Field K] (N n : ℕ) (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n), Br.Interlace hN lam sg → Br.SameShift lam sg → Br.coefLast (K := K) hN (Br.bExp hN (fun _ : Unit => lam) (fun _ : Unit => sg)) (rename (fun v : Fin N × Fin N => (((), v) : Unit × Fin N × Fin N)) (Br.xiBr K hN lam sg)) = rename (fun v : Fin n × Fin n => (((), v) : Unit × Fin n × Fin n)) (extremal K n sg) := by
  intro K _ N n hN lam sg hI hS
  have key := (TopTerm.prod (w := fun p : Unit × Fin n => p.2.val) Finset.univ fun i : Fin n =>
    ((TopTerm.C (lp K n (i.val + 1))).pow (Br.aBr hN lam sg i).toNat).mul
      ((weightedLeadingTerm_split_zMinor K hN i).pow (Br.bBr hN lam sg i).toNat)).1
  rw [coefLast_eq_coeff, Br.xiBr, map_prod, map_prod]
  simp only [map_mul, map_pow]
  have hsp : ∀ i : Fin n, _ := fun i : Fin n =>
    split_lp K hN (k := i.val + 1) i.2 (by have := i.2; omega) (by have := i.2; omega)
  simp only [hsp]
  refine Eq.trans (congrArg (fun e => AddMonoidAlgebra.coeff _ e) ?_) (key.trans ?_)
  · ext ⟨u, s⟩
    simp [Br.bExp, Finsupp.finsetSum_apply, Finsupp.single_apply]
  · rw [Finset.prod_mul_distrib, prod_shift (lp K n) (lp_zero K) fun s => (Br.bBr hN lam sg s).toNat,
      ← Finset.prod_mul_distrib, extremal, Formalism.GradedWeylDivisibility.hw, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← pow_add, exp_eq hN lam sg hI hS, map_pow, lp, dif_pos (show i.val + 1 ≤ n from i.2)]

end GlobalTheory.XiTopCoef
end
end

section

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct

namespace GlobalTheory.OverCompare.StabPart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)}
  {s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F} {k : ℕ}

theorem prP_symm (a b : v.adicCompletion F) : prP s (s.symm (a, b)) = a := by
  show (s (s.symm (a, b))).1 = a
  rw [s.apply_symm_apply]

theorem prPbar_symm (a b : v.adicCompletion F) : prPbar s (s.symm (a, b)) = b := by
  show (s (s.symm (a, b))).2 = b
  rw [s.apply_symm_apply]

theorem map_mulVec_bc {A K : Type} [CommRing A] [CommRing K] (p : A →+* K) (g : GL (Fin k) A)
    (x : Fin k → A) :
    (fun i => p (((g : Matrix (Fin k) (Fin k) A) *ᵥ x) i)) =
      ((bc p g : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) *ᵥ fun j => p (x j) :=
  funext fun _ => RingHom.map_mulVec p _ _ _

theorem mem_iff (hs : IsSplitting σ v s)
    (Λ : Submodule (intV E v) (Fin k → E ⊗[F] v.adicCompletion F))
    (x : Fin k → E ⊗[F] v.adicCompletion F) :
    x ∈ Λ ↔ (fun i => prP s (x i)) ∈ partOf (prP s) Λ ∧
      (fun i => prPbar s (x i)) ∈ partOf (prPbar s) Λ := by
  rw [mem_partOf _ (sur_prP hs), mem_partOf _ (sur_prPbar hs)]
  refine ⟨fun hx => ⟨⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩⟩, ?_⟩
  rintro ⟨⟨a, ha, ha'⟩, ⟨b, hb, hb'⟩⟩
  have h1 : s.symm (1, 0) ∈ intV E v :=
    (hs.2.2 _).2 (by rw [s.apply_symm_apply]; exact ⟨one_mem _, zero_mem _⟩)
  have h2 : s.symm (0, 1) ∈ intV E v :=
    (hs.2.2 _).2 (by rw [s.apply_symm_apply]; exact ⟨zero_mem _, one_mem _⟩)
  have hx : x = (⟨_, h1⟩ : intV E v) • a + (⟨_, h2⟩ : intV E v) • b := by
    funext i
    show x i = s.symm (1, 0) * a i + s.symm (0, 1) * b i
    apply s.injective
    have e1 : (s (a i)).1 = (s (x i)).1 := congrFun ha' i
    have e2 : (s (b i)).2 = (s (x i)).2 := congrFun hb' i
    rw [map_add (f := _), map_mul, map_mul, s.apply_symm_apply, s.apply_symm_apply]
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_add, Prod.fst_mul, Prod.fst_mul, one_mul, zero_mul, add_zero, e1]
    · rw [Prod.snd_add, Prod.snd_mul, Prod.snd_mul, one_mul, zero_mul, zero_add, e2]
  rw [hx]
  exact Λ.add_mem (Λ.smul_mem _ ha) (Λ.smul_mem _ hb)

theorem mulVec_mem_iff (hs : IsSplitting σ v s)
    (Λ : Submodule (intV E v) (Fin k → E ⊗[F] v.adicCompletion F))
    (g : GL (Fin k) (E ⊗[F] v.adicCompletion F)) (y z : Fin k → v.adicCompletion F) :
    (g : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) *ᵥ (fun i => s.symm (y i, z i)) ∈ Λ ↔
      ((bc (prP s) g : GL (Fin k) _) : Matrix (Fin k) (Fin k) _) *ᵥ y ∈ partOf (prP s) Λ ∧
      ((bc (prPbar s) g : GL (Fin k) _) : Matrix (Fin k) (Fin k) _) *ᵥ z ∈ partOf (prPbar s) Λ := by
  rw [mem_iff hs, map_mulVec_bc, map_mulVec_bc]
  simp only [prP_symm, prPbar_symm]

theorem symm_mem_iff (hs : IsSplitting σ v s)
    (Λ : Submodule (intV E v) (Fin k → E ⊗[F] v.adicCompletion F))
    (y z : Fin k → v.adicCompletion F) :
    (fun i => s.symm (y i, z i)) ∈ Λ ↔ y ∈ partOf (prP s) Λ ∧ z ∈ partOf (prPbar s) Λ := by
  rw [mem_iff hs]
  simp only [prP_symm, prPbar_symm]

theorem stabPart : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), IsSplitting σ v s → ∀ (k : ℕ) (Λ : Submodule (intV E v) (Fin k → E ⊗[F] v.adicCompletion F)), (∀ x, x ∈ Λ ↔ (fun i => prP s (x i)) ∈ partOf (prP s) Λ ∧ (fun i => prPbar s (x i)) ∈ partOf (prPbar s) Λ) ∧ (∀ g : GL (Fin k) (E ⊗[F] v.adicCompletion F), g ∈ stabGL Λ ↔ bc (prP s) g ∈ stabGL (partOf (prP s) Λ) ∧ bc (prPbar s) g ∈ stabGL (partOf (prPbar s) Λ)) ∧ ∀ B : GL (Fin k) (E ⊗[F] v.adicCompletion F), (∀ y : Fin k → E ⊗[F] v.adicCompletion F, (B : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) *ᵥ y ∈ Λ ↔ ∀ i, y i ∈ intV E v) → GlobalTheory.OverCompare.IsFrame (partOf (prP s) Λ) (bc (prP s) B) ∧ GlobalTheory.OverCompare.IsFrame (partOf (prPbar s) Λ) (bc (prPbar s) B) := by
  intro F E _ _ _ _ _ σ v s hs k Λ
  refine ⟨mem_iff hs Λ, fun g => ⟨fun hg => ⟨fun y => ?_, fun z => ?_⟩, fun hg x => ?_⟩,
    fun B hB => ⟨fun y => ?_, fun z => ?_⟩⟩
  · have h : _ ↔ _ := hg (fun i => s.symm (y i, (0 : Fin k → v.adicCompletion F) i))
    rw [mulVec_mem_iff hs, symm_mem_iff hs, Matrix.mulVec_zero] at h
    simpa only [zero_mem, and_true] using h
  · have h : _ ↔ _ := hg (fun i => s.symm ((0 : Fin k → v.adicCompletion F) i, z i))
    rw [mulVec_mem_iff hs, symm_mem_iff hs, Matrix.mulVec_zero] at h
    simpa only [zero_mem, true_and] using h
  · rw [mem_iff hs Λ x, mem_iff hs Λ (_ *ᵥ x), map_mulVec_bc, map_mulVec_bc]
    exact and_congr (hg.1 _) (hg.2 _)
  · have h := hB (fun i => s.symm (y i, (0 : Fin k → v.adicCompletion F) i))
    rw [mulVec_mem_iff hs, Matrix.mulVec_zero] at h
    simpa only [zero_mem, and_true, hs.2.2, RingEquiv.apply_symm_apply, Pi.zero_apply] using h
  · have h := hB (fun i => s.symm ((0 : Fin k → v.adicCompletion F) i, z i))
    rw [mulVec_mem_iff hs, Matrix.mulVec_zero] at h
    simpa only [zero_mem, true_and, hs.2.2, RingEquiv.apply_symm_apply, Pi.zero_apply] using h

end GlobalTheory.OverCompare.StabPart
end
