module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Mathlib.Analysis.Normed.Ring.Basic

@[expose] public section

section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section

variable {R R' : Type} [CommRing R] [CommRing R'] {j : R →+* R'}

private theorem adj_map (j : R →+* R') (X : M4 R) : adj (X.map j) = (adj X).map j := by
  ext i i'
  simp only [adj_apply, Matrix.map_apply, map_zsmul]

private theorem conj_map (j : R →+* R') (n X : M4 R) :
    adj (n.map j) * X.map j * n.map j = (adj n * X * n).map j := by
  rw [adj_map, ← Matrix.map_mul, ← Matrix.map_mul]

private theorem map_inj (hj : Function.Injective j) {X Y : M4 R} : X.map j = Y.map j ↔ X = Y :=
  (Matrix.map_injective hj).eq_iff

private theorem isGSp_iff (hj : Function.Injective j) (ν : R) (X : M4 R) : IsGSp (j ν) (X.map j) ↔ IsGSp ν X := by
  have h : (j ν) • (1 : M4 R') = (ν • (1 : M4 R)).map j := by
    ext i i'
    by_cases h : i = i' <;> simp [Matrix.one_apply, h]
  unfold IsGSp
  rw [adj_map, ← Matrix.map_mul, h, map_inj hj]

private theorem one_iff (hj : Function.Injective j) (X : M4 R) : X.map j = 1 ↔ X = 1 := by
  rw [← Matrix.map_one (⇑j) (map_zero j) (map_one j), map_inj hj]

private theorem diag_iff (hj : Function.Injective j) (X : M4 R) : (X.map j).IsDiag ↔ X.IsDiag := by
  simp only [Matrix.IsDiag, Matrix.map_apply, map_eq_zero_iff j hj]

private theorem up_iff (hj : Function.Injective j) (X : M4 R) : IsUp (X.map j) ↔ IsUp X := by
  simp only [IsUp, Matrix.map_apply, map_eq_zero_iff j hj]

private theorem low_iff (hj : Function.Injective j) (X : M4 R) : IsLow (X.map j) ↔ IsLow X := by
  have h := isGSp_iff hj 1 X
  rw [map_one] at h
  simp only [IsLow, h, Matrix.map_apply, map_eq_zero_iff j hj, map_eq_one_iff j hj]

private theorem suppM_iff (hj : Function.Injective j) (S : Finset (ℤ × ℤ)) (X : M4 R) :
    SuppM S (X.map j) ↔ SuppM S X := by
  simp only [SuppM, Matrix.map_apply, map_eq_zero_iff j hj]

variable {ι Γ : Type} [Group Γ]

private theorem r_map (j : R →+* R') (c : PD ι Γ R) (g : Γ) : (c.map j).r g = (c.r g).map j := rfl

private theorem n_map (j : R →+* R') (c : PD ι Γ R) (v : ι) : (c.map j).n v = (c.n v).map j := rfl

private theorem psi_map (j : R →+* R') (c : PD ι Γ R) (v : ι) (i : Fin 4) (s : Γ) :
    (c.map j).ψ v i s = j (c.ψ v i s) := by
  simp only [PD.ψ, r_map, n_map, conj_map, Matrix.map_apply]

private theorem supp_iff (hj : Function.Injective j) (S : Finset (ℤ × ℤ)) (c : PD ι Γ R) :
    Supp S (c.map j).r ↔ Supp S c.r := by
  simp only [Supp, r_map, suppM_iff hj]

private theorem ent_iff (hj : Function.Injective j) (c : PD ι Γ R) (w : ℤ × ℤ) :
    Ent (c.map j).r w ↔ Ent c.r w := by
  simp only [Ent, r_map, Matrix.map_apply, ne_eq, map_eq_zero_iff j hj]

private theorem adic_bot {X : Type} [TopologicalSpace X] (f : X → R) : AdicCont ⊥ f ↔ IsLocallyConstant f := by
  refine ⟨fun h => ?_, fun h N => h.comp _⟩
  refine IsLocallyConstant.desc f (Ideal.Quotient.mk ((⊥ : Ideal R) ^ 1)) (h 1) ?_
  rw [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker, pow_one]

private theorem cont_iff [TopologicalSpace Γ] (hj : Function.Injective j) (c : PD ι Γ R) :
    (c.map j).Cont ⊥ ↔ c.Cont ⊥ := by
  simp only [PD.Cont, adic_bot, r_map, Matrix.map_apply]
  exact forall_congr' fun a => forall_congr' fun b =>
    ⟨fun h => IsLocallyConstant.desc _ j h hj, fun h => h.comp j⟩

end

theorem UpperTheory.V.Ws.chainMap :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (Φ : Fr O Γ) {k k' : Type} [Field k] [Field k'] (a : O →+* k) (j : k →+* k') (c : PD Φ.ι Γ k),
      (Φ.IsRes (j.comp a) (c.map j) ↔ Φ.IsRes a c) ∧ (Φ.Good (j.comp a) (c.map j) ↔ Φ.Good a c) ∧ Function.Injective fun c : PD Φ.ι Γ k => c.map j := by
  intro O Γ _ _ _ _ _ _ Φ k k' _ _ a j c
  have hj : Function.Injective j := j.injective
  have e1 : ∀ g, IsGSp ((j.comp a) (Φ.ν g : O)) ((c.map j).r g) ↔ IsGSp (a (Φ.ν g)) (c.r g) :=
    fun g => by rw [RingHom.comp_apply, r_map, isGSp_iff hj]
  have e2 : ∀ g, (c.map j).r g = 1 ↔ c.r g = 1 := fun g => by rw [r_map, one_iff hj]
  have e3 : Matrix.IsDiag ((c.map j).r Φ.g0) ↔ Matrix.IsDiag (c.r Φ.g0) := by rw [r_map, diag_iff hj]
  have e4 : ∀ v, IsLow ((c.map j).n v) ↔ IsLow (c.n v) := fun v => by rw [n_map, low_iff hj]
  have e5 : ∀ v s, IsUp (adj ((c.map j).n v) * (c.map j).r s * (c.map j).n v) ↔
      IsUp (adj (c.n v) * c.r s * c.n v) :=
    fun v s => by rw [n_map, r_map, conj_map, up_iff hj]
  have e6 : ∀ v i s, (c.map j).ψ v i s = 1 ↔ c.ψ v i s = 1 :=
    fun v i s => by rw [psi_map, map_eq_one_iff j hj]
  have e7 : ∀ g i, (c.map j).r g i i = (j.comp a) (Φ.χ i g : O) ↔ c.r g i i = a (Φ.χ i g) :=
    fun g i => by rw [r_map, Matrix.map_apply, RingHom.comp_apply, hj.eq_iff]
  have e8 : ∀ v i s, (c.map j).ψ v i s = (j.comp a) (Φ.χ i s : O) ↔ c.ψ v i s = a (Φ.χ i s) :=
    fun v i s => by rw [psi_map, RingHom.comp_apply, hj.eq_iff]
  have e9 : ((Supp nP (c.map j).r ∧ ∀ v, SuppM qQ ((c.map j).n v)) ∨ Supp nM (c.map j).r) ↔
      ((Supp nP c.r ∧ ∀ v, SuppM qQ (c.n v)) ∨ Supp nM c.r) := by
    simp only [supp_iff hj, n_map, suppM_iff hj]
  have e10 : Fr.InV (Φ := Φ) (c.map j) ↔ Fr.InV (Φ := Φ) c := by
    simp only [Fr.InV, supp_iff hj, n_map, suppM_iff hj, Matrix.map_apply, ne_eq, map_eq_zero_iff j hj]
  have hP : Φ.IsPair (j.comp a) (c.map j) ↔ Φ.IsPair a c :=
    ⟨fun h => ⟨fun g => (e1 g).1 (h.mult g), fun g hg => (e2 g).1 (h.kill g hg), e3.1 h.nrm,
        fun v => (e4 v).1 (h.low v), fun v s hs => (e5 v s).1 (h.flag v s hs),
        fun v s hs i => (e6 v i s).1 (h.mu v s hs i)⟩,
      fun h => ⟨fun g => (e1 g).2 (h.mult g), fun g hg => (e2 g).2 (h.kill g hg), e3.2 h.nrm,
        fun v => (e4 v).2 (h.low v), fun v s hs => (e5 v s).2 (h.flag v s hs),
        fun v s hs i => (e6 v i s).2 (h.mu v s hs i)⟩⟩
  have hR : Φ.Res (j.comp a) (c.map j) ↔ Φ.Res a c :=
    ⟨fun h => ⟨fun g i => (e7 g i).1 (h.diag g i), fun v s hs i => (e8 v i s).1 (h.char v s hs i),
        e9.1 h.shape⟩,
      fun h => ⟨fun g i => (e7 g i).2 (h.diag g i), fun v s hs i => (e8 v i s).2 (h.char v s hs i),
        e9.2 h.shape⟩⟩
  refine ⟨⟨fun h => ⟨hP.1 h.pair, hR.1 h.res, (cont_iff hj c).1 h.cont⟩,
    fun h => ⟨hP.2 h.pair, hR.2 h.res, (cont_iff hj c).2 h.cont⟩⟩, ?_, ?_⟩
  · simp only [Fr.Good, ent_iff hj, e10, RingHom.comp_apply, ne_eq, map_eq_one_iff j hj]
  · intro x y h
    apply PD.ext
    · ext g : 1
      exact (map_inj hj).1 (congrArg (fun e : PD Φ.ι Γ k' => e.r g) h)
    · funext v
      exact (map_inj hj).1 (congrArg (fun e : PD Φ.ι Γ k' => e.n v) h)
end

section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section SlopeTestRemainingChoices

variable {R : Type} [CommRing R]

private theorem bd_up_mul {Y Z : M4 R} (hY : IsUp Y) (hZ : IsUp Z) : IsUp (Y * Z) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases h : k < i
  · rw [hY i k h, zero_mul]
  · rw [hZ k j (lt_of_lt_of_le hij (not_lt.mp h)), mul_zero]

private theorem bd_up_diag {Y Z : M4 R} (hY : IsUp Y) (hZ : IsUp Z) (i : Fin 4) : (Y * Z) i i = Y i i * Z i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hY i k h, zero_mul]
  · rw [hZ k i h, mul_zero]

private theorem bd_conj_mul {u v : M4 R} (h : u * v = 1) (Y Z : M4 R) :
    v * (Y * Z) * u = (v * Y * u) * (v * Z * u) := by
  have : (v * Y * u) * (v * Z * u) = v * Y * (u * v) * Z * u := by simp only [Matrix.mul_assoc]
  rw [this, h]; simp only [Matrix.mul_assoc, Matrix.one_mul]

private theorem bd_trace {u v : M4 R} (h : u * v = 1) (Y : M4 R) : (v * Y * u).trace = Y.trace := by
  rw [Matrix.trace_mul_cycle, h, Matrix.one_mul]

private theorem bd_key {u v N X : M4 R} (h : u * v = 1) (hN : IsUp (v * N * u)) (hX : IsUp (v * X * u)) :
    (N * X).trace ^ 2 - ((N * X) * (N * X)).trace =
      (∑ i, (v * N * u) i i * (v * X * u) i i) ^ 2 - ∑ i, ((v * N * u) i i * (v * X * u) i i) ^ 2 := by
  have hU := bd_up_mul hN hX
  rw [← bd_trace h (N * X), ← bd_trace h ((N * X) * (N * X)), bd_conj_mul h (N * X), bd_conj_mul h N X]
  simp only [Matrix.trace, Matrix.diag_apply, bd_up_diag hU hU, bd_up_diag hN hX, sq]

private theorem bd_poly {u v S : M4 R} (h : u * v = 1) (h' : v * u = 1) (b c : R) :
    v * (S * S - b • S + c • (1 : M4 R)) * u = (v * S * u) * (v * S * u) - b • (v * S * u) + c • (1 : M4 R) := by
  rw [← bd_conj_mul h]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, h']

private theorem bd_poly_up {T : M4 R} (hT : IsUp T) (b c : R) : IsUp (T * T - b • T + c • (1 : M4 R)) := by
  intro i j hij
  simp [bd_up_mul hT hT i j hij, hT i j hij, Matrix.one_apply_ne hij.ne']

private theorem bd_poly_diag {T : M4 R} (hT : IsUp T) (b c : R) (i : Fin 4) :
    (T * T - b • T + c • (1 : M4 R)) i i = T i i * T i i - b * T i i + c := by
  simp [bd_up_diag hT hT]

private theorem bd_notMem (m : Ideal R) [hm : m.IsPrime] {t x p q p' q' r s : R} (ht : t - x ∈ m) (hp : p' - p ∈ m)
    (hq : q' - q ∈ m) (hr : r ∈ m) (h1 : x - p ∉ m) (h2 : x - q ∉ m) :
    t * t - (p' + q') * t + (p' * q' - r * s) ≠ 0 := by
  intro h0
  have e : (x - p) * (x - q) ∈ m := by
    rw [← Ideal.Quotient.eq] at ht hp hq
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hr ⊢
    have := congrArg (Ideal.Quotient.mk m) h0
    simp only [map_add (f := _), map_sub, map_mul, map_zero, ht, hp, hq, hr] at this ⊢
    linear_combination this
  rcases hm.mem_or_mem e with e | e
  · exact h1 e
  · exact h2 e

private theorem bd_zero {S : M4 R} (h : IsBlock S) : S 0 1 = 0 ∧ S 0 3 = 0 ∧ S 1 0 = 0 ∧ S 1 2 = 0 ∧ S 2 1 = 0 ∧
    S 2 3 = 0 ∧ S 3 0 = 0 ∧ S 3 2 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact h _ _ (by decide)

end SlopeTestRemainingChoices

theorem UpperTheory.V.Ws.blockDet :
    ∀ {R : Type} [CommRing R] [IsDomain R] [CharZero R] (m : Ideal R) [m.IsPrime] (a : Fin 4 → R) (u v S X : M4 R), v * u = 1 →
          (∀ i j, lamW i ≠ lamW j → a i - a j ∉ m) → IsBlock S → (∀ i j, S i j - Matrix.diagonal a i j ∈ m) → IsUp (v * S * u) →
          (∀ i, (v * S * u) i i - a i ∈ m) → IsBlock X → IsUp (v * X * u) →
          (X.submatrix ixA ixA).det = (v * X * u) 0 0 * (v * X * u) 2 2 ∧ (X.submatrix ixB ixB).det = (v * X * u) 1 1 * (v * X * u) 3 3 := by
  intro R _ _ _ m _ a u v S X hvu ha hS hSa hT hTa hX hY
  have huv : u * v = 1 := mul_eq_one_comm.mp hvu
  obtain ⟨s01, s03, s10, s12, s21, s23, s30, s32⟩ := bd_zero hS
  obtain ⟨x01, x03, x10, x12, x21, x23, x30, x32⟩ := bd_zero hX
  have hd : ∀ i, S i i - a i ∈ m := fun i => by simpa using hSa i i
  have h13 : S 1 3 ∈ m := by simpa using hSa 1 3
  have h02 : S 0 2 ∈ m := by simpa using hSa 0 2
  obtain ⟨N, hN⟩ : ∃ N, N = S * S - (S 1 1 + S 3 3) • S + (S 1 1 * S 3 3 - S 1 3 * S 3 1) • (1 : M4 R) := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ N, N = S * S - (S 0 0 + S 2 2) • S + (S 0 0 * S 2 2 - S 0 2 * S 2 0) • (1 : M4 R) := ⟨_, rfl⟩
  have hNz : ∀ i j, (lamW i = 0 ∨ lamW j = 0) → N i j = 0 := by
    intro i j h
    subst hN
    fin_cases i <;> fin_cases j <;> first | (exact absurd h (by decide)) |
      (simp [Matrix.mul_apply, Fin.sum_univ_four, s01, s03, s10, s12, s21, s23, s30, s32]; try ring)
  have hMz : ∀ i j, (lamW i = 1 ∨ lamW j = 1) → M i j = 0 := by
    intro i j h
    subst hM
    fin_cases i <;> fin_cases j <;> first | (exact absurd h (by decide)) |
      (simp [Matrix.mul_apply, Fin.sum_univ_four, s01, s03, s10, s12, s21, s23, s30, s32]; try ring)
  have hNM : N * M = 0 := by
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_four, hMz 0 j (Or.inl rfl), hMz 2 j (Or.inl rfl), hNz i 1 (Or.inr rfl),
      hNz i 3 (Or.inr rfl)]
    simp
  have uN : IsUp (v * N * u) := by rw [hN, bd_poly huv hvu]; exact bd_poly_up hT _ _
  have uM : IsUp (v * M * u) := by rw [hM, bd_poly huv hvu]; exact bd_poly_up hT _ _
  have nN : ∀ i, lamW i = 1 → (v * N * u) i i ≠ 0 := by
    intro i hi
    rw [hN, bd_poly huv hvu, bd_poly_diag hT]
    exact bd_notMem m (hTa i) (hd 1) (hd 3) h13 (ha i 1 (by rw [hi]; decide)) (ha i 3 (by rw [hi]; decide))
  have nM : ∀ i, lamW i = 0 → (v * M * u) i i ≠ 0 := by
    intro i hi
    rw [hM, bd_poly huv hvu, bd_poly_diag hT]
    exact bd_notMem m (hTa i) (hd 0) (hd 2) h02 (ha i 0 (by rw [hi]; decide)) (ha i 2 (by rw [hi]; decide))
  have hz : ∀ i, (v * N * u) i i * (v * M * u) i i = 0 := by
    intro i
    rw [← bd_up_diag uN uM, ← bd_conj_mul huv, hNM]; simp
  have n1 : (v * N * u) 1 1 = 0 := (mul_eq_zero.mp (hz 1)).resolve_right (nM 1 rfl)
  have n3 : (v * N * u) 3 3 = 0 := (mul_eq_zero.mp (hz 3)).resolve_right (nM 3 rfl)
  have m0 : (v * M * u) 0 0 = 0 := (mul_eq_zero.mp (hz 0)).resolve_left (nN 0 rfl)
  have m2 : (v * M * u) 2 2 = 0 := (mul_eq_zero.mp (hz 2)).resolve_left (nN 2 rfl)
  have u1 : IsUp (v * 1 * u) := by
    rw [Matrix.mul_one, hvu]; intro i j hij; exact Matrix.one_apply_ne hij.ne'
  have two : (2 : R) ≠ 0 := two_ne_zero
  constructor
  · have k1 := bd_key huv uN u1
    have k2 := bd_key huv uN hY
    have z1 : ∀ i, N i 1 = 0 := fun i => hNz i 1 (Or.inr rfl)
    have z3 : ∀ i, N i 3 = 0 := fun i => hNz i 3 (Or.inr rfl)
    have z1' : ∀ i, N 1 i = 0 := fun i => hNz 1 i (Or.inl rfl)
    have z3' : ∀ i, N 3 i = 0 := fun i => hNz 3 i (Or.inl rfl)
    have p0 := nN 0 rfl
    have p2 := nN 2 rfl
    rw [Matrix.mul_one v, hvu] at k1
    generalize v * N * u = N' at *
    generalize v * X * u = X' at *
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_four, Matrix.mul_one,
      Matrix.one_apply_eq, z1, z3, z1', z3', n1, n3, x01, x03, x10, x12, x21, x23, x30, x32] at k1 k2
    apply mul_left_cancel₀ (mul_ne_zero two (mul_ne_zero p0 p2))
    simp only [Matrix.det_fin_two, Matrix.submatrix_apply, ixA, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination k2 - (X 0 0 * X 2 2 - X 0 2 * X 2 0) * k1
  · have k1 := bd_key huv uM u1
    have k2 := bd_key huv uM hY
    have z1 : ∀ i, M i 0 = 0 := fun i => hMz i 0 (Or.inr rfl)
    have z3 : ∀ i, M i 2 = 0 := fun i => hMz i 2 (Or.inr rfl)
    have z1' : ∀ i, M 0 i = 0 := fun i => hMz 0 i (Or.inl rfl)
    have z3' : ∀ i, M 2 i = 0 := fun i => hMz 2 i (Or.inl rfl)
    have p0 := nM 1 rfl
    have p2 := nM 3 rfl
    rw [Matrix.mul_one v, hvu] at k1
    generalize v * M * u = N' at *
    generalize v * X * u = X' at *
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_four, Matrix.mul_one,
      Matrix.one_apply_eq, z1, z3, z1', z3', m0, m2, x01, x03, x10, x12, x21, x23, x30, x32] at k1 k2
    apply mul_left_cancel₀ (mul_ne_zero two (mul_ne_zero p0 p2))
    simp only [Matrix.det_fin_two, Matrix.submatrix_apply, ixB, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination k2 - (X 1 1 * X 3 3 - X 1 3 * X 3 1) * k1
end

section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private def eAB : Fin 2 ⊕ Fin 2 ≃ Fin 4 where
  toFun := Sum.elim ixA ixB
  invFun := ![Sum.inl 0, Sum.inr 0, Sum.inl 1, Sum.inr 1]
  left_inv := by decide
  right_inv := by decide

private theorem cp_block {K : Type} [Field K] (X : M4 K) (h : IsBlock X) :
    X.charpoly = (X.submatrix ixA ixA).charpoly * (X.submatrix ixB ixB).charpoly := by
  have e : Matrix.reindex eAB.symm eAB.symm X =
      Matrix.fromBlocks (X.submatrix ixA ixA) (X.submatrix ixA ixB) 0 (X.submatrix ixB ixB) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rfl
    · rfl
    · exact h (ixB i) (ixA j) (by revert i j; decide)
    · rfl
  rw [← Matrix.charpoly_reindex eAB.symm, e, Matrix.charpoly_fromBlocks_zero₂₁]

private theorem det_two {K : Type} [Field K] [IsAlgClosed K] (A : Matrix (Fin 2) (Fin 2) K) :
    ∃ a ∈ A.charpoly.roots, ∃ b ∈ A.charpoly.roots, A.det = a * b := by
  have hc : A.charpoly.roots.card = 2 := by
    rw [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim]; simp
  obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.1 hc
  refine ⟨a, by simp [hab], b, by simp [hab], ?_⟩
  rw [Matrix.det_eq_prod_roots_charpoly, hab]; simp

theorem UpperTheory.V.Ws.pureDet :
    ∀ {K : Type} [Field K] [IsAlgClosed K] (ι : K →+* ℂ) (X : M4 K), IsBlock X →
          (∀ x ∈ X.charpoly.roots, ∀ y ∈ X.charpoly.roots, ‖ι x‖ = ‖ι y‖) →
          ‖ι (X.submatrix ixA ixA).det‖ = ‖ι (X.submatrix ixB ixB).det‖ := by
  intro K _ _ ι X hX h
  have hr : X.charpoly.roots =
      (X.submatrix ixA ixA).charpoly.roots + (X.submatrix ixB ixB).charpoly.roots := by
    rw [cp_block X hX, roots_mul (mul_ne_zero (Matrix.charpoly_monic _).ne_zero (Matrix.charpoly_monic _).ne_zero)]
  obtain ⟨a, ha, b, hb, hA⟩ := det_two (X.submatrix ixA ixA)
  obtain ⟨c, hc, d, hd, hB⟩ := det_two (X.submatrix ixB ixB)
  rw [hr] at h
  rw [hA, hB, map_mul, map_mul, norm_mul, norm_mul,
    h a (Multiset.mem_add.2 (Or.inl ha)) c (Multiset.mem_add.2 (Or.inr hc)),
    h b (Multiset.mem_add.2 (Or.inl hb)) d (Multiset.mem_add.2 (Or.inr hd))]
end
