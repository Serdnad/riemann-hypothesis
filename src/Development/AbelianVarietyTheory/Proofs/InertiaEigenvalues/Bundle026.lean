module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.FieldTheory.Galois.Notation
public import Mathlib.RingTheory.Algebraic.Defs
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Data.Matrix.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

@[expose] public section

section

namespace GlobalTheory.InvariantLift

variable {G : Type} [Group G] {A : Type} [CommRing A] {r : ℕ}

theorem average_step (σ : G → A →+* A) (hσ : ∀ g h a, σ (g * h) a = σ g (σ h a))
    (M : G →* Matrix (Fin r) (Fin r) A) (hM : ∀ g h i j, σ g (M h i j) = M h i j)
    (N : Subgroup G) [hN : N.Normal] [Finite (G ⧸ N)] (τ : A) (hτ : ∀ g ∈ N, σ g τ = τ)
    (hτ1 : ∑ᶠ x : G ⧸ N, σ x.out τ = 1) (c d : A) (hd : ∀ g ∈ N, ∀ i j, d ∣ (M g - 1) i j)
    (W : Matrix (Fin r) (Fin r) A) (hW : ∀ g ∈ N, W.map (σ g) = W)
    (hc : ∀ g i j, c ∣ (M g * W.map (σ g) - W) i j) :
    ∃ W' : Matrix (Fin r) (Fin r) A, (∀ i j, c ∣ (W - W') i j) ∧ (∀ g ∈ N, W'.map (σ g) = W') ∧
      ∀ g i j, d ∣ (M g * W'.map (σ g) - W') i j := by
  classical
  haveI : Fintype (G ⧸ N) := Fintype.ofFinite _

  have dl : ∀ (e : A) (X : Matrix (Fin r) (Fin r) A), (∀ i j, e ∣ X i j) →
      ∀ (Y : Matrix (Fin r) (Fin r) A) i j, e ∣ (X * Y) i j := by
    intro e X hX Y i j
    rw [Matrix.mul_apply]
    exact Finset.dvd_sum fun k _ => (hX i k).mul_right _
  have dr : ∀ (e : A) (Y : Matrix (Fin r) (Fin r) A), (∀ i j, e ∣ Y i j) →
      ∀ (X : Matrix (Fin r) (Fin r) A) i j, e ∣ (X * Y) i j := by
    intro e Y hY X i j
    rw [Matrix.mul_apply]
    exact Finset.dvd_sum fun k _ => (hY k j).mul_left _

  have hfix : ∀ a : A, (∀ m ∈ N, σ m a = a) → ∀ g, ∀ n ∈ N, σ n (σ g a) = σ g a := by
    intro a ha g n hn
    have hm : g⁻¹ * n * g ∈ N := by simpa using hN.conj_mem n hn g⁻¹
    rw [← hσ, show n * g = g * (g⁻¹ * n * g) by group, hσ, ha _ hm]
  obtain ⟨U, hU⟩ : ∃ U : Matrix (Fin r) (Fin r) A, U = τ • W := ⟨_, rfl⟩
  have hUfix : ∀ m ∈ N, ∀ k l, σ m (U k l) = U k l := by
    intro m hm k l
    have hWe : σ m (W k l) = W k l := congrFun (congrFun (hW m hm) k) l
    rw [hU, Matrix.smul_apply, smul_eq_mul, map_mul, hτ m hm, hWe]
  have hUl : ∀ g, ∀ n ∈ N, U.map (σ (n * g)) = U.map (σ g) := by
    intro g n hn
    ext k l
    simp only [Matrix.map_apply, hσ]
    exact hfix _ (fun m hm => hUfix m hm k l) g n hn
  have hUr : ∀ g, ∀ n ∈ N, U.map (σ (g * n)) = U.map (σ g) := by
    intro g n hn
    ext k l
    simp only [Matrix.map_apply, hσ, hUfix n hn]
  have hMfix : ∀ g h, (M h).map (σ g) = M h := by
    intro g h
    ext i j
    exact hM g h i j
  have hUmap : ∀ g h, (U.map (σ h)).map (σ g) = U.map (σ (g * h)) := by
    intro g h
    ext i j
    simp [hσ]
  have hsum : ∀ (f : A →+* A) (X : G ⧸ N → Matrix (Fin r) (Fin r) A),
      (∑ x, X x).map f = ∑ x, (X x).map f := by
    intro f X
    ext i j

    simp [Matrix.sum_apply, map_sum]

  refine ⟨∑ x : G ⧸ N, M x.out * U.map (σ x.out), ?_, ?_, ?_⟩
  · intro i j
    have h1 : ∑ x : G ⧸ N, σ x.out τ = 1 := by
      rw [← finsum_eq_sum_of_fintype]
      exact hτ1
    have hent : ∀ x : G ⧸ N, (M x.out * U.map (σ x.out)) i j =
        σ x.out τ * (M x.out * W.map (σ x.out)) i j := by
      intro x
      simp only [hU, Matrix.mul_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hsplit : (W - ∑ x : G ⧸ N, M x.out * U.map (σ x.out)) i j =
        ∑ x : G ⧸ N, σ x.out τ * (W i j - (M x.out * W.map (σ x.out)) i j) := by
      rw [Matrix.sub_apply, Matrix.sum_apply, Finset.sum_congr rfl (fun x _ => hent x)]
      simp only [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, h1, one_mul]
    rw [hsplit]
    refine Finset.dvd_sum fun x _ => dvd_mul_of_dvd_right ?_ _
    exact dvd_sub_comm.mp (by simpa only [Matrix.sub_apply] using hc x.out i j)
  · intro n hn
    rw [hsum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Matrix.map_mul, hMfix, hUmap, hUl _ n hn]
  · intro g i j
    have hmul : M g * (∑ x : G ⧸ N, M x.out * U.map (σ x.out)).map (σ g) =
        ∑ x : G ⧸ N, M (g * x.out) * U.map (σ (g * x.out)) := by
      rw [hsum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Matrix.map_mul, hMfix, hUmap, map_mul, mul_assoc]
    have hre : ∑ x : G ⧸ N, M x.out * U.map (σ x.out) =
        ∑ x : G ⧸ N, M (g • x).out * U.map (σ (g • x).out) :=
      (Equiv.sum_comp (MulAction.toPerm g) (fun y : G ⧸ N => M y.out * U.map (σ y.out))).symm
    rw [hmul, hre, ← Finset.sum_sub_distrib, Matrix.sum_apply]
    refine Finset.dvd_sum fun x _ => ?_
    obtain ⟨n, hn, hgx⟩ : ∃ n ∈ N, g * x.out = (g • x).out * n := by
      refine ⟨((g • x).out)⁻¹ * (g * x.out), ?_, (mul_inv_cancel_left _ _).symm⟩
      rw [← QuotientGroup.eq]
      simp only [QuotientGroup.out_eq']
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
      simp only [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.mk_mul, QuotientGroup.out_eq',
        Quotient.out_eq]
    rw [hgx, map_mul, hUr _ n hn]
    have hfac : M (g • x).out * M n * U.map (σ (g • x).out) - M (g • x).out * U.map (σ (g • x).out)
        = M (g • x).out * ((M n - 1) * U.map (σ (g • x).out)) := by
      noncomm_ring
    rw [hfac]
    exact dr d _ (dl d _ (fun i' j' => by simpa [Matrix.sub_apply] using hd n hn i' j') _) _ i j

theorem exists_invariant_lift : ∀ (G : Type) [Group G] (A : Type) [CommRing A] (π : A), IsAdicComplete (Ideal.span {π}) A → ∀ (σ : G → A →+* A), (∀ g h a, σ (g * h) a = σ g (σ h a)) → (∀ g, σ g π = π) → ∀ (r : ℕ) (M : G →* Matrix (Fin r) (Fin r) A), (∀ g h i j, σ g (M h i j) = M h i j) → ∀ (S : Set (Subgroup G)), (∀ N ∈ S, N.Normal ∧ Finite (G ⧸ N) ∧ ∃ τ : A, (∀ g ∈ N, σ g τ = τ) ∧ ∑ᶠ x : G ⧸ N, σ x.out τ = 1) → (∀ N ∈ S, ∀ k : ℕ, ∃ N' ∈ S, N' ≤ N ∧ ∀ g ∈ N', ∀ i j, π ^ k ∣ (M g - 1) i j) → ∀ (W₀ : Matrix (Fin r) (Fin r) A), (∃ N ∈ S, ∀ g ∈ N, W₀.map (σ g) = W₀) → (∀ g i j, π ∣ (M g * W₀.map (σ g) - W₀) i j) → ∃ W : Matrix (Fin r) (Fin r) A, (∀ i j, π ∣ (W - W₀) i j) ∧ ∀ g, M g * W.map (σ g) = W := by
  intro G _ A _ π hA σ hσ hσπ r M hM S hS hSk W₀ hW₀ hW₀c
  classical

  have hstep : ∀ (k : ℕ) (N : Subgroup G) (W : Matrix (Fin r) (Fin r) A), N ∈ S →
      (∀ g ∈ N, W.map (σ g) = W) → (∀ g i j, π ^ (k + 1) ∣ (M g * W.map (σ g) - W) i j) →
      ∃ (N' : Subgroup G) (W' : Matrix (Fin r) (Fin r) A), N' ∈ S ∧ (∀ g ∈ N', W'.map (σ g) = W') ∧
        (∀ g i j, π ^ (k + 1 + 1) ∣ (M g * W'.map (σ g) - W') i j) ∧
        ∀ i j, π ^ (k + 1) ∣ (W - W') i j := by
    intro k N W hNS hWN hWc
    obtain ⟨N', hN'S, hN'N, hN'd⟩ := hSk N hNS (k + 1 + 1)
    obtain ⟨hN'n, hN'f, τ, hτ, hτ1⟩ := hS N' hN'S
    haveI := hN'n
    haveI := hN'f
    obtain ⟨W', h1, h2, h3⟩ := GlobalTheory.InvariantLift.average_step σ hσ M hM N' τ hτ hτ1
      (π ^ (k + 1)) (π ^ (k + 1 + 1)) hN'd W (fun g hg => hWN g (hN'N hg)) hWc
    exact ⟨N', W', hN'S, h2, h3, h1⟩
  choose! Nf Wf hNf hWf hcf hdf using hstep
  obtain ⟨N₀, hN₀S, hN₀W⟩ := hW₀
  obtain ⟨seq, hseq0, hseqs⟩ : ∃ seq : ℕ → Subgroup G × Matrix (Fin r) (Fin r) A,
      seq 0 = (N₀, W₀) ∧ ∀ k, seq (k + 1) = (Nf k (seq k).1 (seq k).2, Wf k (seq k).1 (seq k).2) :=
    ⟨fun k => Nat.rec (N₀, W₀) (fun k q => (Nf k q.1 q.2, Wf k q.1 q.2)) k, rfl, fun _ => rfl⟩
  have hP : ∀ k, (seq k).1 ∈ S ∧ (∀ g ∈ (seq k).1, (seq k).2.map (σ g) = (seq k).2) ∧
      ∀ g i j, π ^ (k + 1) ∣ (M g * (seq k).2.map (σ g) - (seq k).2) i j := by
    intro k
    induction k with
    | zero => exact ⟨by simp [hseq0, hN₀S], by simpa [hseq0] using hN₀W,
        by simpa [hseq0] using hW₀c⟩
    | succ k ih =>
      rw [hseqs]
      exact ⟨hNf k _ _ ih.1 ih.2.1 ih.2.2, hWf k _ _ ih.1 ih.2.1 ih.2.2, hcf k _ _ ih.1 ih.2.1 ih.2.2⟩
  have hd : ∀ k i j, π ^ (k + 1) ∣ (seq k).2 i j - (seq (k + 1)).2 i j := by
    intro k i j
    have := hdf k _ _ (hP k).1 (hP k).2.1 (hP k).2.2 i j
    rw [hseqs]
    simpa [Matrix.sub_apply] using this
  have hcauchy : ∀ m n, m ≤ n → ∀ i j, π ^ m ∣ (seq m).2 i j - (seq n).2 i j := by
    intro m n hmn i j
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have e : (seq m).2 i j - (seq (n + 1)).2 i j =
          ((seq m).2 i j - (seq n).2 i j) + ((seq n).2 i j - (seq (n + 1)).2 i j) := by ring
      rw [e]
      exact dvd_add ih ((pow_dvd_pow π (by omega)).trans (hd n i j))

  have hmod : ∀ (n : ℕ) (x y : A),
      x ≡ y [SMOD ((Ideal.span {π}) ^ n • (⊤ : Submodule A A))] ↔ π ^ n ∣ x - y := by
    intro n x y
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
  have hlim : ∀ i j, ∃ L : A, ∀ n, π ^ n ∣ (seq n).2 i j - L := by
    intro i j
    obtain ⟨L, hL⟩ := hA.toIsPrecomplete.prec (f := fun n => (seq n).2 i j)
      (fun {m n} hmn => (hmod m _ _).mpr (hcauchy m n hmn i j))
    exact ⟨L, fun n => (hmod n _ _).mp (hL n)⟩
  choose L hL using hlim
  refine ⟨Matrix.of L, ?_, ?_⟩
  · intro i j
    have a := hd 0 i j
    have b := hL i j 1
    rw [hseq0] at a
    simp only [zero_add, pow_one] at a b
    have c : π ∣ W₀ i j - L i j := by
      have e : W₀ i j - L i j = (W₀ i j - (seq 1).2 i j) + ((seq 1).2 i j - L i j) := by ring
      rw [e]
      exact dvd_add a b
    simpa [Matrix.sub_apply] using dvd_sub_comm.mp c
  · intro g
    ext i j
    apply sub_eq_zero.mp
    rw [← Matrix.sub_apply]
    apply hA.toIsHausdorff.haus
    intro n
    rw [hmod, sub_zero]
    have key : (M g * (Matrix.of L).map (σ g) - Matrix.of L) i j =
        (∑ k, M g i k * σ g (L k j - (seq n).2 k j)) +
          (M g * (seq n).2.map (σ g) - (seq n).2) i j + ((seq n).2 i j - L i j) := by
      simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, map_sub,
        mul_sub, Finset.sum_sub_distrib]
      ring
    rw [key]
    refine dvd_add (dvd_add (Finset.dvd_sum fun k _ => ?_) ?_) (hL i j n)
    · obtain ⟨e, he⟩ := dvd_sub_comm.mp (hL k j n)
      refine dvd_mul_of_dvd_right ⟨σ g e, ?_⟩ _
      rw [he, map_mul, map_pow, hσπ]
    · exact (pow_dvd_pow π (Nat.le_succ n)).trans ((hP n).2.2 g i j)

end GlobalTheory.InvariantLift
end

section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem residue_top_factor_through_bottom : ∀ (O : Type) [CommRing O] [IsLocalRing O] (r t : ℕ) (U : Submodule O (Fin r ⊕ Fin t → O)) (a : Fin r → IsLocalRing.ResidueField O), (∀ u ∈ U, (∀ i, IsLocalRing.residue O (u (Sum.inr i)) = 0) → a ⬝ᵥ (fun i => IsLocalRing.residue O (u (Sum.inl i))) = 0) → ∀ g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O), (∀ v, a ⬝ᵥ v = 0 → g.mulVec v = v) → ∃ b : Matrix (Fin r) (Fin t) (IsLocalRing.ResidueField O), ∀ u ∈ U, g.mulVec (fun i => IsLocalRing.residue O (u (Sum.inl i))) + b.mulVec (fun i => IsLocalRing.residue O (u (Sum.inr i))) = (fun i => IsLocalRing.residue O (u (Sum.inl i))) := by
  intro O _ _ r t U a ha g hg
  let res : (Fin r ⊕ Fin t → O) → (Fin r ⊕ Fin t → IsLocalRing.ResidueField O) :=
    fun u j => IsLocalRing.residue O (u j)
  let Wsp : Submodule (IsLocalRing.ResidueField O) (Fin r ⊕ Fin t → IsLocalRing.ResidueField O) :=
    { carrier := {w | ∃ u ∈ U, res u = w}
      add_mem' := by
        rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
        exact ⟨u + v, U.add_mem hu hv, by ext j; simp [res]⟩
      zero_mem' := ⟨0, U.zero_mem, by ext j; simp [res]⟩
      smul_mem' := by
        rintro c _ ⟨u, hu, rfl⟩
        obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective c
        exact ⟨o • u, U.smul_mem o hu, by ext j; simp [res]⟩ }
  let top : (Fin r ⊕ Fin t → IsLocalRing.ResidueField O) →ₗ[IsLocalRing.ResidueField O] (Fin r → IsLocalRing.ResidueField O) :=
    LinearMap.funLeft _ _ Sum.inl
  let bot : (Fin r ⊕ Fin t → IsLocalRing.ResidueField O) →ₗ[IsLocalRing.ResidueField O] (Fin t → IsLocalRing.ResidueField O) :=
    LinearMap.funLeft _ _ Sum.inr
  let π : Wsp →ₗ[IsLocalRing.ResidueField O] (Fin t → IsLocalRing.ResidueField O) := bot.comp Wsp.subtype
  let f : Wsp →ₗ[IsLocalRing.ResidueField O] (Fin r → IsLocalRing.ResidueField O) :=
    (LinearMap.id - Matrix.toLin' g).comp (top.comp Wsp.subtype)
  have hker : LinearMap.ker π ≤ LinearMap.ker f := by
    rintro ⟨w, u, hu, rfl⟩ hw
    rw [LinearMap.mem_ker] at hw ⊢
    have h2 : ∀ i, IsLocalRing.residue O (u (Sum.inr i)) = 0 := fun i => congrFun hw i
    have h3 := hg _ (ha u hu h2)
    simp only [f, top, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.sub_apply,
      LinearMap.id_apply, Matrix.toLin'_apply]
    rw [sub_eq_zero]
    exact h3.symm
  let b₀ : LinearMap.range π →ₗ[IsLocalRing.ResidueField O] (Fin r → IsLocalRing.ResidueField O) :=
    ((LinearMap.ker π).liftQ f hker).comp (π.quotKerEquivRange.symm.toLinearMap)
  obtain ⟨B, hB⟩ := LinearMap.exists_extend b₀
  refine ⟨LinearMap.toMatrix' B, ?_⟩
  intro u hu
  have hw : res u ∈ Wsp := ⟨u, hu, rfl⟩
  have key : B (π ⟨res u, hw⟩) = f ⟨res u, hw⟩ := by
    have h1 := LinearMap.congr_fun hB ⟨π ⟨res u, hw⟩, LinearMap.mem_range_self π _⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h1
    rw [h1]
    show (LinearMap.ker π).liftQ f hker
      (π.quotKerEquivRange.symm ⟨π ⟨res u, hw⟩, LinearMap.mem_range_self π _⟩) = _
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  have e : π ⟨res u, hw⟩ = fun i => IsLocalRing.residue O (u (Sum.inr i)) := rfl
  have e2 : f ⟨res u, hw⟩ = (fun i => IsLocalRing.residue O (u (Sum.inl i))) -
      g.mulVec (fun i => IsLocalRing.residue O (u (Sum.inl i))) := rfl
  rw [e, e2] at key
  rw [LinearMap.toMatrix'_mulVec, key]
  abel

end GlobalTheory
end

section

open scoped BigOperators

namespace GlobalTheory

theorem pow_sub_dvd_choose_prime_pow_of_lt :
    ∀ (l a c i : ℕ), l.Prime → 1 ≤ i → i < l ^ (c + 1) → l ^ (a - c) ∣ (l ^ a).choose i := by
  intro l a c i hl hi hlt
  obtain ⟨v, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : i ≠ 0) l hl.one_lt.ne'
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hi)
  have hv : v ≤ c := by
    have h1 : l ^ v ≤ l ^ v * m := Nat.le_mul_of_pos_right _ hm0
    have h2 : l ^ v < l ^ (c + 1) := lt_of_le_of_lt h1 hlt
    have := (Nat.pow_lt_pow_iff_right hl.one_lt).1 h2
    omega
  have hpos : 0 < l ^ a := pow_pos hl.pos a
  have key : l ^ a ∣ l ^ v * m * (l ^ a).choose (l ^ v * m) := by
    obtain ⟨n, hn⟩ : ∃ n, l ^ a = n + 1 := ⟨l ^ a - 1, by omega⟩
    obtain ⟨k, hk⟩ : ∃ k, l ^ v * m = k + 1 := ⟨l ^ v * m - 1, by omega⟩
    rw [hn, hk]
    refine ⟨n.choose k, ?_⟩
    rw [mul_comm]
    exact (Nat.add_one_mul_choose_eq n k).symm
  have h2 : l ^ (a - v) ∣ m * (l ^ a).choose (l ^ v * m) := by
    rcases le_or_gt v a with h | h
    · have key' : l ^ v * l ^ (a - v) ∣ l ^ v * (m * (l ^ a).choose (l ^ v * m)) := by
        rw [← pow_add, Nat.add_sub_of_le h, ← mul_assoc]
        exact key
      exact (Nat.mul_dvd_mul_iff_left (pow_pos hl.pos v)).1 key'
    · rw [show a - v = 0 by omega, pow_zero]
      exact one_dvd _
  have hcop : (l ^ (a - v)).Coprime m := Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hl).2 hm)
  have h3 : l ^ (a - v) ∣ (l ^ a).choose (l ^ v * m) := hcop.dvd_of_dvd_mul_left h2
  exact (pow_dvd_pow l (by omega : a - c ≤ a - v)).trans h3

end GlobalTheory
end

section

namespace GlobalTheory.BSP

private theorem span_sup_span_pow_succ_le {A : Type} [CommRing A] (p d : A) (k : ℕ) :
    (Ideal.span {p} ⊔ Ideal.span {d}) ^ (k + 1) ≤
      Ideal.span {p ^ (k + 1)} ⊔ Ideal.span {d} * (Ideal.span {p} ⊔ Ideal.span {d}) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ' _ (k + 1)]
    refine (Ideal.mul_mono_right ih).trans ?_
    rw [Ideal.mul_sup, Ideal.sup_mul, Ideal.sup_mul]
    refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
    ·
      rw [Ideal.span_singleton_mul_span_singleton, ← pow_succ']
      exact le_sup_left
    ·
      refine le_sup_of_le_right (Ideal.mul_mono_right ?_)
      rw [← Ideal.span_singleton_pow]
      exact Ideal.pow_right_mono le_sup_left _
    · refine le_sup_of_le_right ?_
      rw [mul_left_comm, pow_succ' _ k]
      exact Ideal.mul_mono_right (Ideal.mul_mono_left le_sup_left)
    · refine le_sup_of_le_right ?_
      rw [pow_succ' _ k]
      exact Ideal.mul_mono_right (Ideal.mul_mono_left le_sup_right)

private theorem div_cont {A : Type} [CommRing A] (p d : A) (N : ℕ) (hd : d ∈ nonZeroDivisors A)
    (ht : ∀ (x : A) (m : ℕ), p ^ m * x ∈ Ideal.span {d} → p ^ N * x ∈ Ideal.span {d})
    (n : ℕ) (z : A) (hz : d * z ∈ (Ideal.span {p} ⊔ Ideal.span {d}) ^ (2 * (n + N + 1))) :
    z ∈ (Ideal.span {p} ⊔ Ideal.span {d}) ^ n := by

  have h1 := span_sup_span_pow_succ_le p d (2 * (n + N + 1) - 1)
  have e : 2 * (n + N + 1) - 1 + 1 = 2 * (n + N + 1) := by omega
  rw [e] at h1
  obtain ⟨y1, hy1, y2, hy2, hsum⟩ := Submodule.mem_sup.1 (h1 hz)
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hy1
  obtain ⟨w, hw, rfl⟩ := Ideal.mem_span_singleton_mul.1 hy2

  have key : p ^ (2 * (n + N + 1)) * a ∈ Ideal.span {d} := by
    rw [Ideal.mem_span_singleton']
    exact ⟨z - w, by linear_combination (-1 : A) * hsum⟩
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (ht a _ key)
  have hp : p ^ (2 * (n + N + 1)) = p ^ (2 * (n + N + 1) - N) * p ^ N := by
    rw [← pow_add]; congr 1; omega

  have hz' : z = w + p ^ (2 * (n + N + 1) - N) * b := by
    have h0 : d * (z - (w + p ^ (2 * (n + N + 1) - N) * b)) = 0 := by
      linear_combination (-1 : A) * hsum + a * hp - p ^ (2 * (n + N + 1) - N) * hb
    exact sub_eq_zero.1 ((mul_left_mem_nonZeroDivisors_eq_zero_iff hd).1 h0)
  rw [hz']
  refine Ideal.add_mem _ (Ideal.pow_le_pow_right (by omega) hw) (Ideal.mul_mem_right _ _ ?_)
  exact Ideal.pow_le_pow_right (by omega)
    (Ideal.pow_mem_pow (Ideal.mem_sup_left (Ideal.mem_span_singleton_self p)) _)

theorem span_singleton_closed_of_bounded_torsion (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A]
    (d : A) (N : ℕ) (hd : d ∈ nonZeroDivisors A)
    (ht : ∀ (x : A) (m : ℕ), (l : A) ^ m * x ∈ Ideal.span {d} → (l : A) ^ N * x ∈ Ideal.span {d})
    (hc : IsAdicComplete (Ideal.span {(l : A)} ⊔ Ideal.span {d}) A) (x : A)
    (hx : ∀ n : ℕ, ∃ z, x - d * z ∈ (Ideal.span {(l : A)} ⊔ Ideal.span {d}) ^ n) :
    x ∈ Ideal.span {d} := by
  have hsm : ∀ n : ℕ, ((Ideal.span {(l : A)} ⊔ Ideal.span {d}) ^ n • ⊤ : Submodule A A) =
      (Ideal.span {(l : A)} ⊔ Ideal.span {d}) ^ n := fun n => by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  choose z hz using hx

  have hcau : ∀ {m k : ℕ}, m ≤ k → z (2 * (m + N + 1)) - z (2 * (k + N + 1)) ∈
      (Ideal.span {(l : A)} ⊔ Ideal.span {d}) ^ m := by
    intro m k hmk
    apply div_cont (l : A) d N hd ht m
    have h1 := hz (2 * (m + N + 1))
    have h2 := Ideal.pow_le_pow_right (I := Ideal.span {(l : A)} ⊔ Ideal.span {d})
      (show 2 * (m + N + 1) ≤ 2 * (k + N + 1) by omega) (hz (2 * (k + N + 1)))
    have e : d * (z (2 * (m + N + 1)) - z (2 * (k + N + 1))) =
        (x - d * z (2 * (k + N + 1))) - (x - d * z (2 * (m + N + 1))) := by ring
    rw [e]
    exact Ideal.sub_mem _ h2 h1
  obtain ⟨L, hL⟩ := hc.toIsPrecomplete.prec' (fun n => z (2 * (n + N + 1)))
    (fun {m k} hmk => by rw [SModEq.sub_mem, hsm]; exact hcau hmk)

  have h0 : x - d * L = 0 := by
    apply hc.toIsHausdorff.haus'
    intro n
    rw [SModEq.sub_mem, sub_zero, hsm]
    have h2 : z (2 * (n + N + 1)) - L ∈ (Ideal.span {(l : A)} ⊔ Ideal.span {d}) ^ n := by
      have h3 := hL n
      rw [SModEq.sub_mem, hsm] at h3
      exact h3
    have e : x - d * L = (x - d * z (2 * (n + N + 1))) + d * (z (2 * (n + N + 1)) - L) := by ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.pow_le_pow_right (by omega) (hz _)) (Ideal.mul_mem_left _ _ h2)
  rw [sub_eq_zero.1 h0]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self d)

end GlobalTheory.BSP
end

section

namespace GlobalTheory.CardinalPower

open IntermediateField

theorem exists_pow_card_eq {K L : Type} [Field K] [Fintype K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (σ : Gal(L/K)) (X : Finset L) :
    ∃ i : ℕ, ∀ x ∈ X, (σ : L → L) x = x ^ Fintype.card K ^ i := by
  classical
  let M : IntermediateField K L := adjoin K (X : Set L)
  haveI : FiniteDimensional K M :=
    finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  haveI : Finite M := Module.finite_of_finite K
  haveI : Normal K M := inferInstance
  obtain ⟨n, hn⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow K M).2 (σ.restrictNormal M)
  refine ⟨n.1, fun x hx => ?_⟩
  have hxM : x ∈ M := subset_adjoin K _ hx
  have h1 := AlgEquiv.restrictNormal_commutes σ M ⟨x, hxM⟩
  rw [← hn] at h1
  simp only [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic, pow_iterate] at h1
  simpa using h1.symm

end GlobalTheory.CardinalPower
end
