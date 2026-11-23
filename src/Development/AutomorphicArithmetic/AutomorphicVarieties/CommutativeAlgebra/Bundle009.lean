module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle039
public import ReciprocityTheory.GaloisValuations.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle001
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.RingTheory.Ideal.BigOperators

@[expose] public section

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

open Matrix in
private theorem conj_form {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι] {J A A' h : Matrix ι ι R} {ν : R}
    (e1 : A * A' = 1) (hA : Aᵀ * J * A = ν • J) (hh : hᵀ * J * h = J) :
    (A * h * A')ᵀ * J * (A * h * A') = J := by
  have e2 : A'ᵀ * Aᵀ = 1 := by rw [← transpose_mul, e1, transpose_one]
  calc (A * h * A')ᵀ * J * (A * h * A') = A'ᵀ * (hᵀ * (Aᵀ * J * A) * h) * A' := by
        simp only [transpose_mul, Matrix.mul_assoc]
    _ = A'ᵀ * (Aᵀ * J * A) * A' := by
        rw [hA, mul_smul_comm, smul_mul_assoc, hh]
    _ = (A'ᵀ * Aᵀ) * J * (A * A') := by simp only [Matrix.mul_assoc]
    _ = J := by rw [e1, e2, one_mul, mul_one]

private theorem triple_ne {R ι : Type} [CommRing R] [Fintype ι] {A Y B : Matrix ι ι R} {a b : ι}
    (hab : (A * Y * B) a b ≠ 0) : ∃ c d, A a c ≠ 0 ∧ Y c d ≠ 0 ∧ B d b ≠ 0 :=
  _root_.UpperTheory.Reformulated.B.Qk1.triple_ne hab

private theorem blk_inv {R ι κ : Type} [CommRing R] [Fintype ι] [DecidableEq ι] (blk : ι → κ) {h h' : Matrix ι ι R}
    (e1 : h * h' = 1) (e2 : h' * h = 1) (hb : ∀ a b, blk a ≠ blk b → h a b = 0) :
    ∀ a b, blk a ≠ blk b → h' a b = 0 := by
  classical
  intro a b hab
  set E : Matrix ι ι R := Matrix.diagonal fun x => if blk x = blk a then 1 else 0 with hE
  have h1 : E * h = h * E := by
    ext x y
    rw [hE, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hxy : blk x = blk y
    · rw [hxy, mul_comm]
    · rw [hb x y hxy, mul_zero, zero_mul]
  have h2 : h' * E = E * h' := by
    calc h' * E = h' * (E * h) * h' := by rw [mul_assoc, mul_assoc, e1, mul_one]
      _ = E * h' := by rw [h1, ← mul_assoc, e2, one_mul]
  have h3 := congrFun (congrFun h2 a) b
  rw [hE, Matrix.diagonal_mul, Matrix.mul_diagonal, if_neg (Ne.symm hab), if_pos rfl, mul_zero, one_mul] at h3
  exact h3.symm

private theorem map_mul_alg {O R S ι : Type} [CommRing O] [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
    [Fintype ι] [DecidableEq ι] (f : R →ₐ[O] S) (A B : Matrix ι ι R) : (A * B).map f = A.map f * B.map f :=
  Matrix.map_mul (f := (f : R →+* S))

theorem UpperTheory.V.Alg.hh_group :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (ι X : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup X] (w : ι → X) (Φ : FormData O w) (R : Type) [CommRing R] [Algebra O R] [IsCO O R],
      Φ.HH (1 : Matrix ι ι R) ∧ (∀ h h' : Matrix ι ι R, Φ.HH h → Φ.HH h' → Φ.HH (h * h')) ∧ (∀ h : Matrix ι ι R, Φ.HH h → ∃ h', Φ.HH h' ∧ h * h' = 1 ∧ h' * h = 1) ∧
      (∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') (h : Matrix ι ι R), Φ.HH h → Φ.HH (h.map f)) ∧
      (∀ (Γ : Type) [Group Γ] (r0 : Γ →* Matrix ι ι O), Φ.Normalises r0 → ∀ (s : Γ) (h : Matrix ι ι R), Φ.HH h → Φ.HH ((r0 s).map (algebraMap O R) * h * (r0 s⁻¹).map (algebraMap O R))) ∧
      ∀ (t : Multiplicative X →* Rˣ) (h : Matrix ι ι R), Φ.HH h → Φ.HH (Matrix.of fun a b => (t (Multiplicative.ofAdd (w a - w b)) : R) * h a b) := by
  intro O _ _ ι X _ _ _ w Φ R _ _ _
  refine ⟨⟨by simp, fun a b hab => Matrix.one_apply_ne fun e => hab (by rw [e]), by simp⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rintro h h' ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩
    refine ⟨?_, fun a b hab => ?_, by rw [map_mul_alg, a3, b3, one_mul]⟩
    · calc (h * h').transpose * Φ.JR R * (h * h') = h'.transpose * (h.transpose * Φ.JR R * h) * h' := by
            simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = Φ.JR R := by rw [a1, b1]
    · rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases hc : Φ.blk a = Φ.blk c
      · rw [b2 c b (hc ▸ hab), mul_zero]
      · rw [a2 a c hc, zero_mul]
  · rintro h ⟨a1, a2, a3⟩
    have hJ : IsUnit (Φ.JR R) := Φ.unit.map (algebraMap O R).mapMatrix
    obtain ⟨K, hK⟩ := hJ.exists_left_inv
    have e2 : (K * h.transpose * Φ.JR R) * h = 1 := by
      rw [mul_assoc K, mul_assoc K, a1, hK]
    generalize K * h.transpose * Φ.JR R = h' at e2
    have e1 : h * h' = 1 := mul_eq_one_comm.1 e2
    refine ⟨h', ⟨?_, blk_inv Φ.blk e1 e2 a2, ?_⟩, e1, e2⟩
    · have := conj_form (h := h) (ν := (1 : R)) e1 (by rw [a1, one_smul]) a1
      calc h'.transpose * Φ.JR R * h' = h'.transpose * (h.transpose * Φ.JR R * h) * h' := by rw [a1]
        _ = (h * h').transpose * Φ.JR R * (h * h') := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = Φ.JR R := by rw [e1]; simp
    · have := congrArg (fun A : Matrix ι ι R => A.map (res O R)) e1
      simp only [map_mul_alg, a3, one_mul] at this
      rw [this]; simp
  · rintro R' _ _ _ f h ⟨a1, a2, a3⟩
    have hJ : Φ.JR R' = (Φ.JR R).map f := by
      ext a b; simp [FormData.JR]
    refine ⟨?_, fun a b hab => by simp [a2 a b hab], ?_⟩
    · rw [hJ, ← Matrix.transpose_map, ← map_mul_alg, ← map_mul_alg, a1]
    · rw [← a3]
      ext a b
      simp only [Matrix.map_apply, res_map]
  · rintro Γ _ r0 ⟨h1, ⟨π, h2⟩, -⟩ s h ⟨a1, a2, a3⟩
    have e1 : (r0 s).map (algebraMap O R) * (r0 s⁻¹).map (algebraMap O R) = 1 := by
      rw [← Matrix.map_mul, ← map_mul, mul_inv_cancel, map_one]; simp
    refine ⟨?_, fun a b hab => ?_, ?_⟩
    · obtain ⟨ν, hν⟩ := h1 s
      refine conj_form (ν := algebraMap O R ν) e1 ?_ a1
      have hO : Φ.JR O = Φ.J := by ext a b; simp [FormData.JR]
      rw [hO] at hν
      rw [FormData.JR, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hν]
      ext a b; simp
    · by_contra hne
      obtain ⟨c, d, k1, k2, k3⟩ := triple_ne hne
      have k1' : r0 s a c ≠ 0 := fun e => k1 (by simp [e])
      have k3' : r0 s⁻¹ d b ≠ 0 := fun e => k3 (by simp [e])
      have k4 : Φ.blk c = Φ.blk d := by_contra fun n => k2 (a2 c d n)
      apply hab
      rw [h2 s a c k1', k4, h2 s⁻¹ d b k3', map_inv]
      simp
    · rw [map_mul_alg, map_mul_alg, a3, mul_one, ← map_mul_alg, e1]; simp
  · rintro t h ⟨a1, a2, a3⟩
    refine ⟨?_, fun a b hab => by simp [a2 a b hab], ?_⟩
    · have e : (Matrix.of fun a b => (t (Multiplicative.ofAdd (w a - w b)) : R) * h a b) =
          Matrix.diagonal (fun a => (t (Multiplicative.ofAdd (w a)) : R)) * h *
            Matrix.diagonal (fun a => (t (Multiplicative.ofAdd (-w a)) : R)) := by
        ext a b
        rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply, sub_eq_add_neg, ofAdd_add, map_mul,
          Units.val_mul]
        ring
      rw [e]
      refine conj_form (ν := (t (Multiplicative.ofAdd Φ.c) : R)) ?_ ?_ a1
      · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1
        funext a
        rw [← Units.val_mul, ← map_mul, ← ofAdd_add, add_neg_cancel, ofAdd_zero, map_one, Units.val_one]
      · ext a b
        rw [Matrix.diagonal_transpose, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
        by_cases hJ : Φ.J a b = 0
        · simp [FormData.JR, hJ]
        · rw [← Φ.hw a b hJ, ofAdd_add, map_mul, Units.val_mul]
          ring
    · ext a b
      have k := congrFun (congrFun a3 a) b
      rw [Matrix.map_apply] at k
      rw [Matrix.map_apply, Matrix.of_apply, map_mul, k]
      by_cases hab : a = b
      · subst hab; simp
      · simp [Matrix.one_apply_ne hab]
end

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem krull_dim_quotient_comap_eq {k Z A B C : Type} [Field k] [AddCommGroup Z] [Module k Z] [AddCommGroup A] [Module k A]
    [AddCommGroup B] [Module k B] [AddCommGroup C] [Module k C] [Module.Finite k A] [Module.Finite k C]
    (δ : Z →ₗ[k] A) (β : A →ₗ[k] B) (p : B →ₗ[k] C) (h0 : Function.Injective δ)
    (h1 : LinearMap.range δ = LinearMap.ker β) (h2 : LinearMap.range β = LinearMap.ker p) :
    Module.finrank k Z + Module.finrank k B = Module.finrank k A + Module.finrank k (LinearMap.range p) := by
  have hB : Module.Finite k B := by
    refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker p (IsNoetherian.noetherian _) ?_⟩
    rw [top_inf_eq, ← h2, LinearMap.range_eq_map]
    exact Submodule.FG.map _ Module.Finite.fg_top
  have e1 := LinearMap.finrank_range_add_finrank_ker β
  have e2 := LinearMap.finrank_range_add_finrank_ker p
  have e3 := LinearMap.finrank_range_of_inj h0
  rw [← h1, h2] at e1
  omega

private theorem cob_lc {k Γ M : Type} [Field k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [AddCommGroup M] [Module k M] (ρ : Representation k Γ M) (h : IsOpen (ρ.ker : Set Γ)) (m : M) :
    IsLocallyConstant (fun g => ρ g m - m) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (ρ.ker : Set Γ), h.preimage (by fun_prop), by simp, fun y hy => ?_⟩
  have hy' : ρ (x⁻¹ * y) = 1 := hy
  have : ρ y = ρ x := by
    conv_lhs => rw [← mul_inv_cancel_left x y, map_mul, hy', mul_one]
  rw [this]

theorem UpperTheory.V.Alg.finrank_compact_support_H1 :
    ∀ (k Γ M : Type) [Field k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M] [ContinuousConstSMul k M]
      (ρ : Representation k Γ M), IsOpen (ρ.ker : Set Γ) → ∀ (F : Frame Γ), (∀ q, ∀ n ∈ F.N q, ρ (F.ψ q n) = 1) → Module.Finite k (ReciprocityTheory.Gal.H1 ρ) →
      Module.finrank k (ReciprocityTheory.Gal.H0 ρ) + Module.finrank k (F.H1c ρ) = ∑ v, Module.finrank k (ReciprocityTheory.Gal.H0 (ρ.comp (F.φ v) : Representation k _ M)) +
        Module.finrank k (ReciprocityTheory.Gal.Sha1 ρ F.φ F.hφ ⊓ ReciprocityTheory.Gal.Sel ρ F.ψ F.hψ (fun q => ReciprocityTheory.Gal.H1ur (ρ.comp (F.ψ q) : Representation k _ M) (F.N q)) : Submodule k (ReciprocityTheory.Gal.H1 ρ)) := by
  intro k Γ M _ _ _ _ _ _ _ _ _ _ _ ρ hρ F hN hfin
  classical
  let δ : ReciprocityTheory.Gal.H0 ρ →ₗ[k] (∀ v, ReciprocityTheory.Gal.H0 (ρ.comp (F.φ v) : Representation k _ M)) :=
    LinearMap.pi fun v => ReciprocityTheory.Gal.resH0 ρ (F.φ v)
  let β : (∀ v, ReciprocityTheory.Gal.H0 (ρ.comp (F.φ v) : Representation k _ M)) →ₗ[k] F.H1c ρ :=
    { toFun := fun b => ⟨(fun g => ρ g (-(b F.v0).1) - (-(b F.v0).1), fun v => (b v).1 - (b F.v0).1),
        cob_lc ρ hρ _, fun s t => by
          simp only [map_mul, Module.End.mul_apply, map_sub]; abel,
        fun q n hn => by simp [hN q n hn],
        fun v s => by
          have : ρ (F.φ v s) (b v).1 = (b v).1 := (b v).2 s
          simp only [map_sub, map_neg, this]; abel,
        sub_self _⟩
      map_add' := fun b b' => by
        apply Subtype.ext
        refine Prod.ext (funext fun g => ?_) (funext fun v => ?_)
        · simp; abel
        · simp; abel
      map_smul' := fun c b => by
        apply Subtype.ext
        refine Prod.ext (funext fun g => ?_) (funext fun v => ?_)
        · simp [smul_add]
        · simp [smul_sub] }
  let p0 : F.H1c ρ →ₗ[k] ReciprocityTheory.Gal.Z1 ρ :=
    { toFun := fun x => ⟨x.1.1, x.2.1.continuous, x.2.2.1⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let p : F.H1c ρ →ₗ[k] ReciprocityTheory.Gal.H1 ρ := (Submodule.mkQ _).comp p0
  have h0 : Function.Injective δ := by
    intro x y hxy
    have := congrArg (fun b => (b F.v0).1) hxy
    exact Subtype.ext this
  have h1 : LinearMap.range δ = LinearMap.ker β := by
    ext b
    rw [LinearMap.mem_ker]
    constructor
    · rintro ⟨m, rfl⟩
      apply Subtype.ext
      refine Prod.ext (funext fun g => ?_) (funext fun v => ?_)
      · change ρ g (-m.1) - (-m.1) = 0
        rw [map_neg, (ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere ρ m.1).1 m.2 g, sub_self]
      · exact sub_self m.1
    · intro hb
      have e1 : ∀ g, ρ g (-(b F.v0).1) - (-(b F.v0).1) = 0 := fun g =>
        congrArg (fun x : F.H1c ρ => x.1.1 g) hb
      have e2 : ∀ v, (b v).1 - (b F.v0).1 = 0 := fun v =>
        congrArg (fun x : F.H1c ρ => x.1.2 v) hb
      refine ⟨⟨(b F.v0).1, (ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere ρ _).2 fun g => ?_⟩, funext fun v => Subtype.ext ?_⟩
      · have := e1 g
        rw [map_neg, sub_eq_zero] at this
        exact neg_injective this
      · exact (sub_eq_zero.1 (e2 v)).symm
  have h2 : LinearMap.range β = LinearMap.ker p := by
    ext x
    rw [LinearMap.mem_ker]
    change _ ↔ Submodule.Quotient.mk (p0 x) = 0
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, ReciprocityTheory.Gal.mem_coboundaries1]
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨-(b F.v0).1, fun g => rfl⟩
    · rintro ⟨m, hm⟩
      have hm' : ∀ g, x.1.1 g = ρ g m - m := hm
      obtain ⟨-, -, -, a4, a5⟩ := x.2
      refine ⟨fun v => ⟨x.1.2 v - m, (ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere _ _).2 fun s => ?_⟩, ?_⟩
      · change ρ (F.φ v s) (x.1.2 v - m) = x.1.2 v - m
        have := a4 v s
        rw [hm'] at this
        rw [map_sub, sub_eq_sub_iff_sub_eq_sub, this]
      · apply Subtype.ext
        refine Prod.ext (funext fun g => ?_) (funext fun v => ?_)
        · change ρ g (-(x.1.2 F.v0 - m)) - (-(x.1.2 F.v0 - m)) = x.1.1 g
          rw [a5, hm']; simp
        · change x.1.2 v - m - (x.1.2 F.v0 - m) = x.1.2 v
          rw [a5]; abel
  have key : ∀ c : ReciprocityTheory.Gal.Z1 ρ, (Submodule.Quotient.mk c : ReciprocityTheory.Gal.H1 ρ) ∈
      (ReciprocityTheory.Gal.Sha1 ρ F.φ F.hφ ⊓ ReciprocityTheory.Gal.Sel ρ F.ψ F.hψ (fun q => ReciprocityTheory.Gal.H1ur (ρ.comp (F.ψ q) : Representation k _ M) (F.N q)) : Submodule k (ReciprocityTheory.Gal.H1 ρ)) ↔
      (∀ v, ∃ m, ∀ s, c.1 (F.φ v s) = ρ (F.φ v s) m - m) ∧ ∀ q, ∀ n ∈ F.N q, c.1 (F.ψ q n) = 0 := by
    intro c
    rw [Submodule.mem_inf, ReciprocityTheory.Gal.mem_Sel, ReciprocityTheory.Gal.Sha1, Submodule.mem_iInf]
    refine and_congr (forall_congr' fun v => ?_) (forall_congr' fun q => ?_)
    · rw [LinearMap.mem_ker, ReciprocityTheory.Gal.resH1, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_comap, ReciprocityTheory.Gal.mem_coboundaries1]
      rfl
    · rw [ReciprocityTheory.Gal.H1ur, LinearMap.mem_ker, ReciprocityTheory.Gal.resH1]
      refine (Submodule.Quotient.mk_eq_zero _).trans ?_
      rw [ Submodule.mem_comap, ReciprocityTheory.Gal.mem_coboundaries1]
      constructor
      · rintro ⟨m, hm⟩ n hn
        have : c.1 (F.ψ q n) = ρ (F.ψ q n) m - m := hm ⟨n, hn⟩
        rw [this, hN q n hn]; simp
      · intro h
        refine ⟨0, fun n => ?_⟩
        change c.1 (F.ψ q n.1) = ρ (F.ψ q n.1) 0 - 0
        rw [h n.1 n.2]; simp
  have h3 : LinearMap.range p = (ReciprocityTheory.Gal.Sha1 ρ F.φ F.hφ ⊓ ReciprocityTheory.Gal.Sel ρ F.ψ F.hψ (fun q => ReciprocityTheory.Gal.H1ur (ρ.comp (F.ψ q) : Representation k _ M) (F.N q)) : Submodule k (ReciprocityTheory.Gal.H1 ρ)) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨-, -, a3, a4, -⟩ := x.2
      exact (key (p0 x)).2 ⟨fun v => ⟨x.1.2 v, a4 v⟩, a3⟩
    · intro hy
      obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      obtain ⟨k1, k2⟩ := (key c).1 hy
      choose m hm using k1
      refine ⟨⟨(fun g => c.1 g - (ρ g (m F.v0) - m F.v0), fun v => m v - m F.v0),
        ((IsLocallyConstant.iff_continuous _).2 c.2.1).sub (cob_lc ρ hρ _), fun s t => ?_, fun q n hn => ?_,
        fun v s => ?_, sub_self _⟩, ?_⟩
      · simp only [c.2.2 s t, map_mul, Module.End.mul_apply, map_sub]; abel
      · simp [k2 q n hn, hN q n hn]
      · simp only [hm, map_sub]; abel
      · change Submodule.Quotient.mk _ = _
        rw [Submodule.Quotient.eq, Submodule.mem_comap, ReciprocityTheory.Gal.mem_coboundaries1]
        refine ⟨-m F.v0, fun g => ?_⟩
        change c.1 g - (ρ g (m F.v0) - m F.v0) - c.1 g = _
        rw [map_neg]; abel
  have := krull_dim_quotient_comap_eq δ β p h0 h1 h2
  rw [h3, Module.finrank_pi_fintype] at this
  exact this
end

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem UpperTheory.V.Alg.monomial_mem_weight_zero {O σ X : Type} [CommRing O] [AddCommGroup X] (wt : σ → X)
    (m : σ →₀ ℕ) (hm : Finsupp.weight wt m = 0) : (monomial m (1 : O) : MvPowerSeries σ O) ∈ wtPart O wt 0 := by
  classical
  intro n hn
  rw [coeff_monomial, if_neg]
  rintro rfl
  exact hn hm

theorem UpperTheory.V.Alg.wPres_maximalIdeal_gr_zero_eq_sup_span_monomials :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ [IsCO O (W.gr 0)], (∀ b : W.gr 0, b ∈ maximalIdeal (W.gr 0) ↔ ((b : W.A) : R) ∈ maximalIdeal R) ∧
      ∃ u : Finset (W.gr 0), (∀ b ∈ u, ∃ n : W.σ →₀ ℕ, n ≠ 0 ∧ Finsupp.weight W.wt n = 0 ∧ ((b : W.A) : R) = n.prod fun s k => W.z s ^ k) ∧
        maximalIdeal (W.gr 0) = (maximalIdeal O).map (algebraMap O (W.gr 0)) ⊔ Ideal.span (u : Set (W.gr 0)) := by
  intro O _ _ _ _ X _ _ _ _ R _ _ _ W hz _
  classical
  let φ : W.gr 0 →ₐ[O] R :=
    { toFun := fun b => ((b : W.A) : R)
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have hφ : ∀ b : W.gr 0, φ b = ((b : W.A) : R) := fun _ => rfl
  have hinj : Function.Injective φ := fun a b h => Subtype.ext (Subtype.ext h)
  have h1 : ∀ b : W.gr 0, b ∈ maximalIdeal (W.gr 0) ↔ ((b : W.A) : R) ∈ maximalIdeal R := fun b => by
    rw [← hφ, ← res_eq_zero_iff O, ← res_eq_zero_iff O, res_map]
  refine ⟨h1, ?_⟩
  let mk : ∀ f : MvPowerSeries W.σ O, f ∈ wtPart O W.wt 0 → W.gr 0 := fun f hf =>
    ⟨⟨W.π f, W.part_le_A (j := 0) ⟨f, hf, rfl⟩⟩, ⟨f, hf, rfl⟩⟩
  have hmk : ∀ f hf, φ (mk f hf) = W.π f := fun _ _ => rfl
  obtain ⟨μ, hμ, hspan⟩ := UpperTheory.V.Alg.part_span O R X W {n | n ≠ 0 ∧ Finsupp.weight W.wt n = 0} 0
    (fun n hn => hn.2)
  let U : μ → W.gr 0 := fun m => mk (monomial m.1 1) (UpperTheory.V.Alg.monomial_mem_weight_zero W.wt m.1 (hμ m.2).2)
  have hU : ∀ m : μ, φ (U m) = m.1.prod fun s k => W.z s ^ k := fun m => by
    show W.π (monomial m.1 1) = _
    rw [monomial_one_eq, Finsupp.prod, Finsupp.prod, map_prod]
    simp only [map_pow, WPres.z]
  have hUm : ∀ m : μ, U m ∈ maximalIdeal (W.gr 0) := fun m => by
    rw [h1, ← hφ, hU]
    obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.2 (hμ m.2).1
    exact Ideal.prod_mem _ hs (Ideal.pow_mem_of_mem _ (hz s) _
      (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hs)))
  have hle : Ideal.span ((Finset.univ.image U : Finset (W.gr 0)) : Set (W.gr 0)) ≤ maximalIdeal (W.gr 0) := by
    rw [Ideal.span_le]
    intro b hb
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hb)
    exact hUm m
  refine ⟨Finset.univ.image U, fun b hb => ?_, le_antisymm (fun b hb => ?_) (sup_le ?_ hle)⟩
  · obtain ⟨m, -, rfl⟩ := Finset.mem_image.1 hb
    exact ⟨m.1, (hμ m.2).1, (hμ m.2).2, hU m⟩
  · obtain ⟨f, hf, hfb⟩ : ((b : W.A) : R) ∈ W.part 0 := b.2
    obtain ⟨c, hc, hsum⟩ := hspan (f - C (constantCoeff f)) (fun n hn => by
      rw [map_sub, coeff_C]
      by_cases h0 : n = 0
      · subst h0; simp
      · rw [if_neg h0, sub_zero]
        exact hf n fun h => hn ⟨h0, h⟩)
    have hb' : b - algebraMap O (W.gr 0) (constantCoeff f) = ∑ m : μ, mk (c m.1) (hc m.1) * U m := by
      apply hinj
      have h2 := congrArg W.π hsum

      rw [map_sub, map_sum, ← Finset.sum_coe_sort] at h2

      rw [map_sub, map_sum, AlgHom.commutes, hφ, ← hfb, ← W.π.commutes]
      simp only [map_mul] at h2 ⊢
      exact h2
    have hs : b - algebraMap O (W.gr 0) (constantCoeff f) ∈
        Ideal.span ((Finset.univ.image U : Finset (W.gr 0)) : Set (W.gr 0)) := by
      rw [hb']
      exact Ideal.sum_mem _ fun m _ => Ideal.mul_mem_left _ _
        (Ideal.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem U (Finset.mem_univ m))))
    have h3 : algebraMap O (W.gr 0) (constantCoeff f) ∈ maximalIdeal (W.gr 0) := by
      simpa using Ideal.sub_mem _ hb (hle hs)
    have h4 : constantCoeff f ∈ maximalIdeal O := fun h => h3 (h.map _)
    rw [← add_sub_cancel (algebraMap O (W.gr 0) (constantCoeff f)) b]
    exact Submodule.add_mem_sup (Ideal.mem_map_of_mem _ h4) hs
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha h
    exact ha (IsLocalHom.map_nonunit a h)
end
