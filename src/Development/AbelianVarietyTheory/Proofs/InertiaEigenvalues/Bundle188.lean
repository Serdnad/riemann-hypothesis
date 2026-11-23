module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsEqAlgebraMapAddPowMul
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InstTameDescentExponentDataPadicThree
public import Mathlib.RingTheory.FiniteLength
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle155
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemXSmulOfProjective
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle065
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle169
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle108
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle170
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
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDiscExtensionTateElement
public import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

noncomputable section

namespace GlobalTheory.BK

open PowerSeries

theorem exists_pow_smul_eq_zero_of_isFiniteLength {R : Type} [CommRing R] (r : R)
    (hr : ∀ b : R, IsUnit (1 - b * r)) (M : Type) [AddCommGroup M] [Module R M]
    (h : IsFiniteLength R M) : ∃ n : ℕ, ∀ m : M, r ^ n • m = 0 := by
  induction h with
  | of_subsingleton => exact ⟨0, fun m => Subsingleton.elim _ _⟩
  | @of_simple_quotient M _ _ N hs _ ih =>
    obtain ⟨n, hn⟩ := ih
    have hS : ∀ q : M ⧸ N, r • q = 0 := by
      intro q
      by_contra hq
      have htop : (R ∙ (r • q)) = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left
        (by rwa [Submodule.span_singleton_eq_bot])
      obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 (htop ▸ Submodule.mem_top : q ∈ R ∙ (r • q))
      have h1 : (1 - b * r) • q = 0 := by rw [sub_smul, one_smul, mul_smul, hb, sub_self]
      have h2 : q = 0 := (hr b).smul_eq_zero.1 h1
      exact hq (by rw [h2, smul_zero])
    refine ⟨n + 1, fun m => ?_⟩
    have hm : r • m ∈ N := by
      have := hS (N.mkQ m)
      rwa [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
    have := hn ⟨_, hm⟩
    rw [pow_succ, mul_smul]
    simpa using congrArg Subtype.val this

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]

theorem isUnit_one_sub_mul_l (b : A O K) : IsUnit (1 - b * (l : A O K)) := by
  set f : A O K := 1 - b * (l : A O K)
  set g := (equivA O K).symm f
  have hg : equivA O K g = f := AlgEquiv.apply_symm_apply _ _
  suffices IsUnit g by simpa [hg] using this.map (equivA O K)
  rw [PowerSeries.isUnit_iff_constantCoeff]
  have h0 : algebraMap O K (constantCoeff g) = 1 - constantCoeff (b : K⟦X⟧) * l := by
    calc algebraMap O K (constantCoeff g) = constantCoeff ((equivA O K g : A O K) : K⟦X⟧) := by
          rw [coe_equivA, ← coeff_zero_eq_constantCoeff_apply (map _ g), coeff_map,
            coeff_zero_eq_constantCoeff_apply]
      _ = 1 - constantCoeff (b : K⟦X⟧) * l := by
          rw [hg]
          simp only [f, Subalgebra.coe_sub, Subalgebra.coe_one, Subalgebra.coe_mul,
            map_sub, map_one, map_mul]
          congr 2
  have hlt : ‖constantCoeff (b : K⟦X⟧) * (l : K)‖ < 1 := by
    rw [norm_mul]
    have hb : ‖constantCoeff (b : K⟦X⟧)‖ ≤ 1 := by
      simpa using (mem_A.1 b.2) 0
    calc _ ≤ 1 * ‖(l : K)‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact norm_l_lt_one (K := K) l
  have hn : ‖algebraMap O K (constantCoeff g)‖ = 1 := by
    rw [h0, sub_eq_add_neg, add_comm, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by rw [norm_neg, norm_one]; exact hlt.ne), norm_neg, norm_one, max_eq_right hlt.le]
  have hne : algebraMap O K (constantCoeff g) ≠ 0 := by
    intro h; rw [h, norm_zero] at hn; exact zero_ne_one hn
  obtain ⟨c, hc⟩ := (IsUnitBall.mem_range_iff (O := O) (algebraMap O K (constantCoeff g))⁻¹).2
    (by rw [norm_inv, hn, inv_one])
  refine IsUnit.of_mul_eq_one c (IsUnitBall.inj (K := K) ?_)
  rw [map_mul, hc, mul_inv_cancel₀ hne, map_one]

theorem exists_l_pow_smul_eq_app_of_isFiniteLength_coker (O K : Type) [CommRing O] [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ μ : Type) [Fintype κ]
    [DecidableEq κ] [Fintype μ] [DecidableEq μ] (Q : PhiMod O K l e a κ) (T : PhiMod O K l e a μ)
    (G : GlobalTheory.BK.Hom Q T) :
    IsFiniteLength (A O K) G.coker → ∃ n : ℕ, ∀ y ∈ T.M, ∃ x ∈ Q.M, G.app x = (l : K) ^ n • y := by
  intro h
  obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_isFiniteLength (l : A O K)
    (isUnit_one_sub_mul_l l) _ h
  refine ⟨n, fun y hy => ?_⟩
  have h1 := hn (Submodule.Quotient.mk ⟨y, hy⟩)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h1
  change _ ∈ (G.imM).comap T.M.subtype at h1
  rw [Submodule.mem_comap, Hom.imM, Submodule.mem_map] at h1
  obtain ⟨x, hx, hxy⟩ := h1
  refine ⟨x, hx, ?_⟩
  rw [LinearMap.restrictScalars_apply] at hxy
  rw [hxy]
  ext τ i
  simp [Algebra.smul_def]

end GlobalTheory.BK
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp

noncomputable section

namespace GlobalTheory.HWL.Mat

section Abstract

variable {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {N : Submodule A M} {r : ℕ}

theorem coeff_ext (nb : Module.Basis (Fin r) A ↥N) {a b : Fin r → A}
    (h : ∑ i, a i • (nb i : M) = ∑ i, b i • (nb i : M)) (i : Fin r) : a i = b i := by
  have hli : LinearIndependent A (fun i => (nb i : M)) :=
    nb.linearIndependent.map' N.subtype (Submodule.ker_subtype N)
  exact Fintype.linearIndependent_iffₛ.1 hli a b h i

theorem eq_sum (nb : Module.Basis (Fin r) A ↥N) {x : M} (hx : x ∈ N) :
    x = ∑ i, nb.repr ⟨x, hx⟩ i • (nb i : M) := by
  have h := congrArg N.subtype (nb.sum_repr ⟨x, hx⟩)

  rw [map_sum] at h
  simpa using h.symm

theorem semi_sum {f : M →+ M} {σ : A → A} (hf : ∀ a x, f (a • x) = σ a • f x) (a : Fin r → A)
    (x : Fin r → M) : f (∑ i, a i • x i) = ∑ i, σ (a i) • f (x i) := by

  rw [map_sum]; exact Finset.sum_congr rfl fun i _ => hf _ _

theorem sum_sum (P C : Matrix (Fin r) (Fin r) A) (e : Fin r → M) (j : Fin r) :
    ∑ k, C k j • ∑ i, P i k • e i = ∑ i, (P * C) i j • e i := by
  simp only [Finset.smul_sum, Matrix.mul_apply, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by rw [mul_comm]

theorem common_exp (S : Submodule A M) (Q : A) (x : Fin r → M) (h : ∀ j, ∃ k : ℕ, Q ^ k • x j ∈ S) :
    ∃ m : ℕ, ∀ j, Q ^ m • x j ∈ S := by
  choose k hk using h
  refine ⟨∑ j, k j, fun j => ?_⟩
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le
    (Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
  rw [hc, add_comm, pow_add, mul_smul]
  exact S.smul_mem _ (hk j)

theorem exists_matrices {Γ : Type} [Mul Γ] (nb : Module.Basis (Fin r) A ↥N) (Q π : A)
    (φ : M →+ M) (σ : A → A) (hφ : ∀ a x, φ (a • x) = σ a • φ x)
    (γ : Γ → M →+ M) (τ : Γ → A →+* A) (hγ : ∀ g a x, γ g (a • x) = τ g a • γ g x)
    (hmul : ∀ g h x, γ (g * h) x = γ g (γ h x)) (hcomm : ∀ g x, φ (γ g x) = γ g (φ x))
    (hNφ : ∀ x ∈ N, ∃ k : ℕ, Q ^ k • φ x ∈ N)
    (hNinv : ∀ y ∈ N, ∃ k : ℕ, Q ^ k • y ∈ Submodule.span A (φ '' (N : Set M)))
    (hNΓ : ∀ g, ∀ x ∈ N, γ g x ∈ N) (hNπ : ∀ g, ∀ x ∈ N, ∃ y ∈ N, γ g x - x = π • y) :
    ∃ (m m' : ℕ) (Gm : Γ → Matrix (Fin r) (Fin r) A) (Pm Pm' : Matrix (Fin r) (Fin r) A),
      (∀ g h, Gm (g * h) = Gm g * (Gm h).map (τ g)) ∧
      (∀ g i j, ∃ c, Gm g i j = (if i = j then 1 else 0) + π * c) ∧
      Pm * Pm' = (Q ^ m') • (1 : Matrix (Fin r) (Fin r) A) ∧
      (∀ g, (τ g Q ^ m) • (Pm * (Gm g).map σ) = (Q ^ m) • (Gm g * Pm.map (τ g))) ∧
      (∀ g j, γ g (nb j : M) = ∑ i, Gm g i j • (nb i : M)) ∧
      ∀ j, Q ^ m • φ (nb j : M) = ∑ i, Pm i j • (nb i : M) := by
  classical
  obtain ⟨m, hm⟩ := common_exp N Q (fun j => φ (nb j : M)) fun j => hNφ _ (nb j).2
  obtain ⟨k, hk⟩ := common_exp _ Q (fun j => (nb j : M)) fun j => hNinv _ (nb j).2
  have hspan : Submodule.span A (φ '' (N : Set M)) ≤
      Submodule.span A (Set.range fun i => φ (nb i : M)) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [eq_sum nb hx, semi_sum hφ]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun A).1 (hspan (hk j))
  obtain ⟨Gm, hG⟩ : ∃ Gm : Γ → Matrix (Fin r) (Fin r) A,
      ∀ g j, γ g (nb j : M) = ∑ i, Gm g i j • (nb i : M) :=
    ⟨fun g i j => nb.repr ⟨_, hNΓ g _ (nb j).2⟩ i, fun g j => eq_sum nb _⟩
  obtain ⟨Pm, hP⟩ : ∃ Pm : Matrix (Fin r) (Fin r) A,
      ∀ j, Q ^ m • φ (nb j : M) = ∑ i, Pm i j • (nb i : M) :=
    ⟨fun i j => nb.repr ⟨_, hm j⟩ i, fun j => eq_sum nb _⟩
  have hone : ∀ (a : A) (j : Fin r),
      ∑ i, (a * if i = j then 1 else 0) • (nb i : M) = a • (nb j : M) := by
    intro a j
    rw [Finset.sum_eq_single j] <;> simp +contextual
  refine ⟨m, m + k, Gm, Pm, Matrix.of fun i j => c j i, ?_, ?_, ?_, ?_, hG, hP⟩
  · intro g h
    ext i j
    refine coeff_ext nb (a := fun i => Gm (g * h) i j)
      (b := fun i => (Gm g * (Gm h).map (τ g)) i j) ?_ i
    rw [← hG, hmul, hG h, semi_sum (hγ g), ← sum_sum]
    simp only [hG, Matrix.map_apply]
  · intro g i j
    obtain ⟨y, hy, e⟩ := hNπ g _ (nb j).2
    refine ⟨nb.repr ⟨y, hy⟩ i, ?_⟩
    refine coeff_ext nb (a := fun i => Gm g i j)
      (b := fun i => (if i = j then 1 else 0) + π * nb.repr ⟨y, hy⟩ i) ?_ i
    have h1 := hone 1 j
    simp only [one_mul, one_smul] at h1
    simp only [add_smul, Finset.sum_add_distrib, mul_smul]
    rw [← hG, h1, ← Finset.smul_sum, ← eq_sum nb hy, ← e]
    abel
  · ext i j
    refine coeff_ext nb (a := fun i => (Pm * Matrix.of fun i j => c j i) i j)
      (b := fun i => ((Q ^ (m + k)) • (1 : Matrix (Fin r) (Fin r) A)) i j) ?_ i
    rw [← sum_sum]
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, hone, ← hP, Matrix.of_apply]
    rw [pow_add, mul_smul, ← hc j, Finset.smul_sum]
    exact Finset.sum_congr rfl fun l _ => smul_comm _ _ _
  · intro g
    ext i j
    refine coeff_ext nb (a := fun i => ((τ g Q ^ m) • (Pm * (Gm g).map σ)) i j)
      (b := fun i => ((Q ^ m) • (Gm g * Pm.map (τ g))) i j) ?_ i
    simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum]
    rw [← sum_sum, ← sum_sum]
    have h1 : ∑ k, (Gm g).map σ k j • ∑ i, Pm i k • (nb i : M) = Q ^ m • γ g (φ (nb j : M)) := by
      rw [← hcomm, hG, semi_sum hφ, Finset.smul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [← hP, smul_comm, Matrix.map_apply]
    have h2 : ∑ k, Pm.map (τ g) k j • ∑ i, Gm g i k • (nb i : M) =
        τ g Q ^ m • γ g (φ (nb j : M)) := by
      rw [← map_pow, ← hγ, hP, semi_sum (hγ g)]
      exact Finset.sum_congr rfl fun l _ => by rw [← hG, Matrix.map_apply]
    rw [h1, h2, smul_comm]

end Abstract

theorem wach_matrices : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ} {Γ : WGam PD LL O v n s} {R : WSer Γ} {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai] {RW : Type} [CommRing RW] [Algebra O RW] {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai} {I : WIo R (O ⊗[Zl] Ai) RW inclR φR gR πA} {E : WEt I} {zl : PowerSeries Zl →+* LetA O n} (Mo : WN E zl) (T : LocLat G Qp LL O) (r : ℕ) (nb : Module.Basis (Fin r) (LetA O n) ↥(Mo.N T)), ∃ (m m' : ℕ) (Gm : Γ.Gam → Matrix (Fin r) (Fin r) (LetA O n)) (Pm Pm' : Matrix (Fin r) (Fin r) (LetA O n)), (∀ g h, Gm (g * h) = Gm g * (Gm h).map (letγ (R.γ₀ g))) ∧ (∀ g i j k, PowerSeries.constantCoeff (Gm g i j k) = if i = j then 1 else 0) ∧ Pm * Pm' = (R.Q ^ m') • (1 : Matrix (Fin r) (Fin r) (LetA O n)) ∧ (∀ g, (letγ (R.γ₀ g) R.Q ^ m) • (Pm * (Gm g).map (letφ R.φ₀)) = (R.Q ^ m) • (Gm g * Pm.map (letγ (R.γ₀ g)))) ∧ (∀ g j, E.γD T g (nb j : E.DD T) = ∑ i, Gm g i j • (nb i : E.DD T)) ∧ ∀ j, R.Q ^ m • E.φD T (nb j : E.DD T) = ∑ i, Pm i j • (nb i : E.DD T) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n s Γ R Zl Ai _ _ _ _
    RW _ _ inclR φR gR πA I E zl Mo T r nb
  have hφ : ∀ (a : LetA O n) (x : E.DD T), E.φD T (a • x) = letφ R.φ₀ a • E.φD T x := by
    intro a x
    rw [← algebraMap_smul R.EE a x, E.φD_smul, R.φE_ext, algebraMap_smul]
  have hγ : ∀ g (a : LetA O n) (x : E.DD T),
      E.γD T g (a • x) = letγ (R.γ₀ g) a • E.γD T g x := by
    intro g a x
    rw [← algebraMap_smul R.EE a x, E.γD_smul, R.γE_ext, algebraMap_smul]
  obtain ⟨m, m', Gm, Pm, Pm', h1, h2, h3, h4, h5, h6⟩ :=
    exists_matrices nb R.Q letπ (E.φD T).toAddMonoidHom (letφ R.φ₀) hφ
      (fun g => (E.γD T g).toAddMonoidHom) (fun g => (letγ (n := n) (R.γ₀ g)).toRingHom) hγ
      (E.γD_mul T) (E.φγ_comm T) (Mo.N_φ T) (Mo.N_φinv T) (Mo.N_Γ T) (Mo.N_π T)
  refine ⟨m, m', Gm, Pm, Pm', h1, ?_, h3, h4, h5, h6⟩
  intro g i j k
  obtain ⟨c, hc⟩ := h2 g i j
  rw [hc]
  split_ifs <;> simp [letπ]

end GlobalTheory.HWL.Mat
end
end

section

open PowerSeries Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL


open PowerSeries TensorProduct in
theorem _root_.GlobalTheory.HWL.mem_smul_of_projective_comp {D A M : Type} [CommRing D] [IsDomain D] [CommRing A]
    [AddCommGroup M] [Module A M] (f : D⟦X⟧ →+* A)
    (hp : @Module.Projective D⟦X⟧ _ M _ (Module.compHom _ f)) (c : D) (hc : c ≠ 0) {a b : A}
    (ha : f (C c) = a) (hb : f X = b) (x y : M) (h : a • x = b • y) : ∃ z : M, x = b • z := by
  letI : Module D⟦X⟧ M := Module.compHom M f
  obtain ⟨z, hz⟩ := _root_.GlobalTheory.WachFree.mem_X_smul_of_projective c hc x y (by
    change f (C c) • x = f X • y
    rw [ha, hb]
    exact h)
  refine ⟨z, ?_⟩
  rw [hz]
  change f X • z = b • z
  rw [hb]

open PowerSeries TensorProduct in
private theorem isSMulRegular_of_projective_powerSeries_comp_lemma {D A M : Type} [CommRing D]
    [IsDomain D] [CommRing A] [AddCommGroup M] [Module A M] (f : D⟦X⟧ →+* A)
    (hp : @Module.Projective D⟦X⟧ _ M _ (Module.compHom _ f)) {b : A} (hb : f X = b) :
    IsSMulRegular M b := by
  letI : Module D⟦X⟧ M := Module.compHom M f
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (R := D⟦X⟧) (M := M)
    (mem_nonZeroDivisors_of_ne_zero (X_ne_zero : (X : D⟦X⟧) ≠ 0))
  intro x y h
  apply hreg
  change f X • x = f X • y
  rw [hb]
  exact h


open PowerSeries TensorProduct in
set_option maxHeartbeats 8000000 in
theorem _root_.GlobalTheory.HWL.lattice_free : ∀ (l : ℕ) [Fact l.Prime] (P : _root_.Formalism.BasicNotions.LocPrime l) (AI : _root_.Formalism.BasicNotions.LocAinf l P) (K : _root_.Formalism.BasicNotions.Loc.FinExt l) (s : ℕ) (LL : _root_.Formalism.BasicNotions.Loc.FinExt l), _root_.Formalism.BasicNotions.Loc.Good K s LL → ∀ (Γ : _root_.GlobalTheory.HWL.GamS P K s LL) (R : _root_.GlobalTheory.HWL.WSer Γ) (I : _root_.GlobalTheory.HWL.IoS AI R), _root_.GlobalTheory.HWL.IoW I → ∀ (E : _root_.GlobalTheory.HWL.WEt I) (Mo : _root_.GlobalTheory.HWL.NS E) (T : _root_.Formalism.BasicNotions.LocLat ↥(_root_.Formalism.BasicNotions.Loc.GK K) ℚ_[l] ↥LL.1 ↥(_root_.Formalism.BasicNotions.Loc.OL LL)), _root_.Formalism.WeaklyAdmissibleFiltrations.IsCrys (P.PD K) T.ρ → Nonempty (Module.Basis (Fin (Module.finrank ↥(_root_.Formalism.BasicNotions.Loc.OL LL) ↥T.L.T)) (_root_.Formalism.BasicNotions.LetA ↥(_root_.Formalism.BasicNotions.Loc.OL LL) (Module.finrank ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.K0 K))) ↥(Mo.N T)) := by
  set_option synthInstance.maxHeartbeats 400000 in
    intro l _ P AI K s LL _ Γ R I _ E Mo T hc
    obtain ⟨_, -, hl⟩ := _root_.GlobalTheory.FinExtIntegers.dvr_complete LL
    have hfree := E.DD_free T
    haveI := hfree.1
    haveI : FiniteDimensional ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.K0 K) := by
      haveI := K.2
      have hle : _root_.Formalism.BasicNotions.Loc.K0 K ≤ ↑K := inf_le_left
      exact Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
        (IntermediateField.inclusion hle).toRingHom.injective
    haveI : NeZero (Module.finrank ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.K0 K)) := ⟨Module.finrank_pos.ne'⟩
    haveI : Module.Finite _ (Mo.N T) :=
      Module.Finite.iff_fg.mpr (Mo.N_fg T)
    have hl0 : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
    have hzX : _root_.Formalism.BasicNotions.Loc.zlA LL (Module.finrank ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.K0 K)) X = fun _ => X := by
      ext1; simp [_root_.Formalism.BasicNotions.Loc.zlA]
    have hzC : _root_.Formalism.BasicNotions.Loc.zlA LL (Module.finrank ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.K0 K)) (C (l : ℤ_[l])) =
        fun _ => C (l : _root_.Formalism.BasicNotions.Loc.OL LL) := by
      ext1; simp [_root_.Formalism.BasicNotions.Loc.zlA]
    have key := _root_.GlobalTheory.WachFree.basis_of_regular
      (ι := ZMod (Module.finrank ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.K0 K)))
      (O := ↥(_root_.Formalism.BasicNotions.Loc.OL LL))
      (N := ↥(Mo.N T)) (E := R.EE) (D := E.DD T) R.EE_inj
      (Mo.N T).subtype (Mo.N_base T hc) (l : _root_.Formalism.BasicNotions.Loc.OL LL) ?_ hl ?_ ?_
    · rwa [hfree.2] at key
    · intro h0
      haveI : CharZero ↥LL.1 :=
        charZero_of_injective_algebraMap (algebraMap ℚ_[l] ↥LL.1).injective
      have hcast : ((l : _root_.Formalism.BasicNotions.Loc.OL LL) : ↥LL.1) = 0 := by rw [h0]; rfl
      push_cast at hcast
      exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast hcast)
    · exact isSMulRegular_of_projective_powerSeries_comp_lemma _ (Mo.N_proj T) hzX
    · intro x y h
      exact _root_.GlobalTheory.HWL.mem_smul_of_projective_comp (_root_.Formalism.BasicNotions.Loc.zlA LL _) (Mo.N_proj T)
        (l : ℤ_[l]) hl0 hzC hzX x y h

end GlobalTheory.HWL
end

section

noncomputable section
namespace GlobalTheory.PhiGam.PolarKernel
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam Module

section lin
variable {k : Type} [Field k] {U : Type} [AddCommGroup U] [Module k U]

theorem finrank_quot (A B : Submodule k U) :
    finrank k (↥A ⧸ B.submoduleOf A) = finrank k (A.map B.mkQ) := by
  have h := (LinearMap.quotKerEquivRange (B.mkQ.domRestrict A)).finrank_eq
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ] at h
  exact h

theorem finrank_le_gmult (T : Module.End k U) (P Q Z S : Submodule k U) [FiniteDimensional k S]
    (hP : P ≤ S ⊔ Q) (hZ : ∀ x ∈ Z, x ∈ P ∧ T x ∈ Q) :
    finrank k (↥Z ⧸ Q.submoduleOf Z) ≤ gmult T P Q 0 := by
  unfold gmult
  rw [finrank_quot, finrank_quot, map_zero (algebraMap k (Module.End k U)), sub_zero]
  have hfin : FiniteDimensional k ((P ⊓ ⨆ m : ℕ, Q.comap (T ^ m)).map Q.mkQ) := by
    have h : (P ⊓ ⨆ m : ℕ, Q.comap (T ^ m)).map Q.mkQ ≤ S.map Q.mkQ := by
      have := Submodule.map_mono (f := Q.mkQ) ((inf_le_left (b := ⨆ m : ℕ, Q.comap (T ^ m))).trans hP)
      rwa [Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq] at this
    exact Submodule.finiteDimensional_of_le h
  refine Submodule.finrank_mono (Submodule.map_mono fun x hx => ⟨(hZ x hx).1, ?_⟩)
  refine Submodule.mem_iSup_of_mem 1 ?_
  rw [Submodule.mem_comap, pow_one]
  exact (hZ x hx).2
end lin

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]

theorem le_span_sup {ι : Type} (e : ι → V) (P : Submodule k⟦X⟧ V)
    (hP : Submodule.span k⟦X⟧ (Set.range e) = P) :
    P.restrictScalars k ≤ Submodule.span k (Set.range e) ⊔ (sh 1 P).restrictScalars k := by
  intro x hx
  rw [Submodule.restrictScalars_mem, ← hP, Finsupp.mem_span_range_iff_exists_finsupp] at hx
  obtain ⟨c, rfl⟩ := hx
  refine Submodule.sum_mem _ fun i _ => ?_
  show c i • e i ∈ _
  have he : e i ∈ P := hP ▸ Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : k⟦X⟧, c i = algebraMap k k⟦X⟧ (PowerSeries.constantCoeff (c i)) + PowerSeries.X * d :=
    ⟨_, by rw [add_comm]; exact PowerSeries.eq_X_mul_shift_add_const (c i)⟩
  rw [hd, add_smul, algebraMap_smul]
  refine Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)) ?_
  refine mem_sh_iff_exists.2 ⟨d • e i, P.smul_mem _ he, ?_⟩
  rw [zpow_one, vv_eq_coe_X, mul_smul]
  exact algebraMap_smul k⸨X⸩ (PowerSeries.X : k⟦X⟧) _

theorem exists_finite_le_sup (N : Submodule k⟦X⟧ V) (hN : N.FG) (a : ℤ) (m : ℕ) :
    ∃ S : Submodule k V, FiniteDimensional k S ∧
      (sh a N).restrictScalars k ≤ S ⊔ (sh (a + m) N).restrictScalars k := by
  induction m with
  | zero => exact ⟨⊥, inferInstance, by simp⟩
  | succ m ih =>
    obtain ⟨S, hS, h⟩ := ih
    have hfg : (sh (a + m) N).FG := hN.map _
    obtain ⟨n, e, he⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
    have h2 := le_span_sup e _ he
    rw [sh_sh_eq, add_comm (1 : ℤ)] at h2
    have : FiniteDimensional k (Submodule.span k (Set.range e)) :=
      FiniteDimensional.span_of_finite k (Set.finite_range e)
    refine ⟨S ⊔ Submodule.span k (Set.range e), inferInstance, h.trans ?_⟩
    rw [sup_assoc]
    refine sup_le_sup_left ?_ _
    rw [Nat.cast_succ, ← add_assoc]
    exact h2

theorem main : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ N : Submodule k⟦X⟧ V, IsLat N → CondC g N → ∀ (w : ℕ) (Z : Submodule k V), (∀ x ∈ Z, x ∈ sh (-w) N ∧ nab g x ∈ N) → Module.finrank k (↥Z ⧸ (N.restrictScalars k).submoduleOf Z) ≤ ∑ j ∈ Finset.range w, sen g N ((-(w : ℤ) + j : ℤ) : k) := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ g hg N hN hC w Z hZ
  have hr := GlobalTheory.T.genEigenMultiplicity_laurentShift_eq_sum_sen R g hg N hN hC (-w) w 0
  simp only [zero_add, neg_add_cancel, sh_zero_eq] at hr
  obtain ⟨S, hS, hF⟩ := exists_finite_le_sup N hN.1 (-w) w
  rw [neg_add_cancel, sh_zero_eq] at hF
  rw [← hr]
  exact finrank_le_gmult (nab g) _ _ Z S hF hZ

end GlobalTheory.PhiGam.PolarKernel
end
end

section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem trace_int : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ y : K'.O,
    ∃ a : K.O, @Algebra.trace K.E K'.E _ _ φ.toAlgebra (algebraMap K'.O K'.E y) = algebraMap K.O K.E a :=
  fun K K' d φ hU y => trace_int_of_isIntegral hU _ (GlobalTheory.T.isIntegral_integers_unramifiedInvolutionExt K K' d φ hU hU.ne_zero y)

end GlobalTheory.UnitLemma.Unr
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem _root_.GlobalTheory.T.isFullLatticeOver_unramifiedExt_iff : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (L : Submodule K'.O (overExt φ B ψ hψ hσ).A) (M : Submodule K.O B.A), (L : Set (overExt φ B ψ hψ hσ).A) = (M : Set B.A) → (IsLat K'.O K'.E L ↔ IsLat K.O K.E M) := by
  first | exact @GlobalTheory.UnitLemma.Unr.isLat_overExt_iff | exact GlobalTheory.UnitLemma.Unr.isLat_overExt_iff | (intros; apply GlobalTheory.UnitLemma.Unr.isLat_overExt_iff <;> assumption)
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem _root_.GlobalTheory.T.isIntegral_unramifiedExt_iff_isIntegral_base : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (a : B.A), @IsIntegral K'.O (overExt φ B ψ hψ hσ).A _ _ _ a ↔ IsIntegral K.O a := by
  first | exact @GlobalTheory.UnitLemma.Unr.isIntegral_overExt_iff | exact GlobalTheory.UnitLemma.Unr.isIntegral_overExt_iff | (intros; apply GlobalTheory.UnitLemma.Unr.isIntegral_overExt_iff <;> assumption)
end
