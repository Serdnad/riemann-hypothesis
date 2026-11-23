module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ParabolicInductionTrivialPreservesVirtualCharact
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle330
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle493
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoboundaryOfNormOneInSubalgebra
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle496
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import ReciprocityTheory.L2DbarEstimates.NormFibrations.MvBlowup
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
public import ReciprocityTheory.L2DbarEstimates.JacobianInterpolationStatement
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

@[expose] public section

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct GlobalTheory.ParabVirt
open scoped Classical

noncomputable section
namespace GlobalTheory.ShinPsiRec

variable {F : Type} [Field F]

def low (a n : ℕ) : Submodule F (Fin n → F) where
  carrier := {v | ∀ i : Fin n, a ≤ (i : ℕ) → v i = 0}
  add_mem' := fun {u v} hu hv i hi => by simp [hu i hi, hv i hi]
  zero_mem' := fun i _ => rfl
  smul_mem' := fun c v hv i hi => by simp [hv i hi]

theorem mem_stab_low_iff (a n : ℕ) (x : GL (Fin n) F) : x ∈ stab (low (F := F) a n) ↔ InPar a x := by
  rw [mem_stab]
  constructor
  · intro h i j hj hi
    have hv : (Pi.single j 1 : Fin n → F) ∈ low a n := by
      intro k hk
      have : k ≠ j := by intro e; subst e; omega
      simp [Pi.single_apply, this]
    have := h _ hv i hi
    simpa [Matrix.toLin'_apply, Matrix.mulVec_single_one] using this
  · intro h v hv i hi
    rw [Matrix.toLin'_apply]
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : (j : ℕ) < a
    · rw [h i j hj hi, zero_mul]
    · rw [hv j (by omega), mul_zero]

def lowEquiv {a n : ℕ} (ha : a ≤ n) : low (F := F) a n ≃ₗ[F] (Fin a → F) where
  toFun v := fun i => v.1 (Fin.castLE ha i)
  map_add' u v := rfl
  map_smul' c v := rfl
  invFun w := ⟨fun k => if h : (k : ℕ) < a then w ⟨k, h⟩ else 0, fun k hk => dif_neg (by omega)⟩
  left_inv v := by
    ext k
    dsimp only
    split_ifs with h
    · rfl
    · exact (v.2 k (by omega)).symm
  right_inv w := by
    funext i
    simp

theorem resMat_low {a n : ℕ} (ha : a ≤ n) (p : GL (Fin n) F) (hp : p ∈ stab (low (F := F) a n)) :
    resMat (low a n) (lowEquiv ha) ⟨p, hp⟩ = tl a (p : Matrix (Fin n) (Fin n) F) := by
  ext i j
  have hs : ((lowEquiv (F := F) ha).symm (Pi.single j 1)).1 = Pi.single (Fin.castLE ha j) 1 := by
    funext k
    change (if h : (k : ℕ) < a then (Pi.single j 1 : Fin a → F) ⟨k, h⟩ else 0) = _
    split_ifs with h
    · simp only [Pi.single_apply, Fin.ext_iff, Fin.val_castLE]
    · have : k ≠ Fin.castLE ha j := by
        intro e; rw [e, Fin.val_castLE] at h; exact h j.2
      simp [Pi.single_apply, this]
  simp only [resMat, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.toMatrix'_apply, LinearEquiv.conj_apply_apply]
  change (Matrix.toLin' (p : Matrix (Fin n) (Fin n) F) ((lowEquiv (F := F) ha).symm (Pi.single j 1)).1)
    (Fin.castLE ha i) = _
  rw [hs, Matrix.toLin'_apply, Matrix.mulVec_single_one]
  have hi : (i : ℕ) < n := by omega
  have hj : (j : ℕ) < n := by omega
  simp only [tl, ent, dif_pos (And.intro hi hj), Matrix.transpose_apply]
  rfl

theorem tl_isUnit {a n : ℕ} (ha : a ≤ n) (p : GL (Fin n) F) (hp : InPar a p) :
    IsUnit (tl a (p : Matrix (Fin n) (Fin n) F)) := by
  have hp' := (mem_stab_low_iff a n p).2 hp
  rw [← resMat_low ha p hp']
  exact IsUnit.map (resMat (low a n) (lowEquiv ha)) (Group.isUnit _)

theorem coe_tlG {a n : ℕ} (ha : a ≤ n) (p : GL (Fin n) F) (hp : InPar a p) :
    ((tlG a p : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = tl a (p : Matrix (Fin n) (Fin n) F) := by
  unfold tlG toG
  rw [dif_pos (tl_isUnit ha p hp)]
  rfl

theorem psi_restrict_low (S : F[X] → ℂ) {a n : ℕ} (ha : a ≤ n) (p : GL (Fin n) F)
    (hp : p ∈ stab (low (F := F) a n)) :
    psi S (low (F := F) a n) ((Matrix.toLin' (p : Matrix (Fin n) (Fin n) F)).restrict hp) =
      psiG S a (tlG a p) := by
  rw [psiG, coe_tlG ha p ((mem_stab_low_iff a n p).1 hp), ← resMat_low ha p hp]
  simp only [resMat, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.toLin'_toMatrix']
  rw [psi_conj]

def resPsi (S : F[X] → ℂ) {n : ℕ} (x : GL (Fin n) F) (W : Submodule F (Fin n → F)) : ℂ :=
  if h : x ∈ stab W then psi S W ((Matrix.toLin' (x : Matrix (Fin n) (Fin n) F)).restrict h) else 0

theorem finsum_rank_eq_hc [Finite F] (S : F[X] → ℂ) {a n : ℕ} (ha : a ≤ n) (x : GL (Fin n) F) :
    ∑ᶠ W : {W : Submodule F (Fin n → F) // Module.finrank F W = a}, resPsi S x W.1 =
      hc a (n - a) (psiG S a) (fun _ => 1) n x := by
  classical
  haveI : Finite (Submodule F (Fin n → F)) :=
    Finite.of_injective (fun W : Submodule F (Fin n → F) => (W : Set (Fin n → F))) SetLike.coe_injective
  letI := Fintype.ofFinite (GL (Fin n) F)
  letI := Fintype.ofFinite (Submodule F (Fin n → F))
  set W₀ := low (F := F) a n with hW₀def
  have hW₀ : Module.finrank F W₀ = a := (lowEquiv ha).finrank_eq.trans (Module.finrank_fin_fun F)
  let π : GL (Fin n) F → {W : Submodule F (Fin n → F) // Module.finrank F W = a} := fun t =>
    ⟨W₀.map (lin t).toLinearMap, (LinearEquiv.finrank_map_eq _ _).trans hW₀⟩
  have hs : Function.Surjective π := by
    intro W
    obtain ⟨f⟩ : Nonempty (W₀ ≃ₗ[F] W.1) :=
      FiniteDimensional.nonempty_linearEquiv_of_finrank_eq (hW₀.trans W.2.symm)
    obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
    obtain ⟨t, rfl⟩ := lin_surjective g
    refine ⟨t, Subtype.ext ?_⟩
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨v, hv, rfl⟩
      have := (f ⟨v, hv⟩).2
      rw [hg] at this
      exact this
    · exact (π t).2.trans W.2.symm
  have hsum := sum_fibres (stab W₀) π hs
    (fun s t => Subtype.ext_iff.trans (map_eq_map_iff W₀ s t)) (fun W => resPsi S x W.1)
  have hg : ∀ t : GL (Fin n) F, gal (RingHom.id F) n t = t := by
    intro t; ext i j; simp [gal]
  have hterm : ∀ t : GL (Fin n) F, resPsi S x (π t).1 =
      (if InPar a (t⁻¹ * x * gal (RingHom.id F) n t) then
        psiG S a (tlG a (t⁻¹ * x * gal (RingHom.id F) n t)) *
          (fun _ => (1 : ℂ)) (brG a (n - a) (t⁻¹ * x * gal (RingHom.id F) n t)) else 0) := by
    intro t
    rw [hg, mul_one]
    simp only [resPsi, π]
    by_cases h : t⁻¹ * x * t ∈ stab W₀
    · have h' := (conj_mem_stab_iff W₀ x t).1 h
      rw [dif_pos h', if_pos ((mem_stab_low_iff a n _).1 h), ← psi_restrict_low S ha _ h,
        ← psi_conj F S _ _ ((lin t).submoduleMap W₀)]
      congr 1
      refine LinearMap.ext fun v => ?_
      obtain ⟨w, rfl⟩ := ((lin t).submoduleMap W₀).surjective v
      rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
      ext1
      change lin x (lin t w) = lin t (lin (t⁻¹ * x * t) w)
      rw [← lin_mul, ← lin_mul, mul_assoc, mul_inv_cancel_left]
    · rw [dif_neg (fun h' => h ((conj_mem_stab_iff W₀ x t).2 h')),
        if_neg (fun h'' => h ((mem_stab_low_iff a n _).2 h''))]
  have hcard : Nat.card {p : GL (Fin n) F // InPar a p} = Nat.card (stab W₀) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun p => (mem_stab_low_iff a n p).symm)
  have hc0 : (Nat.card (stab W₀) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  simp only [hc, hcTw]
  rw [hcard, ← finsum_congr hterm, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, hsum,
    inv_mul_cancel_left₀ hc0]

end GlobalTheory.ShinPsiRec

namespace GlobalTheory.ShinPsiRec

theorem ne_top_iff_finrank_lt {F : Type} [Field F] {n : ℕ} (W : Submodule F (Fin n → F)) :
    W ≠ ⊤ ↔ Module.finrank F W < n := by
  constructor
  · intro h
    have := Submodule.finrank_lt h
    rwa [Module.finrank_fin_fun] at this
  · intro h htop
    rw [htop, finrank_top, Module.finrank_fin_fun] at h
    exact lt_irrefl _ h

theorem psiG_eq_chG_sub_hc (F : Type) [Field F] [Finite F] (S : F[X] → ℂ) (n : ℕ) (x : GL (Fin n) F) :
    psiG S n x = chG S n x - ∑ a ∈ Finset.range n, hc a (n - a) (psiG S a) (fun _ => 1) n x := by
  classical
  haveI : Finite (Submodule F (Fin n → F)) :=
    Finite.of_injective (fun W : Submodule F (Fin n → F) => (W : Set (Fin n → F))) SetLike.coe_injective
  letI := Fintype.ofFinite (Submodule F (Fin n → F))
  show psi S _ _ = S _ - _
  rw [psi_eq, Matrix.charpoly_toLin']
  congr 1
  rw [Finset.sum_congr rfl fun a ha =>
    (finsum_rank_eq_hc S (le_of_lt (Finset.mem_range.1 ha)) x).symm]
  have step : ∀ a : ℕ, ∑ᶠ W : {W : Submodule F (Fin n → F) // Module.finrank F W = a}, resPsi S x W.1 =
      ∑ W : Submodule F (Fin n → F), if Module.finrank F W = a then resPsi S x W else 0 := by
    intro a
    rw [finsum_eq_sum_of_fintype, ← Finset.sum_filter]
    exact (Finset.sum_subtype _ (by simp) _).symm
  simp only [step]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq]
  rw [finsum_eq_sum_of_fintype]
  rw [Finset.sum_congr rfl (g := fun W => resPsi S x W.1) fun W _ => by
    unfold resPsi; rw [dif_pos (show x ∈ stab W.1 from W.2.2)]]
  rw [← Finset.sum_subtype (Finset.univ.filter fun W : Submodule F (Fin n → F) => W ≠ ⊤ ∧ ∀ v ∈ W, Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) v ∈ W)
    (fun W => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]) (resPsi S x), Finset.sum_filter]
  refine Finset.sum_congr rfl fun W _ => ?_
  by_cases hx : ∀ v ∈ W, Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) v ∈ W
  · simp only [Finset.mem_range, ne_top_iff_finrank_lt, and_iff_left hx]
  · have hx' : x ∉ stab W := hx
    simp [resPsi, hx', hx]

end GlobalTheory.ShinPsiRec
end
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.DerivExpansion

theorem tsum_inv_cube : ∑' m : ℤ, 1 / (m : ℂ) ^ 3 = 0 := by
  have h : ∑' m : ℤ, 1 / (m : ℂ) ^ 3 = -∑' m : ℤ, 1 / (m : ℂ) ^ 3 := by
    conv_lhs => rw [← (Equiv.neg ℤ).tsum_eq]
    rw [← tsum_neg]
    congr 1
    funext b
    simp only [Equiv.neg_apply, Int.cast_neg]
    change 1 / ((-(b : ℂ)) ^ 3) = -(1 / (b : ℂ) ^ 3)
    rw [show (-(b : ℂ)) ^ 3 = -((b : ℂ) ^ 3) by ring, div_neg]
  linear_combination h / 2

theorem row_eq (N : ℕ) [NeZero N] (j : ZMod N) :
    ∑' m : ℤ, 1 / (((j.val : ℂ)) / N + m) ^ 3 =
      -(1 / 2) * (2 * (Real.pi : ℂ) * Complex.I) ^ 3 * (ch N j * (1 + ch N j) / (1 - ch N j) ^ 3) := by
  rcases eq_or_ne j 0 with rfl | hj
  · have hc : ch N 0 = 1 := by simp [ch]
    simp only [ZMod.val_zero, Nat.cast_zero, zero_div, zero_add, hc, sub_self]
    rw [tsum_inv_cube]
    simp
  · set w : ℂ := ((j.val : ℂ)) / N with hw
    have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    have him : w.im = 0 := by simp [hw, -ZMod.natCast_val]
    have hnot : ∀ n : ℤ, w ≠ n := by
      intro n hn
      rw [hw, div_eq_iff hN] at hn
      have hz : (j.val : ℤ) = n * N := by exact_mod_cast hn
      have h1 : 0 < j.val := Nat.pos_of_ne_zero (fun h => hj ((ZMod.val_eq_zero j).mp h))
      have h2 : j.val < N := ZMod.val_lt j
      have h1' : (0 : ℤ) < j.val := by exact_mod_cast h1
      have h2' : (j.val : ℤ) < N := by exact_mod_cast h2
      rcases le_or_gt n 0 with h | h
      · nlinarith
      · nlinarith
    have hc : ch N j = Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w) := by
      rw [hw]
      unfold ch
      congr 1
      ring
    rw [hc]
    exact (GlobalTheory.T.rowSums_two_three_closedForm_real_nonInteger w him hnot).2

theorem main : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N), HasQ N (wpd N x) (cD N x) := by
  intro N _ x
  unfold HasQ
  intro τ
  have hπ : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  obtain ⟨T, hT, hS⟩ := GlobalTheory.T.torsionPoint_rows_sum_eq_divisor_series N 2 τ x _ (by norm_num) (GlobalTheory.T.hasSum_rows_inv_cube_derivWeierstrassP τ (tors N τ x))
  set q := Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) with hq
  set c0 : ℂ := if x 0 = 0 then ch N (x 1) * (1 + ch N (x 1)) / (1 - ch N (x 1)) ^ 3 else 0 with hc0
  have h0 : cSum N 2 (-1) x 0 = 0 := by simp [cSum]
  have hT' : HasSum (fun k : ℕ => cSum N 2 (-1) x k * q ^ k) T := by
    have e1 : ((-1 : ℂ)) ^ (2 + 1) = -1 := by norm_num
    simpa only [e1] using hT
  have hsum : HasSum (fun n : ℕ => cD N x n * Complex.exp (2 * Real.pi * Complex.I * n * τ / N))
      (c0 + T) := by
    have hA : HasSum (fun n : ℕ => if n = 0 then c0 else 0) c0 := hasSum_ite_eq 0 c0
    convert hA.add hT' using 1
    funext n
    have hexp : Complex.exp (2 * Real.pi * Complex.I * n * τ / N) = q ^ n := by
      rw [hq, ← Complex.exp_nat_mul]
      congr 1
      ring
    rw [hexp]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [cD, h0, hc0]
    · simp [cD, hn]
  convert hsum using 1
  have hrow : (if x 0 = 0 then ∑' m : ℤ, 1 / ((((x 1).val : ℂ)) / N + m) ^ (2 + 1) else 0) =
      -(1 / 2) * (2 * (Real.pi : ℂ) * Complex.I) ^ 3 * c0 := by
    rw [hc0]
    split_ifs
    · exact row_eq N (x 1)
    · simp
  have hf : ((Nat.factorial 2 : ℕ) : ℂ) = 2 := by norm_num [Nat.factorial]
  rw [hrow, hf] at hS
  simp only [wpd]
  rw [div_eq_iff (pow_ne_zero 3 hπ)]
  linear_combination (-2) * hS

end GlobalTheory.WpFam.DerivExpansion
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.exists_coboundary_of_norm_one_in_subalgebra : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (B : Subalgebra F' (Matrix (Fin n) (Fin n) F')), (∀ x ∈ B, x.map s ∈ B) → ∀ ε : GL (Fin n) F', (ε : Matrix (Fin n) (Fin n) F') ∈ B → nrm s ε = 1 → ∃ x : GL (Fin n) F', (x : Matrix (Fin n) (Fin n) F') ∈ B ∧ ε = x⁻¹ * galAct F F' n s x := by
  first | (exact @GlobalTheory.HilbertNinety.hilbert90_matrix_subalgebra_norm_one) | (exact GlobalTheory.HilbertNinety.hilbert90_matrix_subalgebra_norm_one) | (intros; apply GlobalTheory.HilbertNinety.hilbert90_matrix_subalgebra_norm_one  <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem zeroSet_null_of_dense_nz : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (Λ : La) (τ : ι → Y → ℂ), A.IsSec Λ τ → Dense (nz A τ) → A.mu (nz A τ)ᶜ = 0 := by
  intro n Y _ _ _ _ _ ι La _ A Λ τ hτ hd
  have hN : EXTNullStatement n := extNull n
  have hiff : ∀ i y, y ∈ (A.chart i).source → (τ (A.pick y) y ≠ 0 ↔ τ i y ≠ 0) := by
    intro i y hy
    rw [hτ.2 (A.pick y) i y trivial (A.mem_pick y) hy]
    simp [A.g_ne Λ (A.pick y) i y (A.mem_pick y) hy]
  refine measure_null_of_locally_null _ fun y _ => ?_
  have hys : y ∈ (A.chart (A.pick y)).source := A.mem_pick y
  have hv := (A.chart (A.pick y)).map_source hys
  obtain ⟨r, hr, hB⟩ := Metric.isOpen_iff.1 (A.chart (A.pick y)).open_target _ hv
  have hUo : IsOpen ((A.chart (A.pick y)).source ∩ A.chart (A.pick y) ⁻¹'
      Metric.ball (A.chart (A.pick y) y) r) :=
    (A.chart _).continuousOn.isOpen_inter_preimage (A.chart _).open_source Metric.isOpen_ball
  have hyU : y ∈ (A.chart (A.pick y)).source ∩ A.chart (A.pick y) ⁻¹'
      Metric.ball (A.chart (A.pick y) y) r := ⟨hys, Set.mem_preimage.mpr (Metric.mem_ball_self hr)⟩
  have hF : DifferentiableOn ℂ (τ (A.pick y) ∘ (A.chart (A.pick y)).symm)
      (A.chart (A.pick y)).target := by
    simpa using hτ.1 (A.pick y)
  have hcont : ContinuousOn (τ (A.pick y)) (A.chart (A.pick y)).source := by
    have := hF.continuousOn.comp (A.chart (A.pick y)).continuousOn
      (fun x hx => (A.chart (A.pick y)).map_source hx)
    refine this.congr fun x hx => ?_
    simp [Function.comp, (A.chart (A.pick y)).left_inv hx]
  have hTo : IsOpen (((A.chart (A.pick y)).source ∩ A.chart (A.pick y) ⁻¹'
      Metric.ball (A.chart (A.pick y) y) r) ∩ τ (A.pick y) ⁻¹' {0}ᶜ) :=
    (hcont.mono Set.inter_subset_left).isOpen_inter_preimage hUo isOpen_compl_singleton
  refine ⟨_, inter_mem_nhdsWithin _ (hUo.mem_nhds hyU), ?_⟩
  refine measure_mono_null (t := ((A.chart (A.pick y)).source ∩ A.chart (A.pick y) ⁻¹'
      Metric.ball (A.chart (A.pick y) y) r) \ (((A.chart (A.pick y)).source ∩ A.chart (A.pick y) ⁻¹'
      Metric.ball (A.chart (A.pick y) y) r) ∩ τ (A.pick y) ⁻¹' {0}ᶜ)) ?_ ?_
  · rintro x ⟨hxn, hxU⟩
    refine ⟨hxU, fun h => hxn ?_⟩
    exact (hiff _ x hxU.1).2 h.2
  rw [A.mu_chart (A.pick y) _ (hUo.measurableSet.diff hTo.measurableSet)
    (Set.diff_subset.trans Set.inter_subset_left)]
  apply setLIntegral_measure_zero
  obtain ⟨y', hy'U, hy'M⟩ := hd.inter_open_nonempty _ hUo ⟨y, hyU⟩
  have hnull := hN (A.chart (A.pick y) y) r (τ (A.pick y) ∘ (A.chart (A.pick y)).symm)
    (hF.mono hB) ⟨A.chart (A.pick y) y', hy'U.2, by
      simp only [Function.comp, (A.chart _).left_inv hy'U.1]
      exact (hiff _ y' hy'U.1).1 hy'M⟩
  refine measure_mono_null ?_ hnull
  rintro _ ⟨x, ⟨hxU, hxn⟩, rfl⟩
  refine ⟨hxU.2, ?_⟩
  simp only [Set.mem_setOf_eq, Function.comp, (A.chart _).left_inv hxU.1]
  by_contra h
  exact hxn ⟨hxU, h⟩

end GlobalTheory
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem etale_isLocalHomeomorph : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → IsLocalHomeomorph (fun y : U => z y) := by
  intro n Y _ _ _ _ _ ι La _ A U z hE
  apply IsLocalHomeomorph.mk
  intro y
  set i := A.pick y
  set e := A.chart i
  set S : Set (V n) := e.target ∩ e.symm ⁻¹' U with hSdef
  have hS : IsOpen S := e.isOpen_inter_preimage_symm hE.isOpen
  have hyU : (y : Y) ∈ U := y.2
  have hys : (y : Y) ∈ e.source := A.mem_pick y
  have hxS : e y ∈ S := ⟨e.map_source hys, by simp [e.left_inv hys, hyU]⟩
  have hd : DifferentiableOn ℂ (z ∘ e.symm) S := hE.holo i
  have hcd : ContDiffOn ℂ ∞ (z ∘ e.symm) S :=
    contDiffOn_piLp' 2 (fun k => contDiffOn_of_differentiableOn n _ S hS
      ((differentiableOn_piLp 2).1 hd k))
  have hca : ContDiffAt ℂ ∞ (z ∘ e.symm) (e y) := hcd.contDiffAt (hS.mem_nhds hxS)
  have hst := hca.hasStrictFDerivAt_fderiv (by simp)
  have hdet : (fderiv ℂ (z ∘ e.symm) (e y)).det ≠ 0 := hE.det_ne i y hyU hys
  let L : V n ≃L[ℂ] V n :=
    (LinearMap.equivOfDetNeZero ((fderiv ℂ (z ∘ e.symm) (e y)) : V n →ₗ[ℂ] V n) hdet).toContinuousLinearEquiv
  have hL : ((L : V n →L[ℂ] V n)) = fderiv ℂ (z ∘ e.symm) (e y) := by
    ext v; rfl
  have hst' : HasStrictFDerivAt (z ∘ e.symm) (L : V n →L[ℂ] V n) (e y) := hL ▸ hst
  let h := hst'.toOpenPartialHomeomorph (z ∘ e.symm)
  let P := e.trans (h.restrOpen S hS)
  have hyP : (y : Y) ∈ P.source := by
    simp only [P, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.restrOpen_source,
      Set.mem_inter_iff, Set.mem_preimage]
    exact ⟨hys, hst'.mem_toOpenPartialHomeomorph_source, hxS⟩
  have hPz : ∀ w ∈ P.source, P w = z w := by
    intro w hw
    have hw1 : w ∈ e.source := by
      simp only [P, OpenPartialHomeomorph.trans_source] at hw; exact hw.1
    have hh : ∀ v, h v = (z ∘ e.symm) v := fun v => by
      simp only [h, HasStrictFDerivAt.toOpenPartialHomeomorph_coe]
    change (h.restrOpen S hS) (e w) = z w
    change h (e w) = z w
    rw [hh, Function.comp_apply, e.left_inv hw1]
  have hne : Nonempty (⟨U, hE.isOpen⟩ : TopologicalSpace.Opens Y) := ⟨y⟩
  let Q := P.subtypeRestr hne
  refine ⟨Q, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact hyP
  · intro w hw
    rw [OpenPartialHomeomorph.subtypeRestr_source] at hw
    rw [OpenPartialHomeomorph.subtypeRestr_coe]
    exact (hPz w hw).symm

end GlobalTheory.OTY
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.finite_cover_ring_localization_chart : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (I : Finset (Fin (d + 1))) (i : Fin (d + 1)), i ∈ I → (∀ J, I ⊆ J → rB k K x I ≤ rB k K x J) ∧ ∀ y : K, y ∈ rB k K x I ↔ ∃ N : ℕ, y * algebraMap F K (∏ j ∈ I, x j / x i) ^ N ∈ rB k K x {i} := by
  first | (exact @GlobalTheory.PD.rB_mono_loc) | (exact GlobalTheory.PD.rB_mono_loc) | (intros; apply GlobalTheory.PD.rB_mono_loc <;> assumption)
end
