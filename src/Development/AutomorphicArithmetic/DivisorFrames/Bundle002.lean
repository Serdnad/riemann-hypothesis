module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle404
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle047
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
open scoped Pointwise

private theorem UpperTheory.pow_sub_eq_one_of_condLE_valuation_le {k : Type} [Field k] [ValuativeRel k] (ϖ : kˣ) (e : ℕ) (ν : kˣ →* ℂˣ)
    (hν : CondLE ϖ e ν) (x : kˣ) (hx : valuation k (x : k) = 1) (a b : ℕ) (hab : a < b)
    (h : valuation k ((x : k) ^ b - (x : k) ^ a) ≤ valuation k ((ϖ ^ e : kˣ) : k)) :
    ν x ^ (b - a) = 1 := by
  have hmem : x ^ (b - a) ∈ unitCong (ϖ ^ e) := by
    show valuation k ((x ^ (b - a) : kˣ) : k) = 1 ∧
      valuation k (((x ^ (b - a) : kˣ) : k) - 1) ≤ valuation k ((ϖ ^ e : kˣ) : k)
    have hfac : (x : k) ^ b - (x : k) ^ a = (x : k) ^ a * ((x : k) ^ (b - a) - 1) := by
      rw [mul_sub, ← pow_add, Nat.add_sub_cancel' hab.le, mul_one]
    rw [hfac, map_mul, map_pow, hx, one_pow, one_mul] at h
    refine ⟨?_, ?_⟩
    · rw [Units.val_pow_eq_pow_val, map_pow, hx, one_pow]
    · rw [Units.val_pow_eq_pow_val]
      exact h
  rw [← map_pow]
  exact hν _ hmem

theorem UpperTheory.isIntegral_unitChar_of_conductor_le :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ) (e : ℕ) (ν : kˣ →* ℂˣ), IsUnif ϖ → CondLE ϖ e ν → ∀ x : kˣ, valuation k (x : k) = 1 → IsIntegral ℤ (ν x : ℂ) := by
  intro k _ _ _ _ ϖ e ν hϖ hν x hx
  have hpow : ∀ n : ℕ, (x : k) ^ n ∈ 𝒪[k] := fun n =>
    (Valuation.mem_integer_iff _ _).2 (by rw [map_pow, hx, one_pow])
  let g : ℕ → Res (k := k) e := fun n => Ideal.Quotient.mk _ ⟨(x : k) ^ n, hpow n⟩
  obtain ⟨i, j, hne, hg⟩ := Finite.exists_ne_map_eq_of_infinite g
  have key : ∀ a b : ℕ, a < b → g a = g b → IsIntegral ℤ (ν x : ℂ) := by
    intro a b hab h
    have h1 := Ideal.Quotient.eq.1 h.symm
    have h2 := (Model.val_le_iff_mem hϖ e _).1 h1
    have h3 : ν x ^ (b - a) = 1 := UpperTheory.pow_sub_eq_one_of_condLE_valuation_le ϖ e ν hν x hx a b hab (by simpa using h2)
    refine IsIntegral.of_pow (Nat.sub_pos_of_lt hab) ?_
    rw [← Units.val_pow_eq_pow_val, h3, Units.val_one]
    exact isIntegral_one
  rcases lt_or_gt_of_ne hne with h | h
  · exact key i j h hg
  · exact key j i h hg.symm
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
open scoped Pointwise

namespace UpperTheory.FourierBlockTranspose

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem mk_eq_iff {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) (a b : 𝒪[k]) :
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ e) a = Ideal.Quotient.mk _ b) ↔
      (((ϖ ^ e)⁻¹ : kˣ) : k) * ((a : k) - b) ∈ 𝒪[k] := by
  rw [Ideal.Quotient.eq, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  have hϖ0 : (ϖ : k) ≠ 0 := ϖ.ne_zero
  constructor
  · rintro ⟨c, hc⟩
    have hc' : (c : k) * (ϖ : k) ^ e = (a : k) - b := by
      simpa using congrArg Subtype.val hc
    rw [← hc', Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    have : ((ϖ : k) ^ e)⁻¹ * ((c : k) * (ϖ : k) ^ e) = c := by
      field_simp
    rw [this]
    exact c.2
  · intro h
    refine ⟨⟨_, h⟩, ?_⟩
    apply Subtype.ext
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, AddSubgroupClass.coe_sub,
      Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    field_simp

private theorem mul_mem_int {A C B : Type} [Fintype C] {X : Matrix A C k} {Y : Matrix C B k}
    (hX : ∀ i j, X i j ∈ 𝒪[k]) (hY : ∀ i j, Y i j ∈ 𝒪[k]) (i : A) (j : B) : (X * Y) i j ∈ 𝒪[k] := by
  rw [Matrix.mul_apply]
  exact sum_mem fun c _ => mul_mem (hX i c) (hY c j)

private theorem sum_res_mul_left {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ϖ : kˣ) (e : ℕ) (hϖ : IsUnif ϖ) (f : Matrix A B k → ℂ)
    (hf : ∀ Z Z' : Matrix A B k, (∀ i j, Z' i j ∈ 𝒪[k]) → f (Z + Z') = f Z)
    (M : GL A k) (hM : M ∈ KO k A) :
    ∑ S : A → B → Res (k := k) e, f (M.val * ((ϖ ^ e)⁻¹ • liftRes S)) =
      ∑ S : A → B → Res (k := k) e, f ((ϖ ^ e)⁻¹ • liftRes S) := by
  obtain ⟨hMi, hMinv⟩ := (mem_KO_iff M).1 hM
  have hint : ∀ (S : A → B → Res (k := k) e) (i : A) (j : B), (M.val * liftRes S) i j ∈ 𝒪[k] :=
    fun S i j => mul_mem_int hMi (liftRes_mem S) i j
  let σ : (A → B → Res (k := k) e) → (A → B → Res (k := k) e) := fun S i j =>
    Ideal.Quotient.mk _ ⟨(M.val * liftRes S) i j, hint S i j⟩
  have hclose : ∀ (S : A → B → Res (k := k) e) (i : A) (j : B),
      (((ϖ ^ e)⁻¹ : kˣ) : k) * (liftRes (σ S) i j - (M.val * liftRes S) i j) ∈ 𝒪[k] := by
    intro S i j
    have h := (mk_eq_iff hϖ e (Quotient.out (σ S i j)) ⟨_, hint S i j⟩).1
      (by rw [Ideal.Quotient.mk_out])
    simpa [liftRes] using h
  have hinj : Function.Injective σ := by
    intro S S' h
    funext i j
    have hd : ∀ a b, ((((ϖ ^ e)⁻¹ : kˣ) : k) • (M.val * (liftRes S - liftRes S'))) a b ∈ 𝒪[k] := by
      intro a b
      have h1 := (mk_eq_iff hϖ e _ _).1 (congrFun (congrFun h a) b)
      simpa [Matrix.mul_sub, Matrix.sub_apply, Matrix.smul_apply] using h1
    have h2 := mul_mem_int hMinv hd i j
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at h2
    have h3 := (mk_eq_iff hϖ e (Quotient.out (S i j)) (Quotient.out (S' i j))).2
      (by simpa [liftRes, Matrix.sub_apply, Matrix.smul_apply] using h2)
    rwa [Ideal.Quotient.mk_out, Ideal.Quotient.mk_out] at h3
  refine Fintype.sum_bijective σ (Finite.injective_iff_bijective.1 hinj) _ _ ?_
  intro S
  have hsplit : (ϖ ^ e)⁻¹ • liftRes (σ S) = M.val * ((ϖ ^ e)⁻¹ • liftRes S) +
      ((ϖ ^ e)⁻¹ • liftRes (σ S) - M.val * ((ϖ ^ e)⁻¹ • liftRes S)) := by abel
  rw [hsplit, hf]
  intro i j
  rw [Matrix.mul_smul]
  simp only [Units.smul_def, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, ← mul_sub]
  exact hclose S i j

end UpperTheory.FourierBlockTranspose

open UpperTheory.FourierBlockTranspose in
theorem UpperTheory.fourierSum_block_transpose_inv_eq :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A D₁ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂] (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ), IsUnif ϖ → HasConductor ψ 1 → ∀ Φ : Matrix A (D₁ ⊕ D₂) k → ℂ, IsNatDatum ϖ e Φ → ∀ u ∈ KO k A, ∀ Y : Matrix A (D₁ ⊕ D₂) k, fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) (fun Z => Φ (fromCols (u.valᵀ * Z.toCols₁) ((u⁻¹).val * Z.toCols₂))) Y = fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ ((u⁻¹).val * Y) := by
  intro k _ _ _ _ A D₁ D₂ _ _ _ _ _ _ ψ ϖ e hϖ hψ Φ hΦ u hu Y
  obtain ⟨huI, huinvI⟩ := (mem_KO_iff u).1 hu
  have hmulcond : ∀ g : Matrix A A k, (∀ i j, g i j ∈ 𝒪[k]) → ∀ Z : Matrix A (D₁ ⊕ D₂) k,
      (∀ i, ∀ j ∈ Assignment.one.block D₁ D₂, ((ϖ ^ e : kˣ) : k) * Z i j ∈ 𝒪[k]) →
      (∀ i, ∀ j ∈ Assignment.one.block D₁ D₂, ((ϖ ^ e : kˣ) : k) * (g * Z) i j ∈ 𝒪[k]) := by
    intro g hg Z hZ i j hj
    have h := mul_mem_int hg
      (Y := Matrix.of fun (a : A) (b : Assignment.one.block D₁ D₂) => ((ϖ ^ e : kˣ) : k) * Z a b)
      (fun a b => hZ a b b.2) i ⟨j, hj⟩
    rw [Matrix.mul_apply] at h
    rw [Matrix.mul_apply, Finset.mul_sum]
    convert h using 2 with l
    simp only [Matrix.of_apply]
    ring
  have hcond : (∀ i, ∀ j ∈ Assignment.one.block D₁ D₂, ((ϖ ^ e : kˣ) : k) * Y i j ∈ 𝒪[k]) ↔
      (∀ i, ∀ j ∈ Assignment.one.block D₁ D₂, ((ϖ ^ e : kˣ) : k) * ((u⁻¹).val * Y) i j ∈ 𝒪[k]) := by
    constructor
    · exact hmulcond _ huinvI Y
    · intro h
      have h2 := hmulcond _ huI _ h
      rwa [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul] at h2
  rw [fourierSum_apply, fourierSum_apply]
  by_cases hc : ∀ i, ∀ j ∈ Assignment.one.block D₁ D₂, ((ϖ ^ e : kˣ) : k) * Y i j ∈ 𝒪[k]
  swap
  · rw [if_neg hc, if_neg (mt hcond.2 hc)]
  rw [if_pos hc, if_pos (hcond.1 hc)]
  have hc' := hcond.1 hc
  congr 1
  have hψ1 : ∀ y : k, y ∈ 𝒪[k] → ψ y = 1 := by
    intro y hy
    have h := (hψ (1 : k)).2 (by simp)
    apply h
    rw [map_one]
    exact (Valuation.mem_integer_iff _ _).1 hy
  have hmat : ∀ L : Matrix A (Assignment.one.block D₁ D₂) k,
      fromCols (u.valᵀ * (setCols (Assignment.one.block D₁ D₂) Y L).toCols₁)
        ((u⁻¹).val * (setCols (Assignment.one.block D₁ D₂) Y L).toCols₂) =
      setCols (Assignment.one.block D₁ D₂) ((u⁻¹).val * Y) (u.valᵀ * L) := by
    intro L
    ext i j
    rcases j with d | d
    · simp [setCols, Assignment.block, Matrix.mul_apply]
      rfl
    · simp [setCols, Assignment.block, Matrix.mul_apply]
  have hpair : ∀ L : Matrix A (Assignment.one.block D₁ D₂) k,
      pairCols (Assignment.one.block D₁ D₂) Y L =
        pairCols (Assignment.one.block D₁ D₂) ((u⁻¹).val * Y) (u.valᵀ * L) := by
    intro L
    rw [pairCols_eq_trace, pairCols_eq_trace]
    have hs : ((u⁻¹).val * Y).submatrix id Subtype.val =
        (u⁻¹).val * Y.submatrix id (Subtype.val : Assignment.one.block D₁ D₂ → D₁ ⊕ D₂) := by
      ext i j
      simp [Matrix.mul_apply]
    rw [hs, Matrix.transpose_mul, ← Matrix.mul_assoc,
      Matrix.trace_mul_comm (u.valᵀ * L * (Y.submatrix id Subtype.val)ᵀ),
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv,
      Matrix.transpose_one, Matrix.one_mul]
  let f : Matrix A (Assignment.one.block D₁ D₂) k → ℂ := fun W =>
    Φ (setCols (Assignment.one.block D₁ D₂) ((u⁻¹).val * Y) ((ϖ ^ e) • W)) *
      (ψ (pairCols (Assignment.one.block D₁ D₂) ((u⁻¹).val * Y) ((ϖ ^ e) • W)) : ℂ)
  have hΦ' : HasDepth ϖ e (stdLat k (D₁ ⊕ D₂)) Φ := hΦ
  obtain ⟨_, hΦinv⟩ := hΦ'
  have hf : ∀ Z Z' : Matrix A (Assignment.one.block D₁ D₂) k, (∀ i j, Z' i j ∈ 𝒪[k]) → f (Z + Z') = f Z := by
    intro Z Z' hZ'
    simp only [f]
    rw [smul_add]
    have hset : setCols (Assignment.one.block D₁ D₂) ((u⁻¹).val * Y) ((ϖ ^ e) • Z + (ϖ ^ e) • Z') =
        setCols (Assignment.one.block D₁ D₂) ((u⁻¹).val * Y) ((ϖ ^ e) • Z) +
          setCols (Assignment.one.block D₁ D₂) 0 ((ϖ ^ e) • Z') := by
      ext i j
      simp only [setCols, Matrix.of_apply, Matrix.add_apply]
      split_ifs <;> simp
    have hlat : setCols (Assignment.one.block D₁ D₂) 0 ((ϖ ^ e) • Z') ∈
        matLat A (ϖ ^ e • stdLat k (D₁ ⊕ D₂)) := by
      rw [FourierDepth.mem_matLat_smul_stdLat]
      intro i j
      simp only [setCols, Matrix.of_apply]
      split_ifs with h
      · rw [Matrix.smul_apply, Units.smul_def, smul_eq_mul, map_mul]
        exact mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).1 (hZ' i ⟨j, h⟩))
      · simp
    have hpadd : pairCols (Assignment.one.block D₁ D₂) ((u⁻¹).val * Y) ((ϖ ^ e) • Z + (ϖ ^ e) • Z') =
        pairCols (Assignment.one.block D₁ D₂) ((u⁻¹).val * Y) ((ϖ ^ e) • Z) +
          pairCols (Assignment.one.block D₁ D₂) ((u⁻¹).val * Y) ((ϖ ^ e) • Z') := by
      simp only [pairCols, Matrix.add_apply, add_mul, Finset.sum_add_distrib]
    have hmemb : pairCols (Assignment.one.block D₁ D₂) ((u⁻¹).val * Y) ((ϖ ^ e) • Z') ∈ 𝒪[k] := by
      simp only [pairCols]
      refine sum_mem fun i _ => sum_mem fun j _ => ?_
      rw [Matrix.smul_apply, Units.smul_def, smul_eq_mul, mul_comm ((ϖ ^ e : kˣ) : k) _, mul_assoc]
      exact mul_mem (hZ' i j) (hc' i j j.2)
    rw [hset, hΦinv _ _ hlat, hpadd, AddChar.map_add_eq_mul, hψ1 _ hmemb, mul_one]
  have key := sum_res_mul_left ϖ e hϖ f hf (invT u⁻¹) (invT_mem_KO (inv_mem hu))
  calc _ = ∑ T : A → Assignment.one.block D₁ D₂ → Res (k := k) e,
        f ((invT u⁻¹).val * ((ϖ ^ e)⁻¹ • liftRes T)) := by
        refine Finset.sum_congr rfl fun T _ => ?_
        simp only [f]
        rw [invT_val, inv_inv, Matrix.mul_smul, smul_inv_smul, ← hmat, ← hpair]
    _ = ∑ T : A → Assignment.one.block D₁ D₂ → Res (k := k) e, f ((ϖ ^ e)⁻¹ • liftRes T) := key
    _ = _ := by
        refine Finset.sum_congr rfl fun T _ => ?_
        simp only [f, smul_inv_smul]
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
open scoped Pointwise

private theorem not_touch_inner {γ : List Edge} {i j : ℕ} (hγ : IsPath γ) (hθ : Edge.theta i j ∈ γ)
    (hx : Edge.ex i j ∈ γ) {b : Edge} (hb : b ∈ γ) (h1 : b ≠ .theta i j) (h2 : b ≠ .ex i j) :
    b.src ≠ (i, j) ∧ b.tgt ≠ (i, j) := by
  refine ⟨fun hs => h2 (hγ.eq_of_vertexDiff_eq hb hx (by rw [hs])), fun ht => h1 ?_⟩
  have h3 := vertexDiff_tgt b
  have h4 := vertexDiff_tgt (.theta i j)
  rw [ht] at h3
  exact hγ.eq_of_vertexDiff_eq hb hθ (by simp only [Edge.tgt] at h4; omega)

private theorem nodup_of_isPath {γ : List Edge} (hγ : IsPath γ) : γ.Nodup :=
  hγ.pairwise_vertexDiff.imp fun {a b} h hab => by subst hab; exact lt_irrefl _ h

theorem UpperTheory.nu_det_mul_sliceB_block_action :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {G : Grid k} (ϖ : kˣ) (e : ℕ) (St : G.PiLocalization₂) (i j : ℕ), PassesThrough i j St.path → St.IsAdmissible .one ϖ e → ∀ u ∈ St.level (i, j), ∀ (x : G.Args) (Z : Matrix (Fin (G.rank (i, j))) (G.Cols i j) k), (G.nu i j (gdet u⁻¹) : ℂ) * G.sliceB i j St.tensor x (fromCols (u.valᵀ * Z.toCols₁) ((u⁻¹).val * Z.toCols₂)) = G.sliceB i j St.tensor x Z := by
  intro k _ _ _ _ G ϖ e St i j hpt hadm u hu x Z
  obtain ⟨γ, J, T⟩ := St
  obtain ⟨hpath, hlev, htens, hinv⟩ := hadm
  simp only at hpt hlev hpath htens hinv hu ⊢
  have hθ : Edge.theta i j ∈ γ := hpt.subset (by simp)
  have hx : Edge.ex i j ∈ γ := hpt.subset (by simp)
  have hnt := fun b hb h1 h2 => not_touch_inner (b := b) hpath hθ hx hb h1 h2
  have hnd := nodup_of_isPath hpath
  obtain ⟨l₁, l₂, hγ⟩ := hpt
  have hin : (i, j) ∈ innerVertices γ := by
    subst hγ
    refine List.mem_map.2 ⟨.ex i j, ?_, rfl⟩
    cases l₁ <;> simp
  have huK : u ∈ KO k _ := (hlev _ hin).2 hu
  have h := congrFun (hinv _ hin u hu)
    (Function.update (Function.update x (.theta i j) Z.toCols₁) (.ex i j) Z.toCols₂ᵀ)
  set g : G.VertexGroup := Pi.mulSingle (i, j) u with hg
  have hg0 : g (i, j) = u := Pi.mulSingle_eq_same _ _
  have hg1 : ∀ Y, Y ≠ (i, j) → g Y = 1 := fun Y hY => Pi.mulSingle_eq_of_ne hY _
  have hoff : ∀ b ∈ γ, b ≠ .theta i j → b ≠ .ex i j → G.edgeFactor .one g b = 1 := fun b hb h1 h2 => by
    simp [Grid.edgeFactor, hg1 _ (hnt b hb h1 h2).1, hg1 _ (hnt b hb h1 h2).2]
  have ha : ∀ z : ℂ, apow (gdet (Assignment.one.read u)) z = 1 := fun z =>
    apow_of_valuation_eq_one (valuation_gdet_of_mem_KO (Assignment.one.read_mem_KO huK)) z
  have hsq : G.edgeFactor .one g (.theta i j) * G.edgeFactor .one g (.ex i j) = (G.nu i j (gdet u⁻¹) : ℂ) := by
    have e1 : g (i, j + 1) = 1 := hg1 _ (by simp)
    have e2 : g (i + 1, j) = 1 := hg1 _ (by simp)
    simp only [Grid.edgeFactor, Edge.src, Edge.tgt, hg0, e1, e2, ha, map_one, apow_one, mul_one]
    simp only [Grid.kappa, Grid.blockChar, Grid.nu, gdet, map_one, map_inv, MonoidHom.div_apply,
      Units.val_div_eq_div_val, Units.val_inv_eq_inv_val, Units.val_one, inv_one, mul_one, one_mul]
    field_simp
  have hprod : (γ.map (G.edgeFactor .one g)).prod = (G.nu i j (gdet u⁻¹) : ℂ) := by
    have p : ∀ l : List Edge, (∀ b ∈ l, b ∈ γ ∧ b ≠ .theta i j ∧ b ≠ .ex i j) →
        (l.map (G.edgeFactor .one g)).prod = 1 := fun l hl => List.prod_eq_one fun c hc => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hc
      exact hoff b (hl b hb).1 (hl b hb).2.1 (hl b hb).2.2
    subst hγ
    have q₁ := p l₁ fun b hb => ⟨by simp [hb], by
      rintro rfl; exact (List.nodup_append.1 (List.nodup_append.1 hnd).1).2.2 _ hb _ (by simp) rfl, by
      rintro rfl; exact (List.nodup_append.1 (List.nodup_append.1 hnd).1).2.2 _ hb _ (by simp) rfl⟩
    have q₂ := p l₂ fun b hb => ⟨by simp [hb], by
      rintro rfl; exact (List.nodup_append.1 hnd).2.2 _ (by simp) _ hb rfl, by
      rintro rfl; exact (List.nodup_append.1 hnd).2.2 _ (by simp) _ hb rfl⟩
    simp only [List.map_append, List.prod_append, q₁, q₂, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, one_mul, hsq]
  rw [Grid.pathAct, hprod] at h
  simp only [Grid.sliceB]
  rw [← h]
  congr 1
  refine htens.1 fun b hb => ?_
  have hne : Edge.theta i j ≠ Edge.ex i j := by simp
  by_cases hb2 : b = .ex i j
  · subst hb2
    simp only [Function.update_self, Grid.moveArgs, Assignment.read, invT_inv_val, hg0, invT_val]
    simp [hg1 (i + 1, j) (by simp), Matrix.transpose_mul]
  · by_cases hb1 : b = .theta i j
    · subst hb1
      simp only [Function.update_of_ne hne, Function.update_self, Grid.moveArgs, Assignment.read, invT_inv_val, hg0]
      simp [hg1 (i, j + 1) (by simp)]
    · simp [Grid.moveArgs, Function.update_of_ne hb1, Function.update_of_ne hb2,
        hg1 _ (hnt b hb hb1 hb2).1, hg1 _ (hnt b hb hb1 hb2).2]
end
