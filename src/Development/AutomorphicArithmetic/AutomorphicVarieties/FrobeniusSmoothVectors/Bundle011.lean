module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle001
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
public import Mathlib.Order.Sym2
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.MvPowerSeries.Inverse
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
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.Data.Sym.Card
public import Mathlib.RingTheory.Nakayama

@[expose] public section

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

section SlopeTestRemainingChoices

variable {O : Type} [CommRing O] [IsLocalRing O] {C : Type} [CommRing C] [Algebra O C]
  {K : Ideal C} (u : K →ₗ[O] ResidueField O)

private theorem evk_add {x y : C} (hx : x ∈ K) (hy : y ∈ K) :
    evK K u (x + y) = evK K u x + evK K u y := by
  rw [evK_of_mem u hx, evK_of_mem u hy, evK_of_mem u (K.add_mem hx hy), ← map_add (f := _)]
  rfl

private theorem evk_sub {x y : C} (hx : x ∈ K) (hy : y ∈ K) :
    evK K u (x - y) = evK K u x - evK K u y := by
  rw [evK_of_mem u hx, evK_of_mem u hy, evK_of_mem u (K.sub_mem hx hy), ← map_sub]
  rfl

private theorem evk_neg {x : C} (hx : x ∈ K) : evK K u (-x) = - evK K u x := by
  rw [evK_of_mem u hx, evK_of_mem u (K.neg_mem hx), ← map_neg]
  rfl

private theorem evk_sum {ι : Type} (s : Finset ι) (f : ι → C) (hf : ∀ i, f i ∈ K) :
    evK K u (∑ i ∈ s, f i) = ∑ i ∈ s, evK K u (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, evK_of_mem u K.zero_mem]
    exact map_zero u
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, evk_add u (hf a) (K.sum_mem fun i _ => hf i), ih]

private theorem evk_mul [IsCO O C] (hK : maximalIdeal C * K = ⊥) (a : C) {x : C} (hx : x ∈ K) :
    evK K u (a * x) = res O C a * evK K u x := by
  obtain ⟨b, hb⟩ := IsCO.res_surj (O := O) a
  have h0 : (a - algebraMap O C b) * x = 0 := by
    have := Ideal.mul_mem_mul hb hx
    rwa [hK, Ideal.mem_bot] at this
  have h1 : res O C a = algebraMap O _ b := by
    have := (res_eq_zero_iff O C _).2 hb
    rwa [map_sub, AlgHom.commutes, sub_eq_zero] at this
  rw [evK_of_mem u hx, evK_of_mem u (K.mul_mem_left a hx), h1, ← Algebra.smul_def, ← map_smul]
  congr 1
  apply Subtype.ext
  show a * x = b • x
  rw [Algebra.smul_def, ← sub_eq_zero, ← sub_mul, h0]

variable {n : ℕ}

private theorem mem_left {Z : Matrix (Fin n) (Fin n) C} (hZ : ∀ i j, Z i j ∈ K)
    (A : Matrix (Fin n) (Fin n) C) (i j : Fin n) : (A * Z) i j ∈ K := by
  rw [Matrix.mul_apply]
  exact K.sum_mem fun k _ => K.mul_mem_left _ (hZ k j)

private theorem mem_right {Z : Matrix (Fin n) (Fin n) C} (hZ : ∀ i j, Z i j ∈ K)
    (A : Matrix (Fin n) (Fin n) C) (i j : Fin n) : (Z * A) i j ∈ K := by
  rw [Matrix.mul_apply]
  exact K.sum_mem fun k _ => K.mul_mem_right _ (hZ i k)

private theorem map_left [IsCO O C] (hK : maximalIdeal C * K = ⊥) {Z : Matrix (Fin n) (Fin n) C}
    (hZ : ∀ i j, Z i j ∈ K) (A : Matrix (Fin n) (Fin n) C) :
    (A * Z).map (evK K u) = A.map (res O C) * Z.map (evK K u) := by
  ext i j
  rw [Matrix.map_apply, Matrix.mul_apply, Matrix.mul_apply,
    evk_sum u _ _ fun k => K.mul_mem_left _ (hZ k j)]
  exact Finset.sum_congr rfl fun k _ => evk_mul u hK _ (hZ k j)

private theorem map_right [IsCO O C] (hK : maximalIdeal C * K = ⊥) {Z : Matrix (Fin n) (Fin n) C}
    (hZ : ∀ i j, Z i j ∈ K) (A : Matrix (Fin n) (Fin n) C) :
    (Z * A).map (evK K u) = Z.map (evK K u) * A.map (res O C) := by
  ext i j
  rw [Matrix.map_apply, Matrix.mul_apply, Matrix.mul_apply,
    evk_sum u _ _ fun k => K.mul_mem_right _ (hZ i k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, evk_mul u hK _ (hZ i k), mul_comm]
  rfl

private theorem mem_theta {Z : Matrix (Fin n) (Fin n) C} (hZ : ∀ i j, Z i j ∈ K) (i j : Fin n) :
    thetaLie Z i j ∈ K :=
  K.neg_mem (mem_right (mem_left (Z := Zᵀ) (fun i j => hZ j i) _) _ i j)

private theorem map_thetaLie [IsCO O C] (hK : maximalIdeal C * K = ⊥) {Z : Matrix (Fin n) (Fin n) C}
    (hZ : ∀ i j, Z i j ∈ K) : (thetaLie Z).map (evK K u) = thetaLie (Z.map (evK K u)) := by
  have hT : ∀ i j, Zᵀ i j ∈ K := fun i j => hZ j i
  have hJ : (Jmat C n).map (res O C) = Jmat (ResidueField O) n :=
    Jmat_map (res O C : C →+* ResidueField O) n
  have e : (Jmat C n * Zᵀ * Jmat C n).map (evK K u) =
      Jmat (ResidueField O) n * (Z.map (evK K u))ᵀ * Jmat (ResidueField O) n := by
    rw [map_right u hK (mem_left hT _), map_left u hK hT, hJ]
    rfl
  unfold thetaLie
  rw [← e]
  ext i j
  exact evk_neg u (mem_right (mem_left hT _) _ i j)

end SlopeTestRemainingChoices

theorem UpperTheory.V.Fr.pr_evk :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (n : ℕ) (K : Ideal C) (u : K →ₗ[O] ResidueField O), maximalIdeal C * K = ⊥ → K ≤ maximalIdeal C → ∀ Z : Matrix (Fin n) (Fin n) C, (∀ i j, Z i j ∈ K) → (∀ Z' : Matrix (Fin n) (Fin n) C, (∀ i j, Z' i j ∈ K) → Z * Z' = 0 ∧ (Z + Z').map (evK K u) = Z.map (evK K u) + Z'.map (evK K u) ∧ (Z - Z').map (evK K u) = Z.map (evK K u) - Z'.map (evK K u)) ∧ (∀ A : Matrix (Fin n) (Fin n) C, (∀ i j, (A * Z) i j ∈ K ∧ (Z * A) i j ∈ K) ∧ (A * Z).map (evK K u) = A.map (res O C) * Z.map (evK K u) ∧ (Z * A).map (evK K u) = Z.map (evK K u) * A.map (res O C)) ∧ ∀ x : GG (m := n) (R := C), (∀ i j, x.adFun Z i j ∈ K) ∧ (x.adFun Z).map (evK K u) = (GG.map (res O C : C →+* ResidueField O) x).adFun (Z.map (evK K u)) ∧ ∀ z : GL (Fin n) C, (z : Matrix (Fin n) (Fin n) C) = 1 + Z → (x * GG.ofGL z * x⁻¹).mat = 1 + x.adFun Z := by
  intro O _ _ C _ _ _ n K u hK hKm Z hZ
  have hsq : ∀ Z' : Matrix (Fin n) (Fin n) C, (∀ i j, Z' i j ∈ K) → Z * Z' = 0 := fun Z' hZ' => by
    ext i j
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    have := Ideal.mul_mem_mul (hKm (hZ i k)) (hZ' k j)
    rwa [hK, Ideal.mem_bot] at this
  refine ⟨fun Z' hZ' => ⟨hsq Z' hZ', ?_, ?_⟩,
    fun A => ⟨fun i j => ⟨mem_left hZ A i j, mem_right hZ A i j⟩, map_left u hK hZ A, map_right u hK hZ A⟩,
    fun x => ?_⟩
  · ext i j
    exact evk_add u (hZ i j) (hZ' i j)
  · ext i j
    exact evk_sub u (hZ i j) (hZ' i j)
  have hY : ∀ i j, (if x.right = 1 then Z else thetaLie Z) i j ∈ K := fun i j => by
    split_ifs
    · exact hZ i j
    · exact mem_theta hZ i j
  refine ⟨mem_right (mem_left hY _) _, ?_, fun z hz => ?_⟩
  · have hY' : (if x.right = 1 then Z else thetaLie Z).map (evK K u) =
        if x.right = 1 then Z.map (evK K u) else thetaLie (Z.map (evK K u)) := by
      split_ifs
      · rfl
      · exact map_thetaLie u hK hZ
    unfold GG.adFun
    rw [map_right u hK (mem_left hY _), map_left u hK hY, hY']
    rfl
  · have hinv : ((z⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) = 1 - Z := by
      have : (z : Matrix (Fin n) (Fin n) C) * (1 - Z) = 1 := by
        rw [hz, add_mul, mul_sub, mul_sub, hsq Z hZ]
        simp
      exact Units.inv_eq_of_mul_eq_one_right this
    have hl : (x * GG.ofGL z * x⁻¹).left = x.left * sgnAct n C x.right z * x.left⁻¹ := by
      rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.mul_right,
        SemidirectProduct.inv_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl, mul_one,
        ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    have hs : ((sgnAct n C x.right z : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) =
        1 + (if x.right = 1 then Z else thetaLie Z) := by
      rcases Int.units_eq_one_or x.right with h | h
      · rw [h, sgnAct_one, if_pos rfl, hz]
      · rw [h, sgnAct_neg_one, if_neg (by decide), theta_val, hinv, thetaLie, Matrix.transpose_sub,
          Matrix.transpose_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Jmat_mul_Jmat,
          sub_eq_add_neg]
    unfold GG.adFun GG.mat
    rw [hl, Units.val_mul, Units.val_mul, hs, mul_add, add_mul, mul_one, Units.mul_inv]
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem upT_mul {C : Type} [CommRing C] {n : ℕ} {M N : Matrix (Fin n) (Fin n) C}
    (hM : UpT M) (hN : UpT N) : UpT (M * N) := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  by_cases ha : a < i
  · rw [hM i a ha, zero_mul]
  · rw [hN a j (lt_of_lt_of_le h (not_lt.mp ha)), mul_zero]

theorem UpperTheory.V.Fr.pr_bstab :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ}, ∀ (C : Type) [CommRing C] (B : Box F n C) (v : F.V) (s : F.Gv v), ∀ X ∈ B.b v, B.ad (F.loc v s) X ∈ B.b v := by
  intro l _ k _ F n C _ B v s X hX
  have h1 : (B.r (F.loc v s)).right = 1 := (B.nu _).trans (F.loc0 v s).2
  have h2 : (B.r (F.loc v s⁻¹)).left = (B.r (F.loc v s)).left⁻¹ := by
    rw [map_inv, map_inv, SemidirectProduct.inv_left, h1, inv_one, sgnAct_one]
  have t1 := B.tri v s
  have t2 := B.tri v s⁻¹
  have t3 := upT_mul (upT_mul t1 hX) t2
  simp only [GG.mat, h2] at t3
  show UpT ((B.g v : Matrix (Fin n) (Fin n) C) * (B.r (F.loc v s)).adFun X *
    (((B.g v)⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C))
  have hg : ∀ Y : Matrix (Fin n) (Fin n) C,
      (((B.g v)⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) * ((B.g v : Matrix (Fin n) (Fin n) C) * Y) = Y :=
    fun Y => Units.inv_mul_cancel_left _ Y
  simp only [Matrix.mul_assoc, hg] at t3
  simp only [GG.adFun, GG.mat, h1, if_true, Matrix.mul_assoc]
  exact t3
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private def borEquiv (K : Type) [Field K] (n : ℕ) (g : GL (Fin n) K) :
    bor g ≃ₗ[K] ({p : Fin n × Fin n // p.1 ≤ p.2} → K) where
  toFun X p := ((g : Matrix (Fin n) (Fin n) K) * X.1 * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) p.1.1 p.1.2
  map_add' X Y := by
    funext p
    simp only [Submodule.coe_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, Pi.add_apply]
  map_smul' c X := by
    funext p
    simp only [Submodule.coe_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, Pi.smul_apply,
      RingHom.id_apply]
  invFun f := ⟨((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (Matrix.of fun i j => if h : i ≤ j then f ⟨(i, j), h⟩ else 0) * (g : Matrix (Fin n) (Fin n) K), by
    intro i j h
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc,
      Units.mul_inv, Matrix.mul_one, Matrix.of_apply, dite_eq_right (not_le.mpr h)]⟩
  left_inv X := by
    apply Subtype.ext
    have e : (Matrix.of fun i j => if i ≤ j then ((g : Matrix (Fin n) (Fin n) K) * X.1 *
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) i j else 0) =
        (g : Matrix (Fin n) (Fin n) K) * X.1 * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      ext i j
      rw [Matrix.of_apply]
      split_ifs with h
      · rfl
      · exact (X.2 i j (not_le.mp h)).symm
    show ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (Matrix.of fun i j => if i ≤ j then ((g : Matrix (Fin n) (Fin n) K) * X.1 *
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) i j else 0) * (g : Matrix (Fin n) (Fin n) K) = X.1
    rw [e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc,
      Units.inv_mul, Matrix.mul_one]
  right_inv f := by
    funext p
    show ((g : Matrix (Fin n) (Fin n) K) * (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (Matrix.of fun i j => if h : i ≤ j then f ⟨(i, j), h⟩ else 0) * (g : Matrix (Fin n) (Fin n) K)) *
      ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) p.1.1 p.1.2 = f p
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc,
      Units.mul_inv, Matrix.mul_one, Matrix.of_apply, dite_eq_left p.2]

theorem UpperTheory.V.Fr.pr_bdim :
    ∀ (K : Type) [Field K] (n : ℕ) (g : GL (Fin n) K), 2 * Module.finrank K (bor g) = n * (n + 1) := by
  intro K _ n g
  rw [(borEquiv K n g).finrank_eq, Module.finrank_fintype_fun_eq_card,
    ← Fintype.card_congr (Sym2.sortEquiv (α := Fin n)), Sym2.card, Fintype.card_fin, Nat.choose_two_right,
    Nat.add_sub_cancel, Nat.mul_comm (n + 1) n]
  exact Nat.mul_div_cancel' (Nat.even_mul_succ_self n).two_dvd
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem ns_mem_max {O σ : Type} [CommRing O] [IsLocalRing O] (x : MvPowerSeries σ O) :
    x ∈ maximalIdeal (MvPowerSeries σ O) ↔ MvPowerSeries.constantCoeff x ∈ maximalIdeal O := by
  rw [mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
    MvPowerSeries.isUnit_iff_constantCoeff]

private theorem ns_loc {O R R' : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') (x : R) :
    f x ∈ maximalIdeal R' ↔ x ∈ maximalIdeal R := by
  rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]

private theorem ns_coeff {O σ : Type} [CommRing O] [DecidableEq σ] (s t : σ) (k : MvPowerSeries σ O) :
    MvPowerSeries.coeff (Finsupp.single s 1) (MvPowerSeries.X t * k) =
      if t = s then MvPowerSeries.constantCoeff k else 0 := by
  rw [MvPowerSeries.X, MvPowerSeries.coeff_monomial_mul]
  by_cases h : t = s
  · subst h
    simp
  · rw [if_neg h, if_neg]
    intro hle
    have := hle t
    simp [Finsupp.single_apply, Ne.symm h] at this

private theorem ns_dec {O σ : Type} [CommRing O] [IsLocalRing O] [Fintype σ] (g : MvPowerSeries σ O)
    (hg : ∀ s, MvPowerSeries.coeff (Finsupp.single s 1) g ∈ maximalIdeal O) :
    ∃ k : σ → MvPowerSeries σ O, (∀ s, k s ∈ maximalIdeal (MvPowerSeries σ O)) ∧
      g = algebraMap O _ (MvPowerSeries.constantCoeff g) + ∑ s, MvPowerSeries.X s * k s := by
  classical
  obtain ⟨h, -, hh⟩ := GlobalTheory.exists_eq_sum_X_mul (n := 0)
    (g := g - algebraMap O _ (MvPowerSeries.constantCoeff g)) (by
      intro d hd
      have hd0 : d.degree = 0 := by omega
      have : d = 0 := (Finsupp.degree_eq_zero_iff d).mp hd0
      subst this
      simp [Algebra.algebraMap_eq_smul_one])
  have e : g = algebraMap O _ (MvPowerSeries.constantCoeff g) + ∑ i, MvPowerSeries.X i * h i := by
    rw [← hh]
    ring
  refine ⟨h, fun s => ?_, e⟩
  rw [ns_mem_max]
  have hs := hg s

  rw [e, map_add (f := _), map_sum] at hs
  simp only [ns_coeff] at hs
  simpa [Algebra.algebraMap_eq_smul_one, MvPowerSeries.coeff_one] using hs

theorem UpperTheory.V.Fr.ep_nosec :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (ι : Type) [Finite ι] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (π : MvPowerSeries ι O →ₐ[O] C) (p : C →ₐ[O] R) (s : R →ₐ[O] C), Function.Surjective π → IsMinPres (p.comp π) → (∀ i, π (MvPowerSeries.X i) ∈ maximalIdeal C) → p.comp s = AlgHom.id O R → Function.Injective p := by
  intro O _ _ _ _ ι _ R _ _ _ C _ _ _ π p s hπ hmin hX hps
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  haveI : IsCO O O := ⟨‹IsAdicComplete (maximalIdeal O) O›, ⟨fun a ha => by simpa using ha⟩,
    fun x => ⟨x, by simp⟩⟩
  haveI : IsCO O (MvPowerSeries ι O) := co_mvps O O ι
  have hq : ∀ x : C, p (s (p x)) = p x := fun x => by
    have := congrArg (fun φ : R →ₐ[O] R => φ (p x)) hps
    simpa using this
  have hE : ∀ x : C, x - s (p x) ∈ RingHom.ker p := fun x => by
    rw [RingHom.mem_ker, map_sub, hq, sub_self]
  have hloc : ∀ x : C, x ∈ maximalIdeal C → s (p x) ∈ maximalIdeal C := fun x hx =>
    (ns_loc s (p x)).2 ((ns_loc p x).2 hx)
  have hle : RingHom.ker p ≤ maximalIdeal C • RingHom.ker p := by
    intro t ht
    obtain ⟨g, rfl⟩ := hπ t
    have hpt : p (π g) = 0 := RingHom.mem_ker.mp ht
    have hg : g ∈ RingHom.ker (p.comp π) := by
      rw [RingHom.mem_ker, AlgHom.comp_apply, hpt]
    obtain ⟨k, hk, hgk⟩ := ns_dec g (hmin.2 g hg)
    have e : π g = π g - s (p (π g)) := by rw [hpt, map_zero, sub_zero]
    rw [e, hgk]

    simp only [map_add (f := _), map_sum, map_mul, AlgHom.commutes]
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hk' : π (k i) ∈ maximalIdeal C := (ns_loc π (k i)).2 (hk i)
    have eq : π (MvPowerSeries.X i) * π (k i) - s (p (π (MvPowerSeries.X i))) * s (p (π (k i))) =
        π (k i) • (π (MvPowerSeries.X i) - s (p (π (MvPowerSeries.X i)))) +
          s (p (π (MvPowerSeries.X i))) • (π (k i) - s (p (π (k i)))) := by
      simp only [smul_eq_mul]
      ring
    rw [eq]
    exact Submodule.add_mem _ (Submodule.smul_mem_smul hk' (hE _))
      (Submodule.smul_mem_smul (hloc _ (hX i)) (hE _))
  have hbot : RingHom.ker p = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal C) _ (IsNoetherian.noetherian _) hle
      (IsLocalRing.maximalIdeal_le_jacobson _)
  exact (RingHom.injective_iff_ker_eq_bot p).2 hbot
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem ac_const {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R) (c : R) :
    AdicCont I fun _ : Γ => c := fun _ => IsLocallyConstant.const _

private theorem ac_mul {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R} {f g : Γ → R}
    (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun s => f s * g s := fun N => by
  simp only [map_mul]
  exact (hf N).mul (hg N)

private theorem ac_sum {Γ R ι : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R} (S : Finset ι)
    {f : ι → Γ → R} (hf : ∀ i, AdicCont I (f i)) : AdicCont I fun s => ∑ i ∈ S, f i s := by
  intro N
  have e : (fun s => Ideal.Quotient.mk (I ^ N) (∑ i ∈ S, f i s)) = ∑ i ∈ S, fun s => Ideal.Quotient.mk (I ^ N) (f i s) := by
    funext s

    simp only [map_sum, Finset.sum_apply]
  rw [e]
  exact Finset.sum_induction _ IsLocallyConstant (fun _ _ ha hb => ha.add hb) (IsLocallyConstant.const 0) (fun i _ => hf i N)

private theorem gl_lift {n : ℕ} (O : Type) [CommRing O] [IsLocalRing O] (C' : Type) [CommRing C'] [Algebra O C']
    [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C) (hp : Function.Surjective p)
    (hk : maximalIdeal C' * RingHom.ker p = ⊥) (Γ : Type) [TopologicalSpace Γ] (x : Γ → GL (Fin n) C)
    (hx : ∀ i j, AdicCont (maximalIdeal C) fun s => x s i j) :
    ∃ y : Γ → GL (Fin n) C', (∀ i j, AdicCont (maximalIdeal C') fun s => y s i j) ∧
      (∀ s, GeneralLinearGroup.map (p : C' →+* C) (y s) = x s) ∧
      ∀ i j, (∀ s, x s i j = 0) → ∀ s, y s i j = 0 := by
  classical
  have hloc : ∀ a : C', IsUnit (p a) → IsUnit a := by
    intro a ha
    by_contra hna
    obtain ⟨b, hb⟩ := hp (↑ha.unit⁻¹ : C)
    have hK : a * b - 1 ∈ RingHom.ker (p : C' →+* C) := by
      rw [RingHom.mem_ker]
      show p (a * b - 1) = 0
      rw [map_sub, map_mul, map_one, hb, IsUnit.mul_val_inv, sub_self]
    have hKm : RingHom.ker (p : C' →+* C) ≤ maximalIdeal C' := IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
    have ham : a ∈ maximalIdeal C' := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact hna
    have h1 : (1 : C') ∈ maximalIdeal C' := by
      have h2 := sub_mem (Ideal.mul_mem_right b _ ham) (hKm hK)
      simpa using h2
    exact (maximalIdeal.isMaximal C').ne_top ((Ideal.eq_top_iff_one _).2 h1)
  let Y : Fin n → Fin n → Γ → C' := fun i j =>
    if ∀ s, x s i j = 0 then fun _ => 0 else Classical.choose (pr_sec O C' C p hp hk Γ (fun s => x s i j) (hx i j))
  have hYc : ∀ i j, AdicCont (maximalIdeal C') (Y i j) := by
    intro i j
    by_cases h : ∀ s, x s i j = 0
    · simp only [Y, if_pos h]
      exact fun _ => IsLocallyConstant.const _
    · simp only [Y, if_neg h]
      exact (Classical.choose_spec (pr_sec O C' C p hp hk Γ (fun s => x s i j) (hx i j))).1
  have hYp : ∀ i j s, p (Y i j s) = x s i j := by
    intro i j s
    by_cases h : ∀ s, x s i j = 0
    · simp only [Y, if_pos h, map_zero]
      exact (h s).symm
    · simp only [Y, if_neg h]
      exact (Classical.choose_spec (pr_sec O C' C p hp hk Γ (fun s => x s i j) (hx i j))).2 s
  have hY0 : ∀ i j, (∀ s, x s i j = 0) → ∀ s, Y i j s = 0 := by
    intro i j h s
    simp only [Y, if_pos h]
  let M : Γ → Matrix (Fin n) (Fin n) C' := fun s => Matrix.of fun i j => Y i j s
  have hMp : ∀ s, (M s).map p = (x s : Matrix (Fin n) (Fin n) C) := by
    intro s
    ext i j
    exact hYp i j s
  have hdet : ∀ s, IsUnit (M s).det := by
    intro s
    apply hloc
    have e : p (M s).det = ((M s).map p).det := RingHom.map_det (p : C' →+* C) (M s)
    rw [e, hMp]
    exact Matrix.isUnits_det_units (x s)
  refine ⟨fun s => Matrix.nonsingInvUnit (M s) (hdet s), fun i j => hYc i j, fun s => ?_, fun i j h s => hY0 i j h s⟩
  apply Units.ext
  exact hMp s

theorem UpperTheory.V.Fr.pr_setlift :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C) (B : Box F n C), Function.Surjective p → maximalIdeal C' * RingHom.ker p = ⊥ → B.Cont (maximalIdeal C) → Nonempty (SetLift p B) := by
  intro l _ k _ _ F C₀ n hF O _ _ C' _ _ _ C _ _ _ p B hp hk hcont
  obtain ⟨r, hrc, hrm, -⟩ := gl_lift O C' C p hp hk F.Γ (fun s => (B.r s).left) (fun i j => hcont i j)
  have hg : ∀ v, ∃ a : GL (Fin n) C', GeneralLinearGroup.map (p : C' →+* C) a = B.g v := by
    intro v
    obtain ⟨y, -, hy, -⟩ := gl_lift O C' C p hp hk Unit (fun _ => B.g v)
      (fun i j N => IsLocallyConstant.of_constant _ (fun _ _ => rfl))
    exact ⟨y (), hy ()⟩
  have ht : ∀ v, ∃ y : F.Gv v → GL (Fin n) C', (∀ i j, AdicCont (maximalIdeal C') fun s => y s i j) ∧
      (∀ s, GeneralLinearGroup.map (p : C' →+* C) (y s) = B.g v * (B.r (F.loc v s)).left * (B.g v)⁻¹) ∧
      ∀ s, UpT (y s : Matrix (Fin n) (Fin n) C') := by
    intro v
    have hM : ∀ a b, AdicCont (maximalIdeal C) fun s : F.Gv v => (B.r (F.loc v s)).mat a b :=
      fun a b N => (hcont a b N).comp_continuous (continuous_subtype_val.comp (hF.loc_cont v))
    have hx : ∀ i j, AdicCont (maximalIdeal C) fun s : F.Gv v => ((B.g v * (B.r (F.loc v s)).left * (B.g v)⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) i j := by
      intro i j
      simp only [Units.val_mul, Matrix.mul_apply]
      exact ac_sum _ (f := fun q s => (∑ a, (B.g v : Matrix (Fin n) (Fin n) C) i a * (B.r (F.loc v s)).mat a q) * ((B.g v)⁻¹ : GL (Fin n) C) q j)
        fun q => ac_mul (ac_sum _ (f := fun a s => (B.g v : Matrix (Fin n) (Fin n) C) i a * (B.r (F.loc v s)).mat a q)
          fun a => ac_mul (ac_const _ _) (hM a q)) (ac_const _ _)
    obtain ⟨y, hyc, hym, hy0⟩ := gl_lift O C' C p hp hk (F.Gv v) _ hx
    refine ⟨y, hyc, hym, fun s i j hij => hy0 i j (fun s' => B.tri v s' i j hij) s⟩
  choose g hgm using hg
  choose t htc htm htt using ht
  exact ⟨⟨r, hrc, hrm, g, hgm, t, htc, htt, htm⟩⟩
end
