module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.HodgeTateFromSandwich
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.EUInvApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle002
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.ThFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle004
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.IsIntegralLf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.Bundle001

@[expose] public section

section

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

private theorem tau_of_roots {k : Type} [Field k] (h2 : (2 : k) ≠ 0) (a : kˣ) (τ : k)
    (h : (X - C (a : k)) * (X - C 1) * (X - C ((a⁻¹ : kˣ) : k)) = ((X - 1) * (X ^ 2 - C τ * X + 1) : k[X])) :
    τ = (a : k) + ((a⁻¹ : kˣ) : k) := by
  have hu : C (a : k) * C ((a⁻¹ : kˣ) : k) = 1 := by
    rw [← C_mul, Units.mul_inv, C_1]
  have e1 : (X - C (a : k)) * (X - C 1) * (X - C ((a⁻¹ : kˣ) : k)) =
      (X - 1) * (X ^ 2 - C ((a : k) + ((a⁻¹ : kˣ) : k)) * X + 1) := by
    rw [C_add, C_1]
    linear_combination (X - 1) * hu
  rw [e1] at h
  have hne : (X - 1 : k[X]) ≠ 0 := by simpa using X_sub_C_ne_zero (1 : k)
  have h' := mul_left_cancel₀ hne h
  have hc := congrArg (fun q : k[X] => q.coeff 1) h'
  simp only [coeff_add, coeff_sub, coeff_C_mul_X, coeff_X_pow, coeff_one] at hc
  norm_num at hc
  rw [Units.val_inv_eq_inv_val]
  linear_combination hc

private theorem charpoly_dg {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b c : kˣ) :
    (((dg ![a, b, c] : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)).charpoly = (X - C (a : k)) * (X - C (b : k)) * (X - C (c : k)) := by
  rw [dg.eq_1, val_diagT, charpoly_diagonal]
  simp [Fin.prod_univ_three]

theorem UpperTheory.V.Z.Sym.Sig.okG :
    UpperTheory.V.Z.Sym.Sig.OkG := by
  intro k _ _ _ _ O _ _ hO h2 Δ s hs hs0 V Ry hRy χ hχ t ht
  simp only [Lev.data.eq_1, Set.mem_setOf_eq] at ht ⊢
  obtain ⟨hbij, htheta, -, htau⟩ := eU_facts k O hO h2 Δ s hs hs0
  have hinv : ∀ (d : Fin 3 → kˣ) (u : GL (Fin 3) k), u ∈ V.J 3 →
      ∀ u' ∈ V.J 3, ∀ g, V.unitaryDoubleCosetIndicator d (u * g * th k 3 u') = V.unitaryDoubleCosetIndicator d g :=
    fun d u hu u' hu' g => ((eqG k V 1 ∅ ∅ 1 1 d).1 u hu u' hu' g).1
  have hfin : ∀ d : Fin 3 → kˣ,
      {y : GL (Fin 3) k ⧸ Subgroup.map (th k 3) (V.J 3) | V.unitaryDoubleCosetIndicator d (Quotient.out y) ≠ 0}.Finite :=
    fun d => (eqG k V 1 ∅ ∅ 1 1 d).2.1
  refine ⟨?_, ?_, ?_⟩
  · intro u hu y
    rw [Subgroup.mem_comap] at hu
    constructor
    · simp only [map_mul, Lev.unitaryHeckeTestSum.eq_1]
      refine Finset.sum_congr rfl fun z _ => ?_
      simpa [map_one] using hinv _ (eU hs u) hu 1 (Subgroup.one_mem _) (eU hs y)
    · simp only [map_mul, htheta, Lev.unitaryHeckeTestSum.eq_1]
      refine Finset.sum_congr rfl fun z _ => ?_
      simpa using hinv _ 1 (Subgroup.one_mem _) (eU hs u) hu (eU hs y)
  · let ψ : U3 Δ ⧸ Subgroup.comap (eU hs) (V.J 3) → GL (Fin 3) k ⧸ Subgroup.map (th k 3) (V.J 3) :=
      fun x => QuotientGroup.mk (th k 3 (eU hs (Quotient.out x)))
    have hψ : Function.Injective ψ := by
      intro x x' hxx
      rw [← QuotientGroup.out_eq' x, ← QuotientGroup.out_eq' x']
      rw [QuotientGroup.eq] at hxx ⊢
      rw [Subgroup.mem_comap]
      obtain ⟨j, hj, hjeq⟩ := Subgroup.mem_map.1 hxx
      have hth : Function.Injective (th k 3) := fun a b hab => by
        have := congrArg (th k 3) hab
        rwa [(thFacts k V).2.2.2.1, (thFacts k V).2.2.2.1] at this
      rw [← map_inv, ← map_mul, ← map_inv, ← map_mul] at hjeq
      rw [← hth hjeq]
      exact hj
    let T : Set (GL (Fin 3) k ⧸ Subgroup.map (th k 3) (V.J 3)) :=
      ⋃ y ∈ Ry, {z | V.unitaryDoubleCosetIndicator ![t * (unif k)⁻¹, y, (unif k)⁻¹] (Quotient.out z) ≠ 0}
    have hT : T.Finite := Set.Finite.biUnion Ry.finite_toSet fun y _ => hfin _
    refine (hT.preimage hψ.injOn).subset fun x hx => ?_
    have hx' : V.unitaryHeckeTestSum Ry t (eU hs (theta Δ (Quotient.out x))) ≠ 0 := hx
    rw [htheta, Lev.unitaryHeckeTestSum.eq_1] at hx'
    obtain ⟨y, hy, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx'
    simp only [Set.mem_preimage, T, Set.mem_iUnion, Set.mem_setOf_eq]
    refine ⟨y, hy, ?_⟩
    obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.map (th k 3) (V.J 3))
      (th k 3 (eU hs (Quotient.out x)))
    obtain ⟨j, hj, hjm⟩ := Subgroup.mem_map.1 m.2
    change V.unitaryDoubleCosetIndicator _ (Quotient.out (QuotientGroup.mk (th k 3 (eU hs (Quotient.out x))) :
      GL (Fin 3) k ⧸ Subgroup.map (th k 3) (V.J 3))) ≠ 0
    rw [hm, ← hjm]
    have e := hinv ![t * (unif k)⁻¹, y, (unif k)⁻¹] 1 (Subgroup.one_mem _) j hj
      (th k 3 (eU hs (Quotient.out x)))
    rw [one_mul] at e
    rw [e]
    exact hne
  · intro δ τ hτ hne
    rw [Lev.unitaryHeckeTestSum.eq_1] at hne
    obtain ⟨y, hy, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hv : (valuation k) ((unif k : kˣ) : k) < 1 := by
      rw [GlAx.unif_spec]
      exact uniformizer_lt_one
    have hv0 : 0 < (valuation k) ((unif k : kˣ) : k) := by
      rw [zero_lt_iff]
      exact (_root_.map_ne_zero _).2 (unif k).ne_zero
    obtain ⟨hy1, hy2⟩ := hRy.1 y hy
    have h01 : (valuation k) ((t * (unif k)⁻¹ : kˣ) : k) < (valuation k) (y : k) := by
      rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, ← div_eq_mul_inv,
        div_lt_iff₀ hv0]
      calc (valuation k) (t : k) < (valuation k) ((unif k : kˣ) : k) ^ 2 := ht
        _ = (valuation k) ((unif k : kˣ) : k) * (valuation k) ((unif k : kˣ) : k) := sq _
        _ ≤ (valuation k) (y : k) * (valuation k) ((unif k : kˣ) : k) := by gcongr
    have h12 : (valuation k) (y : k) < (valuation k) (((unif k)⁻¹ : kˣ) : k) := by
      rw [Units.val_inv_eq_inv_val, map_inv₀]
      exact hy2.trans_lt ((one_lt_inv₀ hv0).2 hv)
    have hSD : SDom ![t * (unif k)⁻¹, y, (unif k)⁻¹] := by
      rw [SDom.eq_1]
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij
      all_goals first
        | exact h01
        | exact h12
        | exact h01.trans h12
    obtain ⟨g₀, x, y', z, hδ, hH⟩ := supp0 k V _ hSD _ hne
    have hd : (![t * (unif k)⁻¹, y, (unif k)⁻¹] 0 / ![t * (unif k)⁻¹, y, (unif k)⁻¹] 2 : kˣ) = t := by
      simp
    rw [hd] at hH
    have hcp := (htau δ τ).1 hτ
    rw [hδ, (normalG k).1 g₀ x y' z] at hcp
    have hc2 : ((g₀ * dg ![x / z, 1, z / x] * g₀⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).charpoly
        = (X - C ((x / z : kˣ) : k)) * (X - C 1) * (X - C (((x / z)⁻¹ : kˣ) : k)) := by
      rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, charpoly_units_conj, charpoly_dg,
        inv_div, Units.val_one]
    rw [hc2] at hcp
    have hτ' := tau_of_roots h2 (x / z) τ hcp
    rw [Ind.eq_1]
    refine ⟨x / z / t, hH, ?_⟩
    have hm : t * (x / z / t) = x / z := by
      rw [mul_comm]
      exact div_mul_cancel (x / z) t
    rw [hm]
    exact hτ'

end
end

section

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

private theorem okK_val_lt (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : kˣ)
    (ht : valuation k (t : k) < valuation k (unif k : k) ^ 2) : valuation k (t : k) < 1 := by
  have hw : valuation k (unif k : k) < 1 := by
    rw [GlAx.unif_spec]
    exact uniformizer_lt_one
  exact ht.trans (pow_lt_one₀ zero_le' hw two_ne_zero)

private theorem okK_conj {k : Type} [Field k] (g₀ : GL (Fin 2) k) (a b : kˣ) :
    ((g₀ * diagT k (Fin 2) ![a, b] * g₀⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).trace = (a : k) + b ∧
    ((g₀ * diagT k (Fin 2) ![a, b] * g₀⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).det = (a : k) * b := by
  have hinv : ((g₀⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * (g₀ : Matrix (Fin 2) (Fin 2) k) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
  simp only [Matrix.GeneralLinearGroup.coe_mul, val_diagT]
  constructor
  · rw [Matrix.trace_mul_cycle, hinv, one_mul]
    simp [Matrix.trace_diagonal, Fin.sum_univ_two]
  · rw [Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul, hinv,
      Matrix.det_one, one_mul]
    simp [Matrix.det_diagonal, Fin.prod_univ_two]

theorem UpperTheory.V.Z.Sym.Sig.okK :
    UpperTheory.V.Z.Sym.Sig.OkK := by
  intro k _ _ _ _ O _ _ hO h2 Δ s hs hs0 V Ry hR χ hχ t ht S
  have htv : valuation k (t : k) < 1 := okK_val_lt k t ht
  have hSD : SDom (![t, 1] : Fin 2 → kˣ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij
    simpa using htv
  have hχH : ∀ u ∈ V.H, χ u = 1 := fun u hu => hχ u (V.H_le hu)
  obtain ⟨_, hZJ, hZd⟩ := eqZ k V χ hχH 2 two_pos
  obtain ⟨_, hmul, hJJ, hfin⟩ := hZd ![t, 1] hSD
  obtain ⟨_, _, _, hIsScal, hmt, hcomap⟩ := eD_facts k O hO h2 Δ s hs hs0
  have hfK : ∀ g, S.fK t g = (((χ t)⁻¹ : ℂˣ) : ℂ) * V.fZ χ ![t, 1] (eD hs g) := fun g => rfl
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro u hu y
    have hu' : eD hs u ∈ V.J 2 := hu
    constructor
    · rw [hfK, hfK, map_mul]
      have e := hJJ (eD hs u) hu' 1 (Subgroup.one_mem _) (eD hs y)
      rw [mul_one] at e
      rw [e]
    · rw [hfK, hfK, map_mul]
      have e := hJJ 1 (Subgroup.one_mem _) (eD hs u) hu' (eD hs y)
      rw [one_mul] at e
      rw [e]
  · intro z s' hz y
    rw [hfK, hfK, map_mul, (hIsScal z s').mp hz, hmul]
    ring
  · have hcj : Subgroup.comap (eD hs) (V.ZJ 2) = ZD Δ ⊔ S.J2 := hcomap V
    have hright : ∀ (g w : GL (Fin 2) k), w ∈ V.ZJ 2 →
        (V.fZ χ ![t, 1] (g * w) ≠ 0 ↔ V.fZ χ ![t, 1] g ≠ 0) := by
      intro g w hw
      obtain ⟨z, j, hj, rfl⟩ := (hZJ w).mp hw
      have hc : g * GeneralLinearGroup.scalar (Fin 2) z = GeneralLinearGroup.scalar (Fin 2) z * g := by
        apply Units.ext
        simp only [Units.val_mul, GeneralLinearGroup.coe_scalar]
        exact (scalar_commute (z : k) (fun r => Commute.all _ r) (g : Matrix (Fin 2) (Fin 2) k)).eq.symm
      have e := hJJ 1 (Subgroup.one_mem _) j hj g
      rw [one_mul] at e
      rw [← mul_assoc, hc, mul_assoc, hmul, e]
      exact ⟨fun h => right_ne_zero_of_mul h, fun h => mul_ne_zero (Units.ne_zero _) h⟩
    let φ : (DX Δ ⧸ (ZD Δ ⊔ S.J2)) → (GL (Fin 2) k ⧸ V.ZJ 2) :=
      fun x => (QuotientGroup.mk (eD hs x.out))
    have hφ : ∀ x x', φ x = φ x' → x = x' := by
      intro x x' he
      have hm := QuotientGroup.eq.mp he
      rw [← map_inv, ← map_mul, ← Subgroup.mem_comap, hcj] at hm
      rw [← QuotientGroup.out_eq' x, ← QuotientGroup.out_eq' x']
      exact QuotientGroup.eq.mpr hm
    refine (Set.Finite.preimage (f := φ) (fun x _ x' _ he => hφ x x' he) hfin).subset ?_
    intro x hx
    simp only [Set.mem_setOf_eq, Set.mem_preimage] at hx ⊢
    rw [hfK] at hx
    have hx' := right_ne_zero_of_mul hx
    show V.fZ χ ![t, 1] (Quotient.out (QuotientGroup.mk (eD hs x.out) : GL (Fin 2) k ⧸ V.ZJ 2)) ≠ 0
    obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul (V.ZJ 2) (eD hs x.out)
    rw [hw, hright _ _ w.2]
    exact hx'
  · intro g hg
    rw [hfK] at hg
    have hg' : V.fZ χ ![t, 1] (eD hs g) ≠ 0 := right_ne_zero_of_mul hg
    obtain ⟨g₀, a, b, hgeq, hab⟩ := suppZ k V χ ![t, 1] hSD (eD hs g) hg'
    have ha := a.ne_zero
    have hb := b.ne_zero
    refine ⟨((a / b : kˣ) : k) + ((a / b : kˣ)⁻¹ : kˣ), ⟨a / b / t, ?_, ?_⟩, ?_⟩
    · exact (by simpa using hab : a / b / t ∈ V.H)
    · have e : t * (a / b / t) = a / b := by rw [mul_comm, div_mul_cancel]
      rw [e]
    · obtain ⟨hdet, htr⟩ := hmt g
      rw [show dg ![a, b] = diagT k (Fin 2) ![a, b] from rfl] at hgeq
      obtain ⟨htr', hdet'⟩ := okK_conj g₀ a b
      rw [hdet, htr, hgeq, htr', hdet', ← map_pow, ← map_mul]
      congr 1
      simp only [Units.val_div_eq_div_val, Units.val_inv_eq_inv_val, inv_div]
      field_simp
      ring

end
end
