module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.Bundle001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteOrderValuation.WeakApprox
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

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So.WeakMultiplicityOne

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

private theorem mem_int (w : Plc L) (x : Kw w) : x ∈ 𝒪[Kw w] ↔ Valued.v x ≤ 1 := by
  rw [Valuation.mem_integer_iff, ← Valuation.vle_one_iff]
  show Valued.v x ≤ Valued.v 1 ↔ _
  rw [map_one]

private theorem mem_Uc (w : Plc L) (n : ℕ) (y : (Kw w)ˣ)
    (h : Valued.v ((y : Kw w) - 1) < WithZero.exp (-(n : ℤ))) : y ∈ Uc (Kw w) n := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer L w
  set ϖ : Kw w := algebraMap L (Kw w) π with hϖdef
  have hϖ : Valued.v ϖ = WithZero.exp (-1) := by rw [hϖdef, PI.FinOrdValD.WA.val_alg, hπ]
  have hpow : Valued.v ϖ ^ n = WithZero.exp (-(n : ℤ)) := by
    rw [hϖ, ← WithZero.exp_nsmul]
    simp
  have hexp1 : WithZero.exp (-(n : ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have hlt1 : Valued.v ((y : Kw w) - 1) < 1 := lt_of_lt_of_le h hexp1
  have hvy : Valued.v (y : Kw w) = 1 := by
    have e : (y : Kw w) = 1 + ((y : Kw w) - 1) := by ring
    rw [e, Valuation.map_add_eq_of_lt_left]
    · exact map_one _
    · rw [map_one]; exact hlt1
  have hvyi : Valued.v ((y⁻¹ : (Kw w)ˣ) : Kw w) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hvy, inv_one]
  have hyO : (y : Kw w) ∈ 𝒪[Kw w] := (mem_int w _).2 hvy.le
  have hyiO : ((y⁻¹ : (Kw w)ˣ) : Kw w) ∈ 𝒪[Kw w] := (mem_int w _).2 hvyi.le
  let u : 𝒪[Kw w]ˣ := ⟨⟨y, hyO⟩, ⟨_, hyiO⟩, Subtype.ext (by simp), Subtype.ext (by simp)⟩
  have hϖO : ϖ ∈ 𝒪[Kw w] := (mem_int w _).2 (by
    rw [hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega)
  let ϖ₀ : 𝒪[Kw w] := ⟨ϖ, hϖO⟩
  have hϖne : ϖ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hϖ
    exact WithZero.exp_ne_zero hϖ.symm
  have hm : ϖ₀ ∈ 𝓂[Kw w] := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨t, ht⟩
    have h1 : ((t : 𝒪[Kw w]) : Kw w) * (((t⁻¹ : 𝒪[Kw w]ˣ) : 𝒪[Kw w]) : Kw w) = 1 := by
      rw [← Subring.coe_mul, t.mul_inv]
      rfl
    have hv : Valued.v (((t⁻¹ : 𝒪[Kw w]ˣ) : 𝒪[Kw w]) : Kw w) ≤ 1 :=
      (mem_int w _).1 ((t⁻¹ : 𝒪[Kw w]ˣ) : 𝒪[Kw w]).2
    have h2 := congrArg Valued.v h1
    rw [map_mul, map_one, ht] at h2
    change Valued.v ϖ * _ = 1 at h2
    rw [hϖ] at h2
    have h3 : WithZero.exp (-1) * Valued.v (((t⁻¹ : 𝒪[Kw w]ˣ) : 𝒪[Kw w]) : Kw w) ≤
        WithZero.exp (-1) := mul_le_of_le_one_right' hv
    rw [h2, ← WithZero.exp_zero, WithZero.exp_le_exp] at h3
    omega
  have hz : ((y : Kw w) - 1) / ϖ ^ n ∈ 𝒪[Kw w] := (mem_int w _).2 (by
    rw [map_div₀, map_pow, hpow]
    exact div_le_one_of_le₀ h.le zero_le')
  refine ⟨u, ?_, Units.ext rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker, Units.ext_iff]
  change Ideal.Quotient.mk _ (u : 𝒪[Kw w]) = 1
  rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
  have e : (u : 𝒪[Kw w]) - 1 = ϖ₀ ^ n * ⟨_, hz⟩ := by
    apply Subtype.ext
    push_cast
    change (y : Kw w) - 1 = ϖ ^ n * (((y : Kw w) - 1) / ϖ ^ n)
    field_simp
  rw [e]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hm n)

end UpperTheory.V.Z.Sym.So.WeakMultiplicityOne

open UpperTheory.V.Z.Sym.So.WeakMultiplicityOne in
theorem UpperTheory.V.Z.Sym.So.weakOne :
    UpperTheory.V.Z.Sym.So.WeakOne := by
  intro L _ _ _ S hS x c
  classical
  set cj := IsCMField.complexConj L with hcj
  have hfr : Module.finrank (maximalRealSubfield L) L = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hsp : ∀ w ∈ S, ∃ u : Plc L, u ≠ w ∧ u ∉ S ∧ GlobalTheory.Mem.Chr.ConjPl cj.toRingEquiv w u := by
    intro w hw
    obtain ⟨u, hne, hu⟩ := hS.split w hw
    refine ⟨u, hne, fun huS => hne (hS.inj huS hw hu), ?_⟩
    rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl cj hfr (IsCMField.complexConj_ne_one L) w u).1 hu with h | h
    · exact absurd h hne
    · exact h
  choose! ub hub using hsp
  set E : ℕ := ∑ w ∈ S, c w with hE
  obtain ⟨a, ha, -⟩ := PI.FinOrdValD.WA.weakApprox_units (S ∪ S.image ub)
    (fun v => if v ∈ S then x v else 1) (fun _ => (E : ℤ))
  have hcc : cj (cj (a : L)) = a := IsCMField.complexConj_apply_apply L _
  have ha0 : (a : L) ≠ 0 := a.ne_zero
  have hca0 : cj (a : L) ≠ 0 := by
    intro h0
    apply ha0
    rw [← hcc, h0, map_zero]
  let ca : Lˣ := Units.mk0 (cj (a : L)) hca0
  refine ⟨a * ca⁻¹, ?_, ?_⟩
  · simp only [Units.val_mul, Units.val_inv_eq_inv_val, ca, Units.val_mk0, map_mul, map_inv₀, hcc]
    field_simp
  · intro w hw
    obtain ⟨hne, hnS, hconj⟩ := hub w hw
    apply mem_Uc w (c w)
    have hA := ha w (Finset.mem_union_left _ hw)
    have hB := ha (ub w) (Finset.mem_union_right _ (Finset.mem_image_of_mem ub hw))
    simp only [hw, hnS, if_true, if_false, inv_one, Units.val_one, mul_one] at hA hB
    have hB' : Valued.v (algebraMap L (Kw w) (cj a) - 1) < WithZero.exp (-(E : ℤ)) := by
      have e1 : algebraMap L (Kw w) (cj a) - 1 = algebraMap L (Kw w) (cj ((a : L) - 1)) := by
        simp [map_sub]
      rw [e1, PI.FinOrdValD.WA.val_alg, ← hconj (cj ((a : L) - 1))]
      change HeightOneSpectrum.valuation L (ub w) (cj (cj ((a : L) - 1))) < _
      rw [IsCMField.complexConj_apply_apply, ← PI.FinOrdValD.WA.val_alg, map_sub, map_one]
      exact hB
    have hexp : WithZero.exp (-(E : ℤ)) ≤ WithZero.exp (-((c w : ℕ) : ℤ)) := by
      have hcw : c w ≤ E := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hw
      rw [WithZero.exp_le_exp]
      omega
    have hexp1 : WithZero.exp (-(E : ℤ)) ≤ 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
    have hvB : Valued.v (algebraMap L (Kw w) (cj a)) = 1 := by
      have e : algebraMap L (Kw w) (cj a) = 1 + (algebraMap L (Kw w) (cj a) - 1) := by ring
      rw [e, Valuation.map_add_eq_of_lt_left]
      · exact map_one _
      · rw [map_one]; exact lt_of_lt_of_le hB' hexp1
    have hB0 : algebraMap L (Kw w) (cj a) ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hvB
      exact zero_ne_one hvB
    have hexpr : ((Units.map (algebraMap L (Kw w) : L →* Kw w) (a * ca⁻¹) / x w : (Kw w)ˣ) : Kw w) =
        (algebraMap L (Kw w) a * (((x w)⁻¹ : (Kw w)ˣ) : Kw w)) * (algebraMap L (Kw w) (cj a))⁻¹ := by
      simp only [Units.val_div_eq_div_val, Units.coe_map, Units.val_mul, Units.val_inv_eq_inv_val, ca,
        Units.val_mk0, MonoidHom.coe_coe, map_mul, map_inv₀, div_eq_mul_inv]
      ring
    rw [hexpr]
    have e2 : (algebraMap L (Kw w) a * (((x w)⁻¹ : (Kw w)ˣ) : Kw w)) * (algebraMap L (Kw w) (cj a))⁻¹ - 1
        = ((algebraMap L (Kw w) a * (((x w)⁻¹ : (Kw w)ˣ) : Kw w) - 1) -
          (algebraMap L (Kw w) (cj a) - 1)) * (algebraMap L (Kw w) (cj a))⁻¹ := by
      field_simp
      ring
    rw [e2, map_mul, map_inv₀, hvB, inv_one, mul_one]
    exact lt_of_lt_of_le (Valuation.map_sub_lt _ hA hB') hexp

end
end

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem det_lt {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (t : Fin n → kˣ) (i : Fin n) :
    Matrix.GeneralLinearGroup.det (leviTorus k (Fin n) t i) = t i := congrFun ((leviTorus k (Fin n)).symm_apply_apply t) i

private theorem abs_one_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    absPow k 1 = (absPow k (-1))⁻¹ := by
  have h0 : absPow k 0 = 1 := by
    ext x
    simp [val_absPow]
  apply eq_inv_of_mul_eq_one_left
  rw [← absPow_add, show (1 : ℂ) + -1 = 0 by ring, h0]

private theorem abs_zero_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    absPow k 0 = 1 := by
  ext x
  simp [val_absPow]

theorem UpperTheory.V.Z.Sym.So.expoEq :
    UpperTheory.V.Z.Sym.So.ExpoEq := by
  intro k _ _ _ _ a
  have hA : ∀ x : kˣ, absPow k 1 x = (absPow k (-1) x)⁻¹ := by
    intro x
    rw [abs_one_eq]
    rfl
  have hZ : ∀ x : kˣ, absPow k 0 x = 1 := by
    intro x
    rw [abs_zero_eq]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro d
    have m0 : modExp (fun _ : Fin 3 => Unit) 0 = 2 := by decide
    have m1 : modExp (fun _ : Fin 3 => Unit) 1 = 0 := by decide
    have m2 : modExp (fun _ : Fin 3 => Unit) 2 = -2 := by decide
    unfold Dict.expo
    rw [← Units.val_mul]
    congr 1
    rw [torusChar_apply, MonoidHom.comp_apply, deltaHalf_apply, Fin.prod_univ_three, Fin.prod_univ_three]
    simp only [MulEquiv.coe_toMonoidHom, det_lt, m0, m1, m2]
    have e0 : ((2 : ℤ) : ℂ) / 2 = 1 := by norm_num
    have e1 : ((0 : ℤ) : ℂ) / 2 = 0 := by norm_num
    have e2 : ((-2 : ℤ) : ℂ) / 2 = -1 := by norm_num
    rw [e0, e1, e2, hA, hZ]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, MonoidHom.one_apply, MonoidHom.inv_apply, map_div]
    ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_div_eq_div_val, Units.val_one]
    simp
    ring
  · intro t
    have m0 : modExp (fun _ : Fin 2 => Unit) 0 = 1 := by decide
    have m1 : modExp (fun _ : Fin 2 => Unit) 1 = -1 := by decide
    unfold Dict.expo
    rw [← Units.val_mul]
    congr 1
    rw [torusChar_apply, MonoidHom.comp_apply, deltaHalf_apply, Fin.prod_univ_two, Fin.prod_univ_two]
    simp only [MulEquiv.coe_toMonoidHom, det_lt, m0, m1]
    have hh : absPow k ((1 : ℤ) / 2) = absPow k 1 * absPow k ((-1 : ℤ) / 2) := by
      rw [← absPow_add]
      congr 1
      push_cast
      ring
    rw [hh]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      MonoidHom.one_apply, MonoidHom.mul_apply, hA, map_inv]
    ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_one]
    field_simp
  · intro n ψ
    refine ⟨fun d => Units.ne_zero _, ?_, ?_⟩
    · unfold Dict.expo
      simp
    · intro d d'
      unfold Dict.expo
      rw [← Units.val_mul]
      congr 1
      rw [map_mul, map_mul, mul_inv]
      ext
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]
      ring

end
end

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

section SlopeTestRemainingChoices

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

private theorem coe_mem_orbit (U : Subgroup G) (a g : G) :
    (g : G ⧸ U) ∈ MulAction.orbit U (a : G ⧸ U) ↔ g ∈ DC U a := by
  constructor
  · rintro ⟨u, hu⟩
    have h : ((u.1 * a : G) : G ⧸ U) = g := by rw [← hu]; rfl
    rw [QuotientGroup.eq] at h
    exact ⟨u.1, u.2, (u.1 * a)⁻¹ * g, h, by group⟩
  · rintro ⟨u, hu, u', hu', rfl⟩
    refine ⟨⟨u, hu⟩, ?_⟩
    show ((u * a : G) : G ⧸ U) = ((u * a * u' : G) : G ⧸ U)
    rw [QuotientGroup.eq, show (u * a)⁻¹ * (u * a * u') = u' by group]
    exact hu'

private theorem out_mem_orbit (U : Subgroup G) (a : G) (y : G ⧸ U) :
    y ∈ MulAction.orbit U (a : G ⧸ U) ↔ y.out ∈ DC U a := by
  rw [← coe_mem_orbit, QuotientGroup.out_eq']

private theorem val_out (U : Subgroup G) {φ : G → V} (hφ : ∀ u ∈ U, ∀ g, φ (g * u) = φ g)
    (g y : G) (q : G ⧸ U) (h : (y : G ⧸ U) = q) : φ (g * q.out) = φ (g * y) := by
  have hm : y⁻¹ * q.out ∈ U := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    exact h
  have e := hφ _ hm (g * y)
  rw [show g * y * (y⁻¹ * q.out) = g * q.out by group] at e
  exact e

private theorem dcF_eq_mem (U : Subgroup G) (a : G) (φ : G → V) :
    dcF U a φ = (∑ᶠ q ∈ MulAction.orbit U (a : G ⧸ U), rightReg ℂ G V q.out) φ := by
  show (∑ᶠ q : ↑(MulAction.orbit U (a : G ⧸ U)), rightReg ℂ G V (Quotient.out (q : G ⧸ U))) φ = _
  rw [finsum_set_coe_eq_finsum_mem (f := fun q : G ⧸ U => rightReg ℂ G V q.out)]

private theorem dcF_apply (U : Subgroup G) (a : G) (h : (MulAction.orbit U (a : G ⧸ U)).Finite)
    (φ : G → V) (g : G) :
    dcF U a φ g = ∑ y ∈ Set.Finite.toFinset h, φ (g * y.out) := by
  rw [dcF_eq_mem, finsum_mem_eq_finite_toFinset_sum _ h]
  simp [LinearMap.sum_apply, Finset.sum_apply, rightReg, LinearMap.funLeft]

end SlopeTestRemainingChoices

end UpperTheory.V.Z.Sym.So

theorem UpperTheory.V.Z.Sym.So.dcBasic :
    UpperTheory.V.Z.Sym.So.DcBasic := by
  intro G V _ _ _ U a hfin0 φ hφ
  classical
  have hfin : (MulAction.orbit U (a : G ⧸ U)).Finite := hfin0
  have hO : ∀ (v : U) (y : G ⧸ U), y ∈ MulAction.orbit U (a : G ⧸ U) →
      v • y ∈ MulAction.orbit U (a : G ⧸ U) := by
    rintro v y ⟨w, rfl⟩
    exact ⟨v * w, mul_smul v w _⟩
  have h5 : ∀ (R : Finset G), (∀ y ∈ R, y ∈ DC U a) →
      (∀ y ∈ DC U a, ∃! r, r ∈ R ∧ r⁻¹ * y ∈ U) → ∀ g, dcF U a φ g = ∑ r ∈ R, φ (g * r) := by
    intro R hR hu g
    rw [dcF_apply U a hfin φ g]
    symm
    refine Finset.sum_bij (fun r _ => (r : G ⧸ U)) ?_ ?_ ?_ ?_
    · intro r hr
      rw [Set.Finite.mem_toFinset]
      exact (coe_mem_orbit U a r).mpr (hR r hr)
    · intro r1 hr1 r2 hr2 he
      have h12 : r1⁻¹ * r2 ∈ U := QuotientGroup.eq.mp he
      have h22 : r2⁻¹ * r2 ∈ U := by rw [inv_mul_cancel]; exact U.one_mem
      exact (hu r2 (hR r2 hr2)).unique ⟨hr1, h12⟩ ⟨hr2, h22⟩
    · intro y hy
      rw [Set.Finite.mem_toFinset] at hy
      obtain ⟨r, ⟨hr, hry⟩, -⟩ := hu _ ((out_mem_orbit U a y).mp hy)
      refine ⟨r, hr, ?_⟩
      show (r : G ⧸ U) = y
      rw [← QuotientGroup.out_eq' y, QuotientGroup.eq]
      exact hry
    · intro r hr
      exact (val_out U hφ g r (r : G ⧸ U) rfl).symm
  refine ⟨?_, ?_, ?_, ?_, h5⟩
  · intro u hu g
    rw [dcF_apply U a hfin φ, dcF_apply U a hfin φ]
    let u' : U := ⟨u, hu⟩
    refine Finset.sum_nbij' (fun y => u' • y) (fun y => u'⁻¹ • y) ?_ ?_ ?_ ?_ ?_
    · intro y hy
      simp only [Finset.mem_coe, Set.Finite.mem_toFinset] at hy ⊢
      exact hO u' y hy
    · intro y hy
      simp only [Finset.mem_coe, Set.Finite.mem_toFinset] at hy ⊢
      exact hO u'⁻¹ y hy
    · intro y _
      exact inv_smul_smul u' y
    · intro y _
      exact smul_inv_smul u' y
    · intro y _
      have hq : ((u * y.out : G) : G ⧸ U) = u' • y := by
        conv_rhs => rw [← QuotientGroup.out_eq' y]
        rfl
      rw [mul_assoc]
      exact (val_out U hφ g (u * y.out) (u' • y) hq).symm
  · intro g
    rw [dcF_apply U a hfin φ g, ← finsum_mem_eq_finite_toFinset_sum _ hfin]
    simp only [out_mem_orbit]
  · intro b hb
    rw [dcF_eq_mem, dcF_eq_mem, MulAction.orbit_eq_iff.mpr ((coe_mem_orbit U a b).mpr hb)]
  · intro ha
    funext g
    rw [h5 {1} ?_ ?_ g, Finset.sum_singleton, mul_one]
    · intro y hy
      rw [Finset.mem_singleton] at hy
      subst hy
      exact ⟨a⁻¹, U.inv_mem ha, 1, U.one_mem, by group⟩
    · rintro y ⟨v, hv, v', hv', rfl⟩
      refine ⟨1, ⟨Finset.mem_singleton_self _, ?_⟩, ?_⟩
      · rw [inv_one, one_mul]
        exact U.mul_mem (U.mul_mem hv ha) hv'
      · rintro r ⟨hr, -⟩
        exact Finset.mem_singleton.mp hr

end
end

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem lev_ext' {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {V V' : Sig.Lev k} (hc : V.c = V'.c) (hH : V.H = V'.H) : V = V' := by
  cases V
  cases V'
  cases hc
  cases hH
  rfl

theorem UpperTheory.V.Z.Sym.So.fitExt :
    UpperTheory.V.Z.Sym.So.FitExt := by
  intro L _ _ _ B T S₀ S V₀ VL A₀ A h₀ h hS hV hI
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := (h₀.sg v).1 hv
    exact (h.sg _).2 ⟨w, hS hw, rfl⟩
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := (h₀.sg v).1 hv
    have hs : IsSplitAt w := h₀.pl.split w (Finset.mem_coe.2 hw)
    rw [h.s w (hS hw) hs, h₀.s w hw hs]
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := (h₀.sg v).1 hv
    have hs : IsSplitAt w := h₀.pl.split w (Finset.mem_coe.2 hw)
    have e : A.V (un w) = A₀.V (un w) :=
      lev_ext' (by rw [h.c w (hS hw), h₀.c w hw, hV w hw]) (by
        ext x
        rw [← h.H w (hS hw) hs x, ← h₀.H w hw hs x, hV w hw])
    rw [e]
  · intro v hv hn
    obtain ⟨w, hw, rfl⟩ := (h.sg v).1 hv
    have hw0 : w ∉ S₀ := fun hw0 => hn ((h₀.sg _).2 ⟨w, hw0, rfl⟩)
    have hs : IsSplitAt w := h.pl.split w (Finset.mem_coe.2 hw)
    have hi := hI w hw hw0
    have e : A.V (un w) = Sig.Lev.iw _ :=
      lev_ext' (by rw [h.c w hw, hi]; rfl) (by
        ext x
        rw [← h.H w hw hs x, hi]
        exact (T w hs).Uo x)
    rw [e]

end
end
