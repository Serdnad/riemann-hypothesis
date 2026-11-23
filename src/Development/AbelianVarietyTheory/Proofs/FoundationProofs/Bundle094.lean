module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle065
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle062
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem corner_val_le_one {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) (i j : Fin n) : valuation k (g.val i j) ≤ 1 := by
  obtain ⟨g, rfl⟩ := hg
  exact (g.val i j).2

theorem corner_mem_KO {g : GL (Fin n) k} (hM : ∀ i j, valuation k (g.val i j) ≤ 1) (hd : valuation k g.val.det = 1) :
    g ∈ KO k (Fin n) := by
  let N : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨g.val i j, hM i j⟩
  have e : (algebraMap 𝒪[k] k).mapMatrix N = g.val := rfl
  have hu : IsUnit N.det := by
    refine (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 ?_
    rw [RingHom.map_det, e, hd]
  obtain ⟨u, hu'⟩ := (Matrix.isUnit_iff_isUnit_det N).2 hu
  refine ⟨u, Units.ext ?_⟩
  change (algebraMap 𝒪[k] k).mapMatrix u.val = g.val
  rw [hu', e]

end

theorem corner_rankOne : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ x ∈ KO k (Fin n), ∀ a b : Fin n, a < b → ¬ Triv (ψ a / ψ b) (x.val a b) → (∀ j, b < j → Triv (ψ a / ψ j) (x.val a j)) → ∃ j ∈ grp ψ, ∃ (u : kˣ) (s : k), valuation k (u : k) = 1 ∧ valuation k s ≤ 1 ∧ s * x.val a b = (u : k) - 1 ∧ ψ a u ≠ ψ b u ∧ theta ψ j = (ψ b u : ℂ) ∧ x * j * x⁻¹ ∈ KO k (Fin n) ∧ (x * j * x⁻¹).val = 1 + Matrix.vecMulVec (fun i => s * x.val i b) (Pi.single a 1) := by
  intro k _ _ _ _ n ψ hord x hx a b hab hnt htr
  have hnt' := hnt
  unfold Triv at hnt'
  push_neg at hnt'
  obtain ⟨u, hu, hle, hne⟩ := hnt'
  have hx0 : x.val a b ≠ 0 := fun h0 => hnt (h0 ▸ triv_zero _)
  set s : k := ((u : k) - 1) / x.val a b with hs
  have hsx : s * x.val a b = (u : k) - 1 := div_mul_cancel₀ _ hx0
  have hs1 : valuation k s ≤ 1 := by
    rw [hs, map_div₀]
    exact div_le_one_of_le₀ hle zero_le'
  have hsm : ∀ i j, valuation k (s * x.val i j) ≤ valuation k (x.val i j) := fun i j => by
    rw [map_mul]
    exact mul_le_of_le_one_left' hs1
  let M : Matrix (Fin n) (Fin n) k := 1 + Matrix.vecMulVec (Pi.single b s) (x.val a)
  have hdet : M.det = (u : k) := by
    simp only [M]
    rw [Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct_single, mul_comm, hsx]
    ring
  let j : GL (Fin n) k := Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact u.ne_zero)
  have hj : j.val = 1 + Matrix.vecMulVec (Pi.single b s) (x.val a) := rfl
  have hjK : j ∈ KO k (Fin n) := by
    refine corner_mem_KO (fun i l => ?_) (by rw [show j.val.det = (u : k) from hdet]; exact hu)
    rw [hj, Matrix.add_apply]
    refine Valuation.map_add_le _ ?_ ?_
    · rw [Matrix.one_apply]; split_ifs <;> simp
    · rw [Matrix.vecMulVec_apply, Pi.single_apply]
      split_ifs
      · exact (hsm _ _).trans (corner_val_le_one hx _ _)
      · simp
  refine ⟨j, ⟨hjK, fun i l hil => ?_⟩, u, s, hu, hs1, hsx, ?_, ?_, ?_, ?_⟩
  · rw [hj, Matrix.add_apply, Matrix.one_apply_ne hil.ne, zero_add, Matrix.vecMulVec_apply, Pi.single_apply]
    split_ifs with h
    · subst h
      exact triv_mono _ _ _ (hsm _ _) (hord a i l l hab.le hil.le le_rfl _ (htr l hil))
    · rw [zero_mul]; exact triv_zero _
  · intro h
    apply hne
    simp [h]
  · refine theta_rankOne k n ψ j _ _ b u hu hj fun i => ?_
    rw [Pi.single_apply]
    split_ifs with h
    · rw [h, hsx]
    · simp
  · exact mul_mem (mul_mem hx hjK) (inv_mem hx)
  · have hxx : x.val * (x⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [Units.val_mul, Units.val_mul, hj, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hxx, Matrix.mul_vecMulVec,
      Matrix.vecMulVec_mul]
    congr 2
    · ext i
      simp [Matrix.mulVec_single, mul_comm]
    · ext l
      have := congrFun (congrFun hxx a) l
      rw [Matrix.mul_apply] at this
      rw [Matrix.vecMul, dotProduct]
      rw [Pi.single_apply, this, Matrix.one_apply]
      simp [eq_comm]

end GlobalTheory.PsType
end
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.EvUniq

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]


variable (Ω) in
def zpHom : ℤ_[p] →+* Ω :=
  (algebraMap (O0 p) Ω).comp ((algebraMap (Lau p) (O0 p)).comp HahnSeries.C)

theorem zpHom_apply (z : ℤ_[p]) : zpHom (Ω := Ω) z = zp Ω z := by
  simp [zpHom, zp, HahnSeries.C_apply]

theorem zp_neg (z : ℤ_[p]) : zp Ω (-z) = - zp Ω z := by
  rw [← zpHom_apply, map_neg, zpHom_apply]

theorem zpHom_injective (hc : IsClo p Ω) : Function.Injective (zpHom (p := p) (Ω := Ω)) := by
  haveI := Basic.charZero_of_isClo hc
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro m hm
  by_contra h0
  rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hm
  have hu : zpHom (Ω := Ω) ((PadicInt.unitCoeff h0 : ℤ_[p])) ≠ 0 :=
    ((Units.isUnit (PadicInt.unitCoeff h0)).map (zpHom (Ω := Ω))).ne_zero
  have hp0 : (p : Ω) ^ m.valuation ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)
  exact mul_ne_zero hu hp0 hm

theorem exists_coords (hc : IsClo p Ω) {ι : Type} [Fintype ι] (E : ι → Ω) :
    ∃ (κ : Type) (_ : Fintype κ) (f : κ → Ω) (M : ι → κ → ℤ_[p]),
      (∀ k, E k = ∑ i, zp Ω (M k i) * f i) ∧
      ∀ v : ι → ℤ_[p], ∑ k, zp Ω (v k) * E k = 0 → ∀ i, ∑ k, v k * M k i = 0 := by
  letI : Algebra ℤ_[p] Ω := (zpHom (p := p) (Ω := Ω)).toAlgebra
  have hsm : ∀ (m : ℤ_[p]) (x : Ω), m • x = zp Ω m * x := fun m x => by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, zpHom_apply]
  haveI : NoZeroSMulDivisors ℤ_[p] Ω := ⟨fun {m x} hmx => by
    rw [hsm] at hmx
    rcases mul_eq_zero.1 hmx with h0 | h0
    · left; exact zpHom_injective hc (by rw [zpHom_apply, h0, map_zero])
    · right; exact h0⟩
  let S : Submodule ℤ_[p] Ω := Submodule.span ℤ_[p] (Set.range E)
  haveI : Module.Finite ℤ_[p] S := Module.Finite.span_of_finite _ (Set.finite_range E)
  haveI : Module.Free ℤ_[p] S := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis ℤ_[p] S
  have hE : ∀ k, E k ∈ S := fun k => Submodule.subset_span ⟨k, rfl⟩
  refine ⟨Module.Free.ChooseBasisIndex ℤ_[p] S, inferInstance, fun i => (b i : Ω),
    fun k i => b.repr ⟨E k, hE k⟩ i, ?_, ?_⟩
  · intro k
    have h2 := congrArg Subtype.val (b.sum_repr ⟨E k, hE k⟩)
    rw [Submodule.coe_sum] at h2
    simp only [Submodule.coe_smul, hsm] at h2
    exact h2.symm
  · intro v hv i
    have h0 : (∑ k, v k • (⟨E k, hE k⟩ : S)) = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul, hsm, Submodule.coe_zero]
      exact hv
    have := congrArg (fun s => b.repr s i) h0

    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at this
    exact this

theorem psi_C {T : Tower p Ω} {n : ℕ} {ψ : O0 p →+* Ω} (h : IsReb T n ψ) (m : ℤ_[p]) :
    ψ (algebraMap (Lau p) (O0 p) (HahnSeries.C m)) = zp Ω m := by
  rw [h.sub (HahnSeries.C m) (HahnSeries.C m), zp, HahnSeries.C_apply]
  · intro i
    simp only [HahnSeries.C_apply, HahnSeries.coeff_single]
    by_cases hi : i = 0
    · simp [hi]
    · have : (p : ℤ) ^ n * i ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)) hi
      simp [hi, this]
  · intro r hr
    have : r ≠ 0 := by rintro rfl; exact hr (dvd_zero _)
    simp [HahnSeries.C_apply, HahnSeries.coeff_single, this]

theorem sum_psi_eq_zero (hc : IsClo p Ω) {T : Tower p Ω} {n : ℕ} {ψ : O0 p →+* Ω} (h : IsReb T n ψ)
    {ι : Type} [Fintype ι] (E : ι → Ω) (A G : ι → Lau p) (φ : ℤ → ℤ_[p])
    (hA : ∀ r, ∑ k, E k * zp Ω ((A k).coeff r) = 0)
    (hG : ∀ k r, (G k).coeff r = φ r * (A k).coeff r) :
    ∑ k, E k * ψ (algebraMap (Lau p) (O0 p) (G k)) = 0 := by
  obtain ⟨κ, _, f, M, hE, hind⟩ := exists_coords hc E
  have hB : ∀ i, ∑ k, HahnSeries.C (M k i) * G k = 0 := by
    intro i
    apply HahnSeries.ext
    funext r
    rw [HahnSeries.coeff_sum]
    simp only [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul, hG,
      HahnSeries.coeff_zero]
    have h1 := hind (fun k => (A k).coeff r) (by rw [← hA r]; exact Finset.sum_congr rfl fun k _ => mul_comm _ _) i
    calc ∑ k, M k i * (φ r * (A k).coeff r) = φ r * ∑ k, (A k).coeff r * M k i := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
      _ = 0 := by rw [h1, mul_zero]
  calc ∑ k, E k * ψ (algebraMap (Lau p) (O0 p) (G k))
      = ∑ i, f i * ψ (algebraMap (Lau p) (O0 p) (∑ k, HahnSeries.C (M k i) * G k)) := by

        simp only [map_sum, map_mul, psi_C h, hE, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
    _ = 0 := by simp only [hB, map_zero, mul_zero, Finset.sum_const_zero]

theorem thL_coeff (a : Lau p) (r : ℤ) : (thL a).coeff r = (r : ℤ_[p]) * a.coeff r := rfl

theorem ev_unique : ∀ (p : ℕ) [Fact p.Prime], ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : GlobalTheory.K5.Tower p Ω) (n : ℕ), ∀ (ψ : O0 p →+* Ω), IsReb T n ψ → ∀ (c : ℤ → Ω) (x x' y y' : Ω),
    Ev ψ c x x' → Ev ψ c y y' → x = y ∧ x' = y' := by
  intro p _ Ω _ _ hc T n ψ h c x x' y y' hx hy
  obtain ⟨d, e, a, -, hca, rfl, rfl⟩ := hx
  obtain ⟨d', e', a', -, hca', rfl, rfl⟩ := hy
  let E : Fin d ⊕ Fin d' → Ω := Sum.elim e e'
  let A : Fin d ⊕ Fin d' → Lau p := Sum.elim a (fun s => -a' s)
  have hA : ∀ r, ∑ k, E k * zp Ω ((A k).coeff r) = 0 := by
    intro r
    simp only [E, A, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, HahnSeries.coeff_neg, zp_neg,
      mul_neg, Finset.sum_neg_distrib]
    linear_combination hca' r - hca r
  have h1 := sum_psi_eq_zero hc h E A A (fun _ => 1) hA (fun k r => by simp)
  have h2 := sum_psi_eq_zero hc h E A (fun k => thL (A k)) (fun r => (r : ℤ_[p])) hA
    (fun k r => thL_coeff _ _)
  have thL_neg : ∀ b : Lau p, thL (-b) = - thL b := fun b => by
    apply HahnSeries.ext
    funext r
    simp only [thL_coeff, HahnSeries.coeff_neg, mul_neg]
  simp only [E, A, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, map_neg, mul_neg,
    Finset.sum_neg_distrib, thL_neg] at h1 h2
  exact ⟨sub_eq_zero.1 (by simpa [sub_eq_add_neg] using h1), sub_eq_zero.1 (by simpa [sub_eq_add_neg] using h2)⟩

end GlobalTheory.EvUniq
end
end

section

open scoped MatrixGroups

open Polynomial

namespace GlobalTheory.K4.LevNormal

open GlobalTheory.KZ

theorem normal_of_fixed (F L : Type) [Field F] [Field L] [Algebra F L] [Algebra.IsAlgebraic F L]
    (h : ∀ x : L, (∀ σ : L ≃ₐ[F] L, σ x = x) → x ∈ Set.range (algebraMap F L)) : Normal F L := by
  classical
  rw [normal_iff]
  intro x
  have hx : IsIntegral F x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  refine ⟨hx, ?_⟩
  have hfin : (Set.range fun σ : L ≃ₐ[F] L => σ x).Finite := by
    refine ((minpoly F x).rootSet_finite L).subset ?_
    rintro _ ⟨σ, rfl⟩
    rw [mem_rootSet]
    refine ⟨minpoly.ne_zero hx, ?_⟩
    show aeval (σ x) (minpoly F x) = 0
    rw [aeval_algHom_apply, minpoly.aeval, map_zero]
  set O := hfin.toFinset with hO
  set P : L[X] := ∏ g ∈ O, (X - C g) with hP
  have hmap : ∀ σ : L ≃ₐ[F] L, P.map (σ : L →+* L) = P := by
    intro σ
    rw [hP, Polynomial.map_prod]
    simp only [Polynomial.map_sub, map_X, map_C]
    refine Finset.prod_bijective σ σ.bijective ?_ (fun _ _ => rfl)
    intro g
    simp only [hO, Set.Finite.mem_toFinset, Set.mem_range]
    constructor
    · rintro ⟨τ, rfl⟩
      exact ⟨σ * τ, rfl⟩
    · rintro ⟨τ, hτ⟩
      refine ⟨σ⁻¹ * τ, ?_⟩
      show σ.symm (τ x) = g
      rw [hτ, σ.symm_apply_apply]
  have hl : P ∈ lifts (algebraMap F L) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    apply h
    intro σ
    have := congrArg (fun Q => Q.coeff n) (hmap σ)
    simpa [coeff_map] using this
  have hmon : P.Monic := monic_prod_of_monic _ _ fun g _ => monic_X_sub_C g
  obtain ⟨Q, hQ⟩ := (mem_lifts P).1 hl
  have h0 : aeval x Q = 0 := by
    rw [aeval_def, ← eval_map, hQ, hP, eval_prod]
    refine Finset.prod_eq_zero (i := x) ?_ (by simp)
    simp only [hO, Set.Finite.mem_toFinset, Set.mem_range]
    exact ⟨1, rfl⟩
  have hd : (minpoly F x).map (algebraMap F L) ∣ P := by
    rw [← hQ]
    exact Polynomial.map_dvd _ (minpoly.dvd F x h0)
  have hs : P.Splits := Splits.prod fun g _ => Splits.X_sub_C g
  exact hs.of_dvd hmon.ne_zero hd

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem isAlgebraic_of_jK_mem [Algebra.IsAlgebraic ℚ Ω] (X : Tower Ω ε) (F : Subfield X.K) (hj : X.jK ∈ F) (f : X.K) :
    IsAlgebraic F f := by
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : CharZero X.K := charZero_of_injective_algebraMap (algebraMap Ω X.K).injective
  let A : IntermediateField F X.K := algebraicClosure F X.K
  have hc : ∀ c : Ω, algebraMap Ω X.K c ∈ A := by
    intro c
    rw [mem_algebraicClosure_iff]
    have h1 : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 (Algebra.IsAlgebraic.isAlgebraic c)
    have h2 : IsAlgebraic ℤ (algebraMap Ω X.K c) := h1.algHom (algebraMap Ω X.K).toIntAlgHom
    exact h2.extendScalars (R := ℤ) (S := F) (RingHom.injective_int _)
  let B : IntermediateField Ω X.K := A.toSubfield.toIntermediateField hc
  have hle : IntermediateField.adjoin Ω {X.jK} ≤ B := by
    rw [IntermediateField.adjoin_simple_le_iff]
    exact A.algebraMap_mem ⟨X.jK, hj⟩
  have h3 : IsAlgebraic A f := by
    obtain ⟨p, hp, h0⟩ := X.alg_j f
    let φ : IntermediateField.adjoin Ω {X.jK} →+* A :=
      (IntermediateField.adjoin Ω {X.jK}).toSubfield.subtype.codRestrict A fun y => hle y.2
    refine ⟨p.map φ, (Polynomial.map_ne_zero_iff φ.injective).2 hp, ?_⟩
    rw [aeval_def, eval₂_map]
    exact h0
  exact h3.restrictScalars F

theorem gal_mem_lev (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (m : ℕ) (ζ : Ω) (hm : 0 < m) (hζ : IsPrimitiveRoot ζ m)
    (hΓ : CongruenceSubgroup.Gamma m ≤ Γ') (s : Ω ≃ₐ[ℚ] Ω) (hs : s ζ = ζ) (f : X.K) (hf : f ∈ lev X Γ') :
    X.gal s f ∈ lev X Γ' := by
  rw [mem_lev_iff] at hf ⊢
  intro γ hγ
  have := X.recip m f hm (fun δ hδ => hf δ (hΓ hδ)) ζ hζ s 1 (by simpa using hs) γ γ (by simp)
  rw [← this, hf γ hγ]

theorem normal : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra.IsAlgebraic ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (m : ℕ) (ζ : Ω), 0 < m → IsPrimitiveRoot ζ m → CongruenceSubgroup.Gamma m ≤ Γ' → letI := GlobalTheory.K4.algMdl X Γ' (IntermediateField.adjoin ℚ {ζ}).fixingSubgroup; Normal (GlobalTheory.K4.mdl X Γ' (IntermediateField.adjoin ℚ {ζ}).fixingSubgroup) (GlobalTheory.K4.lev X Γ') := by
  intro Ω _ _ _ ε X Γ' m ζ hm hζ hΓ
  set S := (IntermediateField.adjoin ℚ {ζ}).fixingSubgroup with hS
  letI := algMdl X Γ' S
  haveI := isScalarTower_mdl X Γ' S
  haveI : Algebra.IsAlgebraic (mdl X Γ' S) (lev X Γ') := ⟨fun f =>
    (isAlgebraic_algebraMap_iff (A := X.K) (lev X Γ').subtype.injective).1
      (isAlgebraic_of_jK_mem X _ (jK_mem_mdl X Γ' S) (f : X.K))⟩
  apply normal_of_fixed
  intro x hx
  refine ⟨⟨x, (mem_mdl_iff X Γ' S _).2 ⟨x.2, fun s hs => ?_⟩⟩, rfl⟩
  have hsζ : s ζ = ζ := hs ⟨ζ, IntermediateField.subset_adjoin ℚ {ζ} rfl⟩
  let φ : lev X Γ' →ₐ[mdl X Γ' S] lev X Γ' :=
    { ((X.gal s).toRingHom.comp (lev X Γ').subtype).codRestrict (lev X Γ')
        (fun f => gal_mem_lev X Γ' m ζ hm hζ hΓ s hsζ f f.2) with
      commutes' := fun y => Subtype.ext (((mem_mdl_iff X Γ' S _).1 y.2).2 s hs) }
  exact congrArg Subtype.val (hx (AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ)))

end GlobalTheory.K4.LevNormal
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.Glue

theorem Prim.mul {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (P Q : HahnSeries ℚ Ω) :
    Prim A P → Prim A Q → Prim A (P * Q) := by
  classical
  rintro ⟨hPA, rP, hrP0, hrPi⟩ ⟨hQA, rQ, hrQ0, hrQi⟩
  let lift : ∀ φ : HahnSeries ℚ Ω, (∀ r, φ.coeff r ∈ A) → HahnSeries ℚ A := fun φ h =>
    { coeff := fun r => ⟨φ.coeff r, h r⟩
      isPWO_support' := φ.isPWO_support.mono (fun r hr h' => hr (Subtype.ext (by simpa using h'))) }
  let P' := lift P hPA
  let Q' := lift Q hQA
  let ι : A →ₙ+* Ω := (A.subtype : A →+* Ω)
  have hPm : P'.map ι = P := by ext r; rfl
  have hQm : Q'.map ι = Q := by ext r; rfl
  have hmul : (P' * Q').map ι = P * Q := by rw [HahnSeries.map_mul, hPm, hQm]
  have hcoeff : ∀ r, (P * Q).coeff r = (((P' * Q').coeff r : A) : Ω) := by
    intro r; rw [← hmul]; rfl

  have hunit : ∀ (x : Ω) (hx : x ∈ A), x ≠ 0 → x⁻¹ ∈ A → IsUnit (⟨x, hx⟩ : A) := by
    intro x hx h0 hi
    have h : (⟨x, hx⟩ : A) * ⟨x⁻¹, hi⟩ = 1 := Subtype.ext (by simp [mul_inv_cancel₀ h0])
    exact (Units.mkOfMulEqOne _ _ h).isUnit
  let π : A →ₙ+* IsLocalRing.ResidueField A := (IsLocalRing.residue A : A →+* IsLocalRing.ResidueField A)
  have hred : ∀ (φ : HahnSeries ℚ Ω) (h : ∀ r, φ.coeff r ∈ A) (r : ℚ), φ.coeff r ≠ 0 → (φ.coeff r)⁻¹ ∈ A →
      (lift φ h).map π ≠ 0 := by
    intro φ h r h0 hi hz
    have := congrArg (fun ψ : HahnSeries ℚ (IsLocalRing.ResidueField A) => ψ.coeff r) hz
    simp only [HahnSeries.coeff_zero] at this
    have hu := hunit _ (h r) h0 hi
    have hres : IsLocalRing.residue A (⟨φ.coeff r, h r⟩ : A) = 0 := this
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hres
    exact hres hu
  have hne : (P' * Q').map π ≠ 0 := by
    rw [HahnSeries.map_mul]
    exact mul_ne_zero (hred P hPA rP hrP0 hrPi) (hred Q hQA rQ hrQ0 hrQi)
  obtain ⟨r, hr⟩ : ∃ r, ((P' * Q').map π).coeff r ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (HahnSeries.ext (funext h))
  have hr' : IsLocalRing.residue A ((P' * Q').coeff r) ≠ 0 := hr
  rw [Ne, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hr'
  obtain ⟨u, hu⟩ := hr'
  have h1 : (((P' * Q').coeff r : A) : Ω) * (((u⁻¹ : Aˣ) : A) : Ω) = 1 := by
    rw [← hu]
    have := congrArg (fun a : A => (a : Ω)) u.mul_inv
    simpa only [MulMemClass.coe_mul, OneMemClass.coe_one] using this
  refine ⟨fun r => by rw [hcoeff r]; exact ((P' * Q').coeff r).2, r, ?_, ?_⟩
  · rw [hcoeff r]; exact left_ne_zero_of_mul_eq_one h1
  · rw [hcoeff r, inv_eq_of_mul_eq_one_right h1]; exact ((u⁻¹ : Aˣ) : A).2

end GlobalTheory.Glue
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.Glue

theorem theta_coeff {Ω : Type} [Field Ω] [Algebra ℚ Ω] (s : ℚ) (φ : HahnSeries ℚ Ω) (r : ℚ) :
    (theta s φ).coeff r = algebraMap ℚ Ω (s * r) * φ.coeff r := rfl

theorem theta_leibniz_add_const :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (s : ℚ) (P Q : HahnSeries ℚ Ω),
      theta s (P * Q) = theta s P * Q + P * theta s Q ∧ theta s (P + Q) = theta s P + theta s Q ∧
        ∀ c : Ω, theta s (HahnSeries.C c) = 0 := by
  intro Ω _ _ s P Q
  refine ⟨?_, ?_, ?_⟩
  · ext r
    have h1 : (theta s P).support ⊆ P.support := fun t ht h => ht (by simp [theta_coeff, h])
    have h2 : (theta s Q).support ⊆ Q.support := fun t ht h => ht (by simp [theta_coeff, h])
    rw [HahnSeries.coeff_add, HahnSeries.coeff_mul_left' P.isPWO_support h1,
      HahnSeries.coeff_mul_right' Q.isPWO_support h2, theta_coeff, HahnSeries.coeff_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ij hij => ?_
    have := (Finset.mem_addAntidiagonal.1 hij).2.2
    rw [← this, theta_coeff, theta_coeff, mul_add, map_add (f := _)]; ring
  · ext r; simp [theta_coeff, mul_add]
  · intro c; ext r
    rw [theta_coeff]
    by_cases h : r = 0
    · simp [h]
    · simp [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne h]

end GlobalTheory.Glue
end
