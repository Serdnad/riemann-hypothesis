module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.ResLeMemDec
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.CuspRep GlobalTheory.GalOfCusp

namespace UpperTheory.V.Ws.Pt

theorem adicPt {l : ℕ} [Fact l.Prime] (c : Coef l) {R : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R]
    (y : R →ₐ[c.O] PadicAlgCl l) {Γ : Type} [TopologicalSpace Γ] (f : Γ → R) (hf : AdicCont (maximalIdeal R) f) :
    Continuous fun g => y (f g) := by
  obtain ⟨a, ha1, ha0, hbd⟩ := ((coPt c R).1 y).2
  rw [continuous_iff_continuousAt]
  intro g0
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε ha1
  have hopen := (hf N).isOpen_fiber (Ideal.Quotient.mk (maximalIdeal R ^ N) (f g0))
  filter_upwards [hopen.mem_nhds rfl] with g hg
  have hmem : f g - f g0 ∈ maximalIdeal R ^ N := Ideal.Quotient.eq.mp hg
  rw [dist_eq_norm, ← map_sub]
  exact lt_of_le_of_lt (hbd N _ hmem) hN

theorem trCont {Γ k ι : Type} [Group Γ] [TopologicalSpace Γ] [ContinuousMul Γ] [CommRing k] [TopologicalSpace k]
    [IsTopologicalRing k] [Fintype ι] [DecidableEq ι] (r : Γ →* Matrix ι ι k) (hr : Irr r)
    (ht : Continuous fun g => (r g).trace) : Continuous r := by
  have hr' : Submodule.span k (Set.range r) = ⊤ := hr
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have hE : Matrix.single j i (1 : k) ∈ Submodule.span k (Set.range r) := by
    rw [hr']
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hE
  have key : ∀ g, r g i j = c.sum fun h a => a * (r (g * h)).trace := by
    intro g
    have h1 : r g i j = (r g * Matrix.single j i 1).trace := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply]
      rw [Finset.sum_eq_single i (by intro b _ hb; simp [Ne.symm hb]) (by simp),
        Finset.sum_eq_single j (by intro b _ hb; simp [Ne.symm hb]) (by simp)]
      simp
    rw [h1, ← hc, Finsupp.sum, Matrix.mul_sum, Matrix.trace_sum, Finsupp.sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, map_mul]
  have hfun : (fun g => r g i j) = fun g => c.sum fun h a => a * (r (g * h)).trace :=
    funext key
  rw [hfun]
  exact continuous_finsetSum _ fun h _ =>
    continuous_const.mul (ht.comp (continuous_id.mul continuous_const))

theorem resLe_cont {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {F L : IntermediateField ℚ Ω} [NumberField F]
    [NumberField L] (hFL : F ≤ L) : Continuous (resLe hFL) := by
  letI : Algebra F L := (IntermediateField.inclusion hFL).toAlgebra
  haveI : IsScalarTower F L Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Af.continuous_restrictScalarsHom F L Ω

private theorem continuous_monoidHom_units_of_continuous_coe {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [ContinuousInv Γ]
    [Monoid M] [TopologicalSpace M] (φ : Γ →* Mˣ) (h : Continuous fun g => (φ g : M)) :
    Continuous φ := by
  rw [Units.continuous_iff]
  refine ⟨h, (h.comp continuous_inv).congr fun g => ?_⟩
  simp only [Function.comp, map_inv]

theorem psi_cont {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : W.Resid V.frame c.O n} {B : W.UniversalOrdinaryDeterminantRing r}
    (x : B.Pt) (v : W.Vl l L) (i : Fin n) : Continuous (x.psi v i) := by
  letI := V.frame.tv v
  have h1 := adicPt c x _ (W.Resid.IsPsi.cont (B.u.psi v i))
  exact continuous_monoidHom_units_of_continuous_coe _ (h1.congr fun g => rfl)

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}
  {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h)

theorem twc_cont (n : ℕ) : Continuous (K.twc n) := by
  refine continuous_monoidHom_units_of_continuous_coe _ ?_
  have hA : AdicCont (maximalIdeal c'.O)
      fun g => ((K.κ g : c'.O) : c'.O) * ((K.β g : c'.O)) ^ n := by
    intro N
    have := (K.κ_cont N).comp₂ (K.β_cont N) (fun a b => a * b ^ n)
    convert this using 1
    funext g
    simp [map_mul, map_pow]
  have h1 := adicPt c' (Algebra.ofId c'.O (PadicAlgCl l)) _ hA
  refine h1.congr fun g => ?_
  rw [Link.twc_val]
  rfl

theorem rho_cont (n : ℕ) {r : G T.F Ω →* M4 (PadicAlgCl l)} (hr : Continuous r) : Continuous (K.rhoQ n r) := by
  refine continuous_monoidHom_units_of_continuous_coe _ ?_
  have h1 : Continuous fun g => ((K.twc n g : (PadicAlgCl l)ˣ) : PadicAlgCl l) :=
    Units.continuous_val.comp (twc_cont K n)
  have h2 := h1.smul (hr.comp (resLe_cont T.F_le))
  refine h2.congr fun g => ?_
  rw [Link.rho_val]
  rfl

variable {K}

theorem pt_cont (X : Space (T.fr ∅) (inc h)) (y : X.A →ₐ[c'.O] PadicAlgCl l)
    (hy : Irr (X.P.map (y : X.A →+* PadicAlgCl l)).r) : Continuous (X.P.map (y : X.A →+* PadicAlgCl l)).r := by
  apply trCont _ hy
  have hcoef := adicPt c' (y.comp (IsScalarTower.toAlgHom c'.O X.B X.A)) _ (X.cp_cont 3)
  refine hcoef.neg.congr fun g => ?_
  show -(y.comp (IsScalarTower.toAlgHom c'.O X.B X.A)) ((X.cp g).coeff 3) =
    ((X.P.r g).map (y : X.A →+* PadicAlgCl l)).trace
  rw [Matrix.trace_eq_neg_charpoly_coeff, Matrix.charpoly_map, ← X.cp_map g, Polynomial.map_map,
    Polynomial.coeff_map]
  simp

end UpperTheory.V.Ws.Pt
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.CuspRep GlobalTheory.GalOfCusp

private def formJ (R : Type) [CommRing R] : M4 R := !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]

private theorem formJ_adj {R : Type} [CommRing R] (X : M4 R) : formJ R * adj X = X.transpose * formJ R := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [formJ, adj_apply, sgn, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four]

private theorem formJ_sq (R : Type) [CommRing R] : formJ R * formJ R = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [formJ, Matrix.mul_apply, Fin.sum_univ_four]

private def formU (R : Type) [CommRing R] : GL (Fin 4) R :=
  ⟨formJ R, -formJ R, by rw [mul_neg, formJ_sq, neg_neg], by rw [neg_mul, formJ_sq, neg_neg]⟩

private theorem form_gsp {R : Type} [CommRing R] {ν : R} {X : M4 R} (hX : IsGSp ν X) :
    X.transpose * formJ R * X = ν • formJ R := by
  have hX' : adj X * X = ν • 1 := hX
  rw [← formJ_adj, Matrix.mul_assoc, hX', Matrix.mul_smul, Matrix.mul_one]

theorem UpperTheory.V.Ws.Pt.ptPair :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (n : ℕ) (r : G T.F Ω →* M4 (PadicAlgCl l)), (∀ g, IsGSp (algebraMap c'.O (PadicAlgCl l) (inc h (D.th (resQ T.F g)))) (r g)) → ∃ P : GL (Fin 4) (PadicAlgCl l), Af.IsPairing K.s.c (K.rhoQ n r) (cycBar T.L Ω l ^ (1 - ((4 : ℕ) : ℤ))) P := by
  intro Ω _ _ _ l _ c D T c' h K n r hr
  obtain ⟨j, hj⟩ := K.s.hc
  have hfixF : ∀ x : T.F, K.s.c (algebraMap T.F Ω x) = algebraMap T.F Ω x := by
    intro x
    apply j.injective
    rw [hj]
    have hw := IsTotallyReal.isReal (InfinitePlace.mk (j.comp (algebraMap T.F Ω)))
    rw [InfinitePlace.isReal_mk_iff, ComplexEmbedding.isReal_iff] at hw
    have hx := RingHom.congr_fun hw x
    simpa [ComplexEmbedding.conjugate_coe_eq] using hx
  let cF : G T.F Ω := AlgEquiv.ofRingEquiv (f := K.s.c.toRingEquiv) hfixF
  have hCiC : r cF⁻¹ * r cF = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hCCi : r cF * r cF⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  let U : GL (Fin 4) (PadicAlgCl l) := ⟨r cF⁻¹, r cF, hCiC, hCCi⟩
  refine ⟨formU (PadicAlgCl l) * U, ?_⟩
  intro s s' hs
  have hres : resLe T.F_le s' = cF * resLe T.F_le s * cF⁻¹ := by
    ext x
    have hx := DFunLike.congr_fun hs x
    first
      | exact hx
      | simpa [cF] using hx
  have hconj := K.conj s s' hs
  rw [K.rho_val, K.rho_val, hres, map_mul, map_mul]
  have hA := form_gsp (hr (resLe T.F_le s))
  have hU : ((formU (PadicAlgCl l) * U : GL (Fin 4) (PadicAlgCl l)) : M4 (PadicAlgCl l)) =
      formJ (PadicAlgCl l) * r cF⁻¹ := rfl
  rw [hU]
  have key : (r (resLe T.F_le s)).transpose * (formJ (PadicAlgCl l) * r cF⁻¹) *
      (r cF * r (resLe T.F_le s) * r cF⁻¹) =
      ((r (resLe T.F_le s)).transpose * formJ (PadicAlgCl l) * r (resLe T.F_le s)) * r cF⁻¹ := by
    calc _ = (r (resLe T.F_le s)).transpose * formJ (PadicAlgCl l) * (r cF⁻¹ * r cF) *
          r (resLe T.F_le s) * r cF⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hCiC, Matrix.mul_one]
  rw [hA, Matrix.smul_mul] at key
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [key, smul_smul]
  congr 1
  rw [K.twc_val, K.twc_val, ← map_mul, ← map_mul]
  have hq : resQ T.F (resLe T.F_le s) = resQ T.L s := rfl
  rw [hq]
  have hb : (↑(K.β s) : c'.O) * ↑(K.β s') = 1 := by rw [← Units.val_mul, hconj.2.1, Units.val_one]
  have e1 : (↑(K.κ s') * ↑(K.β s') ^ n : c'.O) * (↑(K.κ s) * ↑(K.β s) ^ n) * inc h ↑(D.th (resQ T.L s)) =
      ↑(K.κ s) * ↑(K.κ s') * inc h ↑(D.th (resQ T.L s)) := by
    calc _ = ↑(K.κ s) * ↑(K.κ s') * inc h ↑(D.th (resQ T.L s)) * (↑(K.β s) * ↑(K.β s')) ^ n := by ring
      _ = _ := by rw [hb, one_pow, mul_one]
  rw [e1]
  have e3 := congrArg (algebraMap c'.O (PadicAlgCl l)) hconj.1
  rw [map_mul, map_pow, map_one] at e3
  have hχ : algebraMap c'.O (PadicAlgCl l) ↑((chiO T.L Ω l c'.O) s) = (↑(cycBar T.L Ω l s) : PadicAlgCl l) := rfl
  rw [hχ] at e3
  rw [eq_inv_of_mul_eq_one_left e3]
  have hz : (1 - ((4 : ℕ) : ℤ)) = -3 := by norm_num
  rw [hz]
  first
    | simp [zpow_neg, Units.val_zpow_eq_zpow_val]
    | (rw [MonoidHom.zpow_apply]; simp [zpow_neg, Units.val_zpow_eq_zpow_val])
    | done
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.CuspRep GlobalTheory.GalOfCusp

private theorem aux {M : Type} [CommGroup M] (x y z : M) (a b : ℤ) (k n : ℕ) (h1 : (x * z ^ (-a)) ^ k = 1)
    (h2 : (y ^ 2 * z ^ (-b)) ^ k = 1) : ((x * y ^ n) ^ 2 * z ^ (-(2 * a + n * b))) ^ k = 1 := by
  have e : (x * y ^ n) ^ 2 * z ^ (-(2 * a + n * b)) = (x * z ^ (-a)) ^ 2 * (y ^ 2 * z ^ (-b)) ^ n := by
    simp only [mul_pow, ← zpow_natCast, ← zpow_mul, mul_zpow]
    rw [show -(2 * a + (n:ℤ) * b) = -a * 2 + -b * n by ring, zpow_add]
    push_cast
    rw [mul_comm (n:ℤ) 2]
    ac_rfl
  rw [e, mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 k, mul_comm n k, pow_mul, pow_mul, h1, h2, one_pow, one_pow,
    one_mul]

theorem UpperTheory.V.Ws.Pt.twWts :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (n : ℕ) (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∃ (e : ℤ) (k : ℕ), 0 < k ∧ Even (e + n) ∧ ∀ g ∈ Ine (F := T.L) A, (K.twc n g ^ 2 * cycBar T.L Ω l g ^ (-e)) ^ k = 1 := by
  intro Ω _ _ _ l _ c D T c' h K n A hA
  obtain ⟨a, b, k, hk, hb, hg⟩ := K.cyc A hA
  refine ⟨2 * a + n * b, k, hk, ?_, fun g hgA => ?_⟩
  · obtain ⟨m, rfl⟩ := hb
    exact ⟨a + n * m + n, by ring⟩
  · obtain ⟨h1, h2⟩ := hg g hgA
    have hc : cycBar T.L Ω l g
        = Units.map (algebraMap c'.O (PadicAlgCl l) : c'.O →* PadicAlgCl l) (chiO T.L Ω l c'.O g) := by
      ext
      change algebraMap ℚ_[l] (PadicAlgCl l) (PadicInt.Coe.ringHom ((cycZ T.L Ω l g : ℤ_[l]ˣ) : ℤ_[l]))
        = algebraMap c'.O (PadicAlgCl l) (algebraMap ℤ_[l] c'.O ((cycZ T.L Ω l g : ℤ_[l]ˣ) : ℤ_[l]))
      rw [← IsScalarTower.algebraMap_apply ℤ_[l] c'.O (PadicAlgCl l),
        IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
      rfl
    have ht : K.twc n g
        = Units.map (algebraMap c'.O (PadicAlgCl l) : c'.O →* PadicAlgCl l) (K.κ g * K.β g ^ n) := rfl
    rw [hc, ht, ← map_pow, ← map_zpow, ← map_mul, ← map_pow, aux _ _ _ a b k n h1 h2, map_one]
end
