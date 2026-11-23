module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle001
import Mathlib.Algebra.Module.StablyFree.Basic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.NormMod
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq

@[expose] public section

section

noncomputable section

open IsDedekindDomain NumberField TensorProduct

namespace PI.ProdFormulaE.Tr

theorem trace_one_tmul {R S A : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Free R S]
    [Module.Finite R S] [CommRing A] [Algebra R A] (s : S) :
    Algebra.trace A (A ⊗[R] S) (1 ⊗ₜ s) = algebraMap R A (Algebra.trace R S s) := by
  have h : Algebra.lmul A (A ⊗[R] S) (1 ⊗ₜ s) = (Algebra.lmul R S s).baseChange A := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a t
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [Algebra.trace_apply, h, LinearMap.trace_baseChange, Algebra.trace_apply]

theorem trace_pi {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ι → Type*) [∀ i, CommRing (K i)] [∀ i, Algebra R (K i)] [∀ i, Module.Free R (K i)]
    [∀ i, Module.Finite R (K i)] (z : ∀ i, K i) :
    Algebra.trace R (∀ i, K i) z = ∑ i, Algebra.trace R (K i) (z i) := by
  classical
  let bs := fun i => Module.Free.chooseBasis R (K i)
  rw [Algebra.trace_eq_matrix_trace (Pi.basis bs), Matrix.trace, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.trace_eq_matrix_trace (bs i), Matrix.trace]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Matrix.diag, Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply, Pi.basis_apply, Pi.basis_repr, bs]

theorem trSum_of (hI : TrInj) (hS : TrSurj) : TrSum := by
  classical
  intro F _ _ ℓ _ ι _ D hD y
  let e : ℚ_[ℓ] ⊗[ℚ] F ≃ₐ[ℚ_[ℓ]] (∀ i, D.K i) :=
    AlgEquiv.ofBijective D.Φ ⟨hI F ℓ ι D hD, hS F ℓ ι D hD⟩
  have h1 : e (1 ⊗ₜ y) = fun i => D.ιF i y := by
    funext i
    simp [e, LocFam.Φ, Algebra.TensorProduct.lift_tmul]
  rw [← trace_one_tmul, ← Algebra.trace_eq_of_algEquiv e, h1, trace_pi]

end PI.ProdFormulaE.Tr
end
end

section

noncomputable section

open IsDedekindDomain NumberField TensorProduct ValuativeRel

namespace PI.ProdFormulaE.Tr

variable {F : Type} [Field F] [NumberField F] {ℓ : ℕ} [Fact ℓ.Prime] {ι : Type}

lemma vle_iff' {K : Type*} [Field K] [ValuativeRel K] (x y : K) :
    x ≤ᵥ y ↔ valuation K x ≤ valuation K y := by
  exact (Valuation.Compatible.vle_iff_le (v := valuation K) x y)

lemma valuation_natCast_le_one' {K : Type*} [Field K] [ValuativeRel K] (n : ℕ) :
    valuation K (n : K) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    exact Valuation.map_add_le _ ih (by simp)

private theorem isClosed_setOf_valuation_le_one {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : IsClosed {x : K | valuation K x ≤ 1} := by
  have h := Valuation.isClosed_closedBall (R := K) (v := valuation K) 1
  first
  | (convert h using 3 with x; simp)
  | simpa [Valuation.restrict_le_one_iff] using h
  | simpa using h

lemma LocFam.valuation_algebraMap_le_one (D : LocFam F ℓ ι) (i : ι) (c : ℚ_[ℓ]) (hc : ‖c‖ ≤ 1) :
    valuation (D.K i) (algebraMap ℚ_[ℓ] (D.K i) c) ≤ 1 := by
  let c' : ℤ_[ℓ] := ⟨c, hc⟩
  change valuation (D.K i) (algebraMap ℚ_[ℓ] (D.K i) (c' : ℚ_[ℓ])) ≤ 1
  refine PadicInt.denseRange_natCast.induction_on c'
    (p := fun z : ℤ_[ℓ] => valuation (D.K i) (algebraMap ℚ_[ℓ] (D.K i) (z : ℚ_[ℓ])) ≤ 1) ?_ ?_
  · exact isClosed_setOf_valuation_le_one.preimage ((D.cont i).comp continuous_subtype_val)
  · intro n
    simpa using valuation_natCast_le_one' (K := D.K i) n

lemma LocFam.valuation_ιF_le_one (D : LocFam F ℓ ι) (i : ι) (x : 𝓞 F) :
    valuation (D.K i) (D.ιF i (x : F)) ≤ 1 := by
  have h := (D.val i (x : F) 1).2 (by simpa using (D.P i).valuation_le_one x)
  simpa [vle_iff'] using h

theorem LocFam.linearIndependent [Fintype ι] (D : LocFam F ℓ ι) (hD : D.Over)
    (hA : ∀ X : 𝓞 F, (∀ v : HeightOneSpectrum (𝓞 F), (ℓ : 𝓞 F) ∈ v.asIdeal →
      v.valuation F (X : F) ≤ v.valuation F (ℓ : F)) → ∃ Z : 𝓞 F, X = ℓ * Z)
    (hB : ∀ c : ℚ_[ℓ], ‖c‖ ≤ 1 → ∃ m : ℤ, ‖(c - m) / ℓ‖ ≤ 1) :
    LinearIndependent ℚ_[ℓ] (fun k => D.Φ (1 ⊗ₜ integralBasis F k)) := by
  classical
  set b := integralBasis F with hb_def
  set bZ := RingOfIntegers.basis F with hbZ
  have hbb : ∀ k, b k = algebraMap (𝓞 F) F (bZ k) := fun k => by
    rw [hb_def, hbZ, integralBasis_apply]
  have hw : ∀ k i, D.Φ (1 ⊗ₜ b k) i = D.ιF i (b k) := fun k i => by
    rw [LocFam.Φ_tmul, map_one, one_mul]
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hne
  push_neg at hne
  obtain ⟨k1, hk1⟩ := hne
  obtain ⟨k0, -, hk0⟩ := Finset.exists_max_image Finset.univ (fun k => ‖g k‖) ⟨k1, Finset.mem_univ _⟩
  have hg0 : g k0 ≠ 0 := by
    intro h
    have h' := hk0 k1 (Finset.mem_univ _)
    rw [h, norm_zero] at h'
    exact hk1 (norm_le_zero_iff.1 h')
  set c : _ → ℚ_[ℓ] := fun k => g k / g k0 with hc_def
  have hc1 : ∀ k, ‖c k‖ ≤ 1 := fun k => by
    simp only [hc_def, norm_div]
    exact div_le_one_of_le₀ (hk0 k (Finset.mem_univ _)) (norm_nonneg _)
  have hck0 : c k0 = 1 := div_self hg0
  have hrel : ∀ i, ∑ k, algebraMap ℚ_[ℓ] (D.K i) (c k) * D.ιF i (b k) = 0 := by
    intro i
    have h := congrFun hg i
    simp only [Finset.sum_apply, Pi.smul_apply, hw, Pi.zero_apply] at h
    have h2 := congrArg (fun y => algebraMap ℚ_[ℓ] (D.K i) (g k0)⁻¹ * y) h
    simp only [mul_zero, Finset.mul_sum, Algebra.smul_def] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hc_def, div_eq_inv_mul, map_mul, mul_assoc]
  choose m hm using fun k => hB (c k) (hc1 k)
  set d : _ → ℚ_[ℓ] := fun k => (c k - m k) / ℓ with hd_def
  have hd1 : ∀ k, ‖d k‖ ≤ 1 := hm
  have hℓ0 : (ℓ : ℚ_[ℓ]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero
  have hcd : ∀ k, c k - m k = ℓ * d k := fun k => by
    simp only [hd_def]
    field_simp
  set X : 𝓞 F := ∑ k, m k • bZ k with hX_def
  have hXF : ((X : 𝓞 F) : F) = ∑ k, (m k : F) * b k := by
    first
    | (rw [hX_def]; simp [hbb, zsmul_eq_mul])
    | (push_cast [hX_def, hbb, zsmul_eq_mul]; rfl)
  have hval : ∀ v : HeightOneSpectrum (𝓞 F), (ℓ : 𝓞 F) ∈ v.asIdeal →
      v.valuation F (X : F) ≤ v.valuation F (ℓ : F) := by
    intro v hv
    obtain ⟨i, rfl⟩ := (hD.2 v).2 hv
    rw [← D.val i, vle_iff']
    have hterm : ∀ k, D.ιF i ((m k : F) * b k) = algebraMap ℚ_[ℓ] (D.K i) (c k) * D.ιF i (b k)
        - (ℓ : D.K i) * (algebraMap ℚ_[ℓ] (D.K i) (d k) * D.ιF i (b k)) := by
      intro k
      have e : (m k : ℚ_[ℓ]) = c k - ℓ * d k := by rw [← hcd]; ring
      have e' : ((m k : ℤ) : D.K i) = algebraMap ℚ_[ℓ] (D.K i) (c k)
          - (ℓ : D.K i) * algebraMap ℚ_[ℓ] (D.K i) (d k) := by
        rw [← map_intCast (algebraMap ℚ_[ℓ] (D.K i)), e, map_sub, map_mul, map_natCast]
      rw [map_mul, map_intCast, e']
      ring
    have hιX : D.ιF i (X : F) =
        -((ℓ : D.K i) * ∑ k, algebraMap ℚ_[ℓ] (D.K i) (d k) * D.ιF i (b k)) := by

      rw [hXF, map_sum, Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_sub_distrib, hrel i,
      Finset.mul_sum]
      ring
    have hsum : valuation (D.K i) (∑ k, algebraMap ℚ_[ℓ] (D.K i) (d k) * D.ιF i (b k)) ≤ 1 := by
      refine Valuation.map_sum_le _ fun k _ => ?_
      rw [map_mul, hbb]
      exact mul_le_one' (LocFam.valuation_algebraMap_le_one D i _ (hd1 k))
        (LocFam.valuation_ιF_le_one D i (bZ k))
    rw [hιX, Valuation.map_neg, map_mul, map_natCast (D.ιF i) ℓ]
    first
    | exact mul_le_of_le_one_right' hsum
    | exact mul_le_of_le_one_right₀ hsum
    | (calc _ ≤ valuation (D.K i) (ℓ : D.K i) * 1 := by gcongr
        _ = _ := mul_one _)
  obtain ⟨Z, hZ⟩ := hA X hval
  have hrepr : ∀ k, bZ.repr X k = m k := fun k => by
    rw [hX_def, bZ.repr_sum_self]
  have hmk : m k0 = ℓ * bZ.repr Z k0 := by
    have h := congrArg (fun y => bZ.repr y k0) hZ
    simp only [hrepr] at h
    rw [h]
    have e : ((ℓ : 𝓞 F) * Z) = (ℓ : ℤ) • Z := by rw [zsmul_eq_mul]; push_cast; rfl
    rw [e, LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul]
  have e := hcd k0
  rw [hck0, hmk] at e
  push_cast at e
  have h1 : (1 : ℚ_[ℓ]) = ℓ * (((bZ.repr Z k0 : ℤ) : ℚ_[ℓ]) + d k0) := by linear_combination e
  have hn := congrArg norm h1
  rw [norm_one, norm_mul] at hn
  have hlt : ‖(ℓ : ℚ_[ℓ])‖ < 1 := Padic.norm_p_lt_one
  have hle : ‖((bZ.repr Z k0 : ℤ) : ℚ_[ℓ]) + d k0‖ ≤ 1 :=
    (Padic.nonarchimedean _ _).trans (max_le (Padic.norm_int_le_one _) (hd1 k0))
  nlinarith [norm_nonneg (ℓ : ℚ_[ℓ]), norm_nonneg (((bZ.repr Z k0 : ℤ) : ℚ_[ℓ]) + d k0)]

theorem LocFam.injective_of_linearIndependent [Fintype ι] (D : LocFam F ℓ ι)
    (hl : LinearIndependent ℚ_[ℓ] (fun k => D.Φ (1 ⊗ₜ integralBasis F k))) :
    Function.Injective D.Φ := by
  classical
  set bb := Algebra.TensorProduct.basis ℚ_[ℓ] (integralBasis F) with hbb
  have hb : ∀ k, bb k = 1 ⊗ₜ integralBasis F k := fun k => Algebra.TensorProduct.basis_apply _ _
  refine (injective_iff_map_eq_zero D.Φ).2 fun x hx => ?_
  rw [← bb.sum_repr x] at hx ⊢

  simp only [map_sum, map_smul, hb] at hx
  have h0 := (Fintype.linearIndependent_iff.1 hl) (fun k => bb.repr x k) hx
  simp [h0]

theorem toPi_injective : TrInj := by
  intro F _ _ ℓ _ ι _ D hD
  exact LocFam.injective_of_linearIndependent D
    (LocFam.linearIndependent D hD (exists_eq_ell_mul ℓ) (exists_int_approx ℓ))

end PI.ProdFormulaE.Tr
end
end

section

noncomputable section

open IsDedekindDomain NumberField TensorProduct ValuativeRel Filter Topology

namespace PI.ProdFormulaE.Tr

variable {F : Type} [Field F] [NumberField F]

theorem exists_approx {ι : Type} [Finite ι] (P : ι → HeightOneSpectrum (𝓞 F))
    (hP : Function.Injective P) (b : ι → F) (c : F) (hc : c ≠ 0) :
    ∃ x : F, ∀ i, (P i).valuation F (x - b i) ≤ (P i).valuation F c := by
  classical
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 F)) b
  have hd' : ∀ i, ∃ a : 𝓞 F, algebraMap (𝓞 F) F a = (d : 𝓞 F) • b i :=
    fun i => RingHom.mem_rangeS.1 (hd i)
  choose a ha using hd'
  have hd0 : algebraMap (𝓞 F) F (d : 𝓞 F) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 (nonZeroDivisors.coe_ne_zero d)
  have hw : ∀ i, (P i).valuation F (algebraMap (𝓞 F) F (d : 𝓞 F) * c) ≠ 0 := fun i =>
    (Valuation.ne_zero_iff _).2 (mul_ne_zero hd0 hc)
  have hn : ∀ i, WithZero.exp (-((WithZero.log ((P i).valuation F (algebraMap (𝓞 F) F (d : 𝓞 F) * c))).natAbs : ℤ))
      ≤ (P i).valuation F (algebraMap (𝓞 F) F (d : 𝓞 F) * c) := by
    intro i
    conv_rhs => rw [← WithZero.exp_log (hw i)]
    rw [WithZero.exp_le_exp, Int.natCast_natAbs]
    exact neg_abs_le _
  cases nonempty_fintype ι
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := Finset.univ)
    (fun i => (P i).asIdeal)
    (fun i => (WithZero.log ((P i).valuation F (algebraMap (𝓞 F) F (d : 𝓞 F) * c))).natAbs)
    (fun i _ => (P i).prime) (fun i _ j _ hij h => hij (hP (HeightOneSpectrum.ext h)))
    (fun i => a i.1)
  refine ⟨algebraMap (𝓞 F) F y / algebraMap (𝓞 F) F (d : 𝓞 F), fun i => ?_⟩
  have h1 := ((P i).intValuation_le_pow_iff_mem _ _).2 (hy i (Finset.mem_univ _))
  have h2 : (P i).valuation F (algebraMap (𝓞 F) F (y - a i)) ≤
      (P i).valuation F (algebraMap (𝓞 F) F (d : 𝓞 F) * c) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact h1.trans (hn i)
  have h3 : algebraMap (𝓞 F) F (d : 𝓞 F) *
      (algebraMap (𝓞 F) F y / algebraMap (𝓞 F) F (d : 𝓞 F) - b i) = algebraMap (𝓞 F) F (y - a i) := by
    rw [map_sub, ha i, Algebra.smul_def]
    field_simp
  have key : (P i).valuation F (algebraMap (𝓞 F) F (d : 𝓞 F)) *
      (P i).valuation F (algebraMap (𝓞 F) F y / algebraMap (𝓞 F) F (d : 𝓞 F) - b i) ≤
      (P i).valuation F (algebraMap (𝓞 F) F (d : 𝓞 F)) * (P i).valuation F c := by
    rw [← map_mul, ← map_mul, h3]
    exact h2
  exact (mul_le_mul_iff_right₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hd0))).1 key

theorem t2Space_of_isValuativeTopology_alt (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsValuativeTopology K] : T2Space K := by
  apply IsTopologicalAddGroup.t2Space_of_zero_sep
  intro x hx
  refine ⟨{z | valuation K z < valuation K x}, ?_, fun h => lt_irrefl (valuation K x) h⟩
  rw [IsValuativeTopology.mem_nhds_zero_iff]
  exact ⟨Units.mk0 _ ((Valuation.ne_zero_iff _).2 hx), fun z hz => by simpa using hz⟩

variable {ℓ : ℕ} [Fact ℓ.Prime] {ι : Type}

private theorem exists_valuation_sub_lt_of_injective [Finite ι] (D : LocFam F ℓ ι) (hP : Function.Injective D.P)
    (k : ∀ i, D.K i) (γ : ∀ i, (ValueGroupWithZero (D.K i))ˣ) :
    ∃ x : F, ∀ i, valuation (D.K i) (D.ιF i x - k i) < γ i := by
  have hl : ∀ i, Tendsto (fun N : ℕ => D.ιF i ((ℓ : F) ^ N)) atTop (𝓝 0) := by
    intro i
    have h0 : Tendsto (fun N : ℕ => (ℓ : ℚ_[ℓ]) ^ N) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one
    have h1 := ((D.cont i).tendsto 0).comp h0
    rw [map_zero] at h1
    convert h1 using 1
    funext N
    simp
  have hev : ∀ᶠ N in atTop, ∀ i, valuation (D.K i) (D.ιF i ((ℓ : F) ^ N)) < γ i := by
    rw [Filter.eventually_all]
    intro i
    exact hl i ((IsValuativeTopology.hasBasis_nhds_zero (D.K i)).mem_of_mem (i := γ i) trivial)
  obtain ⟨N, hN⟩ := hev.exists
  have hb : ∀ i, ∃ b : F, valuation (D.K i) (D.ιF i b - k i) < γ i := by
    intro i
    obtain ⟨_, hz, b, rfl⟩ := mem_closure_iff_nhds.1 (D.dense i (k i)) _
      ((IsValuativeTopology.hasBasis_nhds (k i)).mem_of_mem (i := γ i) trivial)
    exact ⟨b, hz⟩
  choose b hb using hb
  have hc : ((ℓ : F) ^ N) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero)
  obtain ⟨x, hx⟩ := exists_approx D.P hP b _ hc
  refine ⟨x, fun i => ?_⟩
  have h1 : valuation (D.K i) (D.ιF i (x - b i)) ≤ valuation (D.K i) (D.ιF i ((ℓ : F) ^ N)) :=
    (Valuation.vle_iff_le (valuation (D.K i))).1 ((D.val i _ _).2 (hx i))
  have h2 : D.ιF i x - k i = D.ιF i (x - b i) + (D.ιF i (b i) - k i) := by
    rw [map_sub]
    ring
  rw [h2]
  exact Valuation.map_add_lt _ (lt_of_le_of_lt h1 (hN i)) (hb i)

theorem LocFam.denseDiag [Finite ι] (D : LocFam F ℓ ι) (hP : Function.Injective D.P) :
    DenseRange (fun x : F => fun i => D.ιF i x) := by
  rw [DenseRange, dense_iff_inter_open]
  rintro U hU ⟨k, hk⟩
  obtain ⟨I, u, hu, hIU⟩ := isOpen_pi_iff.1 hU k hk
  have hγ : ∀ i, ∃ γ : (ValueGroupWithZero (D.K i))ˣ,
      i ∈ I → {z | valuation (D.K i) (z - k i) < γ} ⊆ u i := by
    intro i
    by_cases hi : i ∈ I
    · obtain ⟨γ, -, hγ⟩ :=
        (IsValuativeTopology.hasBasis_nhds (k i)).mem_iff.1 ((hu i hi).1.mem_nhds (hu i hi).2)
      exact ⟨γ, fun _ => hγ⟩
    · exact ⟨1, fun h => absurd h hi⟩
  choose γ hγ using hγ
  obtain ⟨x, hx⟩ := exists_valuation_sub_lt_of_injective D hP k γ
  exact ⟨_, hIU (fun i hi => hγ i hi (hx i)), x, rfl⟩

theorem toPi_surjective : TrSurj := by
  intro F _ _ ℓ _ ι _ D hD
  have : ∀ i, T2Space (D.K i) := fun i => t2Space_of_isValuativeTopology_alt (D.K i)
  have : ∀ i, ContinuousSMul ℚ_[ℓ] (D.K i) := fun i => ⟨by
    simp_rw [Algebra.smul_def]
    exact ((D.cont i).comp continuous_fst).mul continuous_snd⟩
  have hcl : IsClosed (LinearMap.range D.Φ.toLinearMap : Set (∀ i, D.K i)) :=
    Submodule.closed_of_finiteDimensional _
  have hdense : Dense (LinearMap.range D.Φ.toLinearMap : Set (∀ i, D.K i)) := by
    refine Dense.mono ?_ (LocFam.denseDiag D hD.1)
    rintro _ ⟨x, rfl⟩
    refine ⟨1 ⊗ₜ x, ?_⟩
    funext i
    simp [LocFam.Φ_tmul]
  intro y
  have hy : y ∈ closure (LinearMap.range D.Φ.toLinearMap : Set (∀ i, D.K i)) := by
    rw [hdense.closure_eq]
    trivial
  rw [hcl.closure_eq] at hy
  obtain ⟨z, hz⟩ := LinearMap.mem_range.1 hy
  exact ⟨z, by simpa using hz⟩

end PI.ProdFormulaE.Tr
end
end

section

noncomputable section

open IsDedekindDomain NumberField MeasureTheory ValuativeRel Formalism.MainNotions.S.Loc

namespace PI.ProdFormulaE.St

def HaarAlg : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    [Module.Free K A] [Module.Finite K A] [IsModuleTopology K A]
    (μ : Measure A) [μ.IsAddHaarMeasure] (y : A), IsUnit y → ∀ S : Set A,
      μ ((fun z => y * z) '' S) = ENNReal.ofReal (modF K (Algebra.norm K y)) * μ S

def NormLoc : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ι : F →+* K), DenseRange ι →
    (∀ x y : F, (ι x ≤ᵥ ι y) ↔ p.valuation F x ≤ p.valuation F y) →
    ∀ z : F, modF K (ι z) = FinitePlace.mk p z

def TrInt : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (K : Type) [Field K] [Algebra ℚ_[ℓ] K] [FiniteDimensional ℚ_[ℓ] K]
    (w : K), IsIntegral ℤ w → ‖Algebra.trace ℚ_[ℓ] K w‖ ≤ 1

def ResCharIff : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F)) (ℓ : ℕ), ℓ.Prime →
    (resChar p = ℓ ↔ ((ℓ : 𝓞 F) ∈ p.asIdeal))

end PI.ProdFormulaE.St

end
end
