module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.ClassSame
public import Mathlib.Order.CompletePartialOrder
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host

namespace PI.AlgValsFin.W

variable {L : Type} [Field L] [NumberField L]

theorem valuation_eq_exp (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ) :
    v.valuation L (k : L) = WithZero.exp (-ordF v k) := by
  rw [ordF, neg_neg, WithZero.exp_log]
  exact (Valuation.ne_zero_iff _).mpr k.ne_zero

theorem toNNReal_exp {e : NNReal} (he : e ≠ 0) (n : ℤ) :
    WithZeroMulInt.toNNReal he (WithZero.exp n) = e ^ n := by
  first
    | (simp [WithZero.exp, WithZeroMulInt.toNNReal_pos_apply he]; done)
    | (rw [WithZeroMulInt.toNNReal_pos_apply he WithZero.exp_ne_zero]; simp [WithZero.exp]; done)
    | rfl

theorem prod_norm_emb (x : L) : ∏ φ : L →+* ℂ, ‖φ x‖ = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  calc ∏ φ : L →+* ℂ, ‖φ x‖ = ∏ σ : L →ₐ[ℚ] ℂ, ‖σ x‖ :=
        Fintype.prod_equiv (RingHom.equivRatAlgHom L ℂ) _ _ fun _ => rfl
    _ = ‖∏ σ : L →ₐ[ℚ] ℂ, σ x‖ := (norm_prod _ _).symm
    _ = ‖algebraMap ℚ ℂ (Algebra.norm ℚ x)‖ := by rw [Algebra.norm_eq_prod_embeddings ℚ ℂ x]
    _ = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
      rw [eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]

theorem finprod_norm_embedding (k : Lˣ) (T : Finset (HeightOneSpectrum (𝓞 L)))
    (hT : ∀ v, v ∉ T → ordF v k = 0) :
    ∏ᶠ w : FinitePlace L, w (k : L) =
      ∏ v ∈ T, (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ ordF v k)⁻¹ := by
  rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
  have hval : ∀ v : HeightOneSpectrum (𝓞 L),
      (FinitePlace.equivHeightOneSpectrum.symm v) (k : L) = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ ordF v k)⁻¹ := by
    intro v
    have e1 : (FinitePlace.equivHeightOneSpectrum.symm v) (k : L) =
        NumberField.HeightOneSpectrum.adicAbv L v (k : L) := by
      first
        | (show (FinitePlace.mk v) (k : L) = _
           rw [FinitePlace.mk_apply, FinitePlace.norm_embedding])
        | (rw [FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.mk_apply, FinitePlace.norm_embedding])
        | (simp only [FinitePlace.equivHeightOneSpectrum, Equiv.coe_fn_symm_mk]
           rw [← FinitePlace.mk_apply, FinitePlace.norm_embedding])
    rw [e1, NumberField.HeightOneSpectrum.adicAbv_def, valuation_eq_exp, toNNReal_exp]
    push_cast
    rw [zpow_neg]
  rw [finprod_congr hval]
  apply finprod_eq_prod_of_mulSupport_subset
  intro v hv
  by_contra hT'
  exact hv (by simp [hT v hT'])

theorem prodNorm : ProdNorm L := by
  intro k T hT
  have h3 := FinitePlace.prod_eq_inv_abs_norm (K := L) k.ne_zero
  rw [finprod_norm_embedding k T hT, Finset.prod_inv_distrib, Rat.cast_inv, Rat.cast_abs, inv_inj] at h3
  rw [prod_norm_emb, h3]

end PI.AlgValsFin.W
end
end

section

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Neutral.B1 Topology

namespace PI.AlgValsFin.W

variable {L : Type} [Field L] [NumberField L]

theorem locNb (v : HeightOneSpectrum (𝓞 L))
    (s : Set ((v.adicCompletionIntegers L : Set (v.adicCompletion L))))
    (hs : s ∈ 𝓝 (⟨1, (v.adicCompletionIntegers L).one_mem⟩ : (v.adicCompletionIntegers L : Set (v.adicCompletion L)))) :
    ∃ n : ℕ, ∀ y : (v.adicCompletionIntegers L : Set (v.adicCompletion L)),
      Valued.v ((y : v.adicCompletion L) - 1) ≤ exp (-(n : ℤ)) → y ∈ s := by
  rw [mem_nhds_subtype] at hs
  obtain ⟨u, hu, hsub⟩ := hs
  rw [Valued.mem_nhds] at hu
  obtain ⟨γ, hγ⟩ := hu
  obtain ⟨n, hn⟩ := exists_exp_neg_natCast_lt (MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ)
  refine ⟨n, fun y hy => hsub (hγ ?_)⟩
  show Valued.v.restrict ((y : v.adicCompletion L) - 1) < γ.1
  rw [← MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.lt_iff_lt, Valuation.embedding_restrict]
  exact lt_of_le_of_lt hy hn

def toInt (x : Ideles L) (hx : x ∈ UFin L) (v : HeightOneSpectrum (𝓞 L)) :
    (v.adicCompletionIntegers L : Set (v.adicCompletion L)) :=
  ⟨(x : AdeleRing (𝓞 L) L).2 v, (mem_adicCompletionIntegers _ _ _).2 (hx.2 v).le⟩

theorem inv_mem_UFin {x : Ideles L} (hx : x ∈ UFin L) : x⁻¹ ∈ UFin L := by
  have hmul : (x : AdeleRing (𝓞 L) L) * ((x⁻¹ : Ideles L) : AdeleRing (𝓞 L) L) = 1 := x.mul_inv
  refine ⟨?_, fun v => ?_⟩
  · have h2 : (x : AdeleRing (𝓞 L) L).1 * ((x⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).1 = 1 :=
      congrArg (fun y : AdeleRing (𝓞 L) L => y.1) hmul
    rw [hx.1, one_mul] at h2
    exact h2
  · have h2 : (x : AdeleRing (𝓞 L) L).2 v * ((x⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v = 1 :=
      congrArg (fun y : AdeleRing (𝓞 L) L => y.2 v) hmul
    have h3 := congrArg Valued.v h2
    rw [map_mul, hx.2 v, one_mul, map_one] at h3
    exact h3

theorem val_inv_sub {x : Ideles L} (hx : x ∈ UFin L) (v : HeightOneSpectrum (𝓞 L)) :
    Valued.v ((x⁻¹ : Ideles L).val.2 v - 1) = Valued.v ((x : AdeleRing (𝓞 L) L).2 v - 1) := by
  have hmul : (x : AdeleRing (𝓞 L) L) * ((x⁻¹ : Ideles L) : AdeleRing (𝓞 L) L) = 1 := x.mul_inv
  have h2 : (x : AdeleRing (𝓞 L) L).2 v * ((x⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v = 1 :=
    congrArg (fun y : AdeleRing (𝓞 L) L => y.2 v) hmul
  have hz : Valued.v (((x⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v) = 1 := (inv_mem_UFin hx).2 v
  have heq : (x⁻¹ : Ideles L).val.2 v - 1 =
      ((x⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v * (1 - (x : AdeleRing (𝓞 L) L).2 v) := by
    rw [mul_sub, mul_one, mul_comm (((x⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v), h2]
  rw [heq, map_mul, hz, one_mul, Valuation.map_sub_swap]

theorem exists_nbhd (W : Set (Ideles L)) (hW : IsOpen W) (h1 : (1 : Ideles L) ∈ W) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 L))) (n : ℕ), ∀ x ∈ UFin L,
      (∀ v ∈ S, Valued.v ((x : AdeleRing (𝓞 L) L).2 v - 1) ≤ exp (-(n : ℤ))) → x ∈ W := by
  classical
  obtain ⟨t, ht, rfl⟩ := (Units.isInducing_embedProduct).isOpen_iff.1 hW
  let one' : Π v : HeightOneSpectrum (𝓞 L), (v.adicCompletionIntegers L : Set (v.adicCompletion L)) :=
    fun v => ⟨1, (v.adicCompletionIntegers L).one_mem⟩
  let sm : (Π v : HeightOneSpectrum (𝓞 L), (v.adicCompletionIntegers L : Set (v.adicCompletion L))) →
      FiniteAdeleRing (𝓞 L) L :=
    RestrictedProduct.structureMap _ _ Filter.cofinite
  have hsm : Continuous sm := RestrictedProduct.isEmbedding_structureMap.continuous
  let g : (Π v : HeightOneSpectrum (𝓞 L), (v.adicCompletionIntegers L : Set (v.adicCompletion L))) ×
      (Π v : HeightOneSpectrum (𝓞 L), (v.adicCompletionIntegers L : Set (v.adicCompletion L))) →
      AdeleRing (𝓞 L) L × (AdeleRing (𝓞 L) L)ᵐᵒᵖ :=
    fun p => (((1 : InfiniteAdeleRing L), sm p.1), MulOpposite.op ((1 : InfiniteAdeleRing L), sm p.2))
  have hg : Continuous g :=
    Continuous.prodMk (Continuous.prodMk continuous_const (hsm.comp continuous_fst))
      (MulOpposite.continuous_op.comp (Continuous.prodMk continuous_const (hsm.comp continuous_snd)))
  have hsm1 : sm one' = 1 := FiniteAdeleRing.ext _ fun v => rfl
  have hg1 : g (one', one') = Units.embedProduct _ (1 : Ideles L) := by
    simp only [g, hsm1]
    rfl
  have hmem : g ⁻¹' t ∈ 𝓝 (one', one') :=
    hg.continuousAt.preimage_mem_nhds (ht.mem_nhds (by rw [hg1]; exact h1))
  rw [nhds_prod_eq] at hmem
  obtain ⟨t1, ht1, t2, ht2, hsub⟩ := Filter.mem_prod_iff.1 hmem
  rw [nhds_pi, Filter.mem_pi] at ht1 ht2
  obtain ⟨I1, hI1, s1, hs1, hsub1⟩ := ht1
  obtain ⟨I2, hI2, s2, hs2, hsub2⟩ := ht2
  choose n1 hn1 using fun v => locNb v (s1 v) (hs1 v)
  choose n2 hn2 using fun v => locNb v (s2 v) (hs2 v)
  let S : Finset (HeightOneSpectrum (𝓞 L)) := hI1.toFinset ∪ hI2.toFinset
  refine ⟨S, ∑ v ∈ S, (n1 v + n2 v), fun x hx hS => ?_⟩
  have hle : ∀ v ∈ S, ∀ k : ℕ, k ≤ n1 v + n2 v →
      exp (-((∑ v ∈ S, (n1 v + n2 v) : ℕ) : ℤ)) ≤ exp (-(k : ℤ)) := by
    intro v hv k hk
    apply exp_le_exp.2
    have := Finset.single_le_sum (f := fun v => n1 v + n2 v) (fun _ _ => Nat.zero_le _) hv
    omega
  have hy : (fun v => toInt x hx v, fun v => toInt x⁻¹ (inv_mem_UFin hx) v) ∈ t1 ×ˢ t2 := by
    refine ⟨hsub1 fun v hv => hn1 v _ ?_, hsub2 fun v hv => hn2 v _ ?_⟩
    · have hvS : v ∈ S := Finset.mem_union_left _ (hI1.mem_toFinset.2 hv)
      exact (hS v hvS).trans (hle v hvS _ (Nat.le_add_right _ _))
    · have hvS : v ∈ S := Finset.mem_union_right _ (hI2.mem_toFinset.2 hv)
      show Valued.v ((x⁻¹ : Ideles L).val.2 v - 1) ≤ _
      rw [val_inv_sub hx v]
      exact (hS v hvS).trans (hle v hvS _ (Nat.le_add_left _ _))
  have hgx : g (fun v => toInt x hx v, fun v => toInt x⁻¹ (inv_mem_UFin hx) v) = Units.embedProduct _ x := by
    have e1 : (((1 : InfiniteAdeleRing L), sm fun v => toInt x hx v) : AdeleRing (𝓞 L) L) = (x : AdeleRing (𝓞 L) L) :=
      Prod.ext hx.1.symm (FiniteAdeleRing.ext _ fun v => rfl)
    have e2 : (((1 : InfiniteAdeleRing L), sm fun v => toInt x⁻¹ (inv_mem_UFin hx) v) : AdeleRing (𝓞 L) L) =
        ((x⁻¹ : Ideles L) : AdeleRing (𝓞 L) L) :=
      Prod.ext (inv_mem_UFin hx).1.symm (FiniteAdeleRing.ext _ fun v => rfl)
    simp only [g]
    rw [e1, e2]
    rfl
  have := hsub hy
  rw [Set.mem_preimage, hgx] at this
  exact this

end PI.AlgValsFin.W
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Neutral.B1

namespace PI.AlgValsFin.W

variable {L : Type} [Field L] [NumberField L]

theorem absNorm_pos (v : HeightOneSpectrum (𝓞 L)) : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  have h : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  exact_mod_cast Nat.pos_of_ne_zero h

theorem factor_one (N : ℝ) (hN : 0 < N) (o : ℤ) (s : ℝ) : (N ^ o) ^ s * (N ^ (-s)) ^ o = 1 := by
  have h1 : (N ^ o) ^ s = N ^ ((o : ℝ) * s) := by
    rw [← Real.rpow_intCast, ← Real.rpow_mul hN.le]
  have h2 : (N ^ (-s)) ^ o = N ^ (-s * (o : ℝ)) := by
    rw [← Real.rpow_intCast, ← Real.rpow_mul hN.le]
  have h3 : (o : ℝ) * s + -s * (o : ℝ) = 0 := by ring
  rw [h1, h2, ← Real.rpow_add hN, h3, Real.rpow_zero]

theorem keyIdOf : KeyIdOf L := by
  intro hD hL hP χ s m hχ k T hT hU
  obtain ⟨r, hr, hk⟩ := hD k T hT
  refine ⟨r, hr, ?_⟩

  have e : χ.1 (diagUnits L k) = 1 := χ.2.2 k
  rw [hk, map_mul, map_mul, map_prod] at e
  have eloc : ∀ v ∈ T, χ.1 (localIdele L v (atFin v k)) = χ.val v ^ ordF v k := by
    intro v hv
    exact hL χ v k (hU v hv)
  rw [Finset.prod_congr rfl eloc] at e
  have einf : χ.1 (infDiag k) = χ.inf k := rfl
  rw [einf] at e
  have e' := congrArg (fun u : ℂˣ => (u : ℂ)) e
  simp only [Units.val_mul, Units.coe_prod, Units.val_zpow_eq_zpow_val, Units.val_one] at e'

  have hreal : (∏ φ : L →+* ℂ, ‖φ (k : L)‖ ^ s) *
      ∏ v ∈ T, (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s)) ^ ordF v k = 1 := by
    rw [Real.finsetProd_rpow Finset.univ (fun φ : L →+* ℂ => ‖φ (k : L)‖) (fun φ _ => norm_nonneg _) s,
      hP k T hT,
      ← Real.finsetProd_rpow T _ (fun v _ => zpow_nonneg (absNorm_pos v).le _) s,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one (fun v _ => factor_one _ (absNorm_pos v) _ s)
  have hc1 : ∏ φ : L →+* ℂ, ((‖φ (k : L)‖ : ℝ) : ℂ) ^ (s : ℂ)
      = ((∏ φ : L →+* ℂ, ‖φ (k : L)‖ ^ s : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl (fun φ _ => ?_)
    rw [Complex.ofReal_cpow (norm_nonneg _)]
  have hc2 : ∏ v ∈ T, (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(s : ℂ))) ^ ordF v k
      = ((∏ v ∈ T, (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s)) ^ ordF v k : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    rw [Complex.ofReal_zpow, Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_neg,
      Complex.ofReal_natCast]
  rw [← hχ k]
  simp only [Formalism.L2.Host.HChar.valTw, mul_zpow, Finset.prod_mul_distrib]
  rw [hc1, hc2]
  set A : ℝ := ∏ φ : L →+* ℂ, ‖φ (k : L)‖ ^ s with hA
  set B : ℝ := ∏ v ∈ T, (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s)) ^ ordF v k with hB
  have hAB : (A : ℂ) * (B : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, hreal, Complex.ofReal_one]
  linear_combination ((A : ℂ) * (B : ℂ)) * e' + hAB

end PI.AlgValsFin.W
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host

namespace PI.AlgValsFin.W

variable {L : Type} [Field L] [NumberField L]

def compo (L : Type) [Field L] [NumberField L] : IntermediateField ℚ ℂ :=
  ⨆ φ : L →+* ℂ, φ.toRatAlgHom.fieldRange

instance (φ : L →+* ℂ) : FiniteDimensional ℚ φ.toRatAlgHom.fieldRange :=
  LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField φ.toRatAlgHom).toLinearEquiv

instance : FiniteDimensional ℚ (compo L) := by
  unfold compo; infer_instance

theorem mem_compo (φ : L →+* ℂ) (x : L) : φ x ∈ compo L :=
  (le_iSup (fun ψ : L →+* ℂ => ψ.toRatAlgHom.fieldRange) φ) (AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩)

theorem prod_mem_compo (m : (L →+* ℂ) → ℤ) (k : L) : ∏ φ : L →+* ℂ, φ k ^ m φ ∈ compo L :=
  prod_mem fun φ _ => zpow_mem (mem_compo φ k) _

theorem isIntegral_of_mem_compo {y : ℂ} (hy : y ∈ compo L) : IsIntegral ℚ y := by
  have h := (IsIntegral.of_finite ℚ (⟨y, hy⟩ : compo L)).map (compo L).val
  exact h

theorem eq_of_key {a b P z : ℂ} (e : a * b⁻¹ * P * z = 1) : a = b * (P * z)⁻¹ := by
  have hb : b ≠ 0 := by rintro rfl; simp at e
  have hP : P ≠ 0 := by rintro rfl; simp at e
  have hz : z ≠ 0 := by rintro rfl; simp at e
  field_simp
  field_simp at e
  linear_combination e

theorem assemble : Assemble L := by
  classical
  intro hTors hKey hPow hSame χ s m hm
  obtain ⟨N, hN0, hN⟩ := hTors χ
  obtain ⟨h, hh0, hk⟩ := hPow
  obtain ⟨ι, hι, c, hc⟩ := hSame
  haveI := hι
  have hz : ∀ r ∈ UFin L, ((χ.1 r : ℂˣ) : ℂ) ^ N = 1 := by
    intro r hr
    rw [← Units.val_pow_eq_pow_val, hN r hr, Units.val_one]
  let U := {i : ι // ∃ v, c v = i ∧ χ.UnrAt v}
  let f : U → ℂ := fun i => χ.valTw s i.2.choose
  let S : Set ℂ := ((Polynomial.nthRoots N (1 : ℂ)).toFinset : Set ℂ) ∪ Set.range f
  haveI : Finite S := ((Set.toFinite _).union (Set.finite_range f)).to_subtype
  have hA : ∀ v, χ.UnrAt v → ∃ P ∈ compo L, ∃ z : ℂ, z ^ N = 1 ∧ χ.valTw s v ^ h * (P * z) = 1 := by
    intro v hv
    obtain ⟨kv, hkv⟩ := hk v
    have h1 : ∀ u, u ∉ ({v} : Finset (HeightOneSpectrum (𝓞 L))) → ordF u kv = 0 := by
      intro u hu
      rw [hkv u, if_neg (fun h' => hu (Finset.mem_singleton.mpr h'))]
    have h2 : ∀ u ∈ ({v} : Finset (HeightOneSpectrum (𝓞 L))), χ.UnrAt u := by
      intro u hu
      rw [Finset.mem_singleton.mp hu]
      exact hv
    obtain ⟨r, hr, e⟩ := hKey χ s m hm kv {v} h1 h2
    refine ⟨_, prod_mem_compo m (kv : L), _, hz r hr, ?_⟩
    rw [Finset.prod_singleton, hkv v, if_pos rfl, zpow_natCast] at e
    rw [← mul_assoc]
    exact e
  let C : IntermediateField ℚ ℂ := compo L ⊔ IntermediateField.adjoin ℚ S
  have hCcompo : compo L ≤ C := le_sup_left
  have hSsub : ∀ x ∈ S, x ∈ C := fun x hx => (le_sup_right : IntermediateField.adjoin ℚ S ≤ C)
    (IntermediateField.subset_adjoin ℚ S hx)
  have hmu : ∀ z : ℂ, z ^ N = 1 → z ∈ C := fun z hz' =>
    hSsub z (Or.inl (by simp [Polynomial.mem_nthRoots hN0, hz']))
  have hf : ∀ i : U, f i ∈ C := fun i => hSsub _ (Or.inr ⟨i, rfl⟩)
  have hval : ∀ v, χ.UnrAt v → χ.valTw s v ∈ C := by
    intro v hv
    have hex : ∃ v', c v' = c v ∧ χ.UnrAt v' := ⟨v, rfl, hv⟩
    have hw := hex.choose_spec
    have hwC : χ.valTw s hex.choose ∈ C := hf ⟨c v, hex⟩
    by_cases hvw : v = hex.choose
    · rw [hvw]
      exact hwC
    · obtain ⟨k, hkk⟩ := hc v hex.choose hw.1.symm
      have h1 : ∀ u, u ∉ ({v, hex.choose} : Finset (HeightOneSpectrum (𝓞 L))) → ordF u k = 0 := by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu
        rw [hkk u, if_neg hu.1, if_neg hu.2, sub_zero]
      have h2 : ∀ u ∈ ({v, hex.choose} : Finset (HeightOneSpectrum (𝓞 L))), χ.UnrAt u := by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl
        · exact hv
        · exact hw.2
      obtain ⟨r, hr, e⟩ := hKey χ s m hm k {v, hex.choose} h1 h2
      have o1 : ordF v k = 1 := by rw [hkk]; simp [hvw]
      have o2 : ordF hex.choose k = -1 := by rw [hkk]; simp [Ne.symm hvw]
      rw [Finset.prod_pair hvw, o1, o2, zpow_one, zpow_neg_one] at e
      rw [eq_of_key e]
      exact C.mul_mem hwC (C.inv_mem (C.mul_mem (hCcompo (prod_mem_compo m (k : L))) (hmu _ (hz r hr))))
  have hint : ∀ x ∈ S, IsIntegral ℚ x := by
    intro x hx
    rcases hx with hx | ⟨i, rfl⟩
    · have hx' : x ^ N = 1 := by simpa [Polynomial.mem_nthRoots hN0] using hx
      exact IsIntegral.of_pow hN0 (by rw [hx']; exact isIntegral_one)
    · obtain ⟨P, hP, z, hzN, e⟩ := hA _ i.2.choose_spec.2
      have hpow : (f i) ^ (h * N) ∈ compo L := by
        have e1 : (f i) ^ h = (P * z)⁻¹ := eq_inv_of_mul_eq_one_left e
        rw [pow_mul, e1, inv_pow, mul_pow, hzN, mul_one]
        exact inv_mem (pow_mem hP N)
      exact IsIntegral.of_pow (Nat.mul_pos hh0 hN0) (isIntegral_of_mem_compo hpow)
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) :=
    IntermediateField.finiteDimensional_adjoin hint
  haveI hC : FiniteDimensional ℚ C := IntermediateField.finiteDimensional_sup _ _
  refine ⟨C.toSubfield, ?_, fun v hv => ⟨⟨χ.valTw s v, hval v hv⟩, rfl⟩⟩
  let e : C ≃ₗ[ℚ] C.toSubfield :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun x y => rfl
      map_smul' := fun q x => rfl
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  exact LinearEquiv.finiteDimensional e

end PI.AlgValsFin.W
end
end
