module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.Bundle002
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
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

noncomputable section

open TensorProduct NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace PI.UnitaryApproxFinWork

theorem unitary_scalars : UnitS := by
  intro F E _ _ _ _ _ v π hπ s hs
  classical
  let O := v.adicCompletionIntegers F
  let S := Sv E v
  have hgen2 : ∀ y : O, ((1 : E) ⊗ₜ[F] (y : v.adicCompletion F)) ∈ S := by
    intro y
    exact Subring.subset_closure (Or.inr ⟨⟨y, y.2⟩, rfl⟩)
  let ψ : O →+* E ⊗[F] v.adicCompletion F :=
    (Algebra.TensorProduct.includeRight :
      v.adicCompletion F →ₐ[F] E ⊗[F] v.adicCompletion F).toRingHom.comp O.subtype
  have hψ : ∀ y : O, ψ y = (1 : E) ⊗ₜ[F] (y : v.adicCompletion F) := fun y => rfl
  let φ : O →+* S := ψ.codRestrict S (fun y => by rw [hψ]; exact hgen2 y)
  letI : Algebra O (E ⊗[F] v.adicCompletion F) := ψ.toAlgebra
  letI : Algebra O S := φ.toAlgebra
  let f : S →ₐ[O] E ⊗[F] v.adicCompletion F := { S.subtype with commutes' := fun r => rfl }
  have hle : S ≤ (integralClosure O (E ⊗[F] v.adicCompletion F)).toSubring := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · obtain ⟨z, rfl⟩ := RingHom.mem_range.1 hx
      obtain ⟨p, hpm, hp⟩ := NumberField.RingOfIntegers.isIntegral_coe z
      refine ⟨p.map (Int.castRingHom O), hpm.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      have hcomp : (algebraMap O (E ⊗[F] v.adicCompletion F)).comp (Int.castRingHom O) =
          (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (E := E)).comp (algebraMap ℤ E) :=
        RingHom.ext_int _ _
      rw [hcomp]
      have := Polynomial.hom_eval₂ p (algebraMap ℤ E) (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (E := E))
        (algebraMap (𝓞 E) E z)
      rw [hp, map_zero] at this
      exact this.symm
    · exact isIntegral_algebraMap (x := (⟨y, hy⟩ : O))
  have hIntS : Algebra.IsIntegral O S :=
    ⟨fun x => (isIntegral_algHom_iff f Subtype.val_injective).1 (hle x.2)⟩
  have hπv : Valued.v (algebraMap F (v.adicCompletion F) (π : F)) < 1 := by
    rw [wa_valued_algebraMap]
    exact (valuation_lt_one_iff_mem v π).2 hπ
  let πO : O := ⟨algebraMap F (v.adicCompletion F) (π : F), by
    rw [mem_adicCompletionIntegers]; exact hπv.le⟩
  have hπmax : πO ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.1 hu
    have h1 : Valued.v (w : v.adicCompletion F) ≤ 1 := by
      have := w.2
      rwa [mem_adicCompletionIntegers] at this
    have h2 : algebraMap F (v.adicCompletion F) (π : F) * (w : v.adicCompletion F) = 1 :=
      congrArg Subtype.val hw
    have h3 : Valued.v (algebraMap F (v.adicCompletion F) (π : F) * (w : v.adicCompletion F)) < 1 :=
      calc _ = Valued.v (algebraMap F (v.adicCompletion F) (π : F)) *
            Valued.v (w : v.adicCompletion F) := map_mul _ _ _
        _ ≤ Valued.v (algebraMap F (v.adicCompletion F) (π : F)) * 1 := mul_le_mul' le_rfl h1
        _ < 1 := by rw [mul_one]; exact hπv
    rw [h2, map_one] at h3
    exact lt_irrefl _ h3
  have hd : dv E v π = (1 : E) ⊗ₜ[F] algebraMap F (v.adicCompletion F) (π : F) := by
    simp only [dv, PI.UnitaryApproxDefs.inclE, Algebra.TensorProduct.includeLeftRingHom_apply,
      Algebra.algebraMap_eq_smul_one]
    exact TensorProduct.smul_tmul _ _ _
  have hxS : 1 + dv E v π * s ∈ S :=
    S.add_mem S.one_mem (S.mul_mem (by rw [hd]; exact hgen2 πO) hs)
  have key : IsUnit (⟨1 + dv E v π * s, hxS⟩ : S) := by
    by_contra h
    obtain ⟨M, hM, hxM⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 h)
    have hP : (M.comap (algebraMap O S)).IsMaximal := by
      letI := hIntS
      exact Ideal.isMaximal_under_of_isIntegral_of_isMaximal M
    have hπM : algebraMap O S πO ∈ M := by
      have : πO ∈ M.comap (algebraMap O S) := by
        rw [IsLocalRing.eq_maximalIdeal hP]; exact hπmax
      exact this
    have e : (1 : S) = ⟨1 + dv E v π * s, hxS⟩ - algebraMap O S πO * ⟨s, hs⟩ := by
      apply Subtype.ext
      change (1 : E ⊗[F] v.adicCompletion F) = (1 + dv E v π * s) -
        ((1 : E) ⊗ₜ[F] algebraMap F (v.adicCompletion F) (π : F)) * s
      rw [hd]; ring
    have h1 : (1 : S) ∈ M := by
      rw [e]; exact M.sub_mem hxM (M.mul_mem_right _ hπM)
    exact hM.ne_top ((Ideal.eq_top_iff_one M).2 h1)
  obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.1 key
  exact ⟨w, w.2, congrArg Subtype.val hw⟩

end PI.UnitaryApproxFinWork

end
end

section

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace PI.UnitaryApproxFinWork

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_span_int : ∃ (d : ℕ) (b : Fin d → E), (∀ k, b k ∈ PI.UnitaryApproxDefs.intOE E) ∧
    ∀ e : E, ∃ f : Fin d → F, e = ∑ k, f k • b k := by
  let B := (NumberField.integralBasis E).reindex (Fintype.equivFin _)
  refine ⟨_, fun k => B k, fun k => ?_, fun e => ?_⟩
  · show B k ∈ (algebraMap (𝓞 E) E).range
    refine ⟨RingOfIntegers.basis E ((Fintype.equivFin _).symm k), ?_⟩
    simp only [B, Module.Basis.reindex_apply, NumberField.integralBasis_apply]
  · refine ⟨fun k => ((B.repr e k : ℚ) : F), ?_⟩
    conv_lhs => rw [← B.sum_repr e]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_ratCast, eq_ratCast]

theorem tensor_decomp {d : ℕ} (b : Fin d → E) (hb : ∀ e : E, ∃ f : Fin d → F, e = ∑ k, f k • b k)
    {R : Type} [CommRing R] [Algebra F R] (x : E ⊗[F] R) :
    ∃ c : Fin d → R, x = ∑ k, b k ⊗ₜ[F] c k := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul e r =>
    obtain ⟨f, hf⟩ := hb e
    refine ⟨fun k => f k • r, ?_⟩
    rw [hf, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [TensorProduct.smul_tmul]
  | add x y hx hy =>
    obtain ⟨c1, h1⟩ := hx
    obtain ⟨c2, h2⟩ := hy
    refine ⟨c1 + c2, ?_⟩
    simp [h1, h2, TensorProduct.tmul_add, Finset.sum_add_distrib]

theorem approxEStep : ApproxEStep := by
  intro hW
  unfold ApproxE
  intro F E _ _ _ _ _ T x D hD
  obtain ⟨d, b, hbint, hb⟩ := exists_span_int (F := F) (E := E)
  have hc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ c : Fin d → v.adicCompletion F,
      x v = ∑ k, b k ⊗ₜ[F] c k := fun v => tensor_decomp b hb (x v)
  choose c hc using hc
  have ha : ∀ k, ∃ a : F, ∀ v ∈ T, ∃ t ∈ v.adicCompletionIntegers F,
      c v k - algebraMap F (v.adicCompletion F) a = algebraMap F (v.adicCompletion F) (D : F) * t :=
    fun k => hW F T (fun v => c v k) D hD
  choose a ht using ha
  refine ⟨∑ k, a k • b k, fun v hv => ?_⟩
  choose t htO hteq using fun k => ht k v hv
  refine ⟨∑ k, (1 : E) ⊗ₜ[F] t k * PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (b k), ?_, ?_⟩
  · exact Subring.sum_mem _ fun k _ =>
      Subring.mul_mem _ (one_tmul_mem_Sv v (htO k)) (inclE_mem_Sv v (hbint k))

  · rw [hc v, map_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [PI.UnitaryApproxDefs.inclE, dv, Algebra.TensorProduct.includeLeftRingHom_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [TensorProduct.smul_tmul, ← TensorProduct.tmul_sub, Algebra.smul_def (a k), mul_one, hteq k,
      ← Algebra.smul_def, ← TensorProduct.smul_tmul, Algebra.smul_def]

end PI.UnitaryApproxFinWork

end
end

section

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace PI.UnitaryApproxFinWork

theorem dv_two {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) : dv E v 2 = 2 := by
  have h2 : ((2 : 𝓞 F) : F) = 2 := map_ofNat (algebraMap (𝓞 F) F) 2
  simp only [dv, h2, map_ofNat]

theorem skew_approx (hAE : ApproxE) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {n : Type} [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e)
    (T : Finset (HeightOneSpectrum (𝓞 F)))
    (Y : (v : HeightOneSpectrum (𝓞 F)) → Matrix n n (E ⊗[F] v.adicCompletion F))
    (hY : ∀ v ∈ T, PI.UnitaryApproxDefs.cT (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F)) (Y v) = -Y v) (δ : 𝓞 F) (hδ : δ ≠ 0) :
    ∃ Y' : Matrix n n E, PI.UnitaryApproxDefs.cT (σ : E →+* E) Y' = -Y' ∧
      ∀ v ∈ T, MC E v δ (Y'.map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F)) - Y v) := by
  have h2δ : (2 * δ : 𝓞 F) ≠ 0 := mul_ne_zero two_ne_zero hδ
  have hz : ∀ i j, ∃ e : E, ∀ v ∈ T,
      Cong E v (2 * δ) (Y v i j - PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) e) :=
    fun i j => hAE F E T (fun v => Y v i j) (2 * δ) h2δ
  choose Z hZ using hz
  refine ⟨Matrix.of fun i j => (2⁻¹ : E) * (Z i j - σ (Z j i)), ?_, fun v hv => ?_⟩
  · ext i j
    show (σ : E →+* E) ((2⁻¹ : E) * (Z j i - σ (Z i j))) = -((2⁻¹ : E) * (Z i j - σ (Z j i)))
    simp only [AlgHom.coe_toRingHom, map_mul, map_inv₀, map_ofNat, map_sub, hσ]
    ring
  · obtain ⟨A, hAS, hAeq⟩ := MC_of_entries (E := E) (v := v) (d := 2 * δ)
      (M := Y v - (Matrix.of Z).map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F))) (fun i j => hZ i j v hv)
    refine ⟨PI.UnitaryApproxDefs.cT (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F)) A - A, MS_sub (MS_cT σ hAS) hAS, ?_⟩
    ext i j
    have e1 := congrFun (congrFun hAeq i) j
    have e2 := congrArg (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F)) (congrFun (congrFun hAeq j) i)
    have e3 := congrFun (congrFun (hY v hv) i) j
    change PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F) (Y v j i) = -(Y v i j) at e3
    change Y v i j - PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (Z i j) = dv E v (2 * δ) * A i j at e1
    change PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F) (Y v j i - PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (Z j i)) =
      PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F) (dv E v (2 * δ) * A j i) at e2
    rw [map_sub, map_mul, sigR_inclE, sigR_dv] at e2
    rw [dv_mul, dv_two] at e1 e2
    change PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) ((2⁻¹ : E) * (Z i j - σ (Z j i))) - Y v i j =
      dv E v δ * (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F) (A j i) - A i j)
    have hh : PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (2⁻¹ : E) * 2 = 1 := by
      rw [← map_ofNat (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F)) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero,
        map_one]
    rw [map_mul, map_sub]
    linear_combination (-(PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (2⁻¹ : E))) * e1 +
      (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (2⁻¹ : E)) * e2 -
      (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (2⁻¹ : E)) * e3 +
      (Y v i j + dv E v δ * (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F) (A j i) - A i j)) * hh

end PI.UnitaryApproxFinWork

end
end

section

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace PI.UnitaryApproxFinWork

theorem topStep : TopStep := by
  unfold TopStep CayleyFin EigAvoid PI.UnitaryApproxFin.UnitaryApproxFin
  intro hC hE F E iF iNF iE iNE iA n iFt iDe σ J hσ hθ hJ hdet T g hg D hD
  obtain ⟨μ, hμ, hinv⟩ := hE F E n σ hσ hθ T (fun v => ((g v : GL n _) : Matrix n n _))
  have hμ' : μ * σ μ = 1 := by rw [mul_comm]; exact hμ
  have hab : ∀ v : HeightOneSpectrum (𝓞 F),
      PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) μ *
        PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (σ μ) = 1 := fun v => by
    rw [← map_mul, hμ', map_one]
  have hρ : ∀ v : HeightOneSpectrum (𝓞 F),
      PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F)
          (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) μ) *
        PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) μ = 1 := fun v => by
    rw [sigR_inclE, ← map_mul, hμ, map_one]
  obtain ⟨c, hc0, hc⟩ := exists_int_mul (F := F) (σ μ)
  obtain ⟨γ', hγ', hcong⟩ := hC F E n σ J hσ hJ hdet T
    (fun v => scU (n := n) (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) μ)
      (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (σ μ)) (hab v) * g v)
    (fun v hv => Subgroup.mul_mem _
      (scU_mem_UJ (n := n) (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F))
        (J.map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F))) _ _ _ (hρ v)) (hg v hv))
    (fun v hv => by
      simp only [Units.val_mul, scU_val, Matrix.smul_mul, Matrix.one_mul]
      exact hinv v hv)
    (D * c) (mul_ne_zero hD hc0)
  refine ⟨scU (n := n) (σ μ) μ hμ * γ',
    Subgroup.mul_mem _ (scU_mem_UJ (n := n) (σ : E →+* E) J (σ μ) μ hμ ?_) hγ', ?_⟩
  · show σ (σ μ) * σ μ = 1
    rw [hσ, hμ']
  · intro v hv i j
    obtain ⟨s, hs, hseq⟩ := hcong v hv i j
    refine ⟨PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (algebraMap F E (c : F) * σ μ) * s,
      Subring.mul_mem _ (inclE_mem_Sv v hc) hs, ?_⟩
    have hdv : dv E v (D * c) =
        PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (algebraMap F E (D : F)) *
          PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (algebraMap F E (c : F)) :=
      dv_mul v D c
    have hba : PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (σ μ) *
        PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) μ = 1 := by
      rw [← map_mul, hμ, map_one]
    simp only [Units.val_mul, scU_val, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply,
      smul_eq_mul] at hseq ⊢
    rw [hdv] at hseq
    simp only [map_mul]
    linear_combination PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (σ μ) * hseq -
      ((g v : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) i j * hba

end PI.UnitaryApproxFinWork

end
end
