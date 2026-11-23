module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle160
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle567
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle568
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle101
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle280
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle185
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle565
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle297
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle414
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle387
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle570
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle403
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle569
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle014
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Isomorphisms
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Mathlib.RingTheory.MvPowerSeries.Basic

@[expose] public section

section

open NumberField MeasureTheory

theorem _root_.GlobalTheory.T.exists_measurable_partitionOfUnity_unitLogTranslates : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∃ p : (I → ℝ) → ℝ, Measurable p ∧ (∀ y, 0 ≤ p y) ∧ (∀ y, HasSum (fun u : (NumberField.RingOfIntegers K)ˣ => p (y + GlobalTheory.HeckeTheta.ulog φ u)) 1) ∧ ∃ R : ℝ, ∀ y, p y ≠ 0 → ∀ i j, y i - y j ≤ R := by
  first | exact @GlobalTheory.exists_measurable_nonneg_hasSum_ulog_translates | exact GlobalTheory.exists_measurable_nonneg_hasSum_ulog_translates | (intros; apply GlobalTheory.exists_measurable_nonneg_hasSum_ulog_translates <;> assumption)
end

section

open NumberField MeasureTheory

theorem _root_.GlobalTheory.T.periodic_bounded_gaussian_summable_cmType : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (M : Ideal (NumberField.RingOfIntegers K)) (F : NumberField.RingOfIntegers K → ℂ), M ≠ ⊥ → (∀ α μ : NumberField.RingOfIntegers K, μ ∈ M → F (α + μ) = F α) → (∃ C : ℝ, ∀ α, ‖F α‖ ≤ C) ∧ (∀ ε : ℝ, 0 < ε → Summable (fun α : NumberField.RingOfIntegers K => ‖F α‖ * Real.exp (-ε * ‖GlobalTheory.HeckeTheta.emb φ (α : K)‖ ^ 2))) ∧ ∀ α : NumberField.RingOfIntegers K, GlobalTheory.HeckeTheta.emb φ (α : K) ≠ 0 → 1 ≤ ‖GlobalTheory.HeckeTheta.emb φ (α : K)‖ := by
  first | exact @GlobalTheory.HeckeLat.periodic_bound_summable_norm | exact GlobalTheory.HeckeLat.periodic_bound_summable_norm | (intros; apply GlobalTheory.HeckeLat.periodic_bound_summable_norm <;> assumption)
end

section

open NumberField MeasureTheory

theorem _root_.GlobalTheory.T.heckeMellinGaussIntegrand_unit_mul : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ) (s : ℂ) (u : (𝓞 K)ˣ) (α : K) (y : I → ℝ), GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (((u : 𝓞 K) : K) * α)) y = GlobalTheory.HeckeStrip.wt φ n ((u : 𝓞 K) : K) * GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ α) (y + GlobalTheory.HeckeTheta.ulog φ u) := by
  first | exact @GlobalTheory.HeckeShift.term_unit_mul | exact GlobalTheory.HeckeShift.term_unit_mul | (intros; apply GlobalTheory.HeckeShift.term_unit_mul <;> assumption)
end

section

open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model

noncomputable section

namespace GlobalTheory.HTRho.CRTSplit

variable {k O C V : Type*} [Field k] [Ring O] [CommRing C] [Algebra C O] [AddCommGroup V] [Module k V]

abbrev actC (τ : O →+* Module.End k V) : MonoidAlgebra k C →ₐ[k] Module.End k V :=
  MonoidAlgebra.lift k (Module.End k V) C (τ.comp (algebraMap C O)).toMonoidHom

abbrev chiC (χ : C →+* k) : MonoidAlgebra k C →ₐ[k] k :=
  MonoidAlgebra.lift k k C χ.toMonoidHom

theorem actC_apply (τ : O →+* Module.End k V) (f : MonoidAlgebra k C) (v : V) :
    actC τ f v = ∑ c ∈ f.coeff.support, f.coeff c • τ (algebraMap C O c) v := by
  rw [actC, MonoidAlgebra.lift_apply, Finsupp.sum, LinearMap.sum_apply]
  rfl

theorem chiC_apply (χ : C →+* k) (f : MonoidAlgebra k C) :
    chiC χ f = ∑ c ∈ f.coeff.support, f.coeff c * χ c := by
  rw [chiC, MonoidAlgebra.lift_apply, Finsupp.sum]
  rfl

theorem actC_of (τ : O →+* Module.End k V) (c : C) :
    actC τ (MonoidAlgebra.of k C c) = τ (algebraMap C O c) := by
  rw [actC, MonoidAlgebra.lift_of]; rfl

theorem chiC_of (χ : C →+* k) (c : C) : chiC χ (MonoidAlgebra.of k C c) = χ c := by
  rw [chiC, MonoidAlgebra.lift_of]; rfl

theorem actC_eq_zero {Idx : Type*} (τ : O →+* Module.End k V) (χ : Idx → C →+* k)
    (hJ : jSub τ χ ⊤ = ⊥) (f : MonoidAlgebra k C) (hf : ∀ i, chiC (χ i) f = 0) (v : V) :
    actC τ f v = 0 := by
  have hmem : actC τ f v ∈ jSub τ χ ⊤ := by
    apply Submodule.subset_span
    refine ⟨f.coeff.support.card, fun l => f.coeff (f.coeff.support.equivFin.symm l),
      fun l => (f.coeff.support.equivFin.symm l : C), v, trivial, fun i => ?_, ?_⟩
    · have h1 := Equiv.sum_comp f.coeff.support.equivFin.symm
        (fun x : f.coeff.support => f.coeff x * χ i x)
      beta_reduce at h1
      rw [h1, Finset.sum_coe_sort f.coeff.support (fun x => f.coeff x * χ i x), ← chiC_apply, hf i]
    · have h1 := Equiv.sum_comp f.coeff.support.equivFin.symm
        (fun x : f.coeff.support => f.coeff x • τ (algebraMap C O x) v)
      beta_reduce at h1
      rw [h1, Finset.sum_coe_sort f.coeff.support (fun x => f.coeff x • τ (algebraMap C O x) v),
        actC_apply]
  rw [hJ] at hmem
  simpa using hmem

theorem actC_mem_mSub (τ : O →+* Module.End k V) (χ : C →+* k) (f : MonoidAlgebra k C)
    (hf : chiC χ f = 0) (x : V) : actC τ f x ∈ mSub τ χ ⊤ := by
  have h : actC τ f x = ∑ c ∈ f.coeff.support, f.coeff c • (τ (algebraMap C O c) x - χ c • x) := by
    simp only [smul_sub, Finset.sum_sub_distrib, smul_smul]
    rw [actC_apply, ← Finset.sum_smul, ← chiC_apply, hf, zero_smul, sub_zero]
  rw [h]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, x, trivial, rfl⟩)

theorem actC_mSub_eq_zero {Idx : Type*} (τ : O →+* Module.End k V) (χ : Idx → C →+* k)
    (hJ : jSub τ χ ⊤ = ⊥) (i : Idx) (e : MonoidAlgebra k C) (he : ∀ l, l ≠ i → chiC (χ l) e = 0)
    (y : V) (hy : y ∈ mSub τ (χ i) ⊤) : actC τ e y = 0 := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨c, x, -, rfl⟩ := hz
    have h2 : τ (algebraMap C O c) x - χ i c • x =
        actC τ (MonoidAlgebra.of k C c - algebraMap k _ (χ i c)) x := by
      rw [map_sub, AlgHom.commutes, actC_of, LinearMap.sub_apply, Module.algebraMap_end_apply]
    rw [h2, ← Module.End.mul_apply, ← map_mul]
    refine actC_eq_zero τ χ hJ _ (fun l => ?_) x
    rw [map_mul]
    by_cases hl : l = i
    · subst hl
      rw [map_sub, AlgHom.commutes, chiC_of, Algebra.algebraMap_self, RingHom.id_apply, sub_self,
        mul_zero]
    · rw [he l hl, zero_mul]
  | zero => simp
  | add _ _ _ _ h1 h2 => rw [map_add (f := _), h1, h2, add_zero]
  | smul a _ _ h => rw [map_smul, h, smul_zero]

end GlobalTheory.HTRho.CRTSplit


open GlobalTheory.HTRho.CRTSplit in
theorem GlobalTheory.HTRho.finrank_homO_eq_sum_quot : ∀ {k O C Idx W V : Type*} [Field k] [Ring O] [CommRing C] [Algebra C O]
    [Fintype Idx] [AddCommGroup W] [Module k W] [FiniteDimensional k W] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (σW : O →+* Module.End k W) (τ : O →+* Module.End k V) (χ : Idx → C →+* k),
    Function.Injective χ → jSub τ χ ⊤ = ⊥ →
    finrank k (homO σW τ) = ∑ i, finrank k (homO σW (qAct τ (mSub τ (χ i) ⊤)
      (mSub_stable τ (χ i) ⊤ (fun _ _ _ => trivial)))) := by
  intro k O C Idx W V _ _ _ _ _ _ _ _ _ _ _ σW τ χ hχ hJ
  classical
  have hb : ∀ i j, ∃ b : MonoidAlgebra k C, i ≠ j → chiC (χ i) b = 1 ∧ chiC (χ j) b = 0 := by
    intro i j
    by_cases hij : i = j
    · exact ⟨0, fun h => (h hij).elim⟩
    obtain ⟨c, hc⟩ := DFunLike.ne_iff.mp (hχ.ne hij)
    have hc' : χ i c - χ j c ≠ 0 := sub_ne_zero.mpr hc
    refine ⟨(χ i c - χ j c)⁻¹ • (MonoidAlgebra.of k C c - algebraMap k _ (χ j c)), fun _ => ⟨?_, ?_⟩⟩
    · rw [map_smul, map_sub, AlgHom.commutes, chiC_of, Algebra.algebraMap_self, RingHom.id_apply,
        smul_eq_mul, inv_mul_cancel₀ hc']
    · rw [map_smul, map_sub, AlgHom.commutes, chiC_of, Algebra.algebraMap_self, RingHom.id_apply,
        sub_self, smul_zero]
  choose b hb using hb
  let e : Idx → MonoidAlgebra k C := fun i => ∏ j ∈ Finset.univ.erase i, b i j
  have he : ∀ i l, chiC (χ l) (e i) = if l = i then 1 else 0 := by
    intro i l
    simp only [e, map_prod]
    split_ifs with hl
    · subst hl; exact Finset.prod_eq_one fun j hj => (hb l j (Finset.ne_of_mem_erase hj).symm).1
    · exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hl, Finset.mem_univ l⟩) (hb i l (Ne.symm hl)).2
  have hsum : ∀ v : V, v = ∑ i, actC τ (e i) v := by
    intro v
    have h0 : actC τ (1 - ∑ i, e i) v = 0 :=
      actC_eq_zero τ χ hJ _ (fun l => by simp [map_sub, map_sum, he]) v

    rw [map_sub, map_one, map_sum, LinearMap.sub_apply, Module.End.one_apply, LinearMap.sum_apply,
    sub_eq_zero] at h0
    exact h0
  let Φ : V →ₗ[k] ((i : Idx) → V ⧸ mSub τ (χ i) ⊤) := LinearMap.pi fun i => (mSub τ (χ i) ⊤).mkQ
  have hΦ : Function.Bijective Φ := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro v hv
      have hv' : ∀ i, v ∈ mSub τ (χ i) ⊤ := fun i => by
        have := congr_fun hv i
        simpa [Φ, Submodule.Quotient.mk_eq_zero] using this
      rw [hsum v]
      exact Finset.sum_eq_zero fun i _ =>
        actC_mSub_eq_zero τ χ hJ i (e i) (fun l hl => by rw [he, if_neg hl]) v (hv' i)
    · intro q
      choose w hw using fun i => Submodule.Quotient.mk_surjective (mSub τ (χ i) ⊤) (q i)
      refine ⟨∑ j, actC τ (e j) (w j), funext fun i => ?_⟩
      simp only [Φ, LinearMap.pi_apply, Submodule.mkQ_apply]
      rw [← hw i, Submodule.Quotient.eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_sub_right_comm]
      refine add_mem ?_ (Submodule.sum_mem _ fun j hj => actC_mem_mSub τ (χ i) _
        (by rw [he, if_neg (Finset.ne_of_mem_erase hj).symm]) (w j))
      have h3 := actC_mem_mSub τ (χ i) (e i - 1) (by rw [map_sub, he, if_pos rfl, map_one, sub_self]) (w i)
      simpa [map_sub] using h3
  let Φe := LinearEquiv.ofBijective Φ hΦ
  let Ψ : homO σW τ →ₗ[k] ((i : Idx) → homO σW (qAct τ (mSub τ (χ i) ⊤)
      (mSub_stable τ (χ i) ⊤ (fun _ _ _ => trivial)))) :=
    LinearMap.pi fun i =>
      { toFun := fun T => ⟨(mSub τ (χ i) ⊤).mkQ ∘ₗ T.1, (mem_homO _ _ _).mpr fun a x => by
            rw [LinearMap.comp_apply, LinearMap.comp_apply, (mem_homO _ _ _).mp T.2 a x, qAct_mk]⟩
        map_add' := fun S T => by ext; simp
        map_smul' := fun c T => by ext; simp }
  have hΨ : Function.Bijective Ψ := by
    constructor
    · intro S T h
      apply Subtype.ext
      apply LinearMap.ext
      intro x
      apply hΦ.1
      funext i
      have := congrArg (fun F => ((F i).1 x)) h
      simpa [Ψ, Φ] using this
    · intro F
      let T : W →ₗ[k] V := Φe.symm.toLinearMap ∘ₗ LinearMap.pi (fun i => (F i).1)
      have hT : ∀ x i, (mSub τ (χ i) ⊤).mkQ (T x) = (F i).1 x := fun x i =>
        congr_fun (Φe.apply_symm_apply (fun i => (F i).1 x)) i
      have hTm : T ∈ homO σW τ := by
        rw [mem_homO]
        intro a x
        apply hΦ.1
        funext i
        change (mSub τ (χ i) ⊤).mkQ (T (σW a x)) = (mSub τ (χ i) ⊤).mkQ (τ a (T x))
        rw [hT, ← qAct_mk τ _ (mSub_stable τ (χ i) ⊤ (fun _ _ _ => trivial)), hT,
          (mem_homO _ _ _).mp (F i).2 a x]
      refine ⟨⟨T, hTm⟩, funext fun i => Subtype.ext (LinearMap.ext fun x => ?_)⟩
      exact hT x i
  rw [LinearEquiv.finrank_eq (LinearEquiv.ofBijective Ψ hΨ), Module.finrank_pi_fintype]
end
end

section

open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model

namespace GlobalTheory.HTRho

theorem mSub_qAct_top {k O C : Type*} {H : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O] [CommRing C]
    [Algebra C O] (σ : O →+* Module.End k H) (G : Submodule k H) (hG : ∀ a, ∀ x ∈ G, σ a x ∈ G)
    (χ : C →+* k) : mSub (qAct σ G hG) χ ⊤ = (mSub σ χ ⊤).map G.mkQ := by
  unfold mSub
  rw [Submodule.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨c, x, -, rfl⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective G x
    refine ⟨σ (algebraMap C O c) y - χ c • y, ⟨c, y, trivial, rfl⟩, ?_⟩
    rw [map_sub, map_smul]
    rfl
  · rintro ⟨w, ⟨c, y, -, rfl⟩, rfl⟩
    refine ⟨c, G.mkQ y, trivial, ?_⟩
    rw [map_sub, map_smul, qAct_mk]

theorem quotFacts {k O C Idx H : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O] [CommRing C]
    [Algebra C O] (σ : O →+* Module.End k H) (G : Submodule k H) (hG : ∀ a, ∀ x ∈ G, σ a x ∈ G)
    (χ : Idx → C →+* k) :
    (jSub σ χ ⊤ ≤ G → jSub (qAct σ G hG) χ ⊤ = ⊥) ∧
      ∀ i, finrank k ((H ⧸ G) ⧸ mSub (qAct σ G hG) (χ i) ⊤) = finrank k (H ⧸ (G ⊔ mSub σ (χ i) ⊤)) := by
  refine ⟨fun hJ => ?_, fun i => ?_⟩
  · unfold jSub
    rw [Submodule.span_eq_bot]
    rintro z ⟨r, lam, c, x, -, hc, rfl⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective G x
    have hmem : (∑ l, lam l • σ (algebraMap C O (c l)) y) ∈ G :=
      hJ (Submodule.subset_span ⟨r, lam, c, y, trivial, hc, rfl⟩)
    have : (∑ l, lam l • qAct σ G hG (algebraMap C O (c l)) (Submodule.Quotient.mk y)) =
        G.mkQ (∑ l, lam l • σ (algebraMap C O (c l)) y) := by

      rw [map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul]
      rfl
    rw [this, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hmem
  · rw [mSub_qAct_top]
    exact LinearEquiv.finrank_eq (Submodule.quotientQuotientEquivQuotientSup G (mSub σ (χ i) ⊤))

end GlobalTheory.HTRho
end

section

open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model

namespace GlobalTheory.HTRho

theorem finrank_homO_eq_quot_mSub : ∀ {k O C W V : Type*} [Field k] [Ring O] [CommRing C] [Algebra C O]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (σW : O →+* Module.End k W) (τ : O →+* Module.End k V) (χ : C →+* k),
    (∀ c, τ (algebraMap C O c) = χ c • 1) →
    finrank k (homO σW τ) = finrank k (homO (qAct σW (mSub σW χ ⊤) (mSub_stable σW χ ⊤ (fun _ _ _ => trivial))) τ) := by
  intro k O C W V _ _ _ _ _ _ _ _ _ _ σW τ χ hτ
  have hker : ∀ T : W →ₗ[k] V, T ∈ homO σW τ → mSub σW χ ⊤ ≤ LinearMap.ker T := by
    intro T hT
    rw [mem_homO] at hT
    refine Submodule.span_le.mpr ?_
    rintro z ⟨c, x, -, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, hT, hτ, LinearMap.smul_apply,
      Module.End.one_apply, sub_self]
  let qa := qAct σW (mSub σW χ ⊤) (mSub_stable σW χ ⊤ (fun _ _ _ => trivial))
  let e : homO qa τ ≃ₗ[k] homO σW τ :=
    { toFun := fun f => ⟨f.1 ∘ₗ (mSub σW χ ⊤).mkQ, by
        rw [mem_homO]
        intro a x
        have h := (mem_homO _ _ _).mp f.2 a ((mSub σW χ ⊤).mkQ x)
        change f.1 ((mSub σW χ ⊤).mkQ (σW a x)) = τ a (f.1 ((mSub σW χ ⊤).mkQ x))
        rw [← qAct_mk]
        exact h⟩
      invFun := fun T => ⟨(mSub σW χ ⊤).liftQ T.1 (hker T.1 T.2), by
        rw [mem_homO]
        intro a y
        induction y using Submodule.Quotient.induction_on with
        | H x =>
          have h := (mem_homO _ _ _).mp T.2 a x
          change (mSub σW χ ⊤).liftQ T.1 _ (qa a ((mSub σW χ ⊤).mkQ x)) = τ a ((mSub σW χ ⊤).liftQ T.1 _ ((mSub σW χ ⊤).mkQ x))
          simp only [qa, qAct_mk, Submodule.liftQ_mkQ, Submodule.mkQ_apply, Submodule.liftQ_apply]
          exact h⟩
      map_add' := fun f g => by ext; rfl
      map_smul' := fun c f => by ext; rfl
      left_inv := fun f => by
        ext y
        rfl
      right_inv := fun T => by ext; rfl }
  exact e.finrank_eq.symm

end GlobalTheory.HTRho
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.finrank_le_frobeniusKernel_mul_span_primePowers : ∀ (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p] [CommRing H] [HopfAlgebra K H] [Module.Finite K H] (r : ℕ), Module.finrank K H ≤ Module.finrank K (H ⧸ frobKerIdeal (p ^ r) K H) * Module.finrank K (Submodule.span K (Set.range fun a : H => a ^ p ^ r)) := by
  first | exact @GlobalTheory.PDiv.finrank_le_frobKer_mul_span_pow | exact GlobalTheory.PDiv.finrank_le_frobKer_mul_span_pow | (intros; apply GlobalTheory.PDiv.finrank_le_frobKer_mul_span_pow <;> assumption)
end

section

open CategoryTheory Limits TensorProduct

namespace GlobalTheory.TorsorColim

theorem faithfullyFlat_of_split : ∀ (R D : Type) [CommRing R] [CommRing D] [Algebra R D], Module.Projective R D →
    (∃ τ : D →ₗ[R] R, τ 1 = 1) → Module.FaithfullyFlat R D := by
  intro R D _ _ _ hP ⟨τ, hτ⟩
  haveI : Module.Flat R D := inferInstance
  refine ⟨fun m hm h => ?_⟩
  have h1 : (1 : D) ∈ m • (⊤ : Submodule R D) := by rw [h]; exact Submodule.mem_top
  have h2 : ∀ x ∈ m • (⊤ : Submodule R D), τ x ∈ m := by
    intro x hx
    refine Submodule.smul_induction_on hx (fun r hr d _ => ?_) (fun x y hx hy => ?_)
    · rw [map_smul, smul_eq_mul]; exact m.mul_mem_right _ hr
    · rw [map_add (f := _)]; exact m.add_mem hx hy
  have := h2 1 h1
  rw [hτ] at this
  exact hm.ne_top ((Ideal.eq_top_iff_one m).2 this)

theorem isZModTorsor_of_algEquiv : ∀ (R D D' : Type) [CommRing R] [CommRing D] [CommRing D'] [Algebra R D] [Algebra R D'] (q : ℕ)
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[R] D)) (act' : Multiplicative (ZMod q) →* (D' ≃ₐ[R] D'))
    (e : D ≃ₐ[R] D'), (∀ (g : Multiplicative (ZMod q)) (x : D), e (act g x) = act' g (e x)) →
    GlobalTheory.LocAcyc.IsZModTorsor R D q act → GlobalTheory.LocAcyc.IsZModTorsor R D' q act' := by
  intro R D D' _ _ _ _ _ q act act' e he hD
  obtain ⟨h1, h2, h3, h4⟩ := hD
  have el : D ≃ₗ[R] D' := e.toLinearEquiv
  refine ⟨Module.Finite.equiv el, Module.Projective.of_equiv el, ?_, ?_⟩
  · exact Module.FaithfullyFlat.of_linearEquiv R D el.symm
  · let eT : D ⊗[R] D ≃ₐ[R] D' ⊗[R] D' := Algebra.TensorProduct.congr e e
    let eP : (Multiplicative (ZMod q) → D) ≃ₐ[R] (Multiplicative (ZMod q) → D') :=
      AlgEquiv.piCongrRight (fun _ => e)
    have key : ∀ x, GlobalTheory.TorsorColim.prodMapOf R D' q act' (eT x) = eP (GlobalTheory.TorsorColim.prodMapOf R D q act x) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        funext g
        simp [eT, eP, he]
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]
    have hb : Function.Bijective (GlobalTheory.TorsorColim.prodMapOf R D q act) := h4
    have : ⇑(GlobalTheory.TorsorColim.prodMapOf R D' q act') = eP ∘ (GlobalTheory.TorsorColim.prodMapOf R D q act) ∘ eT.symm := by
      funext y
      simp only [Function.comp_apply]
      rw [← key, AlgEquiv.apply_symm_apply]
    change Function.Bijective (GlobalTheory.TorsorColim.prodMapOf R D' q act')
    rw [this]
    exact eP.bijective.comp (hb.comp eT.symm.bijective)

theorem exists_torsor_model_of_isColimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (q : ℕ), 0 < q → ∀ (D : Type) [CommRing D] [Algebra c.pt D]
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[c.pt] D)), GlobalTheory.LocAcyc.IsZModTorsor c.pt D q act →
    ∃ (j : J), letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
    ∃ (Dj : Type) (_ : CommRing Dj) (_ : Algebra (F.obj j) Dj)
      (actj : Multiplicative (ZMod q) →* (Dj ≃ₐ[F.obj j] Dj)),
      GlobalTheory.LocAcyc.IsZModTorsor (F.obj j) Dj q actj ∧
      Nonempty (TensorProduct (F.obj j) c.pt Dj ≃ₐ[c.pt] D) := by
  intro J _ _ F c hc q hq D _ _ act hD
  haveI : Module.Finite c.pt D := hD.1
  haveI : Module.Projective c.pt D := hD.2.1
  haveI : Module.FinitePresentation c.pt D := Module.finitePresentation_of_projective c.pt D
  obtain ⟨j, A, _, _, _, he0⟩ := GlobalTheory.T.exists_finitePresentation_descent_of_isColimit J F c hc D inferInstance
  obtain ⟨k, B, _, _, _, actB, e, he⟩ := GlobalTheory.T.exists_zmod_action_model_of_isColimit_filtered J F c hc q hq j A D act he0
  letI : Algebra (F.obj k) c.pt := (c.ι.app k).hom.toAlgebra
  have hT : GlobalTheory.LocAcyc.IsZModTorsor c.pt (c.pt ⊗[F.obj k] B) q
      (GlobalTheory.TorsorColim.bcAct c.pt actB) := by
    refine GlobalTheory.TorsorColim.isZModTorsor_of_algEquiv c.pt D _ q act _ e.symm (fun g y => ?_) hD
    apply e.injective
    rw [he, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  have h1 := GlobalTheory.T.eventually_finite_baseChange_filtered_colimit J F c hc k B hT.1
  have h2 := GlobalTheory.T.projective_eventually_filteredColimit_algebra J F c hc k B ⟨hT.1, hT.2.1⟩
  have h3 := GlobalTheory.T.exists_late_split_of_filteredColimit J F c hc k B ⟨hT.1, GlobalTheory.T.exists_linear_splitting_unit_faithfullyFlat _ _ hT.1 hT.2.1 hT.2.2.1⟩
  have h4 := GlobalTheory.T.eventually_zmodTorsorGaloisProductMap_bijective_colimit J F c hc q hq k B actB hT
  have h34 := GlobalTheory.TorsorColim.eventually_and (fun (m : J) (h : k ⟶ m) => letI : Algebra (F.obj k) (F.obj m) := (F.map h).hom.toAlgebra; ∃ τ : (F.obj m ⊗[F.obj k] B) →ₗ[F.obj m] F.obj m, τ 1 = 1) (fun (m : J) (h : k ⟶ m) => letI : Algebra (F.obj k) (F.obj m) := (F.map h).hom.toAlgebra; Function.Bijective (GlobalTheory.TorsorColim.prodMapOf (F.obj m) (F.obj m ⊗[F.obj k] B) q (GlobalTheory.TorsorColim.bcAct (F.obj m) actB))) h3 h4
  have h234 := GlobalTheory.TorsorColim.eventually_and (fun (m : J) (h : k ⟶ m) => letI : Algebra (F.obj k) (F.obj m) := (F.map h).hom.toAlgebra; Module.Projective (F.obj m) (F.obj m ⊗[F.obj k] B)) (fun (m : J) (h : k ⟶ m) => letI : Algebra (F.obj k) (F.obj m) := (F.map h).hom.toAlgebra; (∃ τ : (F.obj m ⊗[F.obj k] B) →ₗ[F.obj m] F.obj m, τ 1 = 1) ∧ Function.Bijective (GlobalTheory.TorsorColim.prodMapOf (F.obj m) (F.obj m ⊗[F.obj k] B) q (GlobalTheory.TorsorColim.bcAct (F.obj m) actB))) h2 h34
  obtain ⟨m, f₀, hm⟩ := GlobalTheory.TorsorColim.eventually_and (fun (m : J) (h : k ⟶ m) => letI : Algebra (F.obj k) (F.obj m) := (F.map h).hom.toAlgebra; Module.Finite (F.obj m) (F.obj m ⊗[F.obj k] B)) (fun (m : J) (h : k ⟶ m) => letI : Algebra (F.obj k) (F.obj m) := (F.map h).hom.toAlgebra; Module.Projective (F.obj m) (F.obj m ⊗[F.obj k] B) ∧ (∃ τ : (F.obj m ⊗[F.obj k] B) →ₗ[F.obj m] F.obj m, τ 1 = 1) ∧ Function.Bijective (GlobalTheory.TorsorColim.prodMapOf (F.obj m) (F.obj m ⊗[F.obj k] B) q (GlobalTheory.TorsorColim.bcAct (F.obj m) actB))) h1 h234
  obtain ⟨i1, i2, ⟨τ, hτ⟩, i4⟩ := hm m (𝟙 m)
  refine ⟨m, ?_⟩
  letI : Algebra (F.obj k) (F.obj m) := (F.map (f₀ ≫ 𝟙 m)).hom.toAlgebra
  letI : Algebra (F.obj m) c.pt := (c.ι.app m).hom.toAlgebra
  haveI : IsScalarTower (F.obj k) (F.obj m) c.pt := IsScalarTower.of_algebraMap_eq (fun x => by
    change (c.ι.app k).hom x = (c.ι.app m).hom ((F.map (f₀ ≫ 𝟙 m)).hom x)
    rw [← c.w (f₀ ≫ 𝟙 m)]
    rfl)
  exact ⟨F.obj m ⊗[F.obj k] B, inferInstance, inferInstance, GlobalTheory.TorsorColim.bcAct (F.obj m) actB,
    ⟨i1, i2, GlobalTheory.TorsorColim.faithfullyFlat_of_split _ _ i2 ⟨τ, hτ⟩, i4⟩,
    ⟨(Algebra.TensorProduct.cancelBaseChange (F.obj k) (F.obj m) c.pt c.pt B).trans e⟩⟩

end GlobalTheory.TorsorColim
end

section

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

theorem _root_.GlobalTheory.T.exists_diagonalTorus_parametrisation_orthonormalFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), IsOrth X x → ∃ (t : (X.Ψ → Fin (r - 1) → ℝ) → realSU X.Ψ X.Gm) (Dt : (X.Ψ → Fin (r - 1) → ℝ) →L[ℝ] (X.Ψ → Fin r → Fin r → ℂ)), (∀ θ, X.lmulC (fun τ => ((((t θ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x (phaseFrame θ)) ∧ (∀ θ θ', t (θ + θ') = t θ * t θ') ∧ Continuous t ∧ HasStrictFDerivAt (fun θ => (fun τ a b => ((((t θ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) a b)) Dt 0 ∧ (∀ θ, Dt θ ∈ realLie X.Ψ X.Gm ∧ ∀ τ a b, inFrame x (Dt θ) τ a b = if a = b then Complex.I * (angles (θ τ) a : ℂ) else 0) ∧ (∀ g : realSU X.Ψ X.Gm, (∃ b ∈ Bor X.Ψ r, X.lmulC (fun τ => ((((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x b) → ∃ θ, g = t θ) := by
  first | exact @GlobalTheory.TorusFrame.torus_param | exact GlobalTheory.TorusFrame.torus_param | (intros; apply GlobalTheory.TorusFrame.torus_param <;> assumption)
end

section

open ValuativeRel Matrix


theorem _root_.GlobalTheory.T.box_function_twisted_coinvariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (ν β : kˣ →* ℂˣ), (∀ x, ‖(ν x : ℂ)‖ = 1) → ν ϖ ≠ 1 → ∀ (i₀ : A) (r c m : ℕ) (C : Matrix A D k) (H : Matrix (Fin r) A k) (Q : Matrix D (Fin r) k), (∀ l, H l i₀ = 0) → (∀ l i, valuation k (H l i) ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k)) → c + 1 ≤ m → (∀ l j, (H * C) l j ∈ 𝒪[k]) → (∀ j l, Q j l ∈ 𝒪[k]) → H * C * Q = 1 → (∀ j, C i₀ j = 0) → GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m) ∈ GlobalTheory.RankCoinv.lowRank (r + 1) ⊔ GlobalTheory.RankCoinv.twistSpan ν β := by
  first | exact @GlobalTheory.RankCoinv.boxFn_mem_lowRank_succ_sup_twistSpan_of_zero_row | exact GlobalTheory.RankCoinv.boxFn_mem_lowRank_succ_sup_twistSpan_of_zero_row | (intros; apply GlobalTheory.RankCoinv.boxFn_mem_lowRank_succ_sup_twistSpan_of_zero_row <;> assumption)
end
