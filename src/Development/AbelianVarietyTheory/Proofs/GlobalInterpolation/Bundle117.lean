module

public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PFamily
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.Th0CharMulOpUTh0HalfPeriodEq
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.Bundle004
public import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary

@[expose] public section

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.LatInvDenom

theorem lamMM_form (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) :
    ∀ z ∈ lamMM D (lamOf D cc δ), ∃ e ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E),
      z = fun τ => δ * embT D τ e := by
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, a, ha, rfl⟩ := hx
    obtain ⟨c, -, rfl⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.lam_mem D cc δ w hw
    refine ⟨((c : D.host.K) : D.host.E) * a, ?_, ?_⟩
    · exact Submodule.smul_mem (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)
        (⟨_, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.intK D c⟩ : 𝓞 D.host.E) ha
    · funext τ
      rw [map_mul, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.embT_K D τ _ (SetLike.coe_mem _)]
      ring
  | zero => exact ⟨0, Submodule.zero_mem _, by funext τ; simp⟩
  | add x y _ _ h1 h2 =>
    obtain ⟨e1, he1, rfl⟩ := h1
    obtain ⟨e2, he2, rfl⟩ := h2
    exact ⟨e1 + e2, Submodule.add_mem _ he1 he2, by funext τ; simp only [Pi.add_apply, map_add (f := _)]; ring⟩
  | neg x _ h1 =>
    obtain ⟨e1, he1, rfl⟩ := h1
    exact ⟨-e1, Submodule.neg_mem _ he1, by funext τ; simp only [Pi.neg_apply, map_neg]; ring⟩

theorem inverseIsometry_fourfoldLattice_denominator_coprime : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], Nat.Coprime (Ideal.absNorm cc) q → ∀ (u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)), Formalism.L2.Th1.H.IsIsom (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ¬ q ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) ≠ 0 → ∀ (G : (Fin 4 × D.what₂.Tau → D.host.K) ≃ₗ[D.host.K] (Fin 4 × D.what₂.Tau → D.host.K)), (∀ v : Fin 4 × D.what₂.Tau → D.host.K, u (fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E)) = fun w => D.host.φ₀ ((G v w : D.host.K) : D.host.E)) → ∀ v : Fin 4 × D.what₂.Tau → D.host.K, (∀ w, v w ∈ (algebraMap (𝓞 D.host.K) D.host.K).range) → ∃ s : ℕ, Nat.Coprime s q ∧ ∀ a, (s : D.host.E) * B.γ₀.g.symm (G.symm v) a ∈ D.host.AA0 := by
  intro D cc δ B hcc hδ12 q _ hNq u hu hidx hq hidx' G hG v hv
  have hqp : q.Prime := Fact.out
  have hδ : δ ≠ 0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.base_linkage_nonempty D cc δ B
  set S := Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau) with hS
  set M := Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ))
    (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ))
      (Formalism.L2.Th1.H.pow4 B.lamM)) with hM

  have hSd : Formalism.L2.Th1.H.IsSelfDual (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) S :=
    Formalism.L2.Th1.H.stdSelfDual B.L _
  have hMd : Formalism.L2.Th1.H.IsSelfDual (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) M :=
    Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.selfDual_img _ _ u hu _ (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.selfDual B hcc hδ12)
  have heq : Formalism.L2.Th1.H.relIdx S M = Formalism.L2.Th1.H.relIdx M S :=
    Formalism.L2.Th1.H.indexEq _ _ (Formalism.L2.Th1.H.stdHBasic B.L _).2.1 S M hSd hMd hidx hidx'
  set n := Formalism.L2.Th1.H.relIdx M S with hn
  have hnq : Nat.Coprime n q := by
    rw [← heq]; exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hqp).2 hq)
  have h1 : ∀ x ∈ S, n • x ∈ M := by
    intro x hx
    have := AddSubgroup.nsmul_index_mem (M.addSubgroupOf S) (⟨x, hx⟩ : S)
    rw [AddSubgroup.mem_addSubgroupOf, AddSubmonoidClass.coe_nsmul] at this
    exact this

  set N := Ideal.absNorm cc with hNdef
  have hNc : ((N : 𝓞 D.host.K)) ∈ cc := Ideal.absNorm_mem cc
  have hN0 : N ≠ 0 := by
    rw [hNdef, Ne, Ideal.absNorm_eq_zero_iff]; exact hcc.1
  choose o ho using hv
  set V : Fin 4 × D.what₂.Tau → ℂ := fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E) with hV
  have hz : (δ * (N : ℂ)) • V ∈ S := by
    rw [hS, Formalism.L2.Th1.H.mem_stdLat]
    intro w
    rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.mem_iff B]
    refine AddSubgroup.subset_closure ⟨(N : 𝓞 D.host.K) * o w, cc.mul_mem_right _ hNc, ?_⟩
    simp only [hV, Pi.smul_apply, smul_eq_mul, ← ho w]
    push_cast
    rw [map_mul, map_natCast]
    ring
  set y := B.γ₀.g.symm (G.symm v) with hy
  have hgy : u (B.gC (emb4 D y)) = V := by
    rw [show B.gC (emb4 D y) = _ from B.gC_spec y, hy, LinearEquiv.apply_symm_apply, hG (G.symm v),
      LinearEquiv.apply_symm_apply]
  obtain ⟨m', ⟨m₀, hm₀, rfl⟩, hm'⟩ := h1 _ hz
  have hm0eq : m₀ = ((n : ℂ) * δ * (N : ℂ)) • emb4 D y := by
    apply B.gC.injective
    apply u.injective
    have e1 : u (B.gC m₀) = n • ((δ * (N : ℂ)) • V) := hm'
    rw [e1, map_smul, map_smul, hgy, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_assoc]

  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := Fintype.card_pos_iff.mp (by
    rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.card_tau]
    exact Nat.mul_pos (by decide) D.R.ord_pos)
  refine ⟨n * N, Nat.Coprime.mul_left hnq hNq, fun a => ?_⟩
  obtain ⟨e, he, hee⟩ := lamMM_form D cc δ _ (hm₀ a)
  have h2 := congrFun hee τ
  rw [hm0eq] at h2
  simp only [Formalism.L2.Th1.H.slice, Pi.smul_apply, smul_eq_mul, emb4] at h2
  have h3 : embT D τ (((n * N : ℕ) : D.host.E) * y a) = embT D τ e := by
    apply mul_left_cancel₀ hδ
    rw [map_mul, map_natCast]
    push_cast
    linear_combination h2
  rw [(embT D τ).injective h3]
  exact he

end GlobalTheory.LatInvDenom

end
end

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.LatDesc

theorem unitary_maps_rational : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → ∀ (u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)), Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ∀ v : Fin 4 × D.what₂.Tau → D.host.K, ∃ v' : Fin 4 × D.what₂.Tau → D.host.K, u (fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E)) = fun w => D.host.φ₀ ((v' w : D.host.K) : D.host.E) := by
  intro D cc δ B hcc u hidx v
  have hδ : δ ≠ 0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.base_linkage_nonempty D cc δ B
  set S := Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau) with hS
  set M := Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM)) with hM
  set n := Formalism.L2.Th1.H.relIdx S M with hn

  have h1 : ∀ x ∈ M, n • x ∈ S := by
    intro x hx
    have := AddSubgroup.nsmul_index_mem (S.addSubgroupOf M) (⟨x, hx⟩ : M)
    rw [AddSubgroup.mem_addSubgroupOf, AddSubmonoidClass.coe_nsmul] at this
    exact this

  set y := B.γ₀.g.symm v with hy
  obtain ⟨t, ht, hint⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.exists_nat_mul D.host.E (Finset.univ.image y)
  set N := Ideal.absNorm cc with hNdef
  have hN : N ≠ 0 := by
    rw [hNdef, Ne, Ideal.absNorm_eq_zero_iff]; exact hcc.1
  have hNc : ((N : 𝓞 D.host.K)) ∈ cc := Ideal.absNorm_mem cc
  have hw₀ : δ * (N : ℂ) ∈ lamOf D cc δ := by
    refine AddSubgroup.subset_closure ⟨(N : 𝓞 D.host.K), hNc, ?_⟩
    simp
  have hm : (δ * (N : ℂ)) • emb4 D (t • y) ∈ Formalism.L2.Th1.H.pow4 B.lamM :=
    Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.gen_mem hw₀ fun a => Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.int_mem_inverse_half_different (by
      have := hint _ (Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩)
      simpa using this)
  set V : Fin 4 × D.what₂.Tau → ℂ := fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E) with hV
  have hg : B.gC (emb4 D (t • y)) = (t : ℂ) • V := by
    rw [show B.gC (emb4 D (t • y)) = _ from B.gC_spec (t • y), map_nsmul, hy, LinearEquiv.apply_symm_apply]
    funext w
    simp [hV]
  have hmem : (δ * (N : ℂ) * (t : ℂ)) • u V ∈ M := by
    refine ⟨B.gC ((δ * (N : ℂ)) • emb4 D (t • y)), ⟨_, hm, rfl⟩, ?_⟩
    show u (B.gC _) = _
    rw [map_smul, hg, smul_smul, map_smul]
  have hS' := h1 _ hmem
  rw [hS, Formalism.L2.Th1.H.mem_stdLat] at hS'
  have hc : ∀ w, ∃ c ∈ cc, ((n • ((δ * (N : ℂ) * (t : ℂ)) • u V)) w) = δ * D.host.φ₀ (((c : 𝓞 D.host.K) : D.host.K) : D.host.E) :=
    fun w => Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.lam_mem D cc δ _ ((Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.mem_iff B _).1 (hS' w))
  choose c _ hc using hc
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hidx
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  refine ⟨fun w => ((c w : 𝓞 D.host.K) : D.host.K) / ((n : D.host.K) * (N : D.host.K) * (t : D.host.K)), ?_⟩
  funext w
  have h := hc w
  simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul] at h
  have e : D.host.φ₀ (((((c w : 𝓞 D.host.K) : D.host.K) / ((n : D.host.K) * (N : D.host.K) * (t : D.host.K)) : D.host.K)) : D.host.E)
      = D.host.φ₀ (((c w : 𝓞 D.host.K) : D.host.K) : D.host.E) / ((n : ℂ) * (N : ℂ) * (t : ℂ)) := by
    push_cast
    rw [map_div₀, map_mul, map_mul, map_natCast, map_natCast, map_natCast]
  rw [e, eq_div_iff (mul_ne_zero (mul_ne_zero hnC hNC) htC)]
  apply mul_left_cancel₀ hδ
  rw [← h]
  ring

end GlobalTheory.LatDesc

end
end

section

open NumberField IsDedekindDomain GlobalTheory.UnitaryBC

namespace GlobalTheory

theorem algebraMap_mem_maximalRealSubfield_iff {K L : Type} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (x : K) :
    algebraMap K L x ∈ maximalRealSubfield L ↔ x ∈ maximalRealSubfield K := by
  simp only [mem_maximalRealSubfield_iff]
  constructor
  · intro hL ψ
    let : Algebra K ℂ := ψ.toAlgebra
    let φ : L →ₐ[K] ℂ := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    have hφ : φ (algebraMap K L x) = ψ x := φ.commutes x
    rw [← hφ]
    exact hL φ.toRingHom
  · intro hK φ
    exact hK (φ.comp (algebraMap K L))

theorem isCMField_of_sq_eq_totallyPositive :
    ∀ (K L : Type) [Field K] [NumberField K] [IsCMField K] [Field L] [NumberField L] [Algebra K L], Module.finrank K L = 2 → ∀ (d : maximalRealSubfield K) (t : L), t ^ 2 = algebraMap K L d → t ∉ Set.range (algebraMap K L) → (∀ φ : maximalRealSubfield K →+* ℝ, 0 < φ d) → IsCMField L ∧ t ∈ maximalRealSubfield L ∧ ∀ x : K, algebraMap K L x ∈ maximalRealSubfield L ↔ x ∈ maximalRealSubfield K := by
  intro K L _ _ _ _ _ _ hKL d t ht2 htK hpos
  have : Module.Finite K L := Module.finite_of_finrank_pos (by omega)
  have : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L

  have htR : t ∈ maximalRealSubfield L := by
    rw [mem_maximalRealSubfield_iff]
    intro φ
    let ρ : maximalRealSubfield K →+* ℂ :=
      (φ.comp (algebraMap K L)).comp (maximalRealSubfield K).subtype
    have hρ : ComplexEmbedding.IsReal ρ := IsTotallyReal.complexEmbedding_isReal ρ
    have hr : (0 : ℝ) < hρ.embedding d := hpos _
    have hsq : φ t * φ t = ((hρ.embedding d : ℝ) : ℂ) := by
      rw [ComplexEmbedding.IsReal.coe_embedding_apply, ← map_mul, ← pow_two, ht2]
      rfl
    have him : (φ t).im = 0 := by
      have h1 := congrArg Complex.re hsq
      have h2 := congrArg Complex.im hsq
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at h1 h2
      by_contra hne
      have hre : (φ t).re = 0 := by
        have h3 : (φ t).re * (φ t).im = 0 := by linarith
        rcases mul_eq_zero.mp h3 with h | h
        · exact h
        · exact absurd h hne
      rw [hre] at h1
      nlinarith [sq_nonneg (φ t).im]
    exact Complex.conj_eq_iff_im.mpr him

  have : IsScalarTower (maximalRealSubfield K) K L := inferInstance
  have hKp : Module.finrank (maximalRealSubfield K) K = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have h4 : Module.finrank (maximalRealSubfield K) L = 4 := by
    rw [← Module.finrank_mul_finrank (maximalRealSubfield K) K L, hKp, hKL]
  have : Module.Finite (maximalRealSubfield K) L := Module.finite_of_finrank_pos (by omega)
  have hint : IsIntegral (maximalRealSubfield K) t := IsIntegral.of_finite _ t

  have hmin : (minpoly (maximalRealSubfield K) t).natDegree = 2 := by
    have hle : (minpoly (maximalRealSubfield K) t).degree ≤ ((2 : ℕ) : WithBot ℕ) := by
      have h := minpoly.degree_le_of_ne_zero (maximalRealSubfield K) t
        (Polynomial.X_pow_sub_C_ne_zero (n := 2) (by norm_num) d)
        (by rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, ht2]; exact sub_self _)
      rwa [Polynomial.degree_X_pow_sub_C (by norm_num)] at h
    have hne1 : (minpoly (maximalRealSubfield K) t).natDegree ≠ 1 := by
      rw [Ne, minpoly.natDegree_eq_one_iff]
      rintro ⟨y, hy⟩
      exact htK ⟨(y : K), hy⟩
    have hpos' := minpoly.natDegree_pos hint
    have h2 := Polynomial.natDegree_le_of_degree_le hle
    omega
  have hbase : ∀ y : maximalRealSubfield K,
      algebraMap (maximalRealSubfield K) L y ∈ maximalRealSubfield L :=
    fun y => (algebraMap_mem_maximalRealSubfield_iff (L := L) (y : K)).mpr y.2

  have hFdeg : Module.finrank (maximalRealSubfield K)
      (IntermediateField.adjoin (maximalRealSubfield K) ({t} : Set L)) = 2 := by
    rw [IntermediateField.adjoin.finrank hint, hmin]
  have hFle' : IntermediateField.adjoin (maximalRealSubfield K) ({t} : Set L) ≤
      (maximalRealSubfield L).toIntermediateField hbase :=
    IntermediateField.adjoin_simple_le_iff.mpr htR
  have hFle : ∀ y ∈ IntermediateField.adjoin (maximalRealSubfield K) ({t} : Set L),
      y ∈ maximalRealSubfield L := fun y hy => hFle' hy
  generalize IntermediateField.adjoin (maximalRealSubfield K) ({t} : Set L) = F at hFdeg hFle
  have hFL : Module.finrank F L = 2 := by
    have h := Module.finrank_mul_finrank (maximalRealSubfield K) F L
    rw [hFdeg, h4] at h
    omega
  have : Module.Finite F L := Module.finite_of_finrank_pos (by omega)
  let ι : F →+* maximalRealSubfield L :=
    { toFun := fun y => ⟨y.1, hFle y.1 y.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let : Algebra F (maximalRealSubfield L) := ι.toAlgebra
  have : IsScalarTower F (maximalRealSubfield L) L := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.IsAlgebraic F L := Algebra.IsAlgebraic.of_finite F L
  have : Algebra.IsAlgebraic F (maximalRealSubfield L) :=
    Algebra.IsAlgebraic.tower_bot F (maximalRealSubfield L) L
  have : IsTotallyReal F := IsTotallyReal.of_algebra F (maximalRealSubfield L)
  have : Algebra.IsQuadraticExtension F L := ⟨hFL⟩
  have : IsTotallyComplex L := ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.mp fun h =>
    InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex _)
      (InfinitePlace.IsReal.comap (algebraMap K L) h)⟩
  exact ⟨IsCMField.ofCMExtension F L, htR, fun x => algebraMap_mem_maximalRealSubfield_iff x⟩

end GlobalTheory
end

section

open NumberField IsDedekindDomain GlobalTheory.UnitaryBC
open scoped ComplexConjugate

namespace GlobalTheory.CMGen

theorem exists_integer_not_mem (K : Type) [Field K] [NumberField K] [IsCMField K] :
    ∃ x : 𝓞 K, (x : K) ∉ maximalRealSubfield K := by
  by_contra h
  push_neg at h
  apply NumberField.IsCMField.complexConj_ne_one K
  ext y
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) y
  have ha : NumberField.IsCMField.complexConj K (algebraMap (𝓞 K) K a) = algebraMap (𝓞 K) K a :=
    (NumberField.IsCMField.complexConj_eq_self_iff K _).mpr (h a)
  have hb : NumberField.IsCMField.complexConj K (algebraMap (𝓞 K) K b) = algebraMap (𝓞 K) K b :=
    (NumberField.IsCMField.complexConj_eq_self_iff K _).mpr (h b)
  rw [map_div₀, ha, hb, AlgEquiv.one_apply]

theorem exists_extension (K : Type) [Field K] [NumberField K] (φ : maximalRealSubfield K →+* ℝ) :
    ∃ ψ : K →+* ℂ, ∀ x : maximalRealSubfield K,
      ψ (algebraMap (maximalRealSubfield K) K x) = (φ x : ℂ) := by
  letI : Algebra (maximalRealSubfield K) ℂ := (Complex.ofRealHom.comp φ).toAlgebra
  haveI : Algebra.IsAlgebraic (maximalRealSubfield K) K := Algebra.IsAlgebraic.tower_top (K := ℚ) _
  let f : K →ₐ[maximalRealSubfield K] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨f.toRingHom, fun x => f.commutes x⟩

theorem exists_sqrt_totallyNegative : ∀ (K : Type) [Field K] [NumberField K] [IsCMField K],
    ∃ (d : 𝓞 (maximalRealSubfield K)) (δ : K), δ ^ 2 = algebraMap (maximalRealSubfield K) K d ∧
      δ ∉ maximalRealSubfield K ∧
      ∀ φ : maximalRealSubfield K →+* ℝ, φ (d : maximalRealSubfield K) < 0 := by
  intro K _ _ _
  obtain ⟨x, hx⟩ := exists_integer_not_mem K
  let y : 𝓞 K := x - NumberField.IsCMField.ringOfIntegersComplexConj K x
  have hy : (y : K) = (x : K) - NumberField.IsCMField.complexConj K (x : K) := by
    simp [y, NumberField.IsCMField.coe_ringOfIntegersComplexConj]
  have hconj : NumberField.IsCMField.complexConj K (y : K) = -(y : K) := by
    rw [hy, map_sub, NumberField.IsCMField.complexConj_apply_apply, neg_sub]
  have hy0 : (y : K) ≠ 0 := by
    intro h0
    apply hx
    rw [← NumberField.IsCMField.complexConj_eq_self_iff]
    rw [hy, sub_eq_zero] at h0
    exact h0.symm
  have hsq : (y : K) ^ 2 ∈ maximalRealSubfield K := by
    rw [← NumberField.IsCMField.complexConj_eq_self_iff, map_pow, hconj, neg_sq]
  have hint : IsIntegral ℤ (⟨(y : K) ^ 2, hsq⟩ : maximalRealSubfield K) := by
    refine (isIntegral_algebraMap_iff (B := K)).mp ?_
    change IsIntegral ℤ ((y : K) ^ 2)
    exact (RingOfIntegers.isIntegral_coe y).pow 2
  refine ⟨⟨⟨(y : K) ^ 2, hsq⟩, hint⟩, (y : K), rfl, ?_, ?_⟩
  · intro hmem
    apply hy0
    have h2 := hconj
    rw [(NumberField.IsCMField.complexConj_eq_self_iff K _).mpr hmem] at h2
    have h3 : (2 : K) * (y : K) = 0 := by rw [two_mul]; nth_rewrite 1 [h2]; ring
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h two_ne_zero
    · exact h
  · intro φ
    obtain ⟨ψ, hψ⟩ := exists_extension K φ
    have hval := hψ ⟨(y : K) ^ 2, hsq⟩
    have hψy : ψ (y : K) = ψ (x : K) - conj (ψ (x : K)) := by
      rw [hy, map_sub, NumberField.IsCMField.complexEmbedding_complexConj]
    have hne : ψ (y : K) ≠ 0 := by
      rw [map_ne_zero]; exact hy0
    have him : (ψ (x : K)).im ≠ 0 := by
      intro h0
      apply hne
      rw [hψy, Complex.sub_conj, h0]
      simp
    have key : ((φ ⟨(y : K) ^ 2, hsq⟩ : ℝ) : ℂ) = ((-(2 * (ψ (x : K)).im) ^ 2 : ℝ) : ℂ) := by
      rw [← hval]
      change ψ ((y : K) ^ 2) = _
      rw [map_pow, hψy, Complex.sub_conj]
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    have key' : φ ⟨(y : K) ^ 2, hsq⟩ = -(2 * (ψ (x : K)).im) ^ 2 := by exact_mod_cast key
    show φ ⟨(y : K) ^ 2, hsq⟩ < 0
    rw [key']
    have : 0 < (2 * (ψ (x : K)).im) ^ 2 := by positivity
    linarith

end GlobalTheory.CMGen
end
