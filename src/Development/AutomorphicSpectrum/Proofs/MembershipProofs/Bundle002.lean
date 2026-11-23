module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Matrix ValuativeRel GlobalTheory.WeilM MeasureTheory
open scoped ComplexConjugate NNReal

namespace GlobalTheory.CompanionTheory.LagFun

theorem exists_param {k : Type} [Field k] {κ : Type} [Fintype κ] (large₂ : Submodule k ((κ → k) × (κ → k))) :
    ∃ (n : ℕ) (j σ : (Fin n → k) →ₗ[k] (κ → k)) (p : (κ → k) →ₗ[k] (Fin n → k)),
      (∀ t, p (j t) = t) ∧ (∀ t, (j t, σ t) ∈ large₂) ∧ ∀ w ∈ large₂, ∃ t, j t = w.1 := by
  set f : large₂ →ₗ[k] (κ → k) := LinearMap.fst k _ _ ∘ₗ large₂.subtype with hf
  obtain ⟨s, hs⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  set e := (Module.finBasis k (LinearMap.range f)).equivFun.symm
  set j := (LinearMap.range f).subtype ∘ₗ e.toLinearMap with hj
  have hinj : LinearMap.ker j = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact Subtype.val_injective.comp e.injective
  obtain ⟨p, hp⟩ := j.exists_leftInverse_of_injective hinj
  refine ⟨_, j, LinearMap.snd k _ _ ∘ₗ large₂.subtype ∘ₗ s ∘ₗ e.toLinearMap, p, fun t => LinearMap.congr_fun hp t,
    fun t => ?_, fun w hw => ⟨e.symm ⟨w.1, ⟨w, hw⟩, rfl⟩, by simp [hj]⟩⟩
  have h1 : (s (e t) : (κ → k) × (κ → k)).1 = j t := congrArg Subtype.val (LinearMap.congr_fun hs (e t))
  rw [← h1]
  exact (s (e t)).2

theorem exists_invariant_form : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)] (κ : Type) [Fintype κ] (ψ : AddChar k ℂ), Continuous ψ → ψ ≠ 1 → ∀ large₂ : Submodule k ((κ → k) × (κ → k)), (∀ w ∈ large₂, ∀ w' ∈ large₂, w.1 ⬝ᵥ w'.2 = w'.1 ⬝ᵥ w.2) → ∃ l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ, (∃ φ ∈ SB (κ → k), l φ ≠ 0) ∧ ∀ w ∈ large₂, ∀ φ ∈ SB (κ → k), l (schr ψ w φ) = l φ := by
  intro k _ _ _ _ _ κ _ ψ hψ _ large₂ hL
  obtain ⟨n, j, σ, p, hp, hσ, hj⟩ := exists_param large₂
  have hT2 : T2Space k := by
    let := IsTopologicalAddGroup.rightUniformSpace k
    have := isUniformAddGroup_of_addCommGroup (G := k)
    infer_instance
  have hlc : LocallyCompactSpace k := inferInstance
  have htd : TotallyDisconnectedSpace k := by
    let := IsTopologicalAddGroup.rightUniformSpace k
    have := isUniformAddGroup_of_addCommGroup (G := k)
    have : NonarchimedeanAddGroup k := ⟨fun U hU => by
      obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hU
      exact ⟨⟨(Valued.v (R := k)).restrict.ltAddSubgroup γ, by
        simpa [Valuation.ltAddSubgroup] using Valued.isOpen_ball k γ⟩, hγ⟩⟩
    infer_instance
  let : MeasurableSpace (Fin n → k) := borel _
  have : BorelSpace (Fin n → k) := ⟨rfl⟩
  set μ : Measure (Fin n → k) := Measure.addHaar
  have cj : Continuous j := j.continuous_on_pi
  have cσ : Continuous σ := σ.continuous_on_pi
  have cp : Continuous p := p.continuous_on_pi
  have hce : Topology.IsClosedEmbedding j := Function.LeftInverse.isClosedEmbedding hp cp cj
  set g : (Fin n → k) → ℂ := fun t => ψ (⅟(2 : k) * (j t ⬝ᵥ σ t)) with hg
  have cg : Continuous g := hψ.comp (continuous_const.mul (cj.dotProduct cσ))
  set S : Submodule ℂ ((κ → k) → ℂ) :=
    { carrier := {φ | Integrable (fun t => g t * φ (j t)) μ}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, Pi.add_apply, mul_add]
        exact Integrable.add ha hb
      smul_mem' := fun c a ha => by
        simpa only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, mul_left_comm] using Integrable.const_mul ha c }
  have memS : ∀ φ, φ ∈ S ↔ Integrable (fun t => g t * φ (j t)) μ := fun _ => Iff.rfl
  set l₀ : S →ₗ[ℂ] ℂ :=
    { toFun := fun φ => ∫ t, g t * φ.1 (j t) ∂μ
      map_add' := fun a b => by
        rw [← integral_add a.2 b.2]
        simp [mul_add]
      map_smul' := fun c a => by
        simp [← integral_const_mul, mul_left_comm] }
  obtain ⟨l, hl⟩ := l₀.exists_extend
  have hl' : ∀ φ ∈ S, l φ = ∫ t, g t * φ (j t) ∂μ := fun φ hφ => LinearMap.congr_fun hl ⟨φ, hφ⟩
  have cc : ∀ φ ∈ SB (κ → k), Continuous (fun t => g t * φ (j t)) ∧ HasCompactSupport (fun t => g t * φ (j t)) :=
    fun φ hφ => ⟨cg.mul (hφ.1.continuous.comp cj), (hφ.2.comp_isClosedEmbedding hce).mul_left⟩
  have hSB : ∀ φ ∈ SB (κ → k), φ ∈ S := fun φ hφ => (cc φ hφ).1.integrable_of_hasCompactSupport (cc φ hφ).2
  refine ⟨l, ?_, fun w hw φ hφ => ?_⟩
  · have ho : IsOpen {x : κ → k | 0 < (g (p x)).re} :=
      isOpen_lt continuous_const (Complex.continuous_re.comp (cg.comp cp))
    have h0 : (0 : κ → k) ∈ {x : κ → k | 0 < (g (p x)).re} := by simp [hg]
    obtain ⟨K, hK, hK0, hKs⟩ := exists_compact_subset ho h0
    obtain ⟨U, hU, hU0, hUs⟩ := (loc_compact_Haus_tot_disc_of_zero_dim (X := κ → k)).exists_subset_of_mem_open hK0
      isOpen_interior
    have hU : IsClopen U := hU
    have hUK : U ⊆ K := hUs.trans interior_subset
    have hφ : U.indicator (fun _ => (1 : ℂ)) ∈ SB (κ → k) :=
      ⟨(LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) hU).isLocallyConstant,
        HasCompactSupport.intro hK fun x hx => Set.indicator_of_notMem (fun h => hx (hUK h)) _⟩
    refine ⟨_, hφ, fun h => ?_⟩
    rw [hl' _ (hSB _ hφ)] at h
    have h2 := congrArg Complex.re h
    rw [← RCLike.re_to_complex, ← integral_re ((memS _).1 (hSB _ hφ))] at h2
    refine ne_of_gt ?_ h2
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0)
      (RCLike.continuous_re.comp (cc _ hφ).1) ((cc _ hφ).2.comp_left (g := RCLike.re) (map_zero _)) (fun t => ?_) ?_
    · by_cases ht : j t ∈ U
      · have := hKs (hUK ht)
        simp only [Set.mem_ofPred_eq, hp] at this
        simpa [ht] using this.le
      · simp [ht]
    · simp [hU0, hg]
  · obtain ⟨t₁, ht₁⟩ := hj w hw
    have key : (fun t => g t * schr ψ w φ (j t)) = fun t => g (t + t₁) * φ (j (t + t₁)) := by
      funext t
      have e1 := hL _ (hσ t) w hw
      have e2 := hL _ (hσ t₁) w hw
      have e3 := hL _ (hσ t) _ (hσ t₁)
      simp only [← ht₁] at e1 e2 e3
      simp only [hg, schr, ← ht₁, map_add (f := _), ← mul_assoc, ← AddChar.map_add_eq_mul, add_dotProduct, dotProduct_add]
      congr 2
      have h2 : ⅟(2 : k) * 2 = 1 := invOf_mul_self _
      linear_combination e1 + ⅟(2 : k) * e2 - ⅟(2 : k) * e3 - (j t₁ ⬝ᵥ σ t) * h2
    have hi := (memS _).1 (hSB _ hφ)
    rw [hl' _ (hSB _ hφ), hl' _ ((memS _).2 (key ▸ hi.comp_add_right t₁)), key]
    exact integral_add_right_eq_self (fun t => g t * φ (j t)) t₁

end GlobalTheory.CompanionTheory.LagFun
end

section

open Matrix ValuativeRel GlobalTheory.WeilM MeasureTheory
open scoped ComplexConjugate NNReal

namespace GlobalTheory.CompanionTheory.WeilOneMember

section Alg

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem isHerm_dbl {JB : Matrix β β E} (h : IsHerm c JB) : IsHerm c (dbl JB) := by
  obtain ⟨hs, hu⟩ := h
  refine ⟨?_, ?_⟩
  · rintro (i | i) (j | j) <;> simp [dbl, hs]
  · rw [dbl, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]
    exact hu.mul ((isUnit_neg_one.pow _).mul hu)

theorem exists_embed {JB : Matrix β β E} (g : UG c JB) : ∃ gd : UG c (dbl JB),
    ((gd : GL (β ⊕ β) E) : Matrix (β ⊕ β) (β ⊕ β) E) = Matrix.fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1 := by
  let G : GL β E := g
  let M : GL (β ⊕ β) E :=
    ⟨Matrix.fromBlocks (G : Matrix β β E) 0 0 1, Matrix.fromBlocks ((G⁻¹ : GL β E) : Matrix β β E) 0 0 1,
      by simp [Matrix.fromBlocks_multiply], by simp [Matrix.fromBlocks_multiply]⟩
  have hg : (G : Matrix β β E).transpose * JB * (G : Matrix β β E).map c = JB := g.2
  have hM : M ∈ UG c (dbl JB) := by
    show (M : Matrix (β ⊕ β) (β ⊕ β) E).transpose * dbl JB * (M : Matrix (β ⊕ β) (β ⊕ β) E).map c = dbl JB
    simp only [M, dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
      Matrix.transpose_zero, Matrix.transpose_one, Matrix.map_zero _ (map_zero c), Matrix.map_one _ (map_zero c) (map_one c)]
    simp [hg]
  exact ⟨⟨M, hM⟩, rfl⟩

end Alg

theorem boxFun_mem {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {κ κ' : Type}
    {φ₁ : (κ → R) → ℂ} {φ₂ : (κ' → R) → ℂ} (h₁ : φ₁ ∈ SB (κ → R)) (h₂ : φ₂ ∈ SB (κ' → R)) :
    boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → R) := by
  have h₁' : IsLocallyConstant φ₁ ∧ HasCompactSupport φ₁ := h₁
  have h₂' : IsLocallyConstant φ₂ ∧ HasCompactSupport φ₂ := h₂
  have cl : Continuous fun x : κ ⊕ κ' → R => x ∘ Sum.inl := continuous_pi fun i => continuous_apply _
  have cr : Continuous fun x : κ ⊕ κ' → R => x ∘ Sum.inr := continuous_pi fun i => continuous_apply _
  show IsLocallyConstant (boxFun φ₁ φ₂) ∧ HasCompactSupport (boxFun φ₁ φ₂)
  refine ⟨?_, ?_⟩
  · exact IsLocallyConstant.comp₂ (h₁'.1.comp_continuous cl) (h₂'.1.comp_continuous cr) (· * ·)
  · let S : Set (κ ⊕ κ' → R) :=
      (fun x => x ∘ Sum.inl) ⁻¹' tsupport φ₁ ∩ (fun x => x ∘ Sum.inr) ⁻¹' tsupport φ₂
    let gm : (κ → R) × (κ' → R) → (κ ⊕ κ' → R) := fun p => Sum.elim p.1 p.2
    have hgm : Continuous gm := by
      refine continuous_pi fun i => ?_
      cases i with
      | inl i => exact (continuous_apply i).comp continuous_fst
      | inr i => exact (continuous_apply i).comp continuous_snd
    have hK : IsCompact (gm '' (tsupport φ₁ ×ˢ tsupport φ₂)) := (h₁'.2.prod h₂'.2).image hgm
    have hSc : IsClosed S := (isClosed_tsupport φ₁).preimage cl |>.inter ((isClosed_tsupport φ₂).preimage cr)
    have hsub : tsupport (boxFun φ₁ φ₂) ⊆ S := by
      refine closure_minimal ?_ hSc
      intro x hx
      have hx' : φ₁ (x ∘ Sum.inl) * φ₂ (x ∘ Sum.inr) ≠ 0 := hx
      exact ⟨subset_tsupport _ (left_ne_zero_of_mul hx'), subset_tsupport _ (right_ne_zero_of_mul hx')⟩
    have hSK : S ⊆ gm '' (tsupport φ₁ ×ˢ tsupport φ₂) := by
      intro x hx
      exact ⟨(x ∘ Sum.inl, x ∘ Sum.inr), hx, Sum.elim_comp_inl_inr x⟩
    exact hK.of_isClosed_subset (isClosed_tsupport _) (hsub.trans hSK)

end GlobalTheory.CompanionTheory.WeilOneMember
end

section

open Matrix NumberField IsDedekindDomain GlobalTheory.WeilM
open scoped ComplexConjugate

namespace GlobalTheory.CompanionTheory.ThetaReal

theorem thetaSum_star_and_schA_star (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) :
    thetaSum F (star Φ) = conj (thetaSum F Φ) ∧ (Φ ∈ schA F κ → star Φ ∈ schA F κ) := by
  refine ⟨?_, fun h => ?_⟩
  · unfold thetaSum
    rw [← RCLike.star_def, tsum_star]
    rfl
  · classical
    induction h using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, g, hg, rfl⟩ := hx
      refine Submodule.subset_span ⟨SchwartzMap.postcompCLM (𝕜 := ℝ) (Complex.conjCLE : ℂ →L[ℝ] ℂ) f, star g,
        ⟨hg.1.comp star, hg.2.comp_left (g := star) (star_zero ℂ)⟩, ?_⟩
      funext x
      simp [pureA]
    | zero => rw [star_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [star_add]; exact add_mem hx hy
    | smul a x _ hx => rw [star_smul]; exact Submodule.smul_mem _ _ hx

end GlobalTheory.CompanionTheory.ThetaReal
end
