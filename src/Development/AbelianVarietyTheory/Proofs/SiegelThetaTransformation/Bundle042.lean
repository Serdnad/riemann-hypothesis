module

import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsEvenRepsTensorLatticeAndSum
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle036
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetOfTriangular
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemIffConjugateNotMem
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle038
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsClassicalLevelDataCoverSelfDual
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsMemRowHighestTotalDegreeEqTwo
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle066
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaCharacteristicsIffTestFunctionThetaSeries
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle039
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle005
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle008
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.GenLatCmp

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem mem_range_iff (x : E) : x ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ x :=
  ⟨fun ⟨a, ha⟩ => ha ▸ a.isIntegral_coe, fun h => ⟨⟨x, h⟩, rfl⟩⟩

theorem mem_std (v : Fin n → E) : v ∈ Formalism.L2.Pj.stdLat E n ↔ ∀ i, IsIntegral ℤ (v i) := by
  simp only [Formalism.L2.Pj.stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
  exact forall_congr' fun i => mem_range_iff (v i)

theorem std_eq : Formalism.L2.Pj.stdLat E n = stdL E n := by
  apply GlobalTheory.Dict.ZLat.stdLat_eq <;> assumption

theorem span_smul_le (k : ℕ) (A B : Lt E n) :
    Ideal.span {(k : 𝓞 E)} • A ≤ B ↔ ∀ v ∈ A, (k : E) • v ∈ B := by
  have e : ∀ v : Fin n → E, (k : 𝓞 E) • v = (k : E) • v := fun v => by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rw [Submodule.ideal_span_singleton_smul]
  constructor
  · intro h v hv
    rw [← e]
    exact h (Submodule.smul_mem_pointwise_smul v _ A hv)
  · intro h x hx
    obtain ⟨v, hv, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    rw [e]; exact h v hv

theorem natCast_smul_mem (k : ℕ) {A : Lt E n} {v : Fin n → E} (hv : v ∈ A) : (k : E) • v ∈ A := by
  rw [Nat.cast_smul_eq_nsmul]; exact A.toAddSubgroup.nsmul_mem hv k

theorem fg_of_smul_le {Λ : Lt E n} {s : ℕ} (hs : 0 < s) (h : ∀ v ∈ Λ, (s : E) • v ∈ stdL E n) :
    Λ.FG := by
  have h0 : (stdL E n).FG := Submodule.fg_span (Set.finite_range _)
  have h1 := h0.map ((LinearMap.lsmul E (Fin n → E) (s : E)⁻¹).restrictScalars (𝓞 E))
  refine h1.of_le fun v hv => ⟨(s : E) • v, h v hv, ?_⟩
  have : (s : E) ≠ 0 := by exact_mod_cast hs.ne'
  simp [smul_smul, this]

variable [IsCMField E]

theorem herm_one_eq (x y : Fin n → E) :
    herm 1 x y = cc (∑ j, IsCMField.complexConj E (x j) * y j) := by
  simp [herm, cc, Matrix.one_apply]

theorem unimod_iff (Λ : Lt E n) : (⟨Λ⟩ : GenLat E n).Unimod ↔
    ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y) := by
  refine forall_congr' fun x => iff_congr Iff.rfl (forall₂_congr fun y _ => ?_)
  rw [mem_range_iff, herm_one_eq]
  refine ⟨Base.isIntegral_cc, fun h => ?_⟩
  simpa [cc] using Base.isIntegral_cc h

theorem smul_mem_std {Λ : Lt E n} (hU : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) {s : ℕ}
    (h : ∀ v ∈ stdL E n, (s : E) • v ∈ Λ) : ∀ v ∈ Λ, (s : E) • v ∈ stdL E n := by
  intro v hv
  rw [← std_eq, mem_std]
  intro i
  have := (hU v).1 hv _ (h (Pi.single i 1) (Submodule.subset_span ⟨i, rfl⟩))
  convert this using 1
  simp [herm, cc, Matrix.one_apply, Pi.single_apply, mul_comm, apply_ite (IsCMField.complexConj E)]

theorem genLat_vset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (Λ : Lt E n), (∀ bad M : ℕ, 0 < bad → Odd M → Λ ∈ Vset E n (2 * bad * M) → (⟨Λ⟩ : GenLat E n).Unimod ∧ (⟨Λ⟩ : GenLat E n).TrivAt bad ∧ (⟨Λ⟩ : GenLat E n).TrivAt M ∧ ∃ N, NOK Λ N M) ∧ (∀ M N : ℕ, 0 < M → (⟨Λ⟩ : GenLat E n).Unimod → (⟨Λ⟩ : GenLat E n).TrivAt M → NOK Λ N M → Λ ∈ Vset E n M) ∧ (∀ M M' : ℕ, M ∣ M' → Λ ∈ Vset E n M' → Λ ∈ Vset E n M) ∧ stdLat E n = stdL E n := by
  intro E _ _ _ n Λ
  refine ⟨?_, ?_, ?_, std_eq⟩
  · rintro bad M - hM ⟨-, hU, s, -, hs, h1, h2⟩
    have t : ∀ m, s.Coprime m → (⟨Λ⟩ : GenLat E n).TrivAt m := fun m hm =>
      ⟨s, hm, by rw [std_eq, span_smul_le]; exact h1, by rw [std_eq, span_smul_le]; exact h2⟩
    refine ⟨(unimod_iff Λ).2 hU, t _ hs.coprime_mul_right_right.coprime_mul_left_right,
      t _ hs.coprime_mul_left_right, s * M, ?_, Dvd.intro_left _ rfl, ?_⟩
    · exact (Nat.coprime_two_right.1 hs.coprime_mul_right_right.coprime_mul_right_right).mul hM
    · rw [span_smul_le]
      intro v hv
      refine ⟨?_, natCast_smul_mem _ hv⟩
      rw [std_eq] at hv
      rw [mul_comm, Nat.cast_mul, mul_smul]
      exact natCast_smul_mem M (h2 v hv)
  · rintro M N - hU ⟨k, hk, h1, h2⟩ ⟨hN, -, h3⟩
    rw [unimod_iff] at hU
    rw [std_eq, span_smul_le] at h1 h2 h3
    have h4 : ∀ v ∈ stdL E n, (N : E) • v ∈ Λ := fun v hv => (h3 v hv).1
    have h5 := smul_mem_std hU h4
    refine ⟨fg_of_smul_le hN.pos h5, hU, ?_⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [Nat.coprime_zero_left] at hk
      exact ⟨N, hN.pos, hk ▸ Nat.coprime_one_right N, h5, h4⟩
    · exact ⟨k, hk0, hk, h1, h2⟩
  · rintro M M' hM ⟨a, b, s, hs, hc, h⟩
    exact ⟨a, b, s, hs, hc.coprime_dvd_right hM, h⟩

end GlobalTheory.Dict.GenLatCmp
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.Ker

theorem dense_of_span_real {g : ℕ} (S : Submodule ℚ (Fin g → ℂ))
    (hS : Submodule.span ℝ (S : Set (Fin g → ℂ)) = ⊤) : Dense (S : Set (Fin g → ℂ)) := by
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro z
  have hz : z ∈ Submodule.span ℝ (S : Set (Fin g → ℂ)) := hS ▸ Submodule.mem_top
  induction hz using Submodule.span_induction with
  | mem w hw => exact subset_closure hw
  | zero => exact subset_closure S.zero_mem
  | add a b _ _ ha hb => exact map_mem_closure₂ continuous_add ha hb fun c hc d hd => S.add_mem hc hd
  | smul t w _ hw =>

    have hq : ∀ q : ℚ, (q : ℝ) • w ∈ closure (S : Set (Fin g → ℂ)) := fun q =>
      map_mem_closure (continuous_const_smul (q : ℝ)) hw fun u hu => by
        rw [SetLike.mem_coe, Rat.cast_smul_eq_qsmul ℝ q u]
        exact S.smul_mem q hu
    have hcl : IsClosed {s : ℝ | s • w ∈ closure (S : Set (Fin g → ℂ))} :=
      isClosed_closure.preimage (continuous_id.smul continuous_const)
    have hsub : closure (Set.range fun q : ℚ => (q : ℝ)) ⊆ {s : ℝ | s • w ∈ closure (S : Set (Fin g → ℂ))} :=
      hcl.closure_subset_iff.2 (by rintro _ ⟨q, rfl⟩; exact hq q)
    exact hsub ((Rat.denseRange_cast (𝕜 := ℝ)).closure_range ▸ Set.mem_univ t)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (X : Data E r)
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r) {n : ℕ}

noncomputable def zRLin (x : Frame X.Ψ r) : WR X n →ₗ[ℝ] (Fin n → Fin g → ℂ) where
  toFun := zR X idx x
  map_add' u v := by
    funext k i
    simp only [zR, Pi.add_apply]
    split_ifs
    · simp [hermC, mul_add, Finset.sum_add_distrib]
    · rw [mulVec_add, Pi.add_apply]
  map_smul' t v := by
    funext k i
    simp only [zR, Pi.smul_apply, RingHom.id_apply]
    split_ifs
    · simp only [hermC, Pi.smul_apply, real_smul, map_mul, conj_ofReal, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    · rw [mulVec_smul, Pi.smul_apply]

theorem denseRange_pv (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    DenseRange (pv X idx x) := by

  have hrange : ((LinearMap.range ((LinearMap.funLeft ℚ ℂ idx).comp (perLin X x)) :
      Submodule ℚ (Fin g → ℂ)) : Set (Fin g → ℂ)) = Set.range (pv X idx x) := by
    ext z
    simp only [SetLike.mem_coe, LinearMap.mem_range, Set.mem_range]
    exact Iff.rfl
  unfold DenseRange
  rw [← hrange]
  apply dense_of_span_real
  rw [hrange]
  exact GlobalTheory.Dict.span_range_pv idx hs hx

theorem denseRange_zR_embR (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    DenseRange (zR X idx x ∘ embR X (n := n)) := by
  have h : zR X idx x ∘ embR X (n := n) = fun y k => pv X idx x (y k) := by
    funext y k
    exact zR_embR X idx x y k
  rw [h]
  exact DenseRange.piMap fun _ => denseRange_pv X idx hs hx

theorem exists_equiv_zR (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    ∃ L : WR X n ≃L[ℝ] (Fin n → Fin g → ℂ), ∀ v, L v = zR X idx x v := by

  have hsurj : Function.Surjective (zRLin X idx x (n := n)) := by
    have hcl : IsClosed (LinearMap.range (zRLin X idx x (n := n)) : Set (Fin n → Fin g → ℂ)) :=
      Submodule.closed_of_finiteDimensional _
    have hd : Dense (LinearMap.range (zRLin X idx x (n := n)) : Set (Fin n → Fin g → ℂ)) := by
      refine (denseRange_zR_embR X idx hs hx (n := n)).mono ?_
      rintro _ ⟨y, rfl⟩
      exact ⟨embR X y, rfl⟩
    have huniv := hcl.closure_eq.symm.trans hd.closure_eq
    intro z
    have hz : z ∈ (LinearMap.range (zRLin X idx x (n := n)) : Set (Fin n → Fin g → ℂ)) := by
      rw [huniv]
      trivial
    exact LinearMap.mem_range.1 hz

  have hg : g = Fintype.card X.Ψ * r := by
    simpa [Fintype.card_prod] using Fintype.card_congr idx
  have hdim : Module.finrank ℝ (WR X n) = Module.finrank ℝ (Fin n → Fin g → ℂ) := by
    simp only [WR, Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, hg]
    ring
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj
  exact ⟨(LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩).toContinuousLinearEquiv, fun v => rfl⟩

theorem EFR_embR (y y' : Matrix (Fin n) (Fin r) E) :
    EFR X (embR X y) (embR X y') = ((∑ k, EF X (y k) (y' k) : ℚ) : ℝ) := by
  have key : ∀ (τ : X.Ψ) (k : Fin n),
      hermC τ.1 X.Gm (embR X y τ k) (embR X y' τ k) = τ.1 (herm X.Gm (y k) (y' k)) :=
    fun τ k => ReciprocityTheory.ChartRestriction.G.FD.hermC_emb τ.1 X.Gm (y k) (y' k)
  rw [EFR, Rat.cast_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [EF_def, GlobalTheory.UnitFrame.trace_eq_sum_re X.Ψ X.cmType]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [key, map_mul]

theorem zR_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x ∈ X.dom, (∃ L : WR X n ≃L[ℝ] (Fin n → Fin g → ℂ), ∀ v, L v = zR X idx x v) ∧ (∀ v v' : WR X n, (∑ k, hx X bas idx x (zR X idx x v k) (zR X idx x v' k)).im = EFR X v v') ∧ (∀ y y' : Matrix (Fin n) (Fin r) E, EFR X (embR X y) (embR X y') = ((∑ k, EF X (y k) (y' k) : ℚ) : ℝ)) ∧ DenseRange (embR X (n := n)) ∧ ∀ γ : GL (Fin r) E, IsUn X γ → ∀ v : WR X n, zR X idx (lact γ x) (fun τ k => ((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ v τ k) = zR X idx x v := by
  intro E _ _ _ r X g q0 _ bas idx n hs hn x hxd
  obtain ⟨L, hL⟩ := exists_equiv_zR X idx (n := n) hs hxd
  have hlaws := GlobalTheory.Dict.hx_laws E r X g bas idx n hs hn x hxd

  have hD : DenseRange (embR X (n := n)) := by
    have h1 : embR X (n := n) = L.symm ∘ (zR X idx x ∘ embR X) := by
      funext y
      simp only [Function.comp_apply, ← hL, ContinuousLinearEquiv.symm_apply_apply]
    rw [h1]
    exact L.symm.surjective.denseRange.comp (denseRange_zR_embR X idx hs hxd) L.symm.continuous

  have hB : ∀ v v' : WR X n,
      (∑ k, hx X bas idx x (zR X idx x v k) (zR X idx x v' k)).im = EFR X v v' := by
    have hc1 : Continuous fun p : WR X n × WR X n =>
        (∑ k, hx X bas idx x (zR X idx x p.1 k) (zR X idx x p.2 k)).im := by
      simp only [← hL, GlobalTheory.Dict.hx]
      fun_prop
    have hc2 : Continuous fun p : WR X n × WR X n => EFR X p.1 p.2 := by
      simp only [EFR, hermC]
      fun_prop
    have heq := (hD.prodMap hD).equalizer hc1 hc2 (by
      funext ⟨y, y'⟩
      simp only [Function.comp_apply, Prod.map_apply]
      rw [EFR_embR X y y', Complex.im_sum, Rat.cast_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [zR_embR, zR_embR]
      exact hlaws.2.2.1 (y k) (y' k))
    exact fun v v' => congrFun heq (v, v')

  have hF : ∀ γ : GL (Fin r) E, IsUn X γ → ∀ v : WR X n,
      zR X idx (lact γ x) (fun τ k => ((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ v τ k) =
        zR X idx x v := by
    intro γ hγ
    have hA : Continuous fun v : WR X n =>
        (fun τ k => ((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ v τ k : WR X n) := by
      fun_prop
    have hc1 : Continuous fun v : WR X n =>
        zR X idx (lact γ x) (fun τ k => ((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ v τ k) :=
      (LinearMap.continuous_of_finiteDimensional (zRLin X idx (lact γ x) (n := n))).comp hA
    have hc2 : Continuous fun v : WR X n => zR X idx x v := by
      simp only [← hL]
      exact L.continuous
    have heq := hD.equalizer hc1 hc2 (by
      funext y
      simp only [Function.comp_apply]
      have hemb : (fun τ k => ((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ embR X y τ k : WR X n) =
          embR X (Matrix.of fun k => (γ : Matrix (Fin r) (Fin r) E) *ᵥ y k) := by
        funext τ k
        exact (GlobalTheory.PerMove.emb_mulVec τ.1 _ (y k)).symm
      rw [hemb]
      funext k
      rw [zR_embR, zR_embR]
      exact (hlaws.2.2.2.2.2.2.2 γ hγ).2.1 (y k))
    exact fun v => congrFun heq v
  exact ⟨⟨L, hL⟩, hB, fun y y' => EFR_embR X y y', hD, hF⟩

end GlobalTheory.Ker
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

theorem _root_.GlobalTheory.T.vacuum_tensorLattice_fixed_rational_heisenberg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L : Lt E r, SelfD X L → ∀ Λ ∈ Vset E n 1, ∀ v : TF n g, IsVac X bas w (tens Λ L) v → ∃ A ε, VacS A ε v := by
  first | exact @GlobalTheory.Phase.vacS_of_isVac | exact GlobalTheory.Phase.vacS_of_isVac | (intros; apply GlobalTheory.Phase.vacS_of_isVac <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem _root_.GlobalTheory.T.exists_classicalLevelData_coverSelfDual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) (r : ℕ) (X : Data E r) (hn : r ≤ n), r = Dw.p + Dw.q → SelfD X X.Λ → d.IsLev → ¬ 3 ∣ d.pd → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (x₀ : Fin n → LaJ Xo c d), d.PhiPin ph ψ x₀ → ∃ D : SW.Level X, LevTie d σ ph D hn := by
  first | exact @GlobalTheory.LevelTied.exists_levTie | exact GlobalTheory.LevelTied.exists_levTie | (intros; apply GlobalTheory.LevelTied.exists_levTie <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.CuspClass

private theorem hermC_mulVec_mulVec_eq_sum_gram {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (P : Matrix (Fin r) (Fin r) ℂ) (w : Fin r → ℂ) :
    FD.hermC τ G (P *ᵥ w) (P *ᵥ w) = ∑ a, ∑ b, w a * FD.gram τ G P a b * conj (w b) := by

  simp only [FD.hermC, FD.gram, FD.col, Matrix.of_apply, Matrix.mulVec, dotProduct, map_sum, map_mul,
  Finset.sum_mul, Finset.mul_sum]
  conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem not_isIso_of_definite {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (h0 : X.p0 = r) (ξ : Fin r → E) : ¬ X.IsIso ξ := by
  rintro ⟨-, hξ0, hne⟩
  have τ0 : E →+* ℂ := Classical.choice inferInstance
  obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ X.Ψ := by
    by_cases h : τ0 ∈ X.Ψ
    · exact ⟨τ0, h⟩
    · exact ⟨_, not_not.mp (mt (X.cmType τ0).mpr h)⟩
  obtain ⟨P, hPdet, hP⟩ := X.signature ⟨τ, hτ⟩
  have hherm : FD.hermC τ X.Gm (fun a => τ (ξ a)) (fun a => τ (ξ a)) = 0 := by
    have h1 := congrArg τ hξ0
    rw [map_zero] at h1
    rw [← h1]

    simp [FD.herm, FD.hermC, FD.cc, map_sum, map_mul, NumberField.IsCMField.complexEmbedding_complexConj]
  obtain ⟨w, hw⟩ : ∃ w, P *ᵥ w = fun a => τ (ξ a) :=
    ⟨P⁻¹ *ᵥ (fun a => τ (ξ a)), by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv P (isUnit_iff_ne_zero.mpr hPdet), Matrix.one_mulVec]⟩
  have hsum : ∑ a, ((Complex.normSq (w a) : ℝ) : ℂ) = 0 := by
    rw [← hherm, ← hw, hermC_mulVec_mulVec_eq_sum_gram, hP]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a]
    · simp [Matrix.diagonal_apply_eq, FD.sgn, h0, Complex.mul_conj]
    · intro b _ hb
      simp [Matrix.diagonal_apply_ne _ (Ne.symm hb)]
    · simp
  have hsum' : ∑ a, Complex.normSq (w a) = 0 := by exact_mod_cast hsum
  have hw0 : w = 0 := by
    funext a
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Complex.normSq_nonneg (w a))).mp hsum' a
      (Finset.mem_univ a)
    simpa using this
  apply hne
  funext a
  have := congrFun hw a
  rw [hw0, Matrix.mulVec_zero] at this
  exact (map_eq_zero τ).mp this.symm

theorem mem_SS_of_eq_thP : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (k : X.Ψ → Fin q0 → ℕ) (k' : X.Ψ → Fin X.p0 → ℕ), ((∃ τ, ∃ i : Fin q0, i.val + 1 = q0 ∧ 1 ≤ k τ i) ∨ q0 = 0) → r ≤ n → ∀ φ : TF n g, IsSB φ → ∀ P ∈ Harm.rowHighest ℂ k k', ∀ Q : Frame X.Ψ r → ℂ, (∀ x ∈ X.dom, Q x = thP X hr bas idx φ P x) → (∀ ga ∈ X.Γ, ∀ x ∈ X.dom, Q (lact ga x) = X.χ (wtOf X hr k k' n) ga * Q x) → Q ∈ X.SS (wtOf X hr k k' n) := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn k k' hk hrn φ hφ P hP Q hQ hΓ
  obtain ⟨-, hlink⟩ := GlobalTheory.SW.CharLink.harmonicTheta_eq_sum_thetaCharacteristic E r X g q0 hr bas idx n hs hn
  obtain ⟨m, a, b, t, hab⟩ := hlink φ hφ
  refine GlobalTheory.ThFr.mem_SS_of_eq_sum_thFr (idx := idx) (hr := hr) (s := Finset.univ) (t := t)
    (a := fun j k i => (a j k i : ℝ)) (b := fun j k i => (b j k i : ℝ)) (P := fun _ => P) hs hn ?_
    (fun _ _ => hP) ?_ hΓ
  · rcases hk with ⟨τ, i, hi, hki⟩ | hq
    · exact Or.inl ⟨by omega, τ, Or.inl ⟨i, hi, hki⟩⟩
    · exact Or.inr (not_isIso_of_definite X (by omega))
  · intro x hx
    exact (hQ x hx).trans (hab P x hx)

end GlobalTheory.Dict.CuspClass
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.weil_action_preserves_theta_and_inner_product : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ γ : GL (Fin r) E, IsUn X γ → ∀ φ : TF n g, IsSB φ → IsSB (wG X bas idx γ φ) ∧ (∀ x ∈ X.dom, thA X bas idx (wG X bas idx γ φ) (lact γ x) = thA X bas idx φ x) ∧ (∀ ψ, IsSB ψ → ip (wG X bas idx γ φ) (wG X bas idx γ ψ) = ip φ ψ ∧ wG X bas idx γ (φ + ψ) = wG X bas idx γ φ + wG X bas idx γ ψ ∧ ∀ x ∈ X.dom, thA X bas idx φ x = thA X bas idx ψ x → φ = ψ) ∧ (∀ a : ℂ, wG X bas idx γ (a • φ) = a • wG X bas idx γ φ) ∧ wG X bas idx 1 φ = φ ∧ (∀ γ', IsUn X γ' → wG X bas idx (γ' * γ) φ = wG X bas idx γ' (wG X bas idx γ φ)) ∧ ∀ y : Matrix (Fin n) (Fin r) E, wG X bas idx γ (heisG X bas y φ) = heisG X bas (y * (γ : Matrix (Fin r) (Fin r) E)ᵀ) (wG X bas idx γ φ) := by
  first | exact @GlobalTheory.SW.wG_laws | exact GlobalTheory.SW.wG_laws | (intros; apply GlobalTheory.SW.wG_laws <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.heisenbergDerivative_thetaFunction_laws : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ f, C.IsTh f → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ), C.IsTh (dRho (heisO C.ψ S T) C.θ τ z f) ∧ (∀ w, HasDerivAt (fun t : ℝ => C.rho (lineAt C.θ τ z t) f w) (dRho (heisO C.ψ S T) C.θ τ z f w) 0) ∧ (∀ f', C.IsTh f' → dRho (heisO C.ψ S T) C.θ τ z (f + f') = dRho (heisO C.ψ S T) C.θ τ z f + dRho (heisO C.ψ S T) C.θ τ z f') ∧ (∀ a : ℂ, dRho (heisO C.ψ S T) C.θ τ z (a • f) = a • dRho (heisO C.ψ S T) C.θ τ z f) ∧ (∀ z', dRho (heisO C.ψ S T) C.θ τ (z + z') f = dRho (heisO C.ψ S T) C.θ τ z f + dRho (heisO C.ψ S T) C.θ τ z' f) ∧ (∀ t : ℝ, dRho (heisO C.ψ S T) C.θ τ ((t : ℂ) • z) f = (t : ℂ) • dRho (heisO C.ψ S T) C.θ τ z f) ∧ (∀ u, IsFinPt u → dRho (heisO C.ψ S T) C.θ τ z (C.rho u f) = C.rho u (dRho (heisO C.ψ S T) C.θ τ z f)) ∧ ∀ (τ' : D.what₂.Tau) (z' : Matrix (Fin T.rank) (Fin S.rank) ℂ), dRho (heisO C.ψ S T) C.θ τ z (dRho (heisO C.ψ S T) C.θ τ' z' f) - dRho (heisO C.ψ S T) C.θ τ' z' (dRho (heisO C.ψ S T) C.θ τ z f) = (2 * π * I * (EFR C.X (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank) (Pi.single (C.m.e τ') (fun k a => conj (z' a k)) : WR C.X S.rank) : ℝ)) • f := by
  first | exact @GlobalTheory.Ker.HeisDeriv.dRho_laws | exact GlobalTheory.Ker.HeisDeriv.dRho_laws | (intros; apply GlobalTheory.Ker.HeisDeriv.dRho_laws <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.weakWeilRep_carries_derivatives_vacua_fockVectors : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeak C.ψ S T om → ∀ (h : GA D S) (g : GA D T) f, C.IsTh f → (∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ), om (h, g) (dRho (heisO C.ψ S T) C.θ τ z f) = dRho (heisO C.ψ S T) C.θ τ (compAt C.θ τ (mt T g) * z * compAt C.θ τ (mt S h⁻¹)) (om (h, g) f)) ∧ ∀ B, C.IsB B → (C.IsFock B f → C.IsFock (C.mvB g B) (om (h, g) f)) ∧ ∀ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, om (h, g) (C.fvec B f Q) = pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB (C.mvB g B)) (fun τ => compAt C.θ τ (mt S h)) (C.mvB g B) (om (h, g) f) Q := by
  first | exact @GlobalTheory.Ker.WeakMove.om_move | exact GlobalTheory.Ker.WeakMove.om_move | (intros; apply GlobalTheory.Ker.WeakMove.om_move <;> assumption)
end
