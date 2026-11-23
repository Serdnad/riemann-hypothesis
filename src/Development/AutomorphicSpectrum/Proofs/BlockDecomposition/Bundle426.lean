module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.IsStrictDom
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle412
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle413
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle389

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1 GlobalTheory.CuspRep

namespace GlobalTheory.CompanionTheory.LogAbs

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem norm_cW_eq_one (u : Ad E) (hu : IsUnit u) : ∀ᶠ w in Filter.cofinite, ‖cW w u‖ = 1 := by
  have h := (FiniteAdeleRing.isUnit_iff.1 (hu.map (pFin E))).2
  filter_upwards [h] with w hw
  have e : cW w u = (pFin E u) w := rfl
  rw [e, FinitePlace.norm_def, hw]
  simp

theorem support_log_finite (u : Ad E) (hu : IsUnit u) :
    (Function.support fun w => Real.log ‖cW w u‖).Finite := by
  refine (Filter.eventually_cofinite.1 (norm_cW_eq_one u hu)).subset fun w hw h1 => hw ?_
  simp [h1]

theorem logAbs_mul (u u' : Ad E) (hu : IsUnit u) (hu' : IsUnit u') :
    logAbs (u * u') = logAbs u + logAbs u' := by
  have h1 : ∀ v, Real.log (‖cV v (u * u')‖ ^ 2) = Real.log (‖cV v u‖ ^ 2) + Real.log (‖cV v u'‖ ^ 2) := fun v => by
    rw [map_mul, norm_mul, mul_pow, Real.log_mul
      (pow_ne_zero 2 (norm_ne_zero_iff.2 (hu.map (cV v)).ne_zero))
      (pow_ne_zero 2 (norm_ne_zero_iff.2 (hu'.map (cV v)).ne_zero))]
  have h2 : ∀ w, Real.log ‖cW w (u * u')‖ = Real.log ‖cW w u‖ + Real.log ‖cW w u'‖ := fun w => by
    rw [map_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (hu.map (cW w)).ne_zero)
      (norm_ne_zero_iff.2 (hu'.map (cW w)).ne_zero)]
  unfold logAbs
  simp only [h1, h2]
  rw [Finset.sum_add_distrib, finsum_add_distrib (support_log_finite u hu) (support_log_finite u' hu')]
  ring

theorem norm_cV_algebraMap (v : InfinitePlace E) (c : E) : ‖cV v (algebraMap E (Ad E) c)‖ = v c := by
  rw [← InfinitePlace.norm_embedding_eq]
  exact congrArg norm (pInf_algebraMap c v)

theorem norm_cW_algebraMap (w : HeightOneSpectrum (𝓞 E)) (c : E) :
    ‖cW w (algebraMap E (Ad E) c)‖ = FinitePlace.mk w c := rfl

theorem logAbs_algebraMap (c : E) (hc : c ≠ 0) : logAbs (algebraMap E (Ad E) c) = 0 := by
  have hprod := prod_abs_eq_one hc
  have hA : (∏ w : InfinitePlace E, w c ^ w.mult) ≠ 0 := left_ne_zero_of_mul_eq_one hprod
  have hB : (∏ᶠ w : FinitePlace E, w c) ≠ 0 := right_ne_zero_of_mul_eq_one hprod
  have hlog := congrArg Real.log hprod
  rw [Real.log_mul hA hB, Real.log_one, Real.log_prod (fun w _ => pow_ne_zero _ ((InfinitePlace.pos_iff.2 hc).ne')),
    Real.log_finprod fun w : FinitePlace E => FinitePlace.pos_iff.2 hc] at hlog
  have hm : ∀ v : InfinitePlace E, v.mult = 2 := fun v =>
    InfinitePlace.mult_isComplex ⟨v, IsTotallyComplex.isComplex v⟩
  unfold logAbs
  simp only [norm_cV_algebraMap, norm_cW_algebraMap]
  simp only [hm] at hlog
  rw [← hlog, ← finsum_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := E)).symm]
  rfl

theorem logAbsBasic : LogAbsBasic := fun _ _ _ _ =>
  ⟨support_log_finite, logAbs_mul, logAbs_algebraMap⟩

end GlobalTheory.CompanionTheory.LogAbs

end
end

section

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.RadicalForm

variable {K : Type} [Field K] {n : ℕ}

noncomputable def cols (S : Submodule K (Fin n → K)) : Fin (Module.finrank K S) → (Fin n → K) :=
  fun j => (Module.finBasis K S j : Fin n → K)

theorem cols_li (S : Submodule K (Fin n → K)) : LinearIndependent K (cols S) :=
  (Module.finBasis K S).linearIndependent.map' S.subtype S.ker_subtype

theorem cols_span (S : Submodule K (Fin n → K)) : Submodule.span K (Set.range (cols S)) = S := by
  have h : Set.range (cols S) = S.subtype '' Set.range (Module.finBasis K S) := by
    rw [← Set.range_comp]; rfl
  rw [h, Submodule.span_image, (Module.finBasis K S).span_eq, Submodule.map_top,
    Submodule.range_subtype]

def form (σ : K →+* K) (D : Matrix (Fin n) (Fin n) K) (u v : Fin n → K) : K :=
  (fun i => σ (u i)) ⬝ᵥ (D *ᵥ v)

theorem form_add_left (σ : K →+* K) (D : Matrix (Fin n) (Fin n) K) (u u' v : Fin n → K) :
    form σ D (u + u') v = form σ D u v + form σ D u' v := by
  simp [form, dotProduct, add_mul, Finset.sum_add_distrib]

theorem form_smul_left (σ : K →+* K) (D : Matrix (Fin n) (Fin n) K) (c : K) (u v : Fin n → K) :
    form σ D (c • u) v = σ c * form σ D u v := by
  simp [form, dotProduct, Finset.mul_sum, mul_assoc]

theorem form_zero_left (σ : K →+* K) (D : Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    form σ D 0 v = 0 := by
  simp [form, dotProduct]

theorem mem_perpD (σ : K →+* K) (d : GL (Fin n) K) (W : Submodule K (Fin n → K)) (v : Fin n → K) :
    v ∈ perpD σ d W ↔ ∀ x ∈ W, form σ (d⁻¹).val x v = 0 := by
  have h1 : d.val * (d⁻¹).val = 1 := Units.mul_inv d
  have h2 : (d⁻¹).val * d.val = 1 := Units.inv_mul d
  constructor
  · rintro ⟨y, hy, rfl⟩ x hx
    have hy' : ∀ x ∈ W, ∑ i, σ (x i) * y i = 0 := hy
    have h3 : (d⁻¹).val *ᵥ (Matrix.toLin' d.val y) = y := by
      rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
    simp only [form, h3]
    exact hy' x hx
  · intro h
    refine ⟨(d⁻¹).val *ᵥ v, fun x hx => h x hx, ?_⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

theorem form_swap (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) (D γ : Matrix (Fin n) (Fin n) K)
    (hγ : D * γ = (D.map σ)ᵀ) (u v : Fin n → K) :
    form σ D u (γ *ᵥ v) = σ (form σ D v u) := by
  simp only [form, Matrix.mulVec_mulVec, hγ]

  simp only [dotProduct, mulVec, map_sum, map_mul, hσ, transpose_apply, map_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem entry {κ κ' : Type} [Fintype κ] [Fintype κ'] (σ : K →+* K)
    (D : Matrix (Fin n) (Fin n) K) (M : Matrix (Fin n) κ K) (N : Matrix (Fin n) κ' K) (i j) :
    ((M.map σ)ᵀ * D * N) i j = form σ D (fun k => M k i) (fun k => N k j) := by
  rw [Matrix.mul_assoc]; rfl

theorem entry_mulVec {κ κ' : Type} [Fintype κ] [Fintype κ'] (σ : K →+* K)
    (D : Matrix (Fin n) (Fin n) K) (M : Matrix (Fin n) κ K) (N : Matrix (Fin n) κ' K)
    (c : κ' → K) (i) :
    (((M.map σ)ᵀ * D * N) *ᵥ c) i = form σ D (fun k => M k i) (N *ᵥ c) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]; rfl

theorem exists_adapted (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) (d : GL (Fin n) K)
    (γ : Matrix (Fin n) (Fin n) K) (hγ : (d⁻¹).val * γ = ((d⁻¹).val.map σ)ᵀ)
    (W : Submodule K (Fin n → K)) (hW : W.map (Matrix.toLin' γ) = W) :
    ∃ (a b : ℕ) (B : Matrix (Fin n) (Fin a) K) (A : Matrix (Fin n) (Fin b) K),
      LinearIndependent K (fromCols B A)ᵀ ∧
      Submodule.span K (Set.range Bᵀ) = W ⊓ perpD σ d W ∧
      Submodule.span K (Set.range (fromCols B A)ᵀ) = W ∧
      ((fromCols B A).map σ)ᵀ * (d⁻¹).val * B = 0 ∧ (B.map σ)ᵀ * (d⁻¹).val * fromCols B A = 0 ∧
      ((A.map σ)ᵀ * (d⁻¹).val * A).det ≠ 0 := by
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl (W ⊓ perpD σ d W)
  have hC : (W ⊓ perpD σ d W) ⊔ (Q ⊓ W) = W := by
    rw [← sup_inf_assoc_of_le Q (inf_le_left : W ⊓ perpD σ d W ≤ W), hQ.sup_eq_top, top_inf_eq]
  have hdis : Disjoint (W ⊓ perpD σ d W) (Q ⊓ W) := hQ.disjoint.mono_right inf_le_left
  obtain ⟨a, u, hu, hus⟩ : ∃ (a : ℕ) (u : Fin a → Fin n → K), LinearIndependent K u ∧
      Submodule.span K (Set.range u) = W ⊓ perpD σ d W := ⟨_, _, cols_li _, cols_span _⟩
  obtain ⟨b, v, hv, hvs⟩ : ∃ (b : ℕ) (v : Fin b → Fin n → K), LinearIndependent K v ∧
      Submodule.span K (Set.range v) = Q ⊓ W := ⟨_, _, cols_li _, cols_span _⟩
  have hum : ∀ j, u j ∈ W ⊓ perpD σ d W := fun j => hus ▸ Submodule.subset_span ⟨j, rfl⟩
  have hvm : ∀ j, v j ∈ Q ⊓ W := fun j => hvs ▸ Submodule.subset_span ⟨j, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin n) (Fin a) K, Bᵀ = u := ⟨(Matrix.of u)ᵀ, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin n) (Fin b) K, Aᵀ = v := ⟨(Matrix.of v)ᵀ, rfl⟩
  have hT : ((fromCols B A)ᵀ : _ → _ → K) = Sum.elim u v := by
    subst hB hA
    funext s k
    rcases s with j | j <;> rfl
  have hspan : Submodule.span K (Set.range (fromCols B A)ᵀ) = W := by
    rw [hT, Set.Sum.elim_range, Submodule.span_union, hus, hvs, hC]
  have hli : LinearIndependent K (fromCols B A)ᵀ := by
    rw [hT]
    exact hu.sum_type hv (by rw [hus, hvs]; exact hdis)
  have hFW : ∀ s, (fun k => fromCols B A k s) ∈ W := fun s => by
    have : (fun k => fromCols B A k s) ∈ Submodule.span K (Set.range (fromCols B A)ᵀ) :=
      Submodule.subset_span ⟨s, rfl⟩
    rwa [hspan] at this
  have hr : ∀ w ∈ W ⊓ perpD σ d W, ∀ x ∈ W, form σ (d⁻¹).val x w = 0 := fun w hw x hx =>
    (mem_perpD σ d W w).1 hw.2 x hx
  have hl : ∀ w ∈ W ⊓ perpD σ d W, ∀ x ∈ W, form σ (d⁻¹).val w x = 0 := fun w hw x hx => by
    rw [← hW] at hx
    obtain ⟨x', hx', rfl⟩ := hx
    rw [Matrix.toLin'_apply, form_swap σ hσ _ γ hγ, hr w hw x' hx', map_zero]
  have hBc : ∀ j, (fun k => B k j) = u j := fun j => congrFun hB j
  have hAc : ∀ j, (fun k => A k j) = v j := fun j => congrFun hA j
  refine ⟨_, _, B, A, hli, by rw [hB]; exact hus, hspan, ?_, ?_, ?_⟩
  · ext i j
    rw [entry, hBc]
    exact hr _ (hum j) _ (hFW i)
  · ext i j
    rw [entry, hBc]
    exact hl _ (hum i) _ (hFW j)
  · intro h0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hAv : A *ᵥ c = ∑ j, c j • v j := by
      rw [Matrix.mulVec_eq_sum, hA]
      exact Finset.sum_congr rfl fun j _ => op_smul_eq_smul _ _
    have hyC : A *ᵥ c ∈ Q ⊓ W := by
      rw [hAv]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hvm j)
    have hyW : A *ᵥ c ∈ W := hyC.2
    have hcol : ∀ s, form σ (d⁻¹).val (fun k => fromCols B A k s) (A *ᵥ c) = 0 := by
      rintro (j | j)
      · have h := hl _ (hum j) _ hyW
        rw [← hBc j] at h
        exact h
      · have := congrFun hc j
        rw [entry_mulVec] at this
        exact this
    have hperp : A *ᵥ c ∈ perpD σ d W := by
      rw [mem_perpD]
      intro x hx
      rw [← hspan] at hx
      induction hx using Submodule.span_induction with
      | mem x h =>
        obtain ⟨s, rfl⟩ := h
        exact hcol s
      | zero => exact form_zero_left _ _ _
      | add x y _ _ hx hy => rw [form_add_left, hx, hy, add_zero]
      | smul a x _ hx => rw [form_smul_left, hx, mul_zero]
    have hy0 : A *ᵥ c = 0 := by
      have := hdis.le_bot (show A *ᵥ c ∈ _ from ⟨⟨hyW, hperp⟩, hyC⟩)
      simpa using this
    apply hc0
    have hsum : ∑ j, c j • v j = 0 := by rw [← hAv, hy0]
    funext j
    exact Fintype.linearIndependent_iff.1 hv c hsum j

theorem radical : Radical := by
  intro E _ _ _ n d W hW
  have hσ : ∀ x, conjE E (conjE E x) = x := fun x => NumberField.IsCMField.complexConj_apply_apply E x
  refine exists_adapted (conjE E) hσ d (nrm d).val ?_ W hW
  have h2 : (d⁻¹).val * d.val = 1 := Units.inv_mul d
  rw [nrm, Units.val_mul, ← mul_assoc, h2, one_mul, thetaR_val]

end GlobalTheory.CompanionTheory.RadicalForm
end

section

namespace GlobalTheory.CompanionTheory.LinAlg

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

variable {K : Type} [Field K] {n : ℕ}

theorem exists_li_span (S : Submodule K (Fin n → K)) :
    ∃ (a : ℕ) (f : Fin a → Fin n → K), LinearIndependent K f ∧ Submodule.span K (Set.range f) = S := by
  let b := Module.finBasis K S
  refine ⟨Module.finrank K S, S.subtype ∘ b, ?_, ?_⟩
  · exact b.linearIndependent.map' S.subtype (Submodule.ker_subtype S)
  · rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]

theorem exists_compl_le {I W : Submodule K (Fin n → K)} (h : I ≤ W) :
    ∃ P : Submodule K (Fin n → K), P ≤ W ∧ I ⊔ P = W ∧ Disjoint I P := by
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl (I.comap W.subtype)
  have hI : (I.comap W.subtype).map W.subtype = I := by
    rw [Submodule.map_comap_subtype]; exact inf_eq_right.mpr h
  refine ⟨Q.map W.subtype, Submodule.map_subtype_le W Q, ?_, ?_⟩
  · rw [← hI, ← Submodule.map_sup, hQ.sup_eq_top, Submodule.map_subtype_top]
  · rw [← hI]
    exact Submodule.disjoint_map W.injective_subtype hQ.disjoint

theorem transpose_fromCols_two {ι κ : Type} (f : ι → Fin n → K) (g : κ → Fin n → K) :
    (fromCols (of f)ᵀ (of g)ᵀ)ᵀ = of (Sum.elim f g) := by
  ext i j
  rcases i with i | i <;> rfl

theorem transpose_fromCols_three {ι κ μ : Type} (f : ι → Fin n → K) (g : κ → Fin n → K)
    (h : μ → Fin n → K) :
    (fromCols (of f)ᵀ (fromCols (of g)ᵀ (of h)ᵀ))ᵀ = of (Sum.elim f (Sum.elim g h)) := by
  ext i j
  rcases i with i | i | i <;> rfl

theorem span_elim {ι κ : Type} (f : ι → Fin n → K) (g : κ → Fin n → K) :
    Submodule.span K (Set.range (Sum.elim f g)) =
      Submodule.span K (Set.range f) ⊔ Submodule.span K (Set.range g) := by
  rw [Set.Sum.elim_range, Submodule.span_union]

theorem twoBases : TwoBases := by
  intro K _ n W W'
  obtain ⟨P, hPW, hIP, hdP⟩ := exists_compl_le (inf_le_left : W ⊓ W' ≤ W)
  obtain ⟨Q, hQW, hIQ, hdQ⟩ := exists_compl_le (inf_le_right : W ⊓ W' ≤ W')
  obtain ⟨a, f, hf, hfs⟩ := exists_li_span (W ⊓ W')
  obtain ⟨b, g, hg, hgs⟩ := exists_li_span P
  obtain ⟨c, h, hh, hhs⟩ := exists_li_span Q
  have hPQ : Disjoint P Q := by
    rw [Submodule.disjoint_def]
    intro x hxP hxQ
    exact (Submodule.disjoint_def.mp hdP) x (Submodule.mem_inf.mpr ⟨hPW hxP, hQW hxQ⟩) hxP
  have hIPQ : Disjoint (W ⊓ W') (P ⊔ Q) := by
    rw [Submodule.disjoint_def]
    intro x hxI hx
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hx
    have hqI : q ∈ W ⊓ W' := by
      refine Submodule.mem_inf.mpr ⟨?_, hQW hq⟩
      have hq' : q = (p + q) - p := by abel
      rw [hq']
      exact W.sub_mem (Submodule.mem_inf.mp hxI).1 (hPW hp)
    have hq0 : q = 0 := (Submodule.disjoint_def.mp hdQ) q hqI hq
    subst hq0
    rw [add_zero] at hxI ⊢
    exact (Submodule.disjoint_def.mp hdP) p hxI hp
  have e2 : ((of f)ᵀ.fromCols (of g)ᵀ)ᵀ = Sum.elim f g := transpose_fromCols_two f g
  have e2' : ((of f)ᵀ.fromCols (of h)ᵀ)ᵀ = Sum.elim f h := transpose_fromCols_two f h
  have e3 : ((of f)ᵀ.fromCols ((of g)ᵀ.fromCols (of h)ᵀ))ᵀ = Sum.elim f (Sum.elim g h) :=
    transpose_fromCols_three f g h
  have e1 : ((of f)ᵀ)ᵀ = f := transpose_transpose (of f)
  refine ⟨a, b, c, (of f)ᵀ, (of g)ᵀ, (of h)ᵀ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e3]
    refine hf.sum_type (hg.sum_type hh ?_) ?_
    · rw [hgs, hhs]; exact hPQ
    · rw [hfs, span_elim, hgs, hhs]; exact hIPQ
  · rw [e1]; exact hfs
  · rw [e2, span_elim, hfs, hgs, hIP]
  · rw [e2', span_elim, hfs, hhs, hIQ]
  · rw [e3, span_elim, span_elim, hfs, hgs, hhs, sup_sup_distrib_left, hIP, hIQ]

end GlobalTheory.CompanionTheory.LinAlg
end

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.Cutoff

section Img

variable {K : Type} [Field K] {n : ℕ}

def imgEquiv (g : GL (Fin n) K) : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  LinearEquiv.ofLinear (Matrix.toLin' g.val) (Matrix.toLin' (g⁻¹ : GL (Fin n) K).val)
    (by rw [← Matrix.toLin'_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.toLin'_one])

theorem img_eq_map (g : GL (Fin n) K) (W : Submodule K (Fin n → K)) :
    img g W = W.map ((imgEquiv g : (Fin n → K) ≃ₗ[K] (Fin n → K)) : (Fin n → K) →ₗ[K] (Fin n → K)) := rfl

theorem finrank_img (g : GL (Fin n) K) (W : Submodule K (Fin n → K)) :
    Module.finrank K (img g W) = Module.finrank K W := by
  rw [img_eq_map]
  exact LinearEquiv.finrank_map_eq _ _

theorem img_top (g : GL (Fin n) K) : img g (⊤ : Submodule K (Fin n → K)) = ⊤ := by
  rw [img_eq_map, Submodule.map_top]
  exact LinearEquiv.range _

theorem img_img_inv (g : GL (Fin n) K) (W : Submodule K (Fin n → K)) :
    img g (img (g⁻¹ : GL (Fin n) K) W) = W := by
  unfold img
  rw [← Submodule.map_comp, ← Matrix.toLin'_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.toLin'_one, Submodule.map_id]

end Img

theorem mem_cutSet_of_mem (hR : DegRat) {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ} {τ : ℝ}
    (g : GL (Fin n) E) {x : GA E n} (hx : x ∈ cutSet E n τ) : ratGL E n g * x ∈ cutSet E n τ := by
  have hx' : (∀ W : Submodule E (Fin n → E), deg x W ≤ prof n τ (Module.finrank E W)) ∧ -τ ≤ deg x ⊤ := hx
  show (∀ W : Submodule E (Fin n → E), deg (ratGL E n g * x) W ≤ prof n τ (Module.finrank E W)) ∧
    -τ ≤ deg (ratGL E n g * x) ⊤
  refine ⟨fun W => ?_, ?_⟩
  · have h := hR E n x g (img (g⁻¹ : GL (Fin n) E) W)
    rw [img_img_inv] at h
    rw [h, ← finrank_img (g⁻¹ : GL (Fin n) E) W]
    exact hx'.1 _
  · have h := hR E n x g ⊤
    rw [img_top] at h
    rw [h]
    exact hx'.2

theorem mahler_of : DegBdd → DegRat → MahlerC → Mahler := by
  intro hB hR hM E _ _ _ n τ
  refine ⟨?_, ?_, ?_⟩
  · have hset : cutSet E n τ = (⋂ W : Submodule E (Fin n → E), {x : GA E n | deg x W ≤ prof n τ (Module.finrank E W)}) ∩
        {x : GA E n | -τ ≤ deg x ⊤} := by
      ext x
      simp [cutSet]
    rw [hset]
    exact (isClosed_iInter fun W => isClosed_le ((hB E n).2 W) continuous_const).inter
      (isClosed_le continuous_const ((hB E n).2 ⊤))
  · intro g x
    constructor
    · intro h
      have h' := mem_cutSet_of_mem hR (g⁻¹) h
      rwa [map_inv, inv_mul_cancel_left] at h'
    · exact mem_cutSet_of_mem hR g
  · obtain ⟨C, hC, hsub⟩ := hM E n (|τ| * (2 * n + 1) ^ 2)
    refine ⟨C, hC, fun x hx => ?_⟩
    have hx' : (∀ W : Submodule E (Fin n → E), deg x W ≤ prof n τ (Module.finrank E W)) ∧ -τ ≤ deg x ⊤ := hx
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hτ : τ ≤ |τ| := le_abs_self τ
    have hτ0 : 0 ≤ |τ| := abs_nonneg τ
    apply hsub x
    · intro W hW
      have h1 := hx'.1 W
      rw [hW] at h1
      simp only [prof] at h1
      push_cast at h1
      nlinarith [mul_nonneg hτ0 hn, mul_nonneg (sub_nonneg.2 hτ) hn, mul_nonneg hτ0 (mul_nonneg hn hn)]
    · have h1 := hx'.1 ⊤
      rw [finrank_top, Module.finrank_fin_fun] at h1
      simp only [prof] at h1
      have h2 := hx'.2
      rw [abs_le]
      constructor
      · nlinarith [mul_nonneg hτ0 hn, mul_nonneg hτ0 (mul_nonneg hn hn)]
      · nlinarith [mul_nonneg hτ0 hn, mul_nonneg hτ0 (mul_nonneg hn hn),
          mul_nonneg (sub_nonneg.2 hτ) (mul_nonneg hn (by linarith : (0 : ℝ) ≤ n + 1))]

end GlobalTheory.CompanionTheory.Cutoff

end
end

section

open GlobalTheory.PRep PositivityTheory.SphericalProduct

theorem _root_.GlobalTheory.T.jacquet_projection_hecke_holds : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], PositivityTheory.SphericalProduct.A2 G := by
  first | exact @GlobalTheory.CompanionTheory.Cass.jacquet_projection_hecke_intertwines | exact GlobalTheory.CompanionTheory.Cass.jacquet_projection_hecke_intertwines | (intros; apply GlobalTheory.CompanionTheory.Cass.jacquet_projection_hecke_intertwines <;> assumption)
end

section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow

theorem _root_.GlobalTheory.T.dominant_conjugate_unipotent_mem : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ) (t u : GU σ n), IsDiagM (t : GL (Fin n) L) → IsStrictDom (t : GL (Fin n) L) → u ∈ IwU σ n → IsUnipU u → ∀ k : ℕ, t ^ k * u * (t ^ k)⁻¹ ∈ KU σ n := by
  first | exact @GlobalTheory.CompanionTheory.SatPow.conj_unip_mem_KU | exact GlobalTheory.CompanionTheory.SatPow.conj_unip_mem_KU | (intros; apply GlobalTheory.CompanionTheory.SatPow.conj_unip_mem_KU <;> assumption)
end

section

open scoped Matrix

theorem _root_.GlobalTheory.T.parabolic_decomposition_upper_half_space : ∀ (n : ℕ) (p : PositivityTheory.Rg.Sw.GR n), (PositivityTheory.Rg.Sw.mR p).toBlocks₂₁ = 0 → ∃ (nb ma : PositivityTheory.Rg.Sw.GR n) (b a : Matrix (Fin n) (Fin n) ℂ), bᴴ = b ∧ IsUnit a.det ∧ PositivityTheory.Rg.Sw.mR nb = PositivityTheory.Rg.Sw.nU b ∧ PositivityTheory.Rg.Sw.mR ma = Matrix.fromBlocks a 0 0 (aᴴ)⁻¹ ∧ p = nb * ma ∧ ((PositivityTheory.Rg.Sw.mR p).toBlocks₁₁ * (Complex.I • 1) + (PositivityTheory.Rg.Sw.mR p).toBlocks₁₂) * ((PositivityTheory.Rg.Sw.mR p).toBlocks₂₁ * (Complex.I • 1) + (PositivityTheory.Rg.Sw.mR p).toBlocks₂₂)⁻¹ = b + Complex.I • (a * aᴴ) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelPoint.siegel_point | exact GlobalTheory.CompanionTheory.SiegelPoint.siegel_point | (intros; apply GlobalTheory.CompanionTheory.SiegelPoint.siegel_point <;> assumption)
end
