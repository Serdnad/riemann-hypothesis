module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FZEqConstMulIrreduciblePow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HintISBounds
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.SubstitutionSplitIrreducibleOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ArchimedeanLocalHeightTerm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteLocalHeightTerm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HeightProdPowMultiHomogeneous
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationGenericRatioEqRestriction
import ReciprocityTheory.SemistableReduction.Bundle014
import ReciprocityTheory.SemistableReduction.Bundle013
public import Mathlib.NumberTheory.NumberField.ProductFormula

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

theorem ratio_self' {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V] {f : V} (hf : f ≠ 0) :
    ratio (Ω := Ω) f f = 1 := by
  have hex : ∃ a : Ω, f = a • f := ⟨1, (one_smul Ω f).symm⟩
  unfold ratio
  rw [dite_eq_left hex]
  have hs := hex.choose_spec
  have h0 : (hex.choose - 1) • f = 0 := by rw [sub_smul, ← hs, one_smul, sub_self]
  rcases smul_eq_zero.mp h0 with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hf

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def affineRowCombination (c : ι) (a : Fin (d.D + 2)) : MvPolynomial (Fin (d.D + 2) × Fin (d.N + 1)) (Ω c) :=
  ∑ k, X (a, k) * C (d.affineCoord c k)

noncomputable def pluckerSubstitution (c : ι) :
    MvPolynomial (TVar d.D d.N) (Ω c) →ₐ[Ω c] MvPolynomial (Fin (d.D + 2) × Fin (d.N + 1)) (Ω c) :=
  aeval fun t => d.affineRowCombination c 0 * X (t.1.succ, t.2) - d.affineRowCombination c t.1.succ * X (0, t.2)

theorem substitution_comp_relation (hd : d.AxH 𝒜) (c : ι) :
    (d.linearSubstitution c).comp (MvPolynomial.aeval (fun t : TVar d.D d.N =>
      (MvPolynomial.X (Sum.inr 0) * MvPolynomial.X (Sum.inl (t.1.succ, t.2)) -
        MvPolynomial.X (Sum.inr t.1.succ) * MvPolynomial.X (Sum.inl (0, t.2)) :
          MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K))) =
      ((d.pluckerSubstitution c).restrictScalars K).comp (d.relationEliminateColumn c) := by
  have hy : d.affineCoord c (d.jc c) = 1 := ratio_self' (hd.w_base c)
  have hs : ∀ a, d.affineRowCombination c a = ∑ k, X (a, k) * C (d.affineCoord c k) := fun a => rfl
  have hphi_inl : ∀ p, d.linearSubstitution c (X (Sum.inl p)) = X p := by
    intro p
    simp [Data.linearSubstitution]
  have hphi_inr : ∀ i, d.linearSubstitution c (X (Sum.inr i)) = d.affineRowCombination c i := by
    intro i
    simp [Data.linearSubstitution, Data.affineRowCombination]
  have hrho : ∀ t : TVar d.D d.N, d.pluckerSubstitution c (X t) =
      d.affineRowCombination c 0 * X (t.1.succ, t.2) - d.affineRowCombination c t.1.succ * X (0, t.2) := by
    intro t
    simp [Data.pluckerSubstitution]
  apply MvPolynomial.algHom_ext
  intro t
  simp only [AlgHom.comp_apply, aeval_X, map_sub, map_mul, hphi_inl, hphi_inr,
    AlgHom.restrictScalars_apply]
  simp only [Data.relationEliminateColumn, aeval_X]
  split_ifs with ht
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_neg, map_sum]
    simp only [map_mul, hrho, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]

    have htot : ∑ k, (d.affineRowCombination c 0 * X (t.1.succ, k) - d.affineRowCombination c t.1.succ * X (0, k)) *
        C (d.affineCoord c k) = 0 := by
      simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, ← hs]
      ring
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (d.jc c)), hy, map_one, mul_one] at htot
    have hC : ∀ r, d.pluckerSubstitution c (C r) = C r := fun r => by simp [Data.pluckerSubstitution]
    have hyd : ∀ k, ratio (Ω := Ω c) (d.w k c) (d.w (d.jc c) c) = d.affineCoord c k := fun k => rfl
    simp only [hC, hyd]
    rw [ht]
    linear_combination htot
  · rw [hrho]

theorem substitution_vanishes_of_relation (hd : d.AxH 𝒜) (c : ι) (Q : KTp K d.D d.N) (hQ : d.relationEliminateColumn c Q = 0) :
    d.linearSubstitution c (bilinearSubstitution Q) = 0 := by
  have h := congrArg (fun φ => φ Q) (d.substitution_comp_relation hd c)
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, hQ, map_zero] at h
  exact h

theorem substitution_split_irreducible (hd : d.AxH 𝒜) (c : ι) (F0 : KTp K d.D d.N) (hirr : Irreducible F0) (d0 : ℕ)
    (hmh : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d0) F0)
    (hker : ∀ Q : KTp K d.D d.N, d.relationEliminateColumn c Q = 0 ↔ F0 ∣ Q) :
    ∃ (a : ℕ) (F1 : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K) (deF : ℕ),
      bilinearSubstitution F0 = X (Sum.inr 0) ^ a * F1 ∧ Irreducible F1 ∧
      (∀ s ∈ F1.support, ∑ i, s (Sum.inr i) = deF) ∧ deF ≤ d0 ∧
      (∀ s ∈ F1.support, ∑ p, s (Sum.inl p) ≤ (d.D + 1) * d0) := d.substitution_split_irreducible_of c F0 hirr d0 hmh hker

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

theorem finsum_finset_sum_comm' {α β : Type*} (s : Finset β) (f : β → α → ℝ)
    (hf : ∀ b ∈ s, (Function.support (f b)).Finite) :
    ∑ᶠ a, ∑ b ∈ s, f b a = ∑ b ∈ s, ∑ᶠ a, f b a := by
  first
    | exact finsum_sum_comm s (fun a b => f b a) hf
    | (classical
       induction s using Finset.induction_on with
       | empty => simp
       | insert b s hb ih =>
         simp only [Finset.sum_insert hb]
         rw [finsum_add_distrib (hf b (Finset.mem_insert_self b s))
           ((s.finite_toSet.biUnion fun b' hb' => hf b' (Finset.mem_insert_of_mem hb')).subset
             (Function.support_finset_sum)), ih fun b' hb' => hf b' (Finset.mem_insert_of_mem hb')])

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem height_decomposition_local_terms (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (x : Fin (d.N + 1) → K)
    (hx : ∀ c, d.wx x c ≠ 0) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c) :
    (Function.support fun la => d.localHeightAtPrime h (d.wx x) c la * logNorm la).Finite ∧
    (∑ᶠ la, d.localHeightAtPrime h (d.wx x) c la * logNorm la) / (Module.finrank ℚ K : ℝ) +
      meanK (d.localHeightAtEmbedding (d.wx x) c) +
      ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        (d.nPMM h c (d.wx x c) p : ℝ) * ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p) =
      ReciprocityTheory.MultiplicativeHeights.h0 F + d.delc c * (harmonic d.N : ℝ) / 2 := by
  obtain ⟨hFne, hFx⟩ := d.fZ_and_substituted_ne_zero hd h x hx c F hF
  obtain ⟨κ, hκ, hs⟩ := d.substituted_factorization_exists hd h x hx c F hF
  have hfin := d.finite_local_height_term hd h x hx c F κ hκ hF hFne hFx hs
  have harch := d.archimedean_local_height_term hd h x hx c F κ hκ hF hFne hs
  rw [(d.height_substituted_eq_finsum hd h x hx c F hF).2]
  set G : FinitePlace K → ℝ := fun v => Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs v F) -
    Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs v (d.translatedForm x F)) + Real.log (v κ) with hG
  have hg : (fun la => d.localHeightAtPrime h (d.wx x) c la * logNorm la) =
      fun la => G (FinitePlace.equivHeightOneSpectrum.symm la) := by
    funext la; rw [hfin la]; rfl
  have s1 := ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite F hFne
  have s2 := ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite _ hFx
  have s3 : (Function.support fun v : FinitePlace K => Real.log (v κ)).Finite := by
    refine (FinitePlace.hasFiniteMulSupport hκ).subset fun v hv => ?_
    intro h1; apply hv; simp only; rw [show v κ = 1 from h1, Real.log_one]
  have sG : (Function.support G).Finite := ((s1.union s2).union s3).subset (by
    intro v hv; by_contra hn; apply hv
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hn
    simp only [hG, hn.1.1, hn.1.2, hn.2]; ring)
  have hsumG : ∑ᶠ la, d.localHeightAtPrime h (d.wx x) c la * logNorm la = ∑ᶠ v, G v := by
    rw [hg]; exact finsum_comp_equiv FinitePlace.equivHeightOneSpectrum.symm
  refine ⟨?_, ?_⟩
  · rw [hg]
    exact (sG.image FinitePlace.equivHeightOneSpectrum).subset (by
      intro la hla; exact ⟨FinitePlace.equivHeightOneSpectrum.symm la, hla, by simp⟩)
  rw [hsumG, hG, finsum_add_distrib ((s1.union s2).subset (Function.support_sub _ _)) s3,
    finsum_sub_distrib s1 s2]
  have hpf : (∑ᶠ v : FinitePlace K, Real.log (v κ)) + ∑ σ : K →+* ℂ, Real.log ‖σ κ‖ = 0 := by
    classical
    have hm := FinitePlace.hasFiniteMulSupport hκ
    set U := hm.toFinset
    have hsub1 : Function.mulSupport (fun v : FinitePlace K => v κ) ⊆ U := by
      intro v hv; exact hm.mem_toFinset.mpr hv
    have hsub2 : Function.support (fun v : FinitePlace K => Real.log (v κ)) ⊆ U := by
      intro v hv; apply hsub1; intro h1; apply hv; simp only; rw [show v κ = 1 from h1, Real.log_one]
    have hprod := FinitePlace.prod_eq_inv_abs_norm hκ
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub1] at hprod
    rw [finsum_eq_sum_of_support_subset _ hsub2, ReciprocityTheory.MultiplicativeHeights.sum_log_norm_embedding_eq κ hκ,
      ← Real.log_prod fun v _ => (FinitePlace.pos_iff.mpr hκ).ne', hprod]
    push_cast
    rw [Real.log_inv]; ring
  have hcard : (Fintype.card (K →+* ℂ) : ℝ) = Module.finrank ℚ K := by
    rw [NumberField.Embeddings.card]
  have hn : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  unfold meanK ReciprocityTheory.MultiplicativeHeights.h0
  simp_rw [harch]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, hcard]
  field_simp
  linarith [hpf]

theorem height_minMax_eq_sum_heights (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (x : Fin (d.N + 1) → K)
    (hx : ∀ c, d.wx x c ≠ 0) (F : ι → KTp K d.D d.N)
    (hF : ∀ c, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (F c) = d.fZ h c) :
    d.HgtMM h (d.wx x) = ∑ c, ReciprocityTheory.MultiplicativeHeights.h0 (F c) + d.del * (harmonic d.N : ℝ) / 2 := by
  have hc := fun c => d.height_decomposition_local_terms hd h hI2be x hx c (F c) (hF c)
  have hla : ∀ la, d.NlaMM h (d.wx x) la * logNorm la = ∑ c, d.localHeightAtPrime h (d.wx x) c la * logNorm la := by
    intro la
    simp only [NlaMM, localHeightAtPrime, Finset.sum_mul]
  have hsg : d.NsgMM (d.wx x) = fun sg => ∑ c, d.localHeightAtEmbedding (d.wx x) c sg := by
    funext sg
    rfl
  have hmean : meanK (fun sg => ∑ c, d.localHeightAtEmbedding (d.wx x) c sg) = ∑ c, meanK (d.localHeightAtEmbedding (d.wx x) c) := by
    simp only [meanK, Finset.sum_div]
    rw [Finset.sum_comm]
  unfold HgtMM mahlerMeasureHeight
  simp only [hla]
  rw [finsum_finset_sum_comm' Finset.univ (fun c la => d.localHeightAtPrime h (d.wx x) c la * logNorm la) (fun c _ => (hc c).1)]
  rw [hsg, hmean, Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    Finset.sum_congr rfl fun c _ => (hc c).2, Finset.sum_add_distrib]
  simp only [del, Nat.cast_sum, Finset.sum_mul, Finset.sum_div]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem hint_chain (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (c : ι) (sg : K →+* ℂ) :
    d.HintIS c sg (fun P => Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P)) ∧
    d.HintIS c sg (fun P => Real.log (d.nrm c d.wL (d.w (d.jc c) c) P)) ∧
    d.HintIS c sg (fun P => Real.log (d.nrm c ((2 : ℕ) • d.G1) (d.ta1 c) P)) ∧
    (∃ e, e ∈ 𝒜 c d.wF ∧ e ≠ 0 ∧ d.HintIS c sg (fun P => Real.log (d.nrm c d.wF e P))) ∧
    d.HintIS c sg (fun P => Real.log (d.nrm c d.G2 (d.ta2 c) P)) := by
  haveI := hd.graded c
  obtain ⟨Bw, hBw⟩ := d.hint_bdd sg c (f := d.w (d.jc c)) (hd.bdd sg d.wL _ (Or.inl
    ⟨by rw [hd.WW_span]; exact Submodule.subset_span ⟨_, rfl⟩, rfl⟩))
  obtain ⟨Be, hBe⟩ := d.hint_bdd sg c
    (hd.bdd sg (d.n1 • d.wde) d.et (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
  obtain ⟨Bt, hBt⟩ := d.hint_bdd sg c
    (hd.bdd sg ((2 : ℕ) • d.G1) d.ta1 (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
  obtain ⟨B2, hB2⟩ := d.hint_bdd sg c
    (hd.bdd sg d.G2 d.ta2 (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))
  obtain ⟨k, hk⟩ := d.hint_thp_ne hd c
  obtain ⟨Bh, hBh⟩ := d.hint_bdd sg c (f := d.thp k) (hd.bdd sg d.wF _ (Or.inr (Or.inl
    ⟨by rw [hd.Thp_span]; exact Submodule.subset_span ⟨k, rfl⟩, rfl⟩)))
  have hwm := hd.w_mem (d.jc c) c
  have hw0 := hd.w_base c
  have hem := hd.et_mem c
  have he0 := hd.et_ne c
  have htm := hd.firstSectionMem c
  have ht0 := hd.firstSectionNeZero c
  have h2m := hd.secondSectionMem c
  have h20 := hd.secondSectionNeZero c
  have hhm := hd.thp_mem k c
  have hn1 : 0 < d.n1 := Nat.mul_pos hd.i_ge hd.g_zero_ge_ask_sum
  have hi : (1 : ℝ) ≤ d.i := by exact_mod_cast hd.i_ge
  have hn1r : (d.n1 : ℝ) = d.i * d.g0 := by simp [Data.n1]
  have hn1r1 : (1 : ℝ) ≤ d.n1 := by exact_mod_cast hn1
  have hκ : (d.n1 : ℝ) * (d.cc / d.i) = d.g0 * d.cc := by
    rw [hn1r]; field_simp
  have hq : 1 ≤ 2 - 2 * d.cc * d.g0 := by linarith [hd.ccg0]
  have IU : d.HintIS c sg (fun P => Real.log ‖d.hintU c P‖) := d.hint_intU hd h c sg

  obtain ⟨ht1m, ht10, ht1l⟩ := d.hint_pow hd htm ht0 d.n1 hn1
  obtain ⟨he2m, he20, he2l⟩ := d.hint_pow hd hem he0 2 two_pos
  obtain ⟨hwpm, hwp0, hwpl⟩ := d.hint_pow hd hwm hw0 (2 * d.n1) (by omega)
  have hW1 : d.n1 • ((2 : ℕ) • d.G1) + (2 : ℕ) • (d.n1 • d.wde) = (2 * d.n1) • d.wL := by
    simp only [Data.G1, smul_sub, smul_smul, mul_comm d.n1 2]; abel
  have hf1m : d.ta1 c ^ d.n1 * d.et c ^ 2 ∈ 𝒜 c ((2 * d.n1) • d.wL) := by
    rw [← hW1]; exact SetLike.mul_mem_graded ht1m he2m
  have hf10 := hd.mul_ne_zero c ht1m he2m ht10 he20
  have Ir1 : d.HintIS c sg (fun P => Real.log ‖P (ratio (Ω := Ω c) (d.ta1 c ^ d.n1 * d.et c ^ 2)
      (d.w (d.jc c) c ^ (2 * d.n1)))‖) :=
    d.hint_intNorm hd h c sg _ (hint_ratio_ne hd hwpm hwp0 hf1m hf10)
  have E1 : ∀ P, (d.n1 : ℝ) * Real.log (d.nrm c ((2 : ℕ) • d.G1) (d.ta1 c) P) +
      2 * Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P) =
      Real.log ‖P (ratio (Ω := Ω c) (d.ta1 c ^ d.n1 * d.et c ^ 2)
        (d.w (d.jc c) c ^ (2 * d.n1)))‖ + 2 * d.n1 * Real.log (d.nrm c d.wL (d.w (d.jc c) c) P) := by
    intro P
    have h1 := d.hint_log_mul hd ht1m he2m ht10 he20 P
    rw [hW1, ht1l, he2l] at h1
    have h2 := d.hint_log_line hd hwpm hwp0 hf1m hf10 P
    rw [hwpl] at h2
    push_cast at h1 h2
    linarith
  have I2 : ∀ P, -(Real.log (d.nrm c d.wL (d.w (d.jc c) c) P) + Real.log ‖d.hintU c P‖) ≤
      d.tableLineDegreeFive * d.DF + d.cc / d.i * (-Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P)) +
        d.cc * d.tableLineDegreeTwo := by
    intro P; rw [← d.hint_log_be hd c P]; exact hI2be c P

  have Iet : d.HintIS c sg (fun P => Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P)) := by
    refine d.hintIS_bounds hd h (d.hint_meas hd c sg hem he0)
      (d.hintIS_lin hd h Ir1 IU (1 / (2 - 2 * d.cc * d.g0)) (-(2 * d.n1) / (2 - 2 * d.cc * d.g0))
        (-(d.n1 * Real.log Bt + 2 * d.n1 * (d.tableLineDegreeFive * d.DF + d.cc * d.tableLineDegreeTwo)) /
          (2 - 2 * d.cc * d.g0))) (fun P hP => ?_) _ (d.hint_log_le hd hem he0 hBe)
    have e1 := E1 P
    have lt := d.hint_log_le hd htm ht0 hBt P hP
    have lt2 := mul_le_mul_of_nonneg_left lt (by positivity : (0 : ℝ) ≤ d.n1)
    have ib2 := mul_le_mul_of_nonneg_left (I2 P) (by positivity : (0 : ℝ) ≤ 2 * d.n1)
    have hκ' : (d.n1 : ℝ) * (d.cc / d.i) * Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P) =
        d.g0 * d.cc * Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P) := by rw [hκ]
    have hqp : (0 : ℝ) < 2 - 2 * d.cc * d.g0 := by linarith
    rw [← sub_nonneg]
    have : ∀ x y z : ℝ, 1 / (2 - 2 * d.cc * d.g0) * x + -(2 * d.n1) / (2 - 2 * d.cc * d.g0) * y +
        -z / (2 - 2 * d.cc * d.g0) = (x - 2 * d.n1 * y - z) / (2 - 2 * d.cc * d.g0) := by
      intro x y z; ring
    rw [this, sub_nonneg, div_le_iff₀ hqp]
    nlinarith

  have Iw : d.HintIS c sg (fun P => Real.log (d.nrm c d.wL (d.w (d.jc c) c) P)) := by
    refine d.hintIS_bounds hd h (d.hint_meas hd c sg hwm hw0)
      (d.hintIS_lin hd h Iet IU (d.cc / d.i) (-1) (-(d.tableLineDegreeFive * d.DF + d.cc * d.tableLineDegreeTwo)))
      (fun P _ => ?_) _ (d.hint_log_le hd hwm hw0 hBw)
    have := I2 P
    linarith

  have It1 : d.HintIS c sg (fun P => Real.log (d.nrm c ((2 : ℕ) • d.G1) (d.ta1 c) P)) := by
    refine d.hintIS_bounds hd h (d.hint_meas hd c sg htm ht0)
      (d.hintIS_lin hd h Ir1 Iw (1 / d.n1) 2 (-(2 * Real.log Be) / d.n1)) (fun P hP => ?_) _
      (d.hint_log_le hd htm ht0 hBt)
    have e1 := E1 P
    have le := d.hint_log_le hd hem he0 hBe P hP
    have hnp : (0 : ℝ) < d.n1 := by linarith
    have : ∀ x y : ℝ, 1 / (d.n1 : ℝ) * x + 2 * y + -(2 * Real.log Be) / d.n1 =
        (x + 2 * d.n1 * y - 2 * Real.log Be) / d.n1 := by
      intro x y; field_simp; ring
    rw [this, div_le_iff₀ hnp]
    nlinarith

  obtain ⟨hwqm, hwq0, hwql⟩ := d.hint_pow hd hwm hw0 (d.D + 4) (by omega)
  have hW2 : d.wF + d.G2 = (d.D + 4) • d.wL := by rw [Data.G2]; abel
  have hf2m : d.thp k c * d.ta2 c ∈ 𝒜 c ((d.D + 4) • d.wL) := by
    rw [← hW2]; exact SetLike.mul_mem_graded hhm h2m
  have hf20 := hd.mul_ne_zero c hhm h2m hk h20
  have Ir2 : d.HintIS c sg (fun P => Real.log ‖P (ratio (Ω := Ω c) (d.thp k c * d.ta2 c)
      (d.w (d.jc c) c ^ (d.D + 4)))‖) :=
    d.hint_intNorm hd h c sg _ (hint_ratio_ne hd hwqm hwq0 hf2m hf20)
  have E2 : ∀ P, Real.log (d.nrm c d.wF (d.thp k c) P) + Real.log (d.nrm c d.G2 (d.ta2 c) P) =
      Real.log ‖P (ratio (Ω := Ω c) (d.thp k c * d.ta2 c) (d.w (d.jc c) c ^ (d.D + 4)))‖ +
        ((d.D + 4 : ℕ) : ℝ) * Real.log (d.nrm c d.wL (d.w (d.jc c) c) P) := by
    intro P
    have h1 := d.hint_log_mul hd hhm h2m hk h20 P
    rw [hW2] at h1
    have h2 := d.hint_log_line hd hwqm hwq0 hf2m hf20 P
    rw [hwql] at h2
    linarith
  refine ⟨Iet, Iw, It1, ⟨d.thp k c, hhm, hk, ?_⟩, ?_⟩
  · refine d.hintIS_bounds hd h (d.hint_meas hd c sg hhm hk)
      (d.hintIS_lin hd h Ir2 Iw 1 ((d.D + 4 : ℕ) : ℝ) (-Real.log B2)) (fun P hP => ?_) _
      (d.hint_log_le hd hhm hk hBh)
    have e2 := E2 P
    have l2 := d.hint_log_le hd h2m h20 hB2 P hP
    linarith
  · refine d.hintIS_bounds hd h (d.hint_meas hd c sg h2m h20)
      (d.hintIS_lin hd h Ir2 Iw 1 ((d.D + 4 : ℕ) : ℝ) (-Real.log Bh)) (fun P hP => ?_) _
      (d.hint_log_le hd h2m h20 hB2)
    have e2 := E2 P
    have l2 := d.hint_log_le hd hhm hk hBh P hP
    linarith

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end
