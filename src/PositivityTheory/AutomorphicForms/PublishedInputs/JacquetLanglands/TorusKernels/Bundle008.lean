module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula
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
public import Mathlib.MeasureTheory.Integral.Pi
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

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.ActionsPreserveMeasuresLemmas

open UpperTheory.Esk

theorem count_pres {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α] (f : α → α)
    (hf : Function.Bijective f) : MeasurePreserving f Measure.count Measure.count := by
  refine ⟨measurable_of_countable f, ?_⟩
  ext s hs
  rw [Measure.map_apply (measurable_of_countable f) hs, Measure.count_apply hs,
    Measure.count_apply ((Set.to_countable _).measurableSet)]
  congr 1
  exact Set.encard_preimage_of_injective_subset_range hf.1 (hf.2.range_eq ▸ Set.subset_univ s)

theorem countable_PG (F : Type) [Field F] [Countable F] : Countable (PG F) := by
  have : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  have : Countable (GL (Fin 2) F) :=
    Function.Injective.countable (f := fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) fun a b h => Units.ext h
  exact QuotientGroup.mk_surjective.countable

theorem smulX {F I Gf : Type} [Field F] [Group Gf] (D : Dat F I Gf) (g : GL (Fin 2) F) (z : D.Xs) :
    ((g : PG F) • z) = (fun v => D.r v g • z v : I → P) := rfl

end UpperTheory.Esk.ActionsPreserveMeasuresLemmas

open UpperTheory.Esk.ActionsPreserveMeasuresLemmas in
theorem UpperTheory.Esk.actions_preserve_measures_proof : UpperTheory.Esk.B1a → UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.E0a := by
  intro h1 h2 h3 F I Gf _ _ _ D ax
  have : SigmaFinite (volume : Measure P) := h1.1
  have : (volume : Measure P).IsOpenPosMeasure := h1.2.1
  have : Countable F := ax.cF
  have hPG : Countable (PG F) := countable_PG F
  have : Countable D.Om := ax.cO
  have : Countable D.Cj := hPG
  have hXs : SigmaFinite (volume : Measure D.Xs) :=
    show SigmaFinite (Measure.pi fun _ : I => (volume : Measure P)) from inferInstance
  have presX : ∀ γ : PG F, MeasurePreserving (fun z : D.Xs => γ • z) volume volume := by
    intro γ
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective γ
    simp only [smulX]
    exact measurePreserving_pi (fun _ : I => (volume : Measure P)) (fun _ : I => (volume : Measure P))
      (fun v => (h1.2.2 (D.r v g)).2)
  have contX : ∀ γ : PG F, Continuous fun z : D.Xs => γ • z := by
    intro γ
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective γ
    simp only [smulX]
    exact continuous_pi fun v => (h1.2.2 (D.r v g)).1.comp (continuous_apply v)
  refine ⟨hPG, hXs, presX, ?_, ?_, contX, inferInstanceAs (BorelSpace (I → P)), ?_⟩
  · intro γ
    exact (count_pres (fun ω : D.Om => γ • ω) (MulAction.bijective γ)).prod (presX γ)
  · intro γ
    exact (count_pres (fun ω : D.Cj × D.Om => γ • ω) (MulAction.bijective γ)).prod (presX γ)
  · intro δ hδ
    have hk : Continuous fun p : P × P => kap p.1 p.2 := h3.2.2.2.2.1
    have hk1 : ∀ z : P, Continuous fun w => kap z w := fun z => hk.comp (continuous_const.prodMk continuous_id)
    set U : Set P := {w | δ < kap iP w} with hU
    have hUo : IsOpen U := isOpen_lt continuous_const (hk1 iP)
    have hUp : 0 < volume U := hUo.measure_pos volume ⟨iP, by
      show δ < kap iP iP
      rw [h3.2.1 iP]; exact hδ⟩
    obtain ⟨c0, hc0, hc0U⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hUp
    have hS : ∀ z : P, MeasurableSet {w | δ ≤ kap z w} := fun z =>
      measurableSet_le measurable_const (hk1 z).measurable
    have hball : ∀ z : P, (c0 : ℝ≥0∞) ≤ volume {w | δ ≤ kap z w} := by
      intro z
      obtain ⟨g, -, -, hg⟩ := h3.2.2.2.2.2 z
      have hf := (h1.2.2 g).2
      have hpre : (fun w : P => g • w) ⁻¹' {w | δ ≤ kap z w} = {w | δ ≤ kap iP w} := by
        ext w
        show δ ≤ kap z (g • w) ↔ δ ≤ kap iP w
        rw [← hg, h2.2.2.2.1 g iP w]
      rw [← hf.measure_preimage (hS z).nullMeasurableSet, hpre]
      refine hc0U.le.trans (measure_mono fun w hw => ?_)
      exact le_of_lt (show δ < kap iP w from hw)
    refine ⟨c0 ^ Fintype.card I, pow_pos (by exact_mod_cast hc0) _, fun z => ?_⟩
    have hset : {w : X I | Near δ z w} = Set.univ.pi fun v => {w | δ ≤ kap (z v) w} := by
      ext w
      simp [Near, Set.mem_pi]
    rw [hset]
    refine ⟨MeasurableSet.univ_pi fun v => hS (z v), ?_⟩
    rw [volume_pi, Measure.pi_pi, ENNReal.coe_pow, ← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod' fun v _ => hball (z v)
end
end

section

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.EllipticTermsContribution

open UpperTheory.Esk

theorem mk_out {F : Type} [Field F] (q : PG F) : ((q.out : GL (Fin 2) F) : PG F) = q := Quotient.out_eq' q

theorem elliptic_lower_left_ne_zero (h : GL (Fin 2) ℝ) (hh : h.val.trace ^ 2 < 4 * h.val.det) : h 1 0 ≠ 0 := by
  intro e
  rw [Matrix.trace_fin_two, det_eq, e] at hh
  nlinarith [sq_nonneg (h 0 0 - h 1 1)]

def disc (h : GL (Fin 2) ℝ) : ℝ := 4 * h.val.det - h.val.trace ^ 2

def fpC (h : GL (Fin 2) ℝ) : ℂ :=
  (((h 0 0 - h 1 1) / (2 * h 1 0) : ℝ) : ℂ) + Complex.I * ((Real.sqrt (disc h) / (2 * h 1 0) : ℝ) : ℂ)

theorem fpC_im (h : GL (Fin 2) ℝ) (hh : h.val.trace ^ 2 < 4 * h.val.det) : (fpC h).im ≠ 0 := by
  have hr := elliptic_lower_left_ne_zero h hh
  have hd : 0 < disc h := by unfold disc; linarith
  simp only [fpC, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, zero_mul, one_mul, zero_add]
  exact div_ne_zero (Real.sqrt_pos.2 hd).ne' (mul_ne_zero two_ne_zero hr)

def fp (h : GL (Fin 2) ℝ) (hh : h.val.trace ^ 2 < 4 * h.val.det) : P := ⟨fpC h, fpC_im h hh⟩

theorem fp_eq (h : GL (Fin 2) ℝ) (hh : h.val.trace ^ 2 < 4 * h.val.det) :
    ((h 1 0 : ℝ) : ℂ) * fpC h ^ 2 + (((h 1 1 : ℝ) : ℂ) - ((h 0 0 : ℝ) : ℂ)) * fpC h - ((h 0 1 : ℝ) : ℂ) = 0 := by
  have hr := elliptic_lower_left_ne_zero h hh
  have hd : 0 < disc h := by unfold disc; linarith
  have hr' : ((h 1 0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr
  have hs : ((Real.sqrt (disc h) : ℝ) : ℂ) ^ 2 = ((disc h : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hd.le]
  have hD : ((disc h : ℝ) : ℂ) = 4 * (((h 0 0 : ℝ) : ℂ) * ((h 1 1 : ℝ) : ℂ) - ((h 0 1 : ℝ) : ℂ) * ((h 1 0 : ℝ) : ℂ))
      - (((h 0 0 : ℝ) : ℂ) + ((h 1 1 : ℝ) : ℂ)) ^ 2 := by
    simp only [disc, Matrix.trace_fin_two, det_eq]; push_cast; ring
  have hz : 2 * ((h 1 0 : ℝ) : ℂ) * fpC h = (((h 0 0 : ℝ) : ℂ) - ((h 1 1 : ℝ) : ℂ)) + Complex.I * ((Real.sqrt (disc h) : ℝ) : ℂ) := by
    simp only [fpC]; push_cast; field_simp
  have h4 : (4 * ((h 1 0 : ℝ) : ℂ)) * (((h 1 0 : ℝ) : ℂ) * fpC h ^ 2 + (((h 1 1 : ℝ) : ℂ) - ((h 0 0 : ℝ) : ℂ)) * fpC h - ((h 0 1 : ℝ) : ℂ)) = 0 := by
    rw [show (4 * ((h 1 0 : ℝ) : ℂ)) * (((h 1 0 : ℝ) : ℂ) * fpC h ^ 2 + (((h 1 1 : ℝ) : ℂ) - ((h 0 0 : ℝ) : ℂ)) * fpC h - ((h 0 1 : ℝ) : ℂ))
      = (2 * ((h 1 0 : ℝ) : ℂ) * fpC h) ^ 2 + 2 * (((h 1 1 : ℝ) : ℂ) - ((h 0 0 : ℝ) : ℂ)) * (2 * ((h 1 0 : ℝ) : ℂ) * fpC h)
        - 4 * ((h 1 0 : ℝ) : ℂ) * ((h 0 1 : ℝ) : ℂ) by ring, hz]
    linear_combination ((Real.sqrt (disc h) : ℝ) : ℂ) ^ 2 * Complex.I_sq - hs - hD
  rcases mul_eq_zero.1 h4 with h5 | h5
  · exact absurd h5 (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) hr')
  · exact h5

theorem fix_comm (h g : GL (Fin 2) ℝ) (hh : h.val.trace ^ 2 < 4 * h.val.det) (hc : g * h = h * g) :
    g • fp h hh = fp h hh := by
  have hr := elliptic_lower_left_ne_zero h hh
  have hr' : ((h 1 0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr
  have e00 := congrArg (fun M : GL (Fin 2) ℝ => M 0 0) hc
  have e10 := congrArg (fun M : GL (Fin 2) ℝ => M 1 0) hc
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two] at e00 e10
  have e00' : ((g 0 0 : ℝ) : ℂ) * ((h 0 0 : ℝ) : ℂ) + ((g 0 1 : ℝ) : ℂ) * ((h 1 0 : ℝ) : ℂ)
      = ((h 0 0 : ℝ) : ℂ) * ((g 0 0 : ℝ) : ℂ) + ((h 0 1 : ℝ) : ℂ) * ((g 1 0 : ℝ) : ℂ) := by exact_mod_cast e00
  have e10' : ((g 1 0 : ℝ) : ℂ) * ((h 0 0 : ℝ) : ℂ) + ((g 1 1 : ℝ) : ℂ) * ((h 1 0 : ℝ) : ℂ)
      = ((h 1 0 : ℝ) : ℂ) * ((g 0 0 : ℝ) : ℂ) + ((h 1 1 : ℝ) : ℂ) * ((g 1 0 : ℝ) : ℂ) := by exact_mod_cast e10
  have hQ := fp_eq h hh
  apply Subtype.ext
  rw [coe_smul, div_eq_iff (den_ne g (fp h hh).2)]
  apply mul_left_cancel₀ hr'
  change ((h 1 0 : ℝ) : ℂ) * (((g 0 0 : ℝ) : ℂ) * fpC h + ((g 0 1 : ℝ) : ℂ))
    = ((h 1 0 : ℝ) : ℂ) * (fpC h * (((g 1 0 : ℝ) : ℂ) * fpC h + ((g 1 1 : ℝ) : ℂ)))
  linear_combination e00' - fpC h * e10' - ((g 1 0 : ℝ) : ℂ) * hQ

theorem tr_r {F I Gf : Type} [Field F] [Group Gf] (D : Dat F I Gf) (v : I) (g : GL (Fin 2) F) :
    (D.r v g).val.trace = D.σ v g.val.trace := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two, map_add (f := _)]; rfl

theorem det_r {F I Gf : Type} [Field F] [Group Gf] (D : Dat F I Gf) (v : I) (g : GL (Fin 2) F) :
    (D.r v g).val.det = D.σ v g.val.det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two, map_sub, map_mul, map_mul]; rfl

end UpperTheory.Esk.EllipticTermsContribution

open UpperTheory.Esk.EllipticTermsContribution in
theorem UpperTheory.Esk.elliptic_terms_contribution_proof : UpperTheory.Esk.B1a → UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.B4 → UpperTheory.Esk.C1 → UpperTheory.Esk.E0a → UpperTheory.Esk.KernelTermsInvariantBounded → UpperTheory.Esk.E0d → UpperTheory.Esk.Mult → UpperTheory.Esk.Fcen → UpperTheory.Esk.F3 := by
  intro hB1a _ hB1c hB4 hC1 hE0a hE0c _ hMult hFcen F I Gf ι _ _ _ _ D k a hyp γ ω hT hTe
  have : SigmaFinite (volume : Measure P) := hB1a.1
  obtain ⟨_, c2, c3, _, c5, c6⟩ := hE0c F I Gf ι D k a hyp
  have htr : γ.out.val.trace ≠ 0 := by
    obtain ⟨i, hi⟩ := c5 γ ω hTe
    exact (c6 γ ω i hi).1
  have hTv : ∀ v, (D.r v γ.out).val.trace ^ 2 < 4 * (D.r v γ.out).val.det := fun v => by
    rw [tr_r, det_r]; exact hT v
  let z0 : D.Xs := fun v => fp (D.r v γ.out) (hTv v)
  set S := MulAction.stabilizer (PG F) ((γ, ω) : D.Cj × D.Om) with hS
  have memS : ∀ g : PG F, g ∈ S → g * γ * g⁻¹ = γ ∧ g • ω = ω := by
    intro g hg
    rw [hS, MulAction.mem_stabilizer_iff] at hg
    exact ⟨congrArg Prod.fst hg, congrArg Prod.snd hg⟩
  have fixS : ∀ g : PG F, g ∈ S → g • z0 = z0 := by
    intro g hg
    obtain ⟨h1, -⟩ := memS g hg
    have hc : g.out * γ.out = γ.out * g.out := by
      apply hFcen F γ.out g.out htr
      rw [mk_out, mk_out]; exact h1
    rw [← mk_out g, Dat.mk_smulX]
    funext v
    exact fix_comm _ _ (hTv v) (by rw [← map_mul, ← map_mul, hc])
  obtain ⟨c₀, hc₀, hmink⟩ := hyp.ax.mink
  obtain ⟨s, hs, hsc⟩ := hmink z0 (D.rep ω)
  obtain ⟨C, hC⟩ := hMult F I Gf D hyp.ax 1 c₀ one_pos hc₀
  have hfin := (hC (ω, z0) s hs hsc).1
  have hSfin : (S : Set (PG F)).Finite := hfin.subset fun g hg => ⟨(memS g hg).2, fun v => by
      show 1 ≤ kap (z0 v) ((g • z0 : D.Xs) v)
      rw [fixS g hg, hB1c.2.1]⟩
  have hSF : Finite S := hSfin.to_subtype
  refine ⟨hSF, fun β hβ => ?_⟩
  let f : I → P → ℂ := fun v w => q1 (k v) w (D.r v γ.out • w) * j1 (k v) (D.r v γ.out) w
  have hu : ∀ z : D.Xs, D.kk k a γ (ω, z) = D.Te a γ.out (D.rep ω) * ∏ v, f v (z v) := by
    intro z
    show D.Te a γ.out (D.rep ω) * (qq k z (D.act γ.out z) * D.J k γ.out z) =
      D.Te a γ.out (D.rep ω) * ∏ v, (q1 (k v) (z v) (D.r v γ.out • z v) * j1 (k v) (D.r v γ.out) (z v))
    rw [Finset.prod_mul_distrib]; rfl
  have hint : Integrable (fun z : D.Xs => ∏ v, f v (z v)) :=
    Integrable.fintype_prod (f := f) (μ := fun _ => volume) fun v => (hB4 (k v) (hyp.four v) _ (hTv v)).1
  have hval : ∫ z : D.Xs, ∏ v, f v (z v) = D.orb k γ.out := by
    rw [show (∫ z : D.Xs, ∏ v, f v (z v)) = ∫ z : I → P, ∏ v, f v (z v) ∂(Measure.pi fun _ => volume) from rfl,
      integral_fintype_prod_eq_prod]
    unfold Dat.orb
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [(hB4 (k v) (hyp.four v) _ (hTv v)).2, tr_r, det_r]
  haveI : Fintype S := Fintype.ofFinite S
  have hcard : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos_iff.2 ⟨1⟩
  let c : ℝ := (Fintype.card S : ℝ)⁻¹
  have hcut : IsCut S (fun _ : D.Xs => c) := ⟨measurable_const, fun _ => inv_nonneg.2 hcard.le, fun _ => by
      have e : ∑ _ : S, c = 1 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hcard.ne']
      rw [← e]; exact hasSum_fintype _⟩
  have hP : Pres S (volume : Measure D.Xs) := fun g => (hE0a F I Gf D hyp.ax).2.2.1 (g : PG F)
  have hinv : ∀ (g : S) (z : D.Xs), D.kk k a γ (ω, g • z) = D.kk k a γ (ω, z) := by
    intro g z
    obtain ⟨h1, h2⟩ := memS g g.2
    have := c2 g γ (ω, z)
    have e : (g : PG F) • ((ω, z) : D.Y) = (ω, g • z) := Prod.ext h2 rfl
    rw [h1, e] at this
    exact this
  have hmeas : Measurable (fun z : D.Xs => D.kk k a γ (ω, z)) := (c3 γ).comp measurable_prodMk_left
  have hintc : Integrable (fun z : D.Xs => c • D.kk k a γ (ω, z)) := by
    rw [show (fun z : D.Xs => c • D.kk k a γ (ω, z)) = fun z => c • (D.Te a γ.out (D.rep ω) * ∏ v, f v (z v)) from
      funext fun z => by rw [hu]]
    exact (hint.const_mul _).smul c
  obtain ⟨-, heq⟩ := (hC1 (↥S) D.Xs volume hP (fun _ => c) β hcut hβ).2 _ hmeas hinv hintc
  rw [← heq]
  simp_rw [hu]
  rw [integral_smul, integral_const_mul, hval, Nat.card_eq_fintype_card, Complex.real_smul]
  simp only [c, Complex.ofReal_inv, Complex.ofReal_natCast]
end
end

section

noncomputable section

open MeasureTheory Matrix

namespace UpperTheory.Esk.ExponentialSlopeDerivatives

variable {F I Gf : Type} [Field F] [Group Gf] (D : Dat F I Gf)

def A (δ : ℝ) (y : D.Y) : Set (PG F) := {γ : PG F | γ • y.1 = y.1 ∧ Near δ y.2 (γ • y.2 : D.Xs)}

theorem near_smul (hB : B1b) (δ : ℝ) (g : PG F) (z w : D.Xs) :
    Near δ (g • z : D.Xs) (g • w : D.Xs) ↔ Near δ z w := by
  induction g using QuotientGroup.induction_on with
  | H γ =>
    rw [Dat.mk_smulX D γ z, Dat.mk_smulX D γ w]
    simp only [Near, Dat.act, hB.2.2.2.1]

theorem mem_conj (hB : B1b) (δ : ℝ) (g γ : PG F) (y : D.Y) :
    g * γ * g⁻¹ ∈ A D δ (g • y) ↔ γ ∈ A D δ y := by
  simp only [A, Set.mem_setOf_eq, Prod.smul_fst, Prod.smul_snd, mul_smul, inv_smul_smul,
    smul_left_cancel_iff, near_smul D hB]

theorem A_conj (hB : B1b) (δ : ℝ) (g : PG F) (y : D.Y) :
    A D δ (g • y) = (fun γ => g * γ * g⁻¹) '' A D δ y := by
  ext γ'
  constructor
  · intro h
    refine ⟨g⁻¹ * γ' * g, (mem_conj D hB δ g _ y).1 ?_, ?_⟩
    · rwa [show g * (g⁻¹ * γ' * g) * g⁻¹ = γ' by group]
    · show g * (g⁻¹ * γ' * g) * g⁻¹ = γ'
      group
  · rintro ⟨γ, hγ, rfl⟩
    exact (mem_conj D hB δ g γ y).2 hγ

theorem conj_inj (g : PG F) : Function.Injective (fun γ : PG F => g * γ * g⁻¹) := by
  intro a b h
  simpa using h

theorem fin_card (hB : B1b) (δ : ℝ) (g : PG F) (y : D.Y) :
    ((A D δ (g • y)).Finite ↔ (A D δ y).Finite) ∧ (A D δ (g • y)).ncard = (A D δ y).ncard := by
  rw [A_conj D hB δ g y]
  exact ⟨Set.finite_image_iff (conj_inj g).injOn, Set.ncard_image_of_injective _ (conj_inj g)⟩

theorem e01 : (![0, 1] : Fin 2 → F) ≠ 0 := by
  intro h
  have := congrFun h 1
  simp at this

theorem Ht01 [Fintype I] (z : X I) (x : Gf) : D.Ht ![0, 1] z x = (∏ v, |(z v).1.im|) * D.hf ![0, 1] x := by
  simp [Dat.Ht]

end UpperTheory.Esk.ExponentialSlopeDerivatives

open UpperTheory.Esk UpperTheory.Esk.ExponentialSlopeDerivatives

theorem UpperTheory.Esk.pf_Mult : UpperTheory.Esk.B1b → UpperTheory.Esk.E0d → UpperTheory.Esk.Mult := by
  intro hB hE F I Gf _ _ _ D hD δ c₀ hδ hc₀
  obtain ⟨-, h2, h3, -, -, -, -, -, -, h10, -⟩ := hE F I Gf D hD
  obtain ⟨S, C, c, hc, hnorm⟩ := hD.normal c₀ hc₀
  have hcnt : ∀ x' : Gf, ∃ C' : ℝ, ∀ z : D.Xs, Sg C c z →
      (A D δ (((x' : Gf ⧸ D.H), z) : D.Om × D.Xs)).Finite ∧
      ((A D δ (((x' : Gf ⧸ D.H), z) : D.Om × D.Xs)).ncard : ℝ) ≤ C' * (1 + ∏ v, |(z v).1.im|) :=
    fun x' => hD.count ((x' : Gf ⧸ D.H)) δ C c hδ hc
  choose C' hC' using hcnt
  have hapos : ∀ x : Gf, 0 < D.hf ![0, 1] (D.rep ((x : Gf ⧸ D.H))) := fun x => hD.pos _ e01 _
  have final : ∀ (N Cx P a H K : ℝ), N ≤ Cx * (1 + P) → 0 ≤ P → P * a = H → 0 < a → 0 ≤ H →
      max Cx 0 * (1 + 1 / a) ≤ K → N ≤ K * (1 + H) := by
    intro N Cx P a H K hN hP hPa ha hH hK
    have hP' : P = H / a := eq_div_of_mul_eq ha.ne' hPa
    have h1 : N ≤ max Cx 0 * (1 + P) :=
      hN.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
    have h2 : 1 + P ≤ (1 + 1 / a) * (1 + H) := by
      rw [hP']
      have h0 : 0 ≤ 1 / a := by positivity
      have he : (1 + 1 / a) * (1 + H) - (1 + H / a) = H + 1 / a := by ring
      linarith
    have hM : 0 ≤ max Cx 0 := le_max_right _ _
    calc N ≤ max Cx 0 * (1 + P) := h1
      _ ≤ max Cx 0 * ((1 + 1 / a) * (1 + H)) := mul_le_mul_of_nonneg_left h2 hM
      _ = (max Cx 0 * (1 + 1 / a)) * (1 + H) := by ring
      _ ≤ K * (1 + H) := mul_le_mul_of_nonneg_right hK (by linarith)
  refine ⟨∑ x ∈ S, max (C' x) 0 * (1 + 1 / D.hf ![0, 1] (D.rep ((x : Gf ⧸ D.H)))), ?_⟩
  intro y s hs hy
  obtain ⟨γ₀, hγ₀⟩ := h10 s hs
  have e1 : D.HtY ![0, 1] ((γ₀ : PG F) • y) = D.HtY s y := by
    rw [h2 _ e01 γ₀ y, hγ₀]
  have hn : c₀ ≤ D.Ht ![0, 1] ((γ₀ : PG F) • y).2 (D.rep ((γ₀ : PG F) • y).1) := by
    rw [← e1] at hy
    exact hy
  obtain ⟨b, hb10, ⟨x', hx'S, h, hh, hbx⟩, hsg⟩ := hnorm _ _ hn
  have hb11 : b.val 1 1 ≠ 0 := by
    intro h0
    apply b.det_ne_zero
    rw [Matrix.det_fin_two]
    simp [h0, hb10]
  have hvb : ![0, 1] ᵥ* b.val = b.val 1 1 • ![(0 : F), 1] := by
    ext i
    fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, hb10]
  have hsm : ∀ ω : D.Om, (b : PG F) • ω = (((D.j b * D.rep ω : Gf) : Gf ⧸ D.H) : D.Om) := by
    intro ω
    conv_lhs => rw [← QuotientGroup.out_eq' ω]
    rfl
  have hy'' : (b : PG F) • ((γ₀ : PG F) • y) =
      (((x' : Gf ⧸ D.H), D.act b ((γ₀ : PG F) • y).2) : D.Om × D.Xs) := by
    refine Prod.ext ?_ (D.mk_smulX b _)
    show (b : PG F) • ((γ₀ : PG F) • y).1 = _
    rw [hsm, hbx]
    exact QuotientGroup.eq.2 (by simpa using hh)
  obtain ⟨f1, c1⟩ := fin_card D hB δ (γ₀ : PG F) y
  obtain ⟨f2, c2⟩ := fin_card D hB δ (b : PG F) ((γ₀ : PG F) • y)
  rw [hy''] at f2 c2
  obtain ⟨hfin, hle⟩ := hC' x' _ hsg
  refine ⟨f1.1 (f2.1 hfin), ?_⟩
  have hHt : D.HtY ![0, 1] (((x' : Gf ⧸ D.H), D.act b ((γ₀ : PG F) • y).2) : D.Om × D.Xs) = D.HtY s y := by
    rw [← hy'', h2 _ e01 b _, hvb, h3 _ e01 _ hb11, e1]
  have hP : D.HtY ![0, 1] (((x' : Gf ⧸ D.H), D.act b ((γ₀ : PG F) • y).2) : D.Om × D.Xs)
      = (∏ v, |((D.act b ((γ₀ : PG F) • y).2) v).1.im|) * D.hf ![0, 1] (D.rep ((x' : Gf ⧸ D.H))) :=
    Ht01 D (D.act b ((γ₀ : PG F) • y).2) (D.rep ((x' : Gf ⧸ D.H)))
  have hH : 0 ≤ D.HtY s y := by linarith
  show ((A D δ y).ncard : ℝ) ≤ _
  rw [← c1, ← c2]
  exact final _ _ _ _ _ _ hle (Finset.prod_nonneg fun v _ => abs_nonneg _) (hP.symm.trans hHt) (hapos x') hH
    (Finset.single_le_sum (f := fun x => max (C' x) 0 * (1 + 1 / D.hf ![0, 1] (D.rep ((x : Gf ⧸ D.H)))))
      (fun x _ => mul_nonneg (le_max_right _ _) (add_nonneg zero_le_one (one_div_nonneg.2 (hapos x).le))) hx'S)
end
end

section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

theorem UpperTheory.Esk.pf_KapSum : UpperTheory.Esk.Pack → UpperTheory.Esk.Mult → UpperTheory.Esk.KapInt → UpperTheory.Esk.KapSum := by
  intro hPack hMult hKap F I Gf _ _ _ D hD k hk c₀ hc₀
  obtain ⟨C₁, hC₁⟩ := hPack F I Gf D hD
  obtain ⟨C₃, A₃, hK⟩ := hKap I k hk
  obtain ⟨C₂, hC₂⟩ := hMult F I Gf D hD (1 / 16) c₀ (by norm_num) hc₀
  refine ⟨(C₁ : ℝ) * A₃ * max C₂ 0 * C₃, ?_⟩
  intro y s hs hy ω' z
  obtain ⟨hfin, hcard⟩ := hC₂ y s hs hy
  obtain ⟨hmeas, hint, -, hnear⟩ := hK z
  have hpos : 0 ≤ 1 + D.HtY s y := by linarith
  have key : ∀ n : ℕ, (n : ℝ) ≤ C₂ * (1 + D.HtY s y) →
      (n : ℝ≥0∞) ≤ ENNReal.ofReal (max C₂ 0 * (1 + D.HtY s y)) := by
    intro n hn
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (hn.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpos))
  have hA : ∀ w w' : D.Xs, Near (1 / 2) w w' →
      ENNReal.ofReal (Kap k z w) ≤ (A₃ : ℝ≥0∞) * ENNReal.ofReal (Kap k z w') := by
    intro w w' hww
    calc ENNReal.ofReal (Kap k z w) ≤ ENNReal.ofReal (A₃ * Kap k z w') :=
          ENNReal.ofReal_le_ofReal (hnear w w' hww).1
      _ = (A₃ : ℝ≥0∞) * ENNReal.ofReal (Kap k z w') := by
          rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
  have hpack := hC₁ y ω' (fun w => ENNReal.ofReal (Kap k z w)) A₃
    (ENNReal.measurable_ofReal.comp hmeas) hA hfin
  refine hpack.trans ((mul_le_mul' (mul_le_mul' le_rfl (key _ hcard)) hint).trans (le_of_eq ?_))
  rw [show (C₁ : ℝ) * A₃ * max C₂ 0 * C₃ * (1 + D.HtY s y)
      = ((C₁ * A₃ * C₃ : ℝ≥0) : ℝ) * (max C₂ 0 * (1 + D.HtY s y)) by push_cast; ring,
    ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
  push_cast
  ring
end
end
