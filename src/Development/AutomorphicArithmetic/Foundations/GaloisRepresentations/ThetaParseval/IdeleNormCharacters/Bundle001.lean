module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.AbsFactsAlt
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.TwistSatHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.AdelicU

namespace UpperTheory.Gal.TP.Chr

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private lemma exists_ext (τ : E →+* ℂ) :
    ∃ e : (InfinitePlace.mk τ).Completion → ℂ, Continuous e ∧ Function.Surjective e ∧
      ∀ x : E, e (algebraMap E _ x) = τ x := by
  have hs := InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex
    (IsTotallyComplex.isComplex (InfinitePlace.mk τ))
  have hc : Continuous (InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk τ)) :=
    (InfinitePlace.Completion.isometry_extensionEmbedding _).continuous
  have hv : ∀ x : E, InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk τ)
      (algebraMap E _ x) = (InfinitePlace.mk τ).embedding x := fun x => by
    simpa [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply] using
      InfinitePlace.Completion.extensionEmbedding_coe _ (WithAbs.toAbs _ x)
  rcases InfinitePlace.embedding_mk_eq τ with h | h
  · exact ⟨_, hc, hs, fun x => by rw [hv, h]⟩
  · refine ⟨fun z => starRingEnd ℂ (InfinitePlace.Completion.extensionEmbedding _ z),
      Complex.continuous_conj.comp hc, fun y => ?_, fun x => ?_⟩
    · obtain ⟨z, hz⟩ := hs (starRingEnd ℂ y)
      exact ⟨z, by simp [hz]⟩
    · simp only [hv, h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]

private lemma dense_emb (emb : ∀ w : InfinitePlace (maximalRealSubfield E), EmbOver E w) :
    DenseRange (fun (x : E) (w : InfinitePlace (maximalRealSubfield E)) => (emb w).1 x) := by
  classical
  have key : ∀ w, (InfinitePlace.mk (emb w).1).comap (algebraMap (maximalRealSubfield E) E) = w := by
    intro w
    rw [InfinitePlace.comap_mk, (emb w).2, InfinitePlace.mk_embedding]
  have hinj : ∀ w w', InfinitePlace.mk (emb w).1 = InfinitePlace.mk (emb w').1 → w = w' := by
    intro w w' h
    rw [← key w, ← key w', h]
  choose e hc hs he using fun w => exists_ext (emb w).1
  let T : (∀ v : InfinitePlace E, v.Completion) → (∀ _ : InfinitePlace (maximalRealSubfield E), ℂ) :=
    fun f w => e w (f (InfinitePlace.mk (emb w).1))
  have hT : Continuous T := continuous_pi fun w => (hc w).comp (continuous_apply _)
  have hTs : Function.Surjective T := by
    intro y
    choose g hg using fun w => hs w (y w)
    have hcast : ∀ w w' (h : InfinitePlace.mk (emb w').1 = InfinitePlace.mk (emb w).1),
        (h ▸ g w' : (InfinitePlace.mk (emb w).1).Completion) = g w := by
      intro w w' h
      obtain rfl := hinj _ _ h
      rfl
    refine ⟨fun v => if h : ∃ w, InfinitePlace.mk (emb w).1 = v then h.choose_spec ▸ g h.choose else 0, ?_⟩
    funext w
    have hex : ∃ w', InfinitePlace.mk (emb w').1 = InfinitePlace.mk (emb w).1 := ⟨w, rfl⟩
    simp only [T, dif_pos hex]
    rw [hcast w _ hex.choose_spec, hg]
  have hd := hTs.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap E) hT
  convert hd using 1
  funext x w
  exact (he w x).symm

end

theorem expInj : ExpInj := by
  intro E _ _ _ emb m m' s s' h
  classical
  funext w₀
  let F : (InfinitePlace (maximalRealSubfield E) → ℤ) → ℤ →
      (InfinitePlace (maximalRealSubfield E) → ℂ) → ℂ :=
    fun n t y => ∏ w, (y w / ‖y w‖) ^ n w * ((‖y w‖ : ℝ) : ℂ) ^ t
  let U : Set (InfinitePlace (maximalRealSubfield E) → ℂ) := {y | ∀ w, y w ≠ 0}
  have hU : IsOpen U := by
    simp only [U, Set.setOf_forall]
    exact isOpen_iInter_of_finite fun w => isOpen_ne_fun (continuous_apply w) continuous_const
  have hcont : ∀ n t, ContinuousOn (F n t) U := by
    intro n t
    refine continuousOn_finsetProd _ fun w _ => ?_
    have h1 : Continuous fun y : InfinitePlace (maximalRealSubfield E) → ℂ => y w := continuous_apply w
    have h2 : Continuous fun y : InfinitePlace (maximalRealSubfield E) → ℂ => ((‖y w‖ : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp h1.norm
    have hne : ∀ y ∈ U, ((‖y w‖ : ℝ) : ℂ) ≠ 0 := fun y hy => by
      simpa using hy w
    refine ContinuousOn.mul (ContinuousOn.zpow₀ (h1.continuousOn.div h2.continuousOn hne) _
      fun y hy => Or.inl (div_ne_zero (hy w) (hne y hy))) (ContinuousOn.zpow₀ h2.continuousOn _
      fun y hy => Or.inl (hne y hy))
  have hEq : ∀ y ∈ U, F m s y = F m' s' y := by
    intro y hy
    by_contra hne
    have hop := ((hcont m s).sub (hcont m' s')).isOpen_inter_preimage hU
      (isOpen_compl_singleton (x := (0 : ℂ)))
    obtain ⟨x, hxU, hx⟩ := (dense_emb emb).exists_mem_open hop
      ⟨y, hy, fun h0 => hne (sub_eq_zero.1 h0)⟩
    have hx0 : x ≠ 0 := fun h0 => hxU w₀ (by simp [h0])
    exact hx (sub_eq_zero.2 (h (Units.mk0 x hx0)))
  have hF : ∀ n t (θ : ℝ), F n t (Function.update (1 : InfinitePlace (maximalRealSubfield E) → ℂ) w₀ (Complex.exp (θ * Complex.I))) =
      Complex.exp (θ * Complex.I) ^ n w₀ := by
    intro n t θ
    simp only [F]
    rw [Finset.prod_eq_single w₀]
    · simp [Complex.norm_exp_ofReal_mul_I]
    · intro w _ hw
      simp [Function.update_of_ne hw]
    · simp
  have hUy : ∀ θ : ℝ, Function.update (1 : InfinitePlace (maximalRealSubfield E) → ℂ) w₀ (Complex.exp (θ * Complex.I)) ∈ U := by
    intro θ w
    by_cases hw : w = w₀
    · subst hw; simp [Complex.exp_ne_zero]
    · simp [Function.update_of_ne hw]
  by_contra hne
  have hd0 : ((m w₀ - m' w₀ : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.2 hne
  set θ : ℝ := Real.pi / ((m w₀ - m' w₀ : ℤ) : ℝ) with hθ
  have h1 := hEq _ (hUy θ)
  rw [hF, hF] at h1
  have h2 : Complex.exp (θ * Complex.I) ^ (m w₀ - m' w₀) = 1 := by
    rw [zpow_sub₀ (Complex.exp_ne_zero _), h1, div_self (zpow_ne_zero _ (Complex.exp_ne_zero _))]
  rw [← Complex.exp_int_mul] at h2
  have h3 : ((m w₀ - m' w₀ : ℤ) : ℂ) * (θ * Complex.I) = Real.pi * Complex.I := by
    have : ((m w₀ - m' w₀ : ℤ) : ℂ) * (θ : ℂ) = Real.pi := by
      have : ((m w₀ - m' w₀ : ℤ) : ℝ) * θ = Real.pi := by
        rw [hθ]; field_simp
      exact_mod_cast this
    rw [← mul_assoc, this]
  rw [h3, Complex.exp_pi_mul_I] at h2
  norm_num at h2

end UpperTheory.Gal.TP.Chr
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Neutral.B1 ReciprocityTheory.Gal
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.Gal.TP.Chr

private theorem pl_emb {E : Type} [Field E] [NumberField E] [IsCMField E]
    {w : InfinitePlace (maximalRealSubfield E)} (τ : EmbOver E w) : pl τ.1 = w := by
  unfold pl
  rw [InfinitePlace.comap_mk, τ.2, InfinitePlace.mk_embedding]

private theorem pl_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (φ : E →+* ℂ) :
    pl (ComplexEmbedding.conjugate φ) = pl φ := by
  unfold pl
  rw [InfinitePlace.mk_conjugate_eq]

private theorem eq_or_conj_of_pl_eq {E : Type} [Field E] [NumberField E] [IsCMField E]
    {φ ψ : E →+* ℂ} (h : pl φ = pl ψ) : φ = ψ ∨ φ = ComplexEmbedding.conjugate ψ := by
  have hmk : InfinitePlace.mk φ = InfinitePlace.mk ψ :=
    (IsCMField.equivInfinitePlace E).injective (by
      simpa only [IsCMField.equivInfinitePlace_apply, pl] using h)
  rcases InfinitePlace.mk_eq_iff.1 hmk with h' | h'
  · exact Or.inl h'
  · right
    rw [← h']
    exact (star_star φ).symm

theorem UpperTheory.Gal.TP.Chr.typProd :
    UpperTheory.Gal.TP.Chr.TypVal → UpperTheory.Gal.TP.Chr.TypProd := by
  intro hv E _ _ _ emb a b x
  classical
  rw [← Finset.prod_fiberwise Finset.univ (pl (E := E))]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hne : (emb w).1 ≠ ComplexEmbedding.conjugate (emb w).1 := fun h =>
    IsTotallyComplex.complexEmbedding_not_isReal _ (ComplexEmbedding.isReal_iff.2 h.symm)
  have hfib : Finset.univ.filter (fun φ : E →+* ℂ => pl φ = w) =
      {(emb w).1, ComplexEmbedding.conjugate (emb w).1} := by
    ext φ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro h
      exact eq_or_conj_of_pl_eq (h.trans (pl_emb (emb w)).symm)
    · rintro (rfl | rfl)
      · exact pl_emb _
      · rw [pl_conj, pl_emb]
  rw [hfib, Finset.prod_pair hne, (hv E emb a b w).1, (hv E emb a b w).2,
    ComplexEmbedding.conjugate_coe_eq]
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Neutral.B1 ReciprocityTheory.Gal
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.Gal.TP.Chr

noncomputable section

namespace UpperTheory.Gal.TP.Chr

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private def psi (μ : HChar E) (k : ℕ) (s : ℤ) : HChar E := μ ^ k * Model.absC E ((s : ℂ) / 2)

private theorem hpow_apply (μ : HChar E) (k : ℕ) (x) : (μ ^ k).1 x = μ.1 x ^ k := by
  rw [SubgroupClass.coe_pow, MonoidHom.pow_apply]

private theorem hpow_loc (μ : HChar E) (k : ℕ) (w) (x) : (μ ^ k).loc w x = μ.loc w x ^ k :=
  hpow_apply μ k _

private theorem hpow_inf (μ : HChar E) (k : ℕ) (x) : (μ ^ k).inf x = μ.inf x ^ k :=
  hpow_apply μ k _

private theorem hpow_val (μ : HChar E) (k : ℕ) (w) : (μ ^ k).val w = μ.val w ^ k :=
  hpow_apply μ k _

private theorem lc_pow (χ : Chr (maximalRealSubfield E) E) (k : ℕ) (w : HeightOneSpectrum (𝓞 E)) (x) :
    locChar (χ ^ k) w x = locChar χ w x ^ k := by
  show Circle.toUnits ((χ ^ k) (locIdele _ w x)) = Circle.toUnits (χ (locIdele _ w x)) ^ k
  rw [MonoidHom.pow_apply, map_pow]

private theorem typ_term (z : ℂ) (hz : z ≠ 0) (a b : ℤ) :
    (z / ((‖z‖ : ℝ) : ℂ)) ^ (a - b) * ((‖z‖ : ℝ) : ℂ) ^ (a + b) = z ^ a * (starRingEnd ℂ z) ^ b := by
  have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz)
  have hc : starRingEnd ℂ z = ((‖z‖ : ℝ) : ℂ) ^ 2 / z := by
    rw [eq_div_iff hz, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  have h2 : (((‖z‖ : ℝ) : ℂ) ^ 2) ^ b = (((‖z‖ : ℝ) : ℂ) ^ b) ^ 2 := by
    rw [← zpow_natCast, ← zpow_natCast, zpow_comm]
  have hA : z ^ a ≠ 0 := zpow_ne_zero _ hz
  have hB : z ^ b ≠ 0 := zpow_ne_zero _ hz
  have hC : ((‖z‖ : ℝ) : ℂ) ^ a ≠ 0 := zpow_ne_zero _ hn
  have hD : ((‖z‖ : ℝ) : ℂ) ^ b ≠ 0 := zpow_ne_zero _ hn
  rw [hc, div_zpow, div_zpow, zpow_sub₀ hz, zpow_sub₀ hn, zpow_add₀ hn, h2]
  field_simp

private theorem inf_psi (hAb : AbsFacts) (emb : ∀ w : InfinitePlace (maximalRealSubfield E), EmbOver E w)
    (μ : HChar E) (m : InfinitePlace (maximalRealSubfield E) → ℤ) (hμ : InfExp emb μ m) (k : ℕ) (s : ℤ) (x : Eˣ) :
    (((psi μ k s).inf x : ℂˣ) : ℂ) = ∏ w, ((emb w).1 (x : E) / ‖(emb w).1 (x : E)‖) ^ ((k : ℤ) * m w) *
      ((‖(emb w).1 (x : E)‖ : ℝ) : ℂ) ^ s := by
  rw [psi, HChar.inf_mul, Units.val_mul, hpow_inf, Units.val_pow_eq_pow_val, hμ x, (hAb E emb _).2 x,
    ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have h2 : (2 : ℂ) * ((s : ℂ) / 2) = s := by ring
  rw [h2, Complex.cpow_intCast, mul_comm (k : ℤ), zpow_mul, zpow_natCast]

private theorem exps {k : ℕ} {s m : ℤ} (hev : Even ((k : ℤ) + s)) (hm : Odd m) :
    ∃ a b : ℤ, (s + k * m) / 2 = a ∧ (s - k * m) / 2 = b ∧ a + b = s ∧ a - b = k * m := by
  obtain ⟨r, hr⟩ := hev
  obtain ⟨t, rfl⟩ := hm
  refine ⟨r + k * t, r - k * t - k, ?_, ?_, ?_, ?_⟩
  · rw [show s + k * (2 * t + 1) = 2 * (r + k * t) by linear_combination hr,
      Int.mul_ediv_cancel_left _ two_ne_zero]
  · rw [show s - k * (2 * t + 1) = 2 * (r - k * t - k) by linear_combination hr,
      Int.mul_ediv_cancel_left _ two_ne_zero]
  · linear_combination -hr
  · ring

end UpperTheory.Gal.TP.Chr

theorem UpperTheory.Gal.TP.Chr.chrEx :
    UpperTheory.Gal.TP.Chr.MuEmb → UpperTheory.Gal.TP.Chr.ReadEx → UpperTheory.Gal.TP.Chr.ReadLoc → UpperTheory.Gal.TP.Chr.ReadRes → UpperTheory.Gal.TP.Chr.ReadExp → UpperTheory.Gal.TP.Chr.AbsFacts → UpperTheory.Gal.TP.Chr.TypProd → UpperTheory.Gal.TP.Chr.ExpInj → UpperTheory.Gal.TP.Chr.ChrEx := by
  intro hMu hRE hRL hRR hRX hAb hTP hEI E _ _ _ hun emb w₀ m hm
  have hloc (α β : HChar E) (w : HeightOneSpectrum (𝓞 E)) (x) :
      (α * β).loc w x = α.loc w x * β.loc w x := by
    rfl
  obtain ⟨μ, hμu, hμq, hμi, hμ0⟩ := hMu E hun emb w₀ m hm
  obtain ⟨χ, hr, hH⟩ := hRE E μ hμu
  have hl := hRL E μ χ hr
  have hres := hRR E μ χ hr hμq
  have hexp := hRX E emb μ χ m hr hμi
  have hval : ∀ w, val χ w = μ.val w := fun w => by
    show locChar χ w (atFin w (unif w)) = μ.loc w (atFin w (unif w))
    rw [hl]
  refine ⟨χ, psi μ, fun x hx => ?_, fun k => ⟨⟨hH.1.pow k, fun x => ?_⟩, fun z hz => ?_, fun j hj a => ?_⟩,
    fun k s w => ⟨⟨fun h x hx => ?_, fun h x hx => ?_⟩, ?_⟩, fun k s hev x _ => ?_, fun k k' s s' h => ?_⟩
  · rw [hl]
    exact hμ0 x hx
  · rw [MonoidHom.pow_apply, hH.2 x, one_pow]
  · rw [MonoidHom.pow_apply, Circle.coe_pow, hexp z hz, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun w _ => ?_
    beta_reduce
    rw [mul_comm (k : ℤ), zpow_mul, zpow_natCast]
  · rw [MonoidHom.pow_apply, Circle.coe_pow, hres a]
    split_ifs with h
    · simp
    · rw [pow_one, neg_one_pow_eq_pow_mod_two, ← hj, ← neg_one_pow_eq_pow_mod_two]
  · have h1 : (psi μ k s).loc w x = 1 := h x hx
    rw [psi, hloc, hpow_loc, ((hAb E emb _).1 w).1 x hx, mul_one] at h1
    rw [lc_pow, hl]
    exact h1
  · have h1 : locChar (χ ^ k) w x = 1 := h x hx
    rw [lc_pow, hl] at h1
    rw [psi, hloc, hpow_loc, ((hAb E emb _).1 w).1 x hx, mul_one]
    exact h1
  · rw [psi, HChar.val_mul, Units.val_mul, hpow_val, Units.val_pow_eq_pow_val, ((hAb E emb _).1 w).2, hval, neg_div]
  · rw [hTP E emb _ _ (x : E), inf_psi hAb emb μ m hμi]
    refine Finset.prod_congr rfl fun w _ => ?_
    obtain ⟨a, b, ha, hb, h1, h2⟩ := exps hev (hm w)
    have hz : (emb w).1 (x : E) ≠ 0 := (map_ne_zero (emb w).1).2 x.ne_zero
    beta_reduce
    rw [ha, hb, ← typ_term _ hz a b, h1, h2]
  · have h1 := hEI E emb (fun w => k * m w) (fun w => k' * m w) s s' fun x => by
      rw [← inf_psi hAb emb μ m hμi k s x, ← inf_psi hAb emb μ m hμi k' s' x, h]
    obtain ⟨w⟩ : Nonempty (InfinitePlace (maximalRealSubfield E)) := inferInstance
    have h3 : (k : ℤ) * m w = k' * m w := congrFun h1 w
    have hm0 : m w ≠ 0 := fun h0 => by simpa [h0] using hm w
    exact_mod_cast mul_right_cancel₀ hm0 h3

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Neutral.B1 ReciprocityTheory.Gal
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.Gal.TP.Chr


theorem UpperTheory.Gal.TP.Chr.readEx :
    UpperTheory.Gal.TP.Chr.ReadEx := by
  intro E _ _ _ μ hU
  let e := GlobalTheory.UnitaryHeckeBaseChange.adeleEquiv (GlobalTheory.GalOfCusp.isCMExt_real E)
  let f : (AE (↥(maximalRealSubfield E)) E)ˣ →* (AdeleRing (𝓞 E) E)ˣ := Units.map (e : _ →* _)
  refine ⟨{ toFun := fun z => ⟨((μ.1 (f z) : ℂˣ) : ℂ), mem_sphere_zero_iff_norm.2 (hU (f z))⟩,
            map_one' := ?_, map_mul' := ?_ }, ?_, ?_, ?_⟩
  · apply Subtype.ext
    simp
  · intro x y
    apply Subtype.ext
    simp only [map_mul, Units.val_mul]
    rfl
  · intro z
    rfl
  · have hf : Continuous f := by
      show Continuous (Units.map (e : AE (↥(maximalRealSubfield E)) E →* AdeleRing (𝓞 E) E))
      exact Continuous.units_map _ (GlobalTheory.UnitaryHeckeBaseChange.continuous_toAdele _ E)
    have hμc : Continuous (μ.1 : Ideles E → ℂˣ) := μ.2.1
    refine continuous_induced_rng.2 ?_
    exact Units.continuous_val.comp (hμc.comp hf)
  · intro x
    apply Subtype.ext
    show ((μ.1 (f _) : ℂˣ) : ℂ) = 1
    rw [show f _ = diagUnits E x from Units.ext ?_, μ.2.2 x]
    · rfl
    · exact GlobalTheory.UnitaryHeckeBaseChange.toAdele_incA (x : E)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Neutral.B1 ReciprocityTheory.Gal
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.Gal.TP.Chr
open scoped TensorProduct

theorem UpperTheory.Gal.TP.Chr.readRes :
    UpperTheory.Gal.TP.Chr.ReadRes := by
  intro E _ _ _ μ χ hR hμ a
  rw [hR]
  have h3 : ∀ {σ : E →ₐ[↥(maximalRealSubfield E)] E} (h : HeckeCharacterZeroLocus.ThmBIn.IsCMExt (↥(maximalRealSubfield E)) E σ),
      Units.map ((GlobalTheory.UnitaryHeckeBaseChange.adeleEquiv h).toRingHom
        : AE (↥(maximalRealSubfield E)) E →* AdeleRing (𝓞 E) E)
      (Units.map (algebraMap (AF ↥(maximalRealSubfield E)) (AE (↥(maximalRealSubfield E)) E)
        : AF ↥(maximalRealSubfield E) →* AE (↥(maximalRealSubfield E)) E) a)
      = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap _ E a := fun _ =>
    Units.ext (GlobalTheory.UnitaryHeckeBaseChange.toAdele_algebraMap (a : AF ↥(maximalRealSubfield E)))
  erw [h3 (GlobalTheory.GalOfCusp.isCMExt_real E), hμ a]
  simp only [GlobalTheory.GalOfCusp.quadChar, MonoidHom.comp_apply]
  split_ifs with hm
  · obtain ⟨y, ⟨t, rfl⟩, z, hz, hyz⟩ := Subgroup.mem_sup.1 hm
    have hn : GlobalTheory.IdeleNormChar.normSign E a = 1 := by
      refine (GlobalTheory.IdeleNormChar.normSign_eq_one_iff E a).2 ⟨t, ?_⟩
      rw [← hyz]
      simpa [GlobalTheory.QuadSymbol.toUnits, GlobalTheory.QuadSymbol.normGroup] using hz
    simp [hn]
  · rcases Int.units_eq_one_or (GlobalTheory.IdeleNormChar.normSign E a) with hn | hn
    · exfalso
      obtain ⟨t, ht⟩ := (GlobalTheory.IdeleNormChar.normSign_eq_one_iff E a).1 hn
      exact hm (Subgroup.mem_sup.2 ⟨_, ⟨t, rfl⟩, _, ht, mul_div_cancel _ _⟩)
    · simp [hn]
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Neutral.B1 ReciprocityTheory.Gal
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeGal GlobalTheory.CuspRep

namespace UpperTheory.Gal.TP.Chr

private theorem pl_emb {E : Type} [Field E] [NumberField E] [IsCMField E]
    {w : InfinitePlace (maximalRealSubfield E)} (τ : EmbOver E w) : pl τ.1 = w := by
  unfold pl
  rw [InfinitePlace.comap_mk, τ.2, InfinitePlace.mk_embedding]

private theorem pl_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (φ : E →+* ℂ) :
    pl (ComplexEmbedding.conjugate φ) = pl φ := by
  unfold pl
  rw [InfinitePlace.mk_conjugate_eq]

private theorem conj_ne {E : Type} [Field E] [NumberField E] [IsCMField E] (φ : E →+* ℂ) :
    ComplexEmbedding.conjugate φ ≠ φ := fun h =>
  IsTotallyComplex.complexEmbedding_not_isReal φ (ComplexEmbedding.isReal_iff.mpr h)

theorem typVal : TypVal := by
  intro E _ _ _ emb a b w
  have h1 : pl (emb w).1 = w := pl_emb (emb w)
  have h2 : pl (ComplexEmbedding.conjugate (emb w).1) = w := (pl_conj _).trans h1
  constructor
  · unfold typ
    rw [h1]
    exact if_pos rfl
  · unfold typ
    rw [h2]
    exact if_neg (conj_ne _)

end UpperTheory.Gal.TP.Chr

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Neutral.B1 ReciprocityTheory.Gal
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.Gal.TP.Chr

private theorem symm_eq_mk {E : Type} [Field E] [NumberField E] [IsCMField E]
    (emb : ∀ w : InfinitePlace (maximalRealSubfield E), EmbOver E w)
    (w : InfinitePlace (maximalRealSubfield E)) :
    (IsCMField.equivInfinitePlace E).symm w = InfinitePlace.mk (emb w).1 := by
  rw [Equiv.symm_apply_eq, IsCMField.equivInfinitePlace_apply, InfinitePlace.comap_mk, (emb w).2,
    InfinitePlace.mk_embedding]

private theorem logNorm_diag {E : Type} [Field E] [NumberField E] [IsCMField E] (k : Eˣ) :
    GlobalTheory.Mem.Chr.CharModel.logNorm E (infDiag k) = ∑ v : InfinitePlace E, 2 * Real.log (v (k : E)) := by
  have hp : ∀ v : InfinitePlace E, v (k : E) ≠ 0 := fun v => by simp
  have h := InfinitePlace.prod_eq_abs_norm (k : E)
  change GlobalTheory.Mem.Chr.CharModel.logNorm E (GlobalTheory.Mem.Chr.infDiag k) = _
  rw [GlobalTheory.Mem.Chr.CharModel.logNorm, (GlobalTheory.Mem.Chr.CharModel.infDiag_parts k).1,
    (GlobalTheory.Mem.Chr.CharModel.infDiag_parts k).2, GlobalTheory.Mem.Chr.CharModel.logFin_one, sub_zero,
    GlobalTheory.Mem.Chr.CharModel.logInf_principal, ← h, Real.log_prod (fun v _ => pow_ne_zero _ (hp v))]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Real.log_pow, InfinitePlace.mult, if_neg (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex v))]
  norm_num

theorem UpperTheory.Gal.TP.Chr.absFacts :
    UpperTheory.Gal.TP.Chr.AbsFacts := by
  intro E _ _ _ emb z
  refine ⟨fun w => ⟨DiscreteGroups.T1.G.absC_unrAt z w, ?_⟩, fun k => ?_⟩
  · simpa [Formalism.UG.qV, Formalism.ConjugateSelfDual.normV, Ideal.absNorm_apply,
      Submodule.cardQuot_apply] using DiscreteGroups.T1.G.absC_val z w
  ·
    change Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm E (infDiag k)) = _
    rw [logNorm_diag, ← (IsCMField.equivInfinitePlace E).symm.sum_comp, Complex.ofReal_sum, Finset.mul_sum,
      Complex.exp_sum]
    refine Finset.prod_congr rfl fun w _ => ?_
    have h0 : 0 < ‖(emb w).1 (k : E)‖ := norm_pos_iff.2 ((map_ne_zero _).2 k.ne_zero)
    rw [symm_eq_mk emb w, InfinitePlace.apply, Complex.cpow_def_of_ne_zero (by exact_mod_cast h0.ne'),
      ← Complex.ofReal_log h0.le]
    congr 1
    push_cast
    ring
end
