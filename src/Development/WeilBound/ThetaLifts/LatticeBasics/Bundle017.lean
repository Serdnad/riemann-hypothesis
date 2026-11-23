module

public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle006
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle007
public import Development.WeilBound.ThetaLifts.LatticeBasics.GoodNe
public import Development.WeilBound.ThetaLifts.LatticeBasics.ContinuousFlat
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.WeilBound.ThetaLifts.LatticeBasics.IsCompactOfUnits
import Development.WeilBound.ThetaLifts.TowerModels.LeviAd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {m n : ℕ}

variable {Y : Spc F E n} {A : Spc F E m}

theorem eq_zero_of_right {U : Set ℂ} (hU : IsOpen U) (hd : ∀ z : ℂ, ∀ᶠ z' in 𝓝[≠] z, z' ∈ U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (U ∩ {z | 0 < z.re})) {t : ℝ} (ht : ∀ z : ℂ, t < z.re → z ∈ U ∧ f z = 0) {s : ℂ} (hs : s ∈ U)
    (hs' : 0 < s.re) : f s = 0 := by
  have hc : (Uᶜ).Countable := by
    haveI : DiscreteTopology (Uᶜ : Set ℂ) := discreteTopology_subtype_iff.2 fun x _ => by
      rw [Filter.inf_principal_eq_bot, compl_compl]; exact hd x
    exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  let ψ : ℂ → ℂ := fun w => (Real.exp w.re : ℂ) + w.im * Complex.I
  have re : ∀ w, (ψ w).re = Real.exp w.re := fun w => by simp [ψ, Complex.exp_ofReal_re]
  have im : ∀ w, (ψ w).im = w.im := fun w => by simp [ψ, Complex.exp_ofReal_im]
  have inj : Function.Injective ψ := fun w w' e =>
    Complex.ext (Real.exp_injective (by rw [← re, ← re, e])) (by rw [← im, ← im w', e])
  have e : U ∩ {z | 0 < z.re} = ψ '' (ψ ⁻¹' Uᶜ)ᶜ := by
    ext z
    constructor
    · rintro ⟨h1, h2⟩
      have : ψ ⟨Real.log z.re, z.im⟩ = z := Complex.ext (by rw [re]; exact Real.exp_log h2) (by rw [im])
      exact ⟨_, fun h => h (this.symm ▸ h1), this⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨not_not.1 hw, by show 0 < (ψ w).re; rw [re]; exact Real.exp_pos _⟩
  have hcon : IsPreconnected (U ∩ {z | 0 < z.re}) := by
    rw [e]
    exact ((hc.preimage_of_injOn inj.injOn).isConnected_compl_of_one_lt_rank (by simp)).isPreconnected.image _
      (Continuous.continuousOn (by fun_prop))
  have ho : IsOpen (U ∩ {z : ℂ | 0 < z.re}) := hU.inter (isOpen_lt continuous_const Complex.continuous_re)
  have h1 : t < ((max t 0 + 1 : ℝ) : ℂ).re := by rw [Complex.ofReal_re]; linarith [le_max_left t 0]
  refine (hf.analyticOnNhd ho).eqOn_zero_of_preconnected_of_eventuallyEq_zero hcon (z₀ := ((max t 0 + 1 : ℝ) : ℂ))
    ⟨(ht _ h1).1, by show 0 < Complex.re _; rw [Complex.ofReal_re]; linarith [le_max_right t 0]⟩ ?_ ⟨hs, hs'⟩
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds h1] with z hz using (ht z hz).2

theorem hasProd_off {χ : Chr F E} {T : Finset (Pl F)} (h : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ T → ¬ UnrAt χ w)
    {z : ℂ} (hz : 1 < z.re) : HasProd (fun v : {v : Pl F // v ∉ T} => Lv (charFam χ) v.1 z) (charL χ (∅ : Set (Pl F)) z) := by
  have h1 := hasProd_Lv (S := (∅ : Set (Pl F))) (converges_charFam _ χ hz)
  have h2 : HasProd (fun v : Pl F => Lv (charFam χ) v z) (charL χ (∅ : Set (Pl F)) z) :=
    (Equiv.subtypeUnivEquiv (p := fun v => v ∉ (∅ : Set (Pl F))) (fun _ => Set.notMem_empty _)).hasProd_iff.1 h1
  refine (hasProd_subtype_iff_of_mulSupport_subset (s := {v | v ∉ T}) fun v hv hT => hv ?_).2 h2
  refine Finset.prod_eq_one fun w hw => ?_
  have : ¬ UnrAt χ w := h w (by rwa [mem_aboveF.1 hw])
  simp [locL, charFam, this]

theorem pair_ne_zero (hH : HgtEx) (hN : NormZeta) (hE : EulerProd) (hM : LocMeas) (hU : LocUnr) (hB : BadFactor) (hI : RealInv)
    (hD : DProd) {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
    {r s r' s' : ℕ} (h : IsPair B M χX χW om r s r' s') (h0 : min r s = 0) (h0' : min r' s' = 0) (hn : 1 ≤ n) (hd : n < d)
    (he : Even d) {T : Finset (Pl F)} (hT : T ⊆ B.P) (uX : UnrOff χX (T : Set (Pl F))) (uW : UnrOff χW (T : Set (Pl F)))
    (ram : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ T → ¬ UnrAt χW w)
    {P : Type} [AddCommGroup P] [Module ℂ P] [Nontrivial P] {p : SInf F (Fin n × Fin d) →ₗ[ℂ] P} (hp : RealQuot B M om p)
    {Λ : ℂ → ℂ} (l1 : Differentiable ℂ Λ) (l2 : ∀ z : ℂ, 1 < z.re → Λ z = charL χW (∅ : Set (Pl F)) z)
    (l3 : ∀ z : ℤ, -(d : ℤ) ≤ 2 * z → Λ z ≠ 0) : ∃ Φ ∈ PolData B M, M.I om Φ ≠ 0 := by
  obtain ⟨⟨K, a, hK, ha, -⟩, e, -, he'⟩ := hH F E σ B n X r s h.base (Or.inl h.herm)
  obtain ⟨f₀, p0, n0, i0⟩ := hI F E σ B _ _ _ _ _ _ _ _ _ _ _ _ h h0 P p hp
  letI : MeasurableSpace (Fin n × Fin d → AF F) := borel _
  haveI : BorelSpace (Fin n × Fin d → AF F) := ⟨rfl⟩
  let ν : Measure (Fin n × Fin d → AF F) := Measure.addHaar
  have hν : ν.IsAddHaarMeasure := inferInstance
  obtain ⟨Φ, pΦ, b1, b2, b3⟩ := hB F E σ B _ _ _ _ _ _ _ _ _ _ _ _ h h0 h0' hd.le he T hT uX uW f₀ p0 n0 i0 K a e hK ha he' ν hν
  obtain ⟨U, Z, t₀, u1, u2, u3, u4, u5, u6⟩ := hN F E σ B _ _ _ _ _ _ _ _ _ _ _ _ h h0 h0' hn (by omega) K a e hK ha he' ν hν Φ pΦ
  obtain ⟨dT, d1, d2⟩ := hD F E n T
  choose μl hμl using hM F E σ B n X r s h.base h.herm
  refine ⟨Φ, pΦ, fun hz => ?_⟩
  set H : ℂ → ℂ := fun z => ∫ g in {g | ∀ v ∉ T, IntAt v g}, zint om ν a e Φ z g ∂M.μ with hHdef
  have res0 : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW 0 := fun x => by
    rw [h.resW x, he.neg_one_pow, pow_zero]
  have key : ∀ z : ℂ, max t₀ (n / 2) < z.re →
      z ∈ U ∧ Z z * dT z - (∏ i ∈ Finset.range n, Λ (z + n / 2 - i)) * H z = 0 := fun z hz => by
    have z1 := (le_max_left _ _).trans_lt hz
    have z2 := (le_max_right _ _).trans_lt hz
    have n1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    obtain ⟨m1, m2, m3⟩ := u5 z z1
    refine ⟨m1, sub_eq_zero.2 ?_⟩
    choose! f f1 f2 using b1 z
    have lu := fun v (hv : v ∉ T) => hU F E σ B n X r s h.base h.herm χW h.hW res0 K e hK he' v
      (fun w hw => uW w (by show ¬ w.under (𝓞 F) ∈ (T : Set (Pl F)); rw [hw]; exact hv)) (μl v) (hμl v).1 (hμl v).2 z (f v) z2
      (f1 v hv)
    have t1 := hE F E σ B n X r s h.base h.herm T M.μ h.good.haar μl hμl _ (fun v u => f v (e (u, 1))) m2 fun v hv =>
      ⟨fun u hu => (f2 v hv u hu).2, fun u hu => (f2 v hv u hu).1, (lu v hv).1⟩
    have t2 := t1.mul (d2 z (by linarith)).2
    have t3 : HasProd (fun v : {v : Pl F // v ∉ T} => ∏ i ∈ Finset.range n, Lv (charFam χW) v.1 (z + n / 2 - i))
        (∏ i ∈ Finset.range n, Λ (z + n / 2 - i)) := hasProd_prod fun i hi => by
      have hi' : (i : ℝ) + 1 ≤ n := by exact_mod_cast Finset.mem_range.1 hi
      have : 1 < (z + n / 2 - i).re := by
        simp only [Complex.sub_re, Complex.add_re, Complex.natCast_re, Complex.div_ofNat_re]; linarith
      rw [l2 _ this]; exact hasProd_off ram this
    rw [m3]
    refine tendsto_nhds_unique t2 ((Filter.Tendsto.mul_const (H z) t3).congr fun S => ?_)
    rw [mul_right_comm, ← Finset.prod_mul_distrib]
    exact congrArg (· * H z) (Finset.prod_congr rfl fun v _ => (lu v.1 v.2).2.symm)
  have s0 : 0 < (((d : ℂ) - n) / 2).re := by
    have : (n : ℝ) < d := by exact_mod_cast hd
    simp only [Complex.sub_re, Complex.natCast_re, Complex.div_ofNat_re]; linarith
  have fin := eq_zero_of_right u1 u2 (f := fun z => Z z * dT z - (∏ i ∈ Finset.range n, Λ (z + n / 2 - i)) * H z)
    (((u4.mono Set.inter_subset_left).mul (d1.mono Set.inter_subset_right)).sub
      ((Differentiable.fun_finsetProd fun i _ => l1.comp ((differentiable_id.add_const _).sub_const _)).mul b2).differentiableOn)
    key u3 s0
  simp only [u6 hz, zero_mul, zero_sub, neg_eq_zero] at fin
  refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i hi => ?_) b3 fin
  obtain ⟨k, hk⟩ := he
  have := l3 ((k : ℤ) - i) (by have := Finset.mem_range.1 hi; omega)
  rwa [show (((k : ℤ) - i : ℤ) : ℂ) = ((d : ℂ) - n) / 2 + n / 2 - i by rw [hk]; push_cast; ring] at this

theorem nonZeroBottom_of_doubling_integral (hR : KReal) (hL : LInt2) (hH : HgtEx) (hN : NormZeta) (hE : EulerProd) (hM : LocMeas) (hU : LocUnr)
    (hB : BadFactor) (hI : RealInv) (hD : DProd) : NonZeroBot := by
  intro F E _ _ _ _ _ σ B a a' G X om om' h hp hq
  obtain ⟨R, hr⟩ := hR F E σ B a a' G X om om' h
  obtain ⟨Λ, l1, l2, l3⟩ := hL F E σ B a a' G X om om' h X.ν (Or.inl rfl)
  obtain ⟨Λ', l1', l2', l3'⟩ := hL F E σ B a a' G X om om' h X.ν⁻¹ (Or.inr rfl)
  have g1 := h.geo.lt
  have g2 := h.geo.aBig
  have c := h.chars
  have hν := isHecke_nu h
  have e : X.β / X.α = X.ν⁻¹ := by rw [Chars.ν, inv_div]
  have uν : UnrOff X.ν (X.T : Set (Pl F)) := fun w hw => by
    rw [Chars.ν, div_eq_mul_inv]; exact (c.unrα w hw).mul (c.unrβ w hw).inv
  have rν : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range X.ν (a + a') := fun x => by
    show ((X.α _ / X.β _ : Circle) : ℂ) = _
    rw [Circle.coe_div, c.resα x, c.resβ x, h.geo.even.neg_one_pow]
    split_ifs
    · exact div_one _
    · rw [div_eq_one_iff_eq (pow_ne_zero _ (by norm_num)), neg_one_pow_congr (Nat.even_add.1 h.geo.even).symm]
  have rν' : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range X.ν⁻¹ (a + a') := fun x => by
    show (((X.ν _)⁻¹ : Circle) : ℂ) = _
    rw [Circle.coe_inv, rν x, h.geo.even.neg_one_pow, ite_self, inv_one]
  have hν' : IsHecke F E X.ν⁻¹ := ⟨hν.1.inv, fun x => by rw [MonoidHom.inv_apply, hν.2 x, inv_one]⟩
  haveI := hr.nontriv
  exact ⟨pair_ne_zero hH hN hE hM hU hB hI hD (χW := X.ν⁻¹)
      ⟨h.base, h.geo.hV, h.geo.hW, h.geo.hM, c.heckeβ, hν', c.resβ, rν', e ▸ h.weil⟩ (by omega) (by omega) (by omega) (by omega)
      h.geo.even c.sub c.unrβ (fun w hw => (uν w hw).inv) (fun w hw hu => c.ram w hw (by simpa using hu.inv)) hr.quot l1' l2' l3',
    pair_ne_zero hH hN hE hM hU hB hI hD (χW := X.ν)
      ⟨h.base, h.geo.hV', h.geo.hW, h.geo.hM', c.heckeα, hν, c.resα, rν, h.weil'⟩ (by omega) (by omega) (by omega) (by omega)
      h.geo.even c.sub c.unrα uν c.ram hr.quot' l1 l2 l3⟩

end GlobalTheory.ThK.Dbl

end
end

section

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

open PositivityTheory.ThKG.Tow St
open scoped Pointwise

theorem cartan_bound2 {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (h : IsCartan M θ) :
    ∃ R : ℝ, ∀ A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ, Aᵀ * dbl M * A.map star = dbl M →
      Commute A (Matrix.fromBlocks θ 0 0 (-θ)) → ∀ i j, ‖A i j‖ ≤ R := by
  let e := (finSumFinEquiv (m := n) (n := n)).symm
  have c : IsCartan ((dbl M).submatrix e e) ((Matrix.fromBlocks θ 0 0 (-θ)).submatrix e e) := by
    refine ⟨?_, ?_, fun x hx => ?_⟩
    · simp [Matrix.fromBlocks_multiply, h.1]
    · rw [Matrix.transpose_submatrix, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
      have : θᵀ * M * θ.map (starRingEnd ℂ) = M := h.2.1
      simp [dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.map_neg, this]
    · obtain ⟨y, z, rfl⟩ : ∃ y z, x = Sum.elim y z ∘ e := ⟨x ∘ e.symm ∘ .inl, x ∘ e.symm ∘ .inr, by
        ext i; obtain ⟨j, rfl⟩ := e.symm.surjective i; cases j <;> simp⟩
      have q : ∀ v, 0 ≤ ((θ *ᵥ v) ⬝ᵥ M *ᵥ star v).re := fun v => by
        by_cases hv : v = 0
        · simp [hv]
        · exact (h.2.2 v hv).le
      have : ((Matrix.fromBlocks θ 0 0 (-θ)).submatrix e e *ᵥ Sum.elim y z ∘ e) ⬝ᵥ (dbl M).submatrix e e *ᵥ star (Sum.elim y z ∘ e) =
          (θ *ᵥ y) ⬝ᵥ M *ᵥ star y + (θ *ᵥ z) ⬝ᵥ M *ᵥ star z := by
        rw [show star (Sum.elim y z ∘ e) = Sum.elim (star y) (star z) ∘ e by
          ext i; obtain ⟨j, rfl⟩ := e.symm.surjective i; cases j <;> simp]
        simp [Matrix.submatrix_mulVec_equiv, Function.comp_assoc, comp_equiv_dotProduct_comp_equiv, dbl, Matrix.fromBlocks_mulVec,
          Matrix.neg_mulVec]
      rw [this, Complex.add_re]
      by_cases hy : y = 0
      · exact add_pos_of_nonneg_of_pos (q y) (h.2.2 z fun hz => hx (by simp [hy, hz]))
      · exact add_pos_of_pos_of_nonneg (h.2.2 y hy) (q z)
  obtain ⟨R, hR⟩ := cartan_bound c
  refine ⟨R, fun A h1 h2 i j => ?_⟩
  simpa using hR (A.submatrix e e) (by
    rw [Matrix.transpose_submatrix, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h1])
    (by rw [Commute, SemiconjBy, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h2.eq]) (e.symm i) (e.symm j)

attribute [local instance] ae_ring ae_t2 ae_smul

theorem stab2Cpt : Stab2Cpt := by
  intro F E _ _ _ _ _ σ B n Y r s hB hY K hK
  obtain ⟨hL, c, c0, hc⟩ : Y.L.IsFullLattice E ∧ ∃ c : ℂ, c ≠ 0 ∧ ∀ w, IsCartan (c • Y.J.map (B.emb w).1) (Y.θ w) :=
    hY.elim (fun h => ⟨h.lat, 1, one_ne_zero, fun w => by simpa using h.cartan w⟩) fun h => ⟨h.lat, _, Complex.I_ne_zero, h.cartan⟩
  obtain ⟨Φ, hΦ, eΦ⟩ := exists_section hB.cm B.emb
  choose C hC h using fin_bound (F := F) Y hL
  choose R hR using fun w => cartan_bound2 (hc w)
  have hD : IsCompact (Φ '' Set.univ.pi fun w => Metric.closedBall (0 : ℂ) (R w)) :=
    (isCompact_univ_pi fun w => isCompact_closedBall _ _).image hΦ
  have hm : Continuous fun g : G2 σ Y => mat2 g := Units.continuous_val.comp continuous_subtype_val
  have hp : ∀ w, Continuous (piInf (B.emb w)) := fun w => GlobalTheory.Grow.continuous_infEmb_compInf F w (B.emb w)
  have cc : Continuous (cA (F := F) σ) := IsModuleTopology.continuous_of_linearMap (cA (F := F) σ).toLinearMap
  have cl := (isCompact_latHat Y hL.fg).isClosed
  have key : ∀ k ∈ K, mat2 k ∈ Set.univ.pi fun i => Set.univ.pi fun j =>
      (Φ '' Set.univ.pi fun w => Metric.closedBall (0 : ℂ) (R w)) + C (Sum.elim id id i) (Sum.elim id id j) := fun k hk i _ j _ => by
    obtain ⟨k1, k2⟩ := (hK k).1 hk
    rw [eΦ (mat2 k i j)]
    refine Set.add_mem_add ⟨_, fun w _ => ?_, rfl⟩ ?_
    · rw [mem_closedBall_zero_iff]
      refine hR w ((mat2 k).map (piInf (B.emb w))) ?_ (k1 w) i j
      have e := congrArg (fun X => c • Matrix.map X (piInf (B.emb w)))
        (show (mat2 k)ᵀ * dbl (incM F Y.J) * (mat2 k).map (cA σ) = dbl (incM F Y.J) from k.2)
      have d : c • (dbl (incM F Y.J)).map (piInf (B.emb w)) = dbl (c • Y.J.map (B.emb w).1) := by
        ext (a | a) (b | b) <;> simp [dbl, incM, Levi.piInf_incl]
      have d2 : ((mat2 k).map (cA σ)).map (piInf (B.emb w)) = ((mat2 k).map (piInf (B.emb w))).map star :=
        Matrix.ext fun a b => Levi.piInf_cA hB.cm _ _
      simp only [Matrix.map_mul] at e
      rwa [← Matrix.smul_mul, ← Matrix.mul_smul, d, d2] at e
    · have a := fun y hy => k2 y 0 hy (zero_mem _) k (.inl rfl)
      have b := fun y hy => k2 0 y (zero_mem _) hy k (.inl rfl)
      rw [← Matrix.fromBlocks_toBlocks (mat2 k)] at a b
      simp only [Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_zero, add_zero, zero_add] at a b
      rcases i with i | i <;> rcases j with j | j
      exacts [h i j _ fun y hy => (a y hy).1, h i j _ fun y hy => (b y hy).1, h i j _ fun y hy => (a y hy).2,
        h i j _ fun y hy => (b y hy).2]
  refine isCompact_of_units _ (isClosed_eq (((Units.continuous_val.matrix_transpose).matrix_mul continuous_const).matrix_mul
      (Units.continuous_val.matrix_map cc)) continuous_const) _ ?_ _
    (isCompact_univ_pi fun i => isCompact_univ_pi fun j => hD.add (hC _ _)) fun k hk => ⟨key k hk, key _ (inv_mem hk)⟩
  rw [show (K : Set (G2 σ Y)) = {k | _} from Set.ext hK]
  simp only [Set.forall_mem_insert, Set.mem_singleton_iff, forall_eq]
  simp only [Set.setOf_and, Set.setOf_forall]
  have v : ∀ {f : G2 σ Y → G2 σ Y}, Continuous f → ∀ z, IsClosed ({k | (mat2 (f k) *ᵥ z) ∘ Sum.inl ∈ latHat Y} ∩
      {k | (mat2 (f k) *ᵥ z) ∘ Sum.inr ∈ latHat Y}) := fun hf z =>
    have t := (hm.comp hf).matrix_mulVec (continuous_const (y := z))
    (cl.preimage (continuous_pi fun i => (continuous_apply _).comp t)).inter
      (cl.preimage (continuous_pi fun i => (continuous_apply _).comp t))
  exact (isClosed_iInter fun w => isClosed_eq ((hm.matrix_map (hp w)).matrix_mul continuous_const)
      (continuous_const.matrix_mul (hm.matrix_map (hp w)))).inter
    (isClosed_iInter fun z => isClosed_iInter fun z' => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      (v continuous_id _).inter (v continuous_inv _))

end GlobalTheory.ThK.Dbl

end
end
