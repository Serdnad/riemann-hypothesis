module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle072
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle294
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle352
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle347
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelADef
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle003
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle191
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle147
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle192
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
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinOrth

variable {D : D7} {S T : HSp D}

theorem setIntegral_add_right {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure (WO S T))
    [μ.IsAddHaarMeasure] {𝓕 : Set (WO S T)} (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) {g : WO S T → E}
    (hg : ∀ γ ∈ ratL T S, ∀ w, g (γ + w) = g w) (u : WO S T) :
    ∫ w in 𝓕, g (w + u) ∂μ = ∫ w in 𝓕, g w ∂μ := by
  have i6 : BorelSpace (WO S T) := ⟨rfl⟩
  have : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  have : Countable (Matrix (Fin T.rank) (Fin S.rank) D.host.E) :=
    inferInstanceAs (Countable (Fin T.rank → Fin S.rank → D.host.E))
  have : Countable (ratL T S) := (Set.countable_range _).to_subtype
  have : MeasurableConstVAdd (ratL T S) (WO S T) := ⟨fun c => (continuous_const.add continuous_id).measurable⟩
  have : VAddInvariantMeasure (ratL T S) (WO S T) μ := ⟨fun c s _ => measure_preimage_add μ (c : WO S T) s⟩
  have hmp : MeasurePreserving (fun w : WO S T => u + w) μ μ := measurePreserving_add_left μ u
  have hemb : MeasurableEmbedding (fun w : WO S T => u + w) := (MeasurableEquiv.addLeft u).measurableEmbedding
  have hpre : 𝓕 = (fun w : WO S T => u + w) ⁻¹' ((fun w : WO S T => -u + w) ⁻¹' 𝓕) := by
    ext w; simp
  have h𝓕' : IsAddFundamentalDomain (ratL T S) ((fun w : WO S T => -u + w) ⁻¹' 𝓕) μ := by
    refine h𝓕.preimage_of_equiv (measurePreserving_add_left μ (-u)).quasiMeasurePreserving
      (e := id) Function.bijective_id fun γ w => ?_
    simp only [id, AddSubgroup.vadd_def, vadd_eq_add]
    abel
  have e1 : ∫ w in 𝓕, g (w + u) ∂μ = ∫ w in (fun w : WO S T => u + w) ⁻¹' ((fun w : WO S T => -u + w) ⁻¹' 𝓕),
      g (u + w) ∂μ := by
    rw [← hpre]; simp_rw [add_comm _ u]
  rw [e1, hmp.setIntegral_preimage_emb hemb]
  exact h𝓕'.setIntegral_eq h𝓕 fun γ w => by rw [AddSubgroup.vadd_def, vadd_eq_add]; exact hg γ γ.2 w

theorem star_mul_self_psi {ψ : AddChar (AF D.host.F) ℂ} (hn : ∀ x, ‖ψ x‖ = 1) (a : AF D.host.F) :
    star (ψ a) * ψ a = 1 := by
  rw [Complex.star_def, Complex.conj_mul', hn]; simp

theorem thPair_heisO {ψ : AddChar (AF D.host.F) ℂ} (hn : ∀ x, ‖ψ x‖ = 1) (μ : Measure (WO S T))
    [μ.IsAddHaarMeasure] {𝓕 : Set (WO S T)} (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) {f g : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) (u : WO S T) :
    thPair μ 𝓕 (heisO ψ S T u f) (heisO ψ S T u g) = thPair μ 𝓕 f g := by
  have hs := star_mul_self_psi hn
  unfold thPair
  have e : ∀ w, heisO ψ S T u f w * star (heisO ψ S T u g w) = f (w + u) * star (g (w + u)) := by
    intro w
    simp only [heisO, star_mul']
    linear_combination (f (w + u) * star (g (w + u))) * hs (symplOH S T w u)
  simp_rw [e]
  refine setIntegral_add_right μ h𝓕 (g := fun w => f w * star (g w)) ?_ u
  rintro _ ⟨γ, rfl⟩ w
  change f (ratW T S γ + w) * star (g (ratW T S γ + w)) = f w * star (g w)
  rw [hf.quasi, hg.quasi, star_mul']
  linear_combination (f w * star (g w)) * hs (-(symplOH S T (ratW T S γ) w))

theorem thetaNormSq_heisenbergOp_invariant {ψ : AddChar (AF D.host.F) ℂ} (hn : ∀ x, ‖ψ x‖ = 1) (μ : Measure (WO S T))
    [μ.IsAddHaarMeasure] {𝓕 : Set (WO S T)} (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (u : WO S T) : nrm2 μ 𝓕 (heisO ψ S T u f) = nrm2 μ 𝓕 f := by
  unfold nrm2
  have e : ∀ w, ‖heisO ψ S T u f w‖ ^ 2 = ‖f (w + u)‖ ^ 2 := fun w => by
    simp only [heisO, norm_mul, hn, one_mul]
  simp_rw [e]
  refine setIntegral_add_right μ h𝓕 (g := fun w => ‖f w‖ ^ 2) ?_ u
  rintro _ ⟨γ, rfl⟩ w
  change ‖f (ratW T S γ + w)‖ ^ 2 = ‖f w‖ ^ 2
  rw [hf.quasi, norm_mul, hn, one_mul]

theorem thPair_smul_right (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (f g : WO S T → ℂ) (c : ℂ) :
    thPair μ 𝓕 f (c • g) = star c * thPair μ 𝓕 f g := by
  unfold thPair
  rw [← integral_const_mul]
  congr 1; funext w
  simp only [Pi.smul_apply, smul_eq_mul, star_mul']
  ring

theorem orth_all : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ vac, IsVacO ψ θ S T x.s y.s x.L y.L vac → ∀ (v : VolM D T.rank S.rank) f, IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (latO S T x.L y.L fun _ => True) f → (∀ u : WO S T, u.map (finPart D) = 0 → thPair v.μ v.𝓕 f (heisO ψ S T u vac) = 0) → ∀ u : WO S T, thPair v.μ v.𝓕 f (heisO ψ S T u vac) = 0 := by
  intro D ψ θ hθ S T x y hx hy vac hvac v f hf hlat hreal u
  have hψ := hvac.1
  have hn : ∀ a, ‖ψ a‖ = 1 := hψ.1.2.1
  haveI : v.μ.IsAddHaarMeasure := v.covol.1
  have hF : IsAddFundamentalDomain (ratL T S) v.𝓕 v.μ := v.covol.2.1
  have hvt : IsThetaFunO ψ S T vac := hvac.2.theta
  have hvl := hvac.2.lat

  have key : ∀ g : WO S T, heisO ψ S T g f = f → heisO ψ S T g vac = vac → ψ (symplO S T g u) ≠ 1 →
      thPair v.μ v.𝓕 f (heisO ψ S T u vac) = 0 := by
    intro g hgf hgv hne
    have hc : heisO ψ S T g (heisO ψ S T u vac) = ψ (symplO S T g u) • heisO ψ S T u vac := by
      rw [GlobalTheory.SplitScalar.heisO_comm, hgv]
    have e := thPair_heisO hn v.μ hF hf (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hvt u) g
    rw [hgf, hc, thPair_smul_right] at e
    have hne' : star (ψ (symplO S T g u)) ≠ 1 := by
      intro h; apply hne; rw [← star_star (ψ _), h, star_one]
    have h2 : (1 - star (ψ (symplO S T g u))) * thPair v.μ v.𝓕 f (heisO ψ S T u vac) = 0 := by
      linear_combination e.symm
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (Ne.symm hne'))
  by_cases hA1 : ∀ g ∈ latO S T x.L y.L (fun _ => True), ψ (symplO S T (2 • g) u) = 1
  swap
  · push_neg at hA1
    obtain ⟨g, hg, hne⟩ := hA1
    exact key (2 • g) (hlat.1 g hg) (hvl.1 g hg) hne
  by_cases hA2 : ∀ e, IsSplitIdem D e → ∀ g ∈ latO S T x.L y.L (fun _ => True), IsHalf e g →
      ψ (symplO S T g u) = 1
  swap
  · push_neg at hA2
    obtain ⟨e, he, g, hg, hh, hne⟩ := hA2
    exact key g (hlat.2 e he g hg hh) (hvl.2 e he g hg hh) hne

  obtain ⟨ur, uf, hr, hfi, rfl⟩ : ∃ ur uf : WO S T, ur.map (finPart D) = 0 ∧ uf.map (infPart D) = 0 ∧
      u = ur + uf := by
    refine ⟨GlobalTheory.FinTranslate.eInf D • u, (1 - GlobalTheory.FinTranslate.eInf D) • u, ?_, ?_, ?_⟩
    · ext i j; exact GlobalTheory.ThetaClosed.finPart_eInf_smul (u i j)
    · ext i j; exact GlobalTheory.ThetaClosed.infPart_one_sub_eInf_smul (u i j)
    · rw [← add_smul, add_sub_cancel, one_smul]
  have hlf : ∀ g ∈ latO S T x.L y.L (fun _ => True), g.map (infPart D) = 0 := fun g hg =>
    GlobalTheory.SplitScalar.latO_fin hg
  have hsf : ∀ g : WO S T, g.map (infPart D) = 0 → symplO S T g (ur + uf) = symplO S T g uf := by
    intro g hg
    rw [GlobalTheory.LatVac.symplO_add_right, GlobalTheory.SplitScalar.symplO_skew S T ur g, GlobalTheory.SplitScalar.symplO_real_fin S T hr hg,
      neg_zero, zero_add]
  have hv' : IsVacO ψ θ S T x.s y.s x.L y.L (heisO ψ S T uf vac) := by
    have hv2 := hvac
    obtain ⟨-, hinf, hth, hl, hfock, hnorm⟩ := hv2
    refine ⟨hψ, hinf, GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hth uf, ⟨fun g hg => ?_, fun e he g hg hh => ?_⟩,
      fun τ z => ?_, hnorm.1, fun p hp => ?_⟩
    · rw [GlobalTheory.SplitScalar.heisO_comm, hl.1 g hg, ← hsf _ (hlf _ (AddSubgroup.nsmul_mem _ hg 2)), hA1 g hg, one_smul]
    · rw [GlobalTheory.SplitScalar.heisO_comm, hl.2 e he g hg hh, ← hsf _ (hlf g hg), hA2 e he g hg hh, one_smul]
    · have h0 := hfock τ z
      unfold annih at h0 ⊢
      rw [GlobalTheory.FinTranslate.dRho_heisO hinf hfi, GlobalTheory.FinTranslate.dRho_heisO hinf hfi]
      have h1 := congrArg (GlobalTheory.FinTranslate.heisL S T ψ uf) h0
      rw [map_add (f := _), map_smul, map_zero] at h1
      exact h1
    · show nrm2 p.1 p.2 (heisO ψ S T uf vac) = 1
      haveI := hp.1
      rw [thetaNormSq_heisenbergOp_invariant hn p.1 hp.2.1 hth uf]
      exact hnorm.2 p hp
  obtain ⟨c, -, hc⟩ := GlobalTheory.VacUnique.vacUniqueO D ψ θ hψ hθ S T x.s y.s hx.sig hy.sig hx.cart hy.cart x.L y.L
    hx.sd hy.sd vac _ hvac hv'
  have e : heisO ψ S T (ur + uf) vac = c • heisO ψ S T ur vac := by
    rw [GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T (GlobalTheory.SplitScalar.symplO_real_fin S T hr hfi), hc,
      GlobalTheory.SplitScalar.heisO_smul]
  rw [e, thPair_smul_right, hreal ur hr, mul_zero]

end GlobalTheory.FinOrth

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeisComb

variable {D : D7}

theorem heisO_finset_sum (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (x : WO S T) {ι : Type} (s : Finset ι)
    (a : ι → ℂ) (g : ι → WO S T → ℂ) :
    heisO ψ S T x (∑ i ∈ s, a i • g i) = ∑ i ∈ s, a i • heisO ψ S T x (g i) := by
  funext w
  simp only [heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem comb_eq_sum (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T c f = c.sum fun u a => a • heisO ψ S T u f := rfl

theorem comb_comb (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c c' : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T c (comb ψ S T c' f) =
      ∑ x ∈ c.support, ∑ y ∈ c'.support, (c x * c' y) • heisO ψ S T x (heisO ψ S T y f) := by
  unfold comb
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [heisO_finset_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [smul_smul]

theorem symplO_half (S T : HSp D) (e e' : AE D) (x y : WO S T) (he : cA D e = e) (hee : e * e' = 0)
    (hx : IsHalf e x) (hy : IsHalf e' y) : symplO S T x y = 0 := by
  have h0 : e * cA D e' = 0 := by
    conv_lhs => rw [← he]
    rw [← map_mul, hee, map_zero]
  have hh : hO S T x y = 0 := by
    unfold hO
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
      Finset.sum_eq_zero fun d _ => ?_
    rw [← hy c b, ← hx d a, map_mul]
    calc incA D (S.gram⁻¹ a b) * (cA D e' * cA D (y c b)) * incA D (T.gram c d) * (e * x d a)
        = (e * cA D e') * (incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * x d a) := by ring
      _ = 0 := by rw [h0, zero_mul]
  unfold symplO
  rw [hh, mul_zero, map_zero]

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), (∀ c c' : WO S T →₀ ℂ, ∃ c'' : WO S T →₀ ℂ, (∀ w ∈ c''.support, ∃ x ∈ c.support, ∃ y ∈ c'.support, w = x + y) ∧ ∀ f, comb ψ S T c'' f = comb ψ S T c (comb ψ S T c' f)) ∧ (∀ c c' : WO S T →₀ ℂ, (∀ x ∈ c.support, ∀ y ∈ c'.support, symplO S T x y = 0) → ∀ f, comb ψ S T c (comb ψ S T c' f) = comb ψ S T c' (comb ψ S T c f)) ∧ (∀ (c : WO S T →₀ ℂ) f, IsThetaFunO ψ S T f → IsFinComb c → IsStdChar D ψ (-1) → IsThetaFunO ψ S T (comb ψ S T c f)) ∧ ∀ (e e' : AE D) (x y : WO S T), cA D e = e → e * e' = 0 → IsHalf e x → IsHalf e' y → symplO S T x y = 0 := by
  intro D ψ S T
  refine ⟨fun c c' => ?_, fun c c' h f => ?_, fun c f hf hc hψ => ?_,
    fun e e' x y he hee hx hy => symplO_half S T e e' x y he hee hx hy⟩
  · classical
    refine ⟨∑ x ∈ c.support, ∑ y ∈ c'.support, Finsupp.single (x + y) (c x * c' y * ψ (symplOH S T x y)), ?_,
      fun f => ?_⟩
    · intro w hw
      have h1 := Finsupp.support_finsetSum hw
      rw [Finset.mem_biUnion] at h1
      obtain ⟨x, hx, hw2⟩ := h1
      have h2 := Finsupp.support_finsetSum hw2
      rw [Finset.mem_biUnion] at h2
      obtain ⟨y, hy, hw3⟩ := h2
      have h3 := Finsupp.support_single_subset hw3
      rw [Finset.mem_singleton] at h3
      exact ⟨x, hx, y, hy, h3⟩
    · rw [comb_comb, comb_eq_sum]
      rw [← Finsupp.sum_finsetSum_index (fun u => zero_smul ℂ (heisO ψ S T u f)) (fun u a b => add_smul a b (heisO ψ S T u f))]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finsupp.sum_finsetSum_index (fun u => zero_smul ℂ (heisO ψ S T u f)) (fun u a b => add_smul a b (heisO ψ S T u f))]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finsupp.sum_single_index (zero_smul ℂ (heisO ψ S T (x + y) f)), GlobalTheory.WeilVacMove.heisO_heisO, smul_smul]
  · rw [comb_comb, comb_comb, Finset.sum_comm]
    refine Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun x hx => ?_
    have h0 : symplOH S T x y = 0 := by
      unfold symplOH
      rw [h x hx y hy, mul_zero]
    have h1 : symplOH S T y x = 0 := by
      rw [GlobalTheory.MixModel.symplOH_skew, h0, neg_zero]
    rw [GlobalTheory.WeilVacMove.heisO_heisO, GlobalTheory.WeilVacMove.heisO_heisO, h0, h1, add_comm x y, mul_comm (c x)]
  · exact GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hψ.1 f hf (WO S T) c.support id (fun u => c u) hc

end GlobalTheory.HeisComb
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

namespace GlobalTheory.FockScal

open GlobalTheory.FockSubst

theorem foldr_scal {ι X : Type} {A A' : ι → (X → ℂ) → (X → ℂ)} {P : (X → ℂ) → Prop} (c : ι → ℂ)
    (hsm : ∀ (a : ℂ) f, P f → P (a • f)) (hA : ∀ i f, P f → P (A i f))
    (Asm : ∀ i (a : ℂ) f, P f → A i (a • f) = a • A i f) (h : ∀ i f, P f → A' i f = c i • A i f)
    {f : X → ℂ} (hf : P f) (l : List ι) :
    P (l.foldr (fun i g => A i g) f) ∧
      l.foldr (fun i g => A' i g) f = (l.map c).prod • l.foldr (fun i g => A i g) f := by
  induction l with
  | nil => simpa using hf
  | cons i l ih =>
    refine ⟨hA _ _ ih.1, ?_⟩
    simp only [List.foldr_cons, List.map_cons, List.prod_cons]
    rw [ih.2, h _ _ (hsm _ _ ih.1), Asm _ _ _ ih.1, smul_smul]

theorem pure_monomial {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (f : X → ℂ) (α : ι →₀ ℕ) :
    pureTensorL A f (MvPolynomial.monomial α 1) = opPow A α f := by
  unfold pureTensorL
  have := (MvPolynomial.basisMonomials ι ℂ).constr_basis ℂ (fun k : ι →₀ ℕ => opPow A k f) α
  rwa [MvPolynomial.coe_basisMonomials] at this

theorem prod_fiber {ι κ : Type} [Fintype κ] [DecidableEq κ] (g : ι → κ) (μ : κ → ℂ) (α : ι →₀ ℕ) :
    ((Finsupp.toMultiset α).toList.map fun i => μ (g i)).prod = ∏ τ, μ τ ^ (∑ v ∈ α.support with g v = τ, α v) := by
  rw [← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList, Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
    Finsupp.prod_mapDomain_index (by simp) (by intros; rw [pow_add]), Finsupp.prod,
    ← Finset.prod_fiberwise (s := α.support) (g := g)]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun v hv => ?_
  rw [(Finset.mem_filter.1 hv).2]

theorem pure_scal {ι κ X : Type} [Fintype κ] [DecidableEq κ] {A A' : ι → (X → ℂ) → (X → ℂ)} {P : (X → ℂ) → Prop}
    (g : ι → κ) (μ : κ → ℂ) (hsm : ∀ (a : ℂ) f, P f → P (a • f)) (hA : ∀ i f, P f → P (A i f))
    (Asm : ∀ i (a : ℂ) f, P f → A i (a • f) = a • A i f) (h : ∀ i f, P f → A' i f = μ (g i) • A i f)
    {f : X → ℂ} (hf : P f) (α : ι →₀ ℕ) :
    pureTensorL A' f (MvPolynomial.monomial α 1) =
      (∏ τ, μ τ ^ (∑ v ∈ α.support with g v = τ, α v)) • pureTensorL A f (MvPolynomial.monomial α 1) := by
  rw [pure_monomial, pure_monomial]
  unfold opPow
  rw [(foldr_scal (fun i => μ (g i)) hsm hA Asm h hf _).2, prod_fiber]

theorem unitMap_smul {m n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (B' : Matrix (Fin m) (Fin m) ℂ) {z : ℂ} (hz : z ≠ 0)
    (a : Fin m) (j : Fin n) : unitMap (z • B) B' a j = z⁻¹ • unitMap B B' a j := by
  have e : z • B = B * (z • (1 : Matrix (Fin n) (Fin n) ℂ)) := by simp
  have e' : (z • (1 : Matrix (Fin n) (Fin n) ℂ))⁻¹ = z⁻¹ • 1 :=
    Matrix.inv_eq_left_inv (by simp [smul_smul, hz])
  unfold unitMap
  rw [e, Matrix.mul_inv_rev, e']
  simp

theorem cplxO_pm {m n : ℕ} {s : Matrix (Fin n) (Fin n) ℂ} {t : Matrix (Fin m) (Fin m) ℂ} (hs : s = 1 ∨ s = -1)
    (ht : t = 1 ∨ t = -1) (a : Fin m) (j : Fin n) (u : Matrix (Fin m) (Fin n) ℂ) :
    cplxO s t u = ((if decide (s = 1 ↔ t = 1) then 1 else -1 : ℂ) * Complex.I) • u := by
  have h1 : (-1 : Matrix (Fin n) (Fin n) ℂ) ≠ 1 := fun h => by
    have := congrFun (congrFun h j) j
    simp at this
    norm_num at this
  have h2 : (-1 : Matrix (Fin m) (Fin m) ℂ) ≠ 1 := fun h => by
    have := congrFun (congrFun h a) a
    simp at this
    norm_num at this
  unfold cplxO
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp [h1, h2]

theorem pureTensorO_scal : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ ζ : D.what₂.Tau → ℂ, (∀ τ, ‖ζ τ‖ = 1) → ∀ α : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ S T x.s y.s (fun τ => ζ τ • x.B τ) y.B f (MvPolynomial.monomial α 1) = (∏ τ, (if (x.s τ = 1 ↔ y.s τ = 1) then (ζ τ)⁻¹ else ζ τ) ^ (∑ v ∈ α.support with v.1 = τ, α v)) • pureTensorO ψ θ S T x.s y.s x.B y.B f (MvPolynomial.monomial α 1) := by
  intro D ψ θ hψ hθ S T x y hx hy f hf ζ hζ α
  have hz : ∀ τ, ζ τ ≠ 0 := fun τ h => by simpa [h] using hζ τ
  let μ : D.what₂.Tau → ℂ := fun τ => if (x.s τ = 1 ↔ y.s τ = 1) then (ζ τ)⁻¹ else ζ τ
  have key : ∀ (i : FVar D T.rank S.rank) g, IsThetaFunO ψ S T g →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO (x.s τ) (y.s τ)) (fun τ => ζ τ • x.B τ) y.B i g =
      μ i.1 • aPlusAll (heisO ψ S T) θ (fun τ => cplxO (x.s τ) (y.s τ)) x.B y.B i g := by
    rintro ⟨ρ, a, j⟩ g hg
    simp only [aPlusAll, μ]
    rw [unitMap_smul _ _ (hz ρ), aPlus_dir_smul hψ hθ ρ _ _ hg _ _ (cplxO_pm (hx.pm ρ) (hy.pm ρ) a j _)]
    congr 1
    rw [map_inv₀, ← Complex.inv_eq_conj (hζ ρ), inv_inv]
    simp only [decide_eq_true_eq]
  have hA : ∀ i f, IsThetaFunO ψ S T f →
      IsThetaFunO ψ S T (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (x.s τ) (y.s τ)) x.B y.B i f) :=
    fun _ _ h => aPlus_th hψ hθ _ _ _ h
  have Asm : ∀ i (a : ℂ) f, IsThetaFunO ψ S T f →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO (x.s τ) (y.s τ)) x.B y.B i (a • f) =
      a • aPlusAll (heisO ψ S T) θ (fun τ => cplxO (x.s τ) (y.s τ)) x.B y.B i f :=
    fun _ a _ h => aPlus_smul hψ hθ _ _ _ a h
  unfold pureTensorO
  exact pure_scal (P := IsThetaFunO ψ S T) (fun v : FVar D T.rank S.rank => v.1) μ
    (fun a _ => GlobalTheory.OrientedHeis.theta_smul a) hA Asm key hf α

end GlobalTheory.FockScal
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

open scoped ComplexOrder

theorem sig_eq_of_definite {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef ∨ (-G).PosDef) {p q : ℕ}
    (h : Formalism.UG.HasSignature G p q) : (p, q) = (n, 0) ∨ (p, q) = (0, n) := by
  rcases hG with hG | hG
  · exact Or.inl (GlobalTheory.DefLiftMult.sig_of_posDef hG h)
  · right
    obtain ⟨hn, Q, hQ⟩ := Formalism.UG.P.sig_data G p q h
    have hp : p = 0 := by
      by_contra hp
      have i : Fin p := ⟨0, Nat.pos_of_ne_zero hp⟩
      have h1 := (hG.posSemidef.conjTranspose_mul_mul_same Q).diag_nonneg (i := Sum.inl i)
      rw [Matrix.mul_neg, Matrix.neg_mul, hQ] at h1
      simp [Formalism.UG.Jpq] at h1
      exact absurd h1 (by norm_num)
    subst hp
    simp at hn
    rw [hn]

theorem isDefinite_of_defSp {D : D7} {A : HSp D} (x : DefSp A) (hx : x.Is) : A.IsDefinite := by
  have hτ : ∀ τ, (gramAt D A τ).PosDef ∨ (-(gramAt D A τ)).PosDef := by
    intro τ
    have hp := (hx.cart τ).2.2
    rcases hx.pm τ with h | h
    · left
      rwa [h, Matrix.mul_one] at hp
    · right
      rwa [h, Matrix.mul_neg, Matrix.mul_one] at hp
  intro σ
  have hs := hx.sig σ
  have key : (A.sig σ).1 = A.rank ∧ (A.sig σ).2 = 0 ∨ (A.sig σ).1 = 0 ∧ (A.sig σ).2 = A.rank := by
    obtain ⟨τ, rfl | rfl⟩ := GlobalTheory.DefLiftMult.exists_tauE D σ
    · simpa [Prod.ext_iff] using sig_eq_of_definite (hτ τ) hs
    · have e : A.gram.map ((starRingEnd ℂ).comp (tauE D τ)) = (gramAt D A τ)ᴴᵀ := by
        ext i j
        rfl
      rw [e] at hs
      have hd : ((gramAt D A τ)ᴴᵀ).PosDef ∨ (-(gramAt D A τ)ᴴᵀ).PosDef := by
        rcases hτ τ with h | h
        · exact Or.inl h.conjTranspose.transpose
        · right
          have := h.conjTranspose.transpose
          rwa [Matrix.conjTranspose_neg, Matrix.transpose_neg] at this
      simpa [Prod.ext_iff] using sig_eq_of_definite hd hs
  rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (Prod.ext h1 h2)
  · exact Or.inr (Prod.ext h1 h2)

theorem isCompact_ginfC_of_defSp : ∀ (D : D7) (A : HSp D) (x : DefSp A), x.Is → IsCompact (GinfC A : Set (GA D A)) :=
  fun _ _ x hx => Formalism.IndefR.Eqv.isCompact_GinfC hx.sig (isDefinite_of_defSp x hx)

end GlobalTheory.SeeSaw

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.isThetaFunction_superposition_orthogonalSlices : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A B T : HSp D) (o : OrthDec S A B) (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (k : Ω → WO B T) (a : Ω → ℂ), Measurable k → Integrable a μ → IsThetaFunO ψ A T fun u => ∫ w, a w * F ((o.resS T).symm (u, k w)) ∂μ := by
  first | exact @GlobalTheory.SuperposS.superpos_isTheta | exact GlobalTheory.SuperposS.superpos_isTheta | (intros; apply GlobalTheory.SuperposS.superpos_isTheta <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

theorem _root_.GlobalTheory.T.isSelfDualLatticeAtPlace_latticeCompletion : ∀ (D : D7) (S : HSp D) (L : Lat S) (v : Pl D), IsSelfDualC S L → IsSDAt S v (latV S L (· = v)) := by
  first | exact @GlobalTheory.IwaPlace.LocSD.isSDAt_latV | exact GlobalTheory.IwaPlace.LocSD.isSDAt_latV | (intros; apply GlobalTheory.IwaPlace.LocSD.isSDAt_latV <;> assumption)
end
