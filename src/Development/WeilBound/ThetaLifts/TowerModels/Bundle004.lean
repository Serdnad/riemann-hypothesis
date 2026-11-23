module

import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle067
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle022
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.WeilBound.ThetaLifts.TowerModels.Bundle002
public import Development.WeilBound.ThetaLifts.TowerModels.Bundle003
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.PlaneRemovalConfiguration
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

noncomputable section

namespace PositivityTheory.ThKG.Tow.Pln

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem trace_mixedEmbedding (y : F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (mixedEmbedding F y) = (Algebra.trace ℚ F y : ℝ) :=
  _root_.UpperTheory.Reformulated.B.DYhb7.main y

theorem psi_fin_rat {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (x : F) :
    ψ (pairA F 0 (algebraMap F (Af F) x)) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F x : ℚ) : ℂ)) := by
  apply Tw.LatVacArith.psi_fin_rat <;> assumption

theorem psi_int {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (t : F)
    (ht : ∀ a : 𝓞 F, ∃ k : ℤ, Algebra.trace ℚ F ((a : F) * t) = k) (α : Af F) (hα : ∀ v, α v ∈ v.adicCompletionIntegers F) :
    ψ (pairA F 0 (α * algebraMap F (Af F) t)) = 1 := by
  refine GlobalTheory.IntDense.addChar_eq_one_of_integral F ψ hψ.1 t (fun a => ?_) α hα
  obtain ⟨k, hk⟩ := ht a
  rw [psi_fin_rat hψ, hk, Complex.exp_eq_one_iff]
  exact ⟨k, by push_cast; ring⟩

theorem trace_cm (h : IsCMExt F E σ) (x : E) : algebraMap F E (Algebra.trace F E x) = x + σ x := by
  classical
  have h1 := trace_eq_sum_embeddings (K := F) (L := E) (AlgebraicClosure E) (x := x)
  let τ : E →ₐ[F] AlgebraicClosure E := IsScalarTower.toAlgHom F E _
  have h2 : (Finset.univ : Finset (E →ₐ[F] AlgebraicClosure E)) = {τ, τ.comp σ} := by
    ext τ'
    simpa using eq_or_eq_comp_conj h τ τ'
  rw [h2, Finset.sum_pair (comp_conj_ne h τ).symm] at h1
  apply (algebraMap E (AlgebraicClosure E)).injective
  rw [← IsScalarTower.algebraMap_apply, h1, map_add (f := _)]
  rfl

theorem val_le_one_of_codiff {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {v : Pl F} (hv : PsiUnr ψ v) (a : F)
    (ha : ∀ o : 𝓞 F, IsIntegral ℤ (Algebra.trace ℚ F (o * a))) : Valued.v (algebraMap F (Fv F v) a) ≤ 1 := by
  have h2 := psi_int hψ a fun o => by
    obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 (ha o)
    exact ⟨k, hk.symm⟩
  refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ((hv _).1 fun y hy => ?_)
  have h3 := h2 (singleFin v y) fun w => by
    by_cases hw : w = v
    · subst hw
      change evalV _ w (singleFin w y) ∈ _
      rw [evalV_singleFin_self]
      exact hy
    · change evalV _ w (singleFin v y) ∈ _
      rw [evalV_singleFin_ne hw]
      exact zero_mem _
  have e : singleFin v y * algebraMap F (Af F) a = singleFin v (algebraMap F (Fv F v) a * y) := by
    apply af_ext
    intro u
    by_cases hu : u = v
    · subst hu
      rw [map_mul, evalV_singleFin_self, evalV_singleFin_self, mul_comm]
      rfl
    · rw [map_mul, evalV_singleFin_ne hu, evalV_singleFin_ne hu, zero_mul]
  rw [e] at h3
  exact h3


variable (E) in
def codE : Submodule (𝓞 E) E where
  carrier := {c | ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * c))}
  zero_mem' o := by simpa using isIntegral_zero
  add_mem' ha hb o := by rw [mul_add, map_add (f := _)]; exact (ha o).add (hb o)
  smul_mem' a c hc o := by
    have := hc (o * a)
    change IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * (a : E) * c)) at this
    rwa [mul_assoc] at this

theorem one_mem_codE : (1 : E) ∈ codE E := fun o => by
  rw [mul_one]; exact Algebra.isIntegral_trace o.isIntegral_coe


variable (E) in
def intE : Submodule (𝓞 E) E where
  carrier := {c | IsIntegral ℤ c}
  zero_mem' := isIntegral_zero
  add_mem' ha hb := ha.add hb
  smul_mem' a _ hc := a.isIntegral_coe.mul hc

theorem val_le_one_of_intE {v : Pl F} (τ : E →ₐ[F] Fv F v) (c : E) (hc : c ∈ intE E) : Valued.v (τ c) ≤ 1 :=
  apply_coe_mem τ (⟨c, hc⟩ : 𝓞 E)

theorem val_le_one_of_codE (h : IsCMExt F E σ) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {v : Pl F} (hv : PsiUnr ψ v)
    (τ : E →ₐ[F] Fv F v) (c : E) (hc : c ∈ codE E) : Valued.v (τ c) ≤ 1 := by
  have h1 : ∀ o : 𝓞 E, Valued.v (τ (o * c) + τ (σ (o * c))) ≤ 1 := fun o => by
    rw [← map_add (f := _), ← trace_cm h, AlgHom.commutes]
    refine val_le_one_of_codiff hψ hv _ fun a => ?_
    have := hc (algebraMap (𝓞 F) (𝓞 E) a * o)
    rw [← Algebra.trace_trace (S := F)] at this
    convert this using 2
    rw [← smul_eq_mul, ← map_smul, Algebra.smul_def, ← mul_assoc]
    rfl
  have hne : ¬ (splitPrime (τ.comp σ)).asIdeal ≤ (splitPrime τ).asIdeal := fun hle =>
    splitPrime_comp_ne h τ (HeightOneSpectrum.ext
      ((splitPrime (τ.comp σ)).isMaximal.eq_of_le (splitPrime τ).isPrime.ne_top hle))
  obtain ⟨p, hp, hp'⟩ := Set.not_subset.1 hne
  have a1 : Valued.v (τ (σ p)) < 1 := (mem_splitPrime (τ.comp σ) p).1 hp
  have a2 : Valued.v (τ p) = 1 := le_antisymm (apply_coe_mem τ p) (not_lt.1 fun e => hp' ((mem_splitPrime τ p).2 e))
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Valued.v (τ (σ p)) ^ k * Valued.v (τ (σ c)) ≤ 1 := by
    by_cases h0 : Valued.v (τ (σ c)) = 0
    · exact ⟨0, by simp [h0]⟩
    · obtain ⟨k, hk⟩ := exists_pow_lt₀ a1 (Units.mk0 _ h0)⁻¹
      refine ⟨k, ?_⟩
      rw [Units.val_inv_eq_inv_val, Units.val_mk0] at hk
      calc _ ≤ (Valued.v (τ (σ c)))⁻¹ * Valued.v (τ (σ c)) := by gcongr
        _ = 1 := inv_mul_cancel₀ h0
  have b1 := h1 (p ^ k)
  have b2 : Valued.v (τ (σ (((p ^ k : 𝓞 E) : E) * c))) ≤ 1 := by
    push_cast
    simpa only [map_mul, map_pow] using hk
  have b3 := Valuation.map_sub_le _ b1 b2
  rw [add_sub_cancel_right] at b3
  push_cast at b3
  simpa only [map_mul, map_pow, a2, one_pow, one_mul] using b3

end PositivityTheory.ThKG.Tow.Pln

end
end

section

noncomputable section

namespace PositivityTheory.ThKG.Tow.Pln

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_adapted_pair (h : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hdet : J.det ≠ 0) {ε : E}
    (hε : ε = 1 ∨ ε = -1) (hJ : ∀ i j, σ (J j i) = ε * J i j) (D : Submodule (𝓞 E) E) (hD1 : (1 : E) ∈ D)
    (L : Submodule (𝓞 E) (Fin n → E)) (hlat : L.IsFullLattice E) (hd : ∀ y, y ∈ L ↔ ∀ x ∈ L, form σ J y x ∈ D)
    (θ : 𝓞 E) (hθ : (θ : E) + σ θ = 1) (P : Finset (Pl F)) (τ : ∀ v : P, E →ₐ[F] Fv F v)
    (hDτ : ∀ v, ∀ c ∈ D, Valued.v (τ v c) ≤ 1) (x₀ : Fin n → E) (hx₀ : x₀ ≠ 0) (hxx₀ : form σ J x₀ x₀ = 0) :
    ∃ x y : Fin n → E, form σ J x x = 0 ∧ form σ J y y = 0 ∧ form σ J x y = 1 ∧
      (∀ z ∈ L, form σ J z x • y ∈ L ∧ form σ J z y • x ∈ L) ∧
      ∀ v : P, ((∀ c : E, c • x ∈ L → Valued.v (τ v c) ≤ 1) ∧ ∃ c : E, c • x ∈ L ∧ Valued.v (τ v c) = 1) ∧
        ((∀ c : E, c • y ∈ L → Valued.v (τ v c) ≤ 1) ∧ ∃ c : E, c • y ∈ L ∧ Valued.v (τ v c) = 1) := by
  classical
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> simp
  have hεv : ∀ v, Valued.v (τ v ε) = 1 := fun v => by rcases hε with rfl | rfl <;> simp
  have hεD : ∀ a ∈ D, ε * a ∈ D := fun a ha => by
    rcases hε with rfl | rfl
    · simpa using ha
    · simpa using ha
  have sw : ∀ a b, form σ J b a = ε * σ (form σ J a b) := fun a b => by
    rw [form_swap h hJ, ← mul_assoc, hεε, one_mul]
  have hne : ∃ z ∈ L, formL (σ := σ) J x₀ z ≠ 0 := by
    by_contra H
    push Not at H
    have h0 : formL (σ := σ) J x₀ = 0 := LinearMap.ext_on hlat.span_eq_top fun z hz => H z hz
    have h1 : J *ᵥ (fun i => σ (x₀ i)) = 0 := by
      funext k
      have := LinearMap.congr_fun h0 (Pi.single k 1)
      simpa [formL, form] using this
    have h2 := Matrix.eq_zero_of_mulVec_eq_zero hdet h1
    exact hx₀ (funext fun i => by simpa using congrFun h2 i)
  let S : Finset (HeightOneSpectrum (𝓞 E)) :=
    Finset.univ.image (fun v : P => splitPrime (τ v)) ∪ Finset.univ.image (fun v : P => splitPrime ((τ v).comp σ))
  obtain ⟨z₀, hz₀, hc0, hmax⟩ := exists_max_val L hlat.fg (formL (σ := σ) J x₀) hne S
  change form σ J z₀ x₀ ≠ 0 at hc0
  set c₀ := form σ J z₀ x₀ with hc₀
  obtain ⟨x, hxx, hz₀x, hle⟩ : ∃ x, form σ J x x = 0 ∧ form σ J z₀ x = 1 ∧
      ∀ w ∈ S, ∀ z ∈ L, w.valuation E (form σ J z x) ≤ 1 := by
    refine ⟨σ c₀⁻¹ • x₀, by rw [form_smul_left, form_smul_right, hxx₀]; simp,
      by rw [form_smul_right, sigma_sigma h, inv_mul_cancel₀ hc0], fun w hw z hz => ?_⟩
    rw [form_smul_right, sigma_sigma h, map_mul, map_inv₀]
    exact inv_mul_le_one_of_le₀ (hmax w hw z hz) zero_le
  obtain ⟨y, hyy, hxy, hL⟩ := exists_partner h hε hJ D L hlat.fg hd θ hθ x hxx z₀ hz₀ (by rw [hz₀x]; exact one_ne_zero)
  have hyx : form σ J y x = ε := by rw [sw, hxy, map_one, mul_one]
  refine ⟨x, y, hxx, hyy, hxy, hL, fun v => ⟨⟨fun c hc => ?_, ?_⟩, fun c hc => ?_, 1, ?_, by simp⟩⟩
  · have := hεD _ ((hd _).1 hc z₀ hz₀)
    rw [form_smul_left, sw z₀ x, hz₀x, map_one, mul_one, mul_left_comm, hεε, mul_one] at this
    exact hDτ v c this
  · obtain ⟨d, hdw, hdC⟩ := exists_denom (L.map ((formL (σ := σ) J x).restrictScalars (𝓞 E))) (hlat.fg.map _)
      (splitPrime ((τ v).comp σ)) (by
        rintro _ ⟨z, hz, rfl⟩
        exact hle _ (by simp [S]) z hz)
    refine ⟨σ d, (hd _).2 fun z hz => ?_, ?_⟩
    · obtain ⟨o, ho⟩ := hdC _ ⟨z, hz, rfl⟩
      change (d : E) * form σ J z x = o at ho
      rw [form_smul_left, sw z x, mul_left_comm, ← map_mul, ho]
      refine hεD _ ?_
      have := D.smul_mem (conjInt σ o) hD1
      rwa [← algebraMap_smul E, smul_eq_mul, mul_one] at this
    · change Valued.v (((τ v).comp σ) d) = 1
      rw [valued_apply_eq_valuation]
      exact ((splitPrime ((τ v).comp σ)).valuation_eq_one_iff_notMem (K := E)).2 hdw
  · have := hle (splitPrime (τ v)) (by simp [S]) _ hc
    rwa [form_smul_left, hyx, ← valued_apply_eq_valuation, map_mul, map_mul, hεv, mul_one] at this
  · have := (hL z₀ hz₀).1
    rwa [hz₀x] at this

end PositivityTheory.ThKG.Tow.Pln

end
end

section

noncomputable section

namespace PositivityTheory.ThKG.Tow

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem resEtaPow_of_add_two {R E : Type} [CommRing R] [CommRing E] [Algebra R E] {K : Subgroup Rˣ}
    {χ : Eˣ →* Circle} {n : ℕ} (h : ResEtaPow K χ (n + 2)) : ResEtaPow K χ n := by
  intro a
  rw [h a]
  simp [pow_add]

theorem resEtaPow_div {R E : Type} [CommRing R] [CommRing E] [Algebra R E] {K : Subgroup Rˣ}
    {χ χ' : Eˣ →* Circle} {n m : ℕ} (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' m) :
    ResEtaPow K (χ / χ') (n + m) := by
  intro a
  rw [MonoidHom.div_apply, Circle.coe_div, h a, h' a]
  split_ifs
  · simp
  · rw [div_eq_mul_inv, ← inv_pow, inv_neg, inv_one, ← pow_add]

theorem isHecke_div {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {χ χ' : Chr F E} (h : IsHecke F E χ) (h' : IsHecke F E χ') : IsHecke F E (χ / χ') := by
  refine ⟨h.1.div' h'.1, fun x => ?_⟩
  simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_one]

theorem towerB_of (hP : PlaneEx) (hM : ModelEx) (hW : WeilEx) : TowerB := by
  intro F E _ _ _ _ _ σ B a b G X om om' hT hq
  have g := hT.geo
  have c := hT.chars
  have hb := g.aBig
  have hl := g.lt
  obtain ⟨Y', V₁, H, hY', hV₁, hH⟩ := hP.1 F E σ B hT.base (b + 2) b rfl (by omega) G.V' G.q (b + 2 - G.q)
    hq (by omega) g.hV' 0 (b + 1) (by omega) (by omega)
  obtain ⟨W', W₁, H', hW', hW₁, hH'⟩ := hP.2 F E σ B hT.base (a + (b + 2)) (a + b) (by omega) (by omega) G.W
    (a + (b + 2) - (G.p + G.q)) (G.p + G.q) (by omega) (by omega) g.hW a (a + b + 1) (by omega) (by omega)
  have hV0 : (reS G.V G.V).IsHerm σ B (a - G.p) G.p := g.hV
  obtain ⟨M₁, hM₁⟩ := hM F E σ B hT.base a (a + b) (reS G.V G.V) W₁ _ _ _ _ hV0 hW₁
  obtain ⟨M₁', hM₁'⟩ := hM F E σ B hT.base b (a + b) V₁ W₁ _ _ _ _ hV₁ hW₁
  have rα : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range X.α b := resEtaPow_of_add_two c.resα
  obtain ⟨om₁, hom₁⟩ := hW F E σ B hT.base a (a + b) (reS G.V G.V) W₁ _ _ _ _ hV0 hW₁ M₁ hM₁ X.β (X.β / X.α)
    c.heckeβ (isHecke_div c.heckeβ c.heckeα) c.resβ (resEtaPow_div c.resβ rα)
  obtain ⟨om₁', hom₁'⟩ := hW F E σ B hT.base b (a + b) V₁ W₁ _ _ _ _ hV₁ hW₁ M₁' hM₁' X.α (X.α / X.β)
    c.heckeα (isHecke_div c.heckeα c.heckeβ) rα (by rw [Nat.add_comm]; exact resEtaPow_div rα c.resβ)
  refine ⟨G.V, Y', W', ⟨hT.base, ⟨g.lt, g.even, g.kappa, g.eBig, g.aBig, hV0, hY', hW', ⟨g.hM.rat, g.hM.vac, g.hM.std, g.hM.haar, g.hM.dom⟩,
      ⟨g.hM'.rat, g.hM'.vac, g.hM'.std, g.hM'.haar, g.hM'.dom⟩⟩, c, hT.weil, hT.weil'⟩,
    ⟨G.p, G.q - 1, reS G.V G.V, V₁, W₁, M₁, M₁'⟩, H, H', ⟨rfl, rfl, ?_, hH, hH'⟩, om₁, om₁', ⟨hT.base, ?_, ?_, hom₁, hom₁'⟩⟩
  · show G.q - 1 + 1 = G.q
    omega
  · have he := g.eBig
    refine ⟨by omega, ?_, fun w => ?_, ?_, ?_, hV0, ?_, ?_, hM₁, hM₁'⟩
    · obtain ⟨k, hk⟩ := g.even
      exact ⟨k - 1, by omega⟩
    · have := g.kappa w
      push_cast at this ⊢
      omega
    · show 2 * (G.p + (G.q - 1)) + 1 < (a - b) / 2
      omega
    · show 2 * (G.p + (G.q - 1)) + 1 < b
      omega
    · show V₁.IsHerm σ B (G.q - 1) (b - (G.q - 1))
      rw [show b - (G.q - 1) = b + 2 - G.q - 1 by omega]
      exact hV₁
    · show W₁.IsSkew σ B (a + b - (G.p + (G.q - 1))) (G.p + (G.q - 1))
      rw [show a + b - (G.p + (G.q - 1)) = a + (b + 2) - (G.p + G.q) - 1 by omega,
        show G.p + (G.q - 1) = G.p + G.q - 1 by omega]
      exact hW₁
  · exact ⟨c.heckeα, c.heckeβ, rα, c.resβ, c.expα, c.expβ, c.disj, c.sub, c.ram, c.unrα, c.unrβ, c.good⟩

theorem towerA_of (hP : PlaneEx) (hM : ModelEx) (hW : WeilEx) : TowerA := by
  intro F E _ _ _ _ _ σ B b a' G X om om' hT hq0 hp
  have g := hT.geo
  have c := hT.chars
  have hb := g.aBig
  have hl := g.lt
  have he := g.eBig
  rw [hq0] at hb he
  obtain ⟨Y', V₁, H, hY', hV₁, hH⟩ := hP.1 F E σ B hT.base (b + 2) b rfl (by omega) G.V (b + 2 - G.p) G.p
    (by omega) hp g.hV 0 (b + 1) (by omega) (by omega)
  have hW0 := g.hW
  rw [hq0] at hW0
  obtain ⟨W', W₁, H', hW', hW₁, hH'⟩ := hP.2 F E σ B hT.base (b + 2 + a') (b + a') (by omega) (by omega) G.W
    (b + 2 + a' - (G.p + 0)) (G.p + 0) (by omega) (by omega) hW0 0 (b + 1) (by omega) (by omega)
  have hV0' : (reS G.V' G.V').IsHerm σ B 0 (a' - 0) := by
    have := g.hV'
    rw [hq0] at this
    exact this
  obtain ⟨M₁, hM₁⟩ := hM F E σ B hT.base b (b + a') V₁ W₁ _ _ _ _ hV₁ hW₁
  obtain ⟨M₁', hM₁'⟩ := hM F E σ B hT.base a' (b + a') (reS G.V' G.V') W₁ _ _ _ _ hV0' hW₁
  have rβ : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range X.β b := resEtaPow_of_add_two c.resβ
  obtain ⟨om₁, hom₁⟩ := hW F E σ B hT.base b (b + a') V₁ W₁ _ _ _ _ hV₁ hW₁ M₁ hM₁ X.β (X.β / X.α)
    c.heckeβ (isHecke_div c.heckeβ c.heckeα) rβ (resEtaPow_div rβ c.resα)
  obtain ⟨om₁', hom₁'⟩ := hW F E σ B hT.base a' (b + a') (reS G.V' G.V') W₁ _ _ _ _ hV0' hW₁ M₁' hM₁' X.α (X.α / X.β)
    c.heckeα (isHecke_div c.heckeα c.heckeβ) c.resα (by rw [Nat.add_comm]; exact resEtaPow_div c.resα rβ)
  refine ⟨Y', G.V', W', ⟨hT.base, ⟨g.lt, g.even, g.kappa, g.eBig, g.aBig, hY', g.hV',
      (by show (reS G.W W').IsSkew σ B (b + 2 + a' - (G.p + G.q)) (G.p + G.q); rw [hq0]; exact hW'),
      ⟨g.hM.rat, g.hM.vac, g.hM.std, g.hM.haar, g.hM.dom⟩, ⟨g.hM'.rat, g.hM'.vac, g.hM'.std, g.hM'.haar, g.hM'.dom⟩⟩,
      c, hT.weil, hT.weil'⟩,
    ⟨G.p - 1, 0, V₁, reS G.V' G.V', W₁, M₁, M₁'⟩, H, H', ⟨rfl, hq0, rfl, ?_, hH, hH'⟩, om₁, om₁', ⟨hT.base, ?_, ?_, hom₁, hom₁'⟩⟩
  · show G.p - 1 + 1 = G.p
    omega
  · refine ⟨?_, ?_, fun w => ?_, ?_, ?_, ?_, hV0', ?_, hM₁, hM₁'⟩
    · show a' < b
      omega
    · obtain ⟨k, hk⟩ := g.even
      exact ⟨k - 1, by omega⟩
    · have := g.kappa w
      push_cast at this ⊢
      omega
    · show 2 * (G.p - 1 + 0) + 1 < (b - a') / 2
      omega
    · show 2 * (G.p - 1 + 0) + 1 < a'
      omega
    · show V₁.IsHerm σ B (b - (G.p - 1)) (G.p - 1)
      rw [show b - (G.p - 1) = b + 2 - G.p - 1 by omega]
      exact hV₁
    · show W₁.IsSkew σ B (b + a' - (G.p - 1 + 0)) (G.p - 1 + 0)
      rw [show b + a' - (G.p - 1 + 0) = b + 2 + a' - (G.p + 0) - 1 by omega,
        show G.p - 1 + 0 = G.p + 0 - 1 by omega]
      exact hW₁
  · exact ⟨c.heckeα, c.heckeβ, c.resα, rβ, c.expα, c.expβ, c.disj, c.sub, c.ram, c.unrα, c.unrβ, c.good⟩

theorem towerCodimensionTwo_of (hP : PlaneEx) (hM : ModelEx) (hW : WeilEx) : PositivityTheory.ThKEnd.TowerCodimensionTwo := by
  intro F E _ _ _ _ _ σ B b a' G X om om' hT hp
  have g := hT.geo
  have c := hT.chars
  have hb := g.aBig
  have hl := g.lt
  have he := g.eBig
  obtain ⟨Y', V₁, H, hY', hV₁, hH⟩ := hP.1 F E σ B hT.base (b + 2) b rfl (by omega) G.V (b + 2 - G.p) G.p
    (by omega) hp g.hV 0 (b + 1) (by omega) (by omega)
  obtain ⟨W', W₁, H', hW', hW₁, hH'⟩ := hP.2 F E σ B hT.base (b + 2 + a') (b + a') (by omega) (by omega) G.W
    (b + 2 + a' - (G.p + G.q)) (G.p + G.q) (by omega) (by omega) g.hW 0 (b + 1) (by omega) (by omega)
  have hV0' : (reS G.V' G.V').IsHerm σ B G.q (a' - G.q) := g.hV'
  obtain ⟨M₁, hM₁⟩ := hM F E σ B hT.base b (b + a') V₁ W₁ _ _ _ _ hV₁ hW₁
  obtain ⟨M₁', hM₁'⟩ := hM F E σ B hT.base a' (b + a') (reS G.V' G.V') W₁ _ _ _ _ hV0' hW₁
  have rβ : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range X.β b := resEtaPow_of_add_two c.resβ
  obtain ⟨om₁, hom₁⟩ := hW F E σ B hT.base b (b + a') V₁ W₁ _ _ _ _ hV₁ hW₁ M₁ hM₁ X.β (X.β / X.α)
    c.heckeβ (isHecke_div c.heckeβ c.heckeα) rβ (resEtaPow_div rβ c.resα)
  obtain ⟨om₁', hom₁'⟩ := hW F E σ B hT.base a' (b + a') (reS G.V' G.V') W₁ _ _ _ _ hV0' hW₁ M₁' hM₁' X.α (X.α / X.β)
    c.heckeα (isHecke_div c.heckeα c.heckeβ) c.resα (by rw [Nat.add_comm]; exact resEtaPow_div c.resα rβ)
  refine ⟨Y', G.V', W', ⟨hT.base, ⟨g.lt, g.even, g.kappa, g.eBig, g.aBig, hY', g.hV', hW',
      ⟨g.hM.rat, g.hM.vac, g.hM.std, g.hM.haar, g.hM.dom⟩, ⟨g.hM'.rat, g.hM'.vac, g.hM'.std, g.hM'.haar, g.hM'.dom⟩⟩,
      c, hT.weil, hT.weil'⟩,
    ⟨G.p - 1, G.q, V₁, reS G.V' G.V', W₁, M₁, M₁'⟩, H, H', ⟨rfl, rfl, ?_, hH, hH'⟩, om₁, om₁', ⟨hT.base, ?_, ?_, hom₁, hom₁'⟩⟩
  · show G.p - 1 + 1 = G.p
    omega
  · refine ⟨?_, ?_, fun w => ?_, ?_, ?_, ?_, hV0', ?_, hM₁, hM₁'⟩
    · show a' < b
      omega
    · obtain ⟨k, hk⟩ := g.even
      exact ⟨k - 1, by omega⟩
    · have := g.kappa w
      push_cast at this ⊢
      omega
    · show 2 * (G.p - 1 + G.q) + 1 < (b - a') / 2
      omega
    · show 2 * (G.p - 1 + G.q) + 1 < a'
      omega
    · show V₁.IsHerm σ B (b - (G.p - 1)) (G.p - 1)
      rw [show b - (G.p - 1) = b + 2 - G.p - 1 by omega]
      exact hV₁
    · show W₁.IsSkew σ B (b + a' - (G.p - 1 + G.q)) (G.p - 1 + G.q)
      rw [show b + a' - (G.p - 1 + G.q) = b + 2 + a' - (G.p + G.q) - 1 by omega,
        show G.p - 1 + G.q = G.p + G.q - 1 by omega]
      exact hW₁
  · exact ⟨c.heckeα, c.heckeβ, c.resα, rβ, c.expα, c.expβ, c.disj, c.sub, c.ram, c.unrα, c.unrβ, c.good⟩

end PositivityTheory.ThKG.Tow

end
end
