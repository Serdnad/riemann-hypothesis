module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle194
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle174
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle319
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle286
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle320
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle180
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeSum.GrowthAtPlace

open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.AutSpace

variable {n : ℕ} {ε : Fin n → Bool} {P G : Mx n}

theorem norm_entry_le (A : Mx n) (i j : Fin n) : ‖A i j‖ ≤ 1 + hs A := by
  have h : ‖A i j‖ ^ 2 ≤ hs A :=
    (Finset.single_le_sum (f := fun b => ‖A i b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun a => ∑ b, ‖A a b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i))
  nlinarith [norm_nonneg (A i j)]

theorem one_add_hs_conj_le (Q y P : Mx n) : 1 + hs (Q * y * P) ≤ (1 + hs Q) * (1 + hs P) * (1 + hs y) := by
  have h1 := one_add_hs_mul_le (Q * y) P
  have h2 := mul_le_mul_of_nonneg_right (one_add_hs_mul_le Q y) (show 0 ≤ 1 + hs P by linarith [hs_nonneg P])
  nlinarith

theorem conj_mul (hP : IsUnit P) (a b : Mx n) : P⁻¹ * (a * b) * P = (P⁻¹ * a * P) * (P⁻¹ * b * P) := by
  have hd := (isUnit_iff_isUnit_det _).1 hP
  calc P⁻¹ * (a * b) * P = P⁻¹ * a * (P * P⁻¹) * b * P := by
        rw [Matrix.mul_nonsing_inv _ hd]; simp only [Matrix.mul_assoc, Matrix.one_mul]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem conj_exp (hP : IsUnit P) (X : Mx n) (t : ℝ) :
    P⁻¹ * NormedSpace.exp (t • X) * P = NormedSpace.exp (t • (P⁻¹ * X * P)) := by
  have hd := (isUnit_iff_isUnit_det _).1 hP
  rw [Matrix.mul_assoc, exp_mul_eq hP, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]

theorem conj_lie (hP : IsUnit P) (h : Pᴴ * Jm ε * P = G) {X : Mx n} (hX : X ∈ lieSet ε) :
    (P⁻¹ * X * P)ᴴ * G + G * (P⁻¹ * X * P) = 0 := by
  have hd := (isUnit_iff_isUnit_det _).1 hP
  have h1 : Xᴴ * Jm ε + Jm ε * X = 0 := hX
  calc (P⁻¹ * X * P)ᴴ * G + G * (P⁻¹ * X * P)
      = Pᴴ * Xᴴ * (P * P⁻¹)ᴴ * Jm ε * P + Pᴴ * Jm ε * (P * P⁻¹) * X * P := by
        rw [← h]; simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Pᴴ * (Xᴴ * Jm ε + Jm ε * X) * P := by
        rw [Matrix.mul_nonsing_inv _ hd]
        simp only [conjTranspose_one, Matrix.mul_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [h1, Matrix.mul_zero, Matrix.zero_mul]

theorem normInf_atTau_le {D : D7} {θ : InfF D} (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau)
    {ε : Fin V.rank → Bool} {P : Mx V.rank} (hP : IsUnit P) (h : Pᴴ * Jm ε * P = gramAt D V τ) :
    ∃ c : ℝ, ∀ y ∈ UJset ε, normInf θ V (atTau θ V τ (P⁻¹ * y * P)) ≤ c * (1 + hs y) := by
  have hd := (isUnit_iff_isUnit_det _).1 hP
  set K : ℝ := (1 + hs P⁻¹) * (1 + hs P) + (1 + hs (1 : Mx V.rank)) with hK
  refine ⟨∑ _τ : D.what₂.Tau, ∑ _i : Fin V.rank, ∑ _j : Fin V.rank, (K + K), fun y hy => ?_⟩
  have hs1 := hs_nonneg (1 : Mx V.rank)
  have hsy := hs_nonneg y
  have hPP : 0 ≤ (1 + hs P⁻¹) * (1 + hs P) := mul_nonneg (by linarith [hs_nonneg P⁻¹]) (by linarith [hs_nonneg P])
  have b1 : ∀ z : Mx V.rank, hs z = hs y → 1 + hs (P⁻¹ * z * P) ≤ K * (1 + hs y) := fun z hz => by
    have := one_add_hs_conj_le P⁻¹ z P
    rw [hz] at this
    nlinarith
  have b2 : 1 + hs (1 : Mx V.rank) ≤ K * (1 + hs y) := by nlinarith
  have sp := atTau_spec hθ V τ (conj_inv_mem hP h hy)
  unfold normInf
  simp only [Finset.sum_mul]
  refine Finset.sum_le_sum fun τ' _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have e := infMat_mul_inv θ V τ' (atTau θ V τ (P⁻¹ * y * P))
  rw [add_mul]
  refine add_le_add ((norm_entry_le _ i j).trans ?_) ((norm_entry_le _ i j).trans ?_)
  · by_cases c : τ' = τ
    · subst c
      rw [sp.2.1]
      exact b1 y rfl
    · rw [sp.2.2 τ' c]
      exact b2
  · by_cases c : τ' = τ
    · subst c
      rw [sp.2.1] at e
      have e2 : (P⁻¹ * y⁻¹ * P) * (P⁻¹ * y * P) = 1 := by
        rw [← conj_mul hP, inv_mul_UJ hy, Matrix.mul_one, Matrix.nonsing_inv_mul _ hd]
      rw [← left_inv_eq_right_inv e2 e]
      exact b1 _ (hs_inv hy)
    · rw [sp.2.2 τ' c, Matrix.one_mul] at e
      rw [e]
      exact b2

theorem umg_atTau : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (φ : GA D V → ℂ), IsAutFunSm θ V φ → ∀ (ε : Fin V.rank → Bool) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = gramAt D V τ → ∀ x : GA D V, GlobalTheory.TypeSum.UMG ε (fun y => φ (x * atTau θ V τ (P⁻¹ * y * P))) := by
  intro D θ hθ V τ φ hφ ε P hP h x
  obtain ⟨N, hN⟩ := hφ.growth
  obtain ⟨c, hc⟩ := normInf_atTau_le hθ V τ hP h
  have hl : ∀ l : List (Mx V.rank), (∀ Y ∈ l, Y ∈ lieSet ε) →
      ∀ p ∈ l.map fun X => (τ, P⁻¹ * X * P), p.2 ∈ lieAt V p.1 := fun l hl p hp => by
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hp
    exact conj_lie hP h (hl Y hY)
  refine ⟨N, fun l y => ((l.map fun X => (τ, P⁻¹ * X * P)).foldr (fun p f => Rder θ V p.1 p.2 f) φ)
    (x * atTau θ V τ (P⁻¹ * y * P)), fun _ _ => rfl, fun l hl' X hX g hg => ?_, fun l hl' => ?_⟩
  · have hs := (linOnSm_foldr (θ := θ) (fun p : D.what₂.Tau × Mx V.rank => Rder θ V p.1 p.2) _
      fun p hp => linOnSm_Rder (hl l hl' p hp)).mem φ hφ.smooth
    have hd := (differentiable_oneP hs (τ := τ) (conj_lie hP h hX) (x * atTau θ V τ (P⁻¹ * g * P)) 0).hasDerivAt
    refine HasDerivAt.congr_of_eventuallyEq hd (Filter.Eventually.of_forall fun t => ?_)
    beta_reduce
    rw [conj_mul hP, atTau_mul hθ V τ (conj_inv_mem hP h hg) (conj_inv_mem hP h (exp_mem_UJ hX t)), conj_exp hP,
      ← mul_assoc]
    rfl
  · obtain ⟨C, hC⟩ := hN _ (hl l hl') x
    refine ⟨|C| * c ^ N, fun g hg => (hC _ (atTau_mem V τ _)).trans ?_⟩
    have h0 := normInf_nonneg (θ := θ) (atTau θ V τ (P⁻¹ * g * P))
    rw [mul_assoc |C|, ← mul_pow]
    exact mul_le_mul (le_abs_self _) (pow_le_pow_left₀ h0 (hc g hg) N) (pow_nonneg h0 _) (abs_nonneg _)

end GlobalTheory.TypeSum.GrowthAtPlace

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open Formalism.L2.Host (HChar atFin unif ordF)
open GlobalTheory.CharValCompare (IsFr)

namespace GlobalTheory.Mem.Col2.DetProj

section General

variable {E : Type} [Field E] [NumberField E]

theorem valuation_eq_exp (w : HeightOneSpectrum (𝓞 E)) (k : Eˣ) :
    w.valuation E (k : E) = WithZero.exp (-_root_.Formalism.L2.Host.ordF w k) := by
  unfold _root_.Formalism.L2.Host.ordF
  rw [neg_neg, WithZero.exp_log (by simp)]

variable [StarRing E] {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem ordSub_conjP (p : DecoF E n ST SG Q) (w : HeightOneSpectrum (𝓞 E)) :
    ordSub (conjPrime₂ w) (detSub p.deco.1.N) = -ordSub w (detSub p.deco.1.N) := by
  have hfull : Submodule.IsFullLattice E p.deco.1.N := by
    letI : Submodule.IsLattice E p.deco.1.N := p.deco.2.lat
    refine ⟨?_⟩
    apply top_unique
    rw [← ((Pi.basisFun E (Fin n)).map (ptFr p w)).span_eq]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    obtain ⟨s, hs, hx⟩ := (mem_locP _ _ _).1 ((isFr_ptFr p w _).2 (CharValCompare.single_mem_stdAt w i))
    have hs0 : (algebraMap (𝓞 E) E s) ≠ 0 := by
      intro h
      have : s = 0 := (FaithfulSMul.algebraMap_injective (𝓞 E) E) (by simpa using h)
      exact hs (this ▸ w.asIdeal.zero_mem)
    have hx' : (algebraMap (𝓞 E) E s) • ptFr p w (Pi.single i 1) ∈ p.deco.1.N := by
      rwa [IsScalarTower.algebraMap_smul]
    have hm := Submodule.smul_mem (Submodule.span E (p.deco.1.N : Set (Sp E n)))
      (algebraMap (𝓞 E) E s)⁻¹ (Submodule.subset_span hx')
    rw [← mul_smul, inv_mul_cancel₀ hs0, one_smul] at hm
    simpa only [Module.Basis.map_apply, Pi.basisFun_apply, SetLike.mem_coe] using hm
  have h := CharValCompare.val_dual (P := w) ⟨p.deco.2.lat, p.deco.2.uni⟩ (isFr_ptFr p w) (isFr_ptFr p (conjPrime₂ w))
  rw [map_mul, valuation_star, CharValCompare.conjP_conjP] at h
  rw [ordSub_detSub_eq hfull (isFr_ptFr p w), ordSub_detSub_eq hfull (isFr_ptFr p (conjPrime₂ w))]
  have h' : w.valuation E ((LinearEquiv.det (ptFr p w) : Eˣ) : E) *
      (conjPrime₂ w).valuation E ((LinearEquiv.det (ptFr p (conjPrime₂ w)) : Eˣ) : E) = 1 := h
  rw [valuation_eq_exp, valuation_eq_exp, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_inj] at h'
  omega


open Classical in
theorem valued_compAt_detIdl (SB : Finset (HeightOneSpectrum (𝓞 E))) (p : DecoF E n ST SG Q)
    (w : HeightOneSpectrum (𝓞 E)) :
    Valued.v (compAt w (detIdl SB p.deco.1.N (ptFr p))) = WithZero.exp (-(if w ∈ SB then ordSub w (detSub p.deco.1.N)
      else if conjPrime₂ w ∈ SB then 0 else ((ordSub w (detSub p.deco.1.N)).toNat : ℤ))) := by
  have hfull : Submodule.IsFullLattice E p.deco.1.N := by
    letI : Submodule.IsLattice E p.deco.1.N := p.deco.2.lat
    refine ⟨?_⟩
    apply top_unique
    rw [← ((Pi.basisFun E (Fin n)).map (ptFr p w)).span_eq]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    obtain ⟨s, hs, hx⟩ := (mem_locP _ _ _).1 ((isFr_ptFr p w _).2 (CharValCompare.single_mem_stdAt w i))
    have hs0 : (algebraMap (𝓞 E) E s) ≠ 0 := by
      intro h
      have : s = 0 := (FaithfulSMul.algebraMap_injective (𝓞 E) E) (by simpa using h)
      exact hs (this ▸ w.asIdeal.zero_mem)
    have hx' : (algebraMap (𝓞 E) E s) • ptFr p w (Pi.single i 1) ∈ p.deco.1.N := by
      rwa [IsScalarTower.algebraMap_smul]
    have hm := Submodule.smul_mem (Submodule.span E (p.deco.1.N : Set (Sp E n)))
      (algebraMap (𝓞 E) E s)⁻¹ (Submodule.subset_span hx')
    rw [← mul_smul, inv_mul_cancel₀ hs0, one_smul] at hm
    simpa only [Module.Basis.map_apply, Pi.basisFun_apply, SetLike.mem_coe] using hm
  rw [compAt_detIdl SB p.deco.2.lat]
  split_ifs
  · rw [valued_algebraMap, valuation_eq_exp, ordSub_detSub_eq hfull (isFr_ptFr p w)]
  · simp
  · rw [map_pow, valued_algebraMap, valuation_eq_exp, ordF_unif_self, ← WithZero.exp_nsmul]
    simp

theorem valued_compAt_conjP {SB : Finset (HeightOneSpectrum (𝓞 E))} (hs : ∀ P ∈ SB, conjPrime₂ P ∉ SB)
    (p : DecoF E n ST SG Q) (w : HeightOneSpectrum (𝓞 E)) :
    Valued.v (compAt w (detIdl SB p.deco.1.N (ptFr p))) =
      Valued.v (compAt (conjPrime₂ w) (detIdl SB p.deco.1.N (ptFr p))) * WithZero.exp (-ordSub w (detSub p.deco.1.N)) := by
  rw [valued_compAt_detIdl, valued_compAt_detIdl, ← WithZero.exp_add, WithZero.exp_inj, CharValCompare.conjP_conjP,
    ordSub_conjP]
  by_cases h : w ∈ SB
  · rw [if_pos h, if_neg (hs w h), if_pos h]
    omega
  · rw [if_neg h, if_neg h]
    split_ifs <;> omega

end General

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem toDtQ_detPt : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (n : ℕ) (ST SG Q SQ : Finset (HeightOneSpectrum (𝓞 H.E)))
    (h : Q ⊆ SQ) (p : DecoF H.E n ST SG Q), LevOk H SG SQ → toDtQ H h (detPt H SQ p) = detPt H Q p := by
  intro R H n ST SG Q SQ h p hL
  classical
  have hL' := hL.mono h
  have hsub : uSG SG Q ⊆ uSG SG SQ := by
    intro P
    simp only [Finset.mem_union]
    exact Or.imp_right fun h' => h h'
  unfold detPt
  rw [toDtQ_mk]
  symm
  rw [QuotientGroup.eq, inv_mul_eq_div]
  have h0 : ∀ w (a : _root_.Neutral.B1.Ideles H.E), compAt w a ≠ 0 := fun w a => ((Group.isUnit a).map (compAt w)).ne_zero
  refine mem_KDq_of_conj hL' _ (fun w => ?_) fun P hP => ?_
  · rw [map_div, map_div, map_div₀, map_div₀]
    unfold ptIdl
    rw [valued_compAt_conjP hL.split p w, valued_compAt_conjP hL'.split p w, mul_div_mul_right _ _ WithZero.exp_ne_zero]
  · have e1 : compAt P (ptIdl H SQ p / ptIdl H Q p) = 1 := by
      rw [map_div, div_eq_one_iff_eq (h0 _ _)]
      unfold ptIdl
      rw [compAt_detIdl _ p.deco.2.lat, compAt_detIdl _ p.deco.2.lat, if_pos hP, if_pos (hsub hP)]
    have e2 : compAt (conjPrime₂ P) (ptIdl H SQ p / ptIdl H Q p) = 1 := by
      rw [map_div, div_eq_one_iff_eq (h0 _ _)]
      unfold ptIdl
      rw [compAt_detIdl _ p.deco.2.lat, compAt_detIdl _ p.deco.2.lat, if_neg (hL.split P (hsub hP)),
        if_neg (hL'.split P hP), CharValCompare.conjP_conjP, if_pos hP, if_pos (hsub hP)]
    have e3 := valued_sigR (host_cmData R H) P ((finAf H.F H.E (ptIdl H SQ p / ptIdl H Q p) : AfE H.F H.E) - 1)
    rw [map_sub (adAt _ _), adAt_finAf, e2, map_one (adAt _ _), sub_self, map_zero, Valuation.zero_iff,
      map_sub (Formalism.UG.sigR _ _), map_one (Formalism.UG.sigR _ _), map_sub (adAt _ _), map_one (adAt _ _), sub_eq_zero] at e3
    rw [e1, e3, div_one, sub_self, map_zero]
    exact zero_lt_one

end GlobalTheory.Mem.Col2.DetProj
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open Formalism.L2.Host (HChar atFin unif ordF)
open GlobalTheory.Mem.Chr.RelDet GlobalTheory.Mem.Chr.IdlFact
open GlobalTheory.CharValCompare (IsFr)

namespace GlobalTheory.Mem.Col2.DetLat

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem ordSub_conj {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N)
    (hu : Formalism.HermitianLatticesTheory.IsUnimodular (hStd E n) N) (P : HeightOneSpectrum (𝓞 E)) :
    ordSub (conjPrime₂ P) (detSub N) = -ordSub P (detSub N) := by
  have hfr (w : HeightOneSpectrum (𝓞 E)) : IsFr w N (latFr w N) := by
    first | exact isFr_latFr w ⟨hN, hu⟩ | exact isFr_latFr w hN
  have hfull : Submodule.IsFullLattice E N := by
    letI : Submodule.IsLattice E N := hN
    refine ⟨?_⟩
    apply top_unique
    rw [← ((Pi.basisFun E (Fin n)).map (latFr P N)).span_eq]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    obtain ⟨s, hs, hx⟩ := (mem_locP _ _ _).1 ((hfr P _).2 (CharValCompare.single_mem_stdAt P i))
    have hs0 : (algebraMap (𝓞 E) E s) ≠ 0 := by
      intro h
      have : s = 0 := (FaithfulSMul.algebraMap_injective (𝓞 E) E) (by simpa using h)
      exact hs (this ▸ P.asIdeal.zero_mem)
    have hx' : (algebraMap (𝓞 E) E s) • (latFr P N) (Pi.single i 1) ∈ N := by
      rwa [IsScalarTower.algebraMap_smul]
    have hm := Submodule.smul_mem (Submodule.span E (N : Set (Sp E n)))
      (algebraMap (𝓞 E) E s)⁻¹ (Submodule.subset_span hx')
    rw [← mul_smul, inv_mul_cancel₀ hs0, one_smul] at hm
    simpa only [Module.Basis.map_apply, Pi.basisFun_apply, SetLike.mem_coe] using hm
  have h := CharValCompare.val_dual (P := P) ⟨hN, hu⟩ (hfr P) (hfr (conjPrime₂ P))
  rw [map_mul, valuation_star, CharValCompare.conjP_conjP] at h
  rw [ordSub_detSub_eq hfull (hfr P), ordSub_detSub_eq hfull (hfr (conjPrime₂ P))]
  unfold _root_.Formalism.L2.Host.ordF
  rw [eq_inv_of_mul_eq_one_right h, WithZero.log_inv]

theorem ordSub_std (w : HeightOneSpectrum (𝓞 E)) : ordSub w (detSub (stdLat E n)) = 0 := by
  have hfull : Submodule.IsFullLattice E (stdLat E n) := by
    letI : Submodule.IsLattice E (stdLat E n) := stdLat_lattice
    refine ⟨?_⟩
    apply top_unique
    rw [← ((Pi.basisFun E (Fin n)).map ((1 : Sp E n ≃ₗ[E] Sp E n))).span_eq]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    obtain ⟨s, hs, hx⟩ := (mem_locP _ _ _).1 (((show IsFr w (stdLat E n) 1 from fun _ => Iff.rfl) _).2 (CharValCompare.single_mem_stdAt w i))
    have hs0 : (algebraMap (𝓞 E) E s) ≠ 0 := by
      intro h
      have : s = 0 := (FaithfulSMul.algebraMap_injective (𝓞 E) E) (by simpa using h)
      exact hs (this ▸ w.asIdeal.zero_mem)
    have hx' : (algebraMap (𝓞 E) E s) • ((1 : Sp E n ≃ₗ[E] Sp E n)) (Pi.single i 1) ∈ (stdLat E n) := by
      rwa [IsScalarTower.algebraMap_smul]
    have hm := Submodule.smul_mem (Submodule.span E ((stdLat E n) : Set (Sp E n)))
      (algebraMap (𝓞 E) E s)⁻¹ (Submodule.subset_span hx')
    rw [← mul_smul, inv_mul_cancel₀ hs0, one_smul] at hm
    simpa only [Module.Basis.map_apply, Pi.basisFun_apply, SetLike.mem_coe] using hm
  rw [ordSub_detSub_eq (f := 1) hfull fun _ => Iff.rfl]
  simp [_root_.Formalism.L2.Host.ordF]


open Classical in
theorem ordI_detIdl (SB : Finset (HeightOneSpectrum (𝓞 E))) {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N)
    {fr : HeightOneSpectrum (𝓞 E) → Sp E n ≃ₗ[E] Sp E n} (hf : ∀ P, IsFr P N (fr P)) (w : HeightOneSpectrum (𝓞 E)) :
    ordI w (detIdl SB N fr) =
      if w ∈ SB then ordSub w (detSub N) else if conjPrime₂ w ∈ SB then 0 else ((ordSub w (detSub N)).toNat : ℤ) := by
  have hfull : Submodule.IsFullLattice E N := by
    letI : Submodule.IsLattice E N := hN
    refine ⟨?_⟩
    apply top_unique
    rw [← ((Pi.basisFun E (Fin n)).map (fr w)).span_eq]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    obtain ⟨s, hs, hx⟩ := (mem_locP _ _ _).1 ((hf w _).2 (CharValCompare.single_mem_stdAt w i))
    have hs0 : (algebraMap (𝓞 E) E s) ≠ 0 := by
      intro h
      have : s = 0 := (FaithfulSMul.algebraMap_injective (𝓞 E) E) (by simpa using h)
      exact hs (this ▸ w.asIdeal.zero_mem)
    have hx' : (algebraMap (𝓞 E) E s) • (fr w) (Pi.single i 1) ∈ N := by
      rwa [IsScalarTower.algebraMap_smul]
    have hm := Submodule.smul_mem (Submodule.span E (N : Set (Sp E n)))
      (algebraMap (𝓞 E) E s)⁻¹ (Submodule.subset_span hx')
    rw [← mul_smul, inv_mul_cancel₀ hs0, one_smul] at hm
    simpa only [Module.Basis.map_apply, Pi.basisFun_apply, SetLike.mem_coe] using hm
  have e : valAt w (detIdl SB N fr) = Valued.v (compAt w (detIdl SB N fr)) := valAt_apply _ _
  rw [ordI, e, compAt_detIdl SB hN]
  split_ifs
  · rw [valued_algebraMap, ordSub_detSub_eq hfull (hf w)]
    rfl
  · simp
  · have h := ordF_unif_self w
    unfold _root_.Formalism.L2.Host.ordF at h
    rw [map_pow, valued_algebraMap, WithZero.log_pow, neg_eq_iff_eq_neg.1 h]
    simp

end General

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mk_mk_eq_of_ord {R : Ranks} (H : Formalism.BasicNotions.Host R) (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) {a b : _root_.Neutral.B1.Ideles H.E}
    (h : ∀ w, ordI w a - ordI (conjPrime₂ w) a = ordI w b - ordI (conjPrime₂ w) b) :
    (QuotientGroup.mk (QuotientGroup.mk a) : DtQ H SQ ⧸ UOQ H SQ) = QuotientGroup.mk (QuotientGroup.mk b) := by
  refine QuotientGroup.eq.2 ?_
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, mk_mem_UOQ, KDq_sup_unitIdl]
  refine (GlobalTheory.Mem.Chr.mem_KD_sup_unitIdl_iff R H _).2 fun w w' hw => ?_
  rw [← valAt_apply, ← valAt_apply, valAt_eq, valAt_eq, ordI_mul, ordI_mul, ordI_inv, ordI_inv,
    (isConjPl_iff H w w').1 hw]
  have := h w
  congr 1
  omega

end GlobalTheory.Mem.Col2.DetLat

namespace GlobalTheory.Mem.Col2

open DetLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mk_detPt_eq_relDetQ : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (n : ℕ) (ST SG Q SQ : Finset (HeightOneSpectrum (𝓞 H.E))) (p : DecoF H.E n ST SG Q), LevOk H SG SQ → (QuotientGroup.mk (detPt H SQ p) : DtQ H SQ ⧸ UOQ H SQ) = relDetQ H SQ n (stdLat H.E n) p.deco.1.N := by
  intro R H n ST SG Q SQ p hL
  have hN := p.deco.2.lat
  have hf : {w | (ordSub w (detSub p.deco.1.N) - ordSub w (detSub (stdLat H.E n))).toNat ≠ 0}.Finite :=
    (finite_ordSub hN).subset fun v hv h0 => hv (by simp [h0, ordSub_std])
  refine mk_mk_eq_of_ord H SQ (a := ptIdl H SQ p)
    (b := powI fun w => (ordSub w (detSub p.deco.1.N) - ordSub w (detSub (stdLat H.E n))).toNat) fun w => ?_
  rw [ordI_powI _ hf, ordI_powI _ hf, ptIdl, ordI_detIdl _ hN (isFr_ptFr p), ordI_detIdl _ hN (isFr_ptFr p),
    CharValCompare.conjP_conjP, ordSub_std, ordSub_std, ordSub_conj hN p.deco.2.uni]
  have hs := hL.split w
  by_cases h1 : w ∈ uSG SG SQ
  · rw [if_pos h1, if_neg (hs h1), if_pos h1]
    omega
  · by_cases h2 : conjPrime₂ w ∈ uSG SG SQ
    · rw [if_neg h1, if_pos h2, if_pos h2]
      omega
    · rw [if_neg h1, if_neg h2, if_neg h2, if_neg h1]
      omega

end GlobalTheory.Mem.Col2
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3


theorem _root_.GlobalTheory.T.exists_lattice_congruence_in_level_character_one : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank), ∃ N : ℕ, 0 < N ∧ ∀ k ∈ GfC V, GlobalTheory.Member.FinCong V N k → k ∈ levS V β L ∧ levChi V β L k = 1 := by
  first | exact @GlobalTheory.LevFinCong.exists_finCong_lev | exact GlobalTheory.LevFinCong.exists_finCong_lev | (intros; apply GlobalTheory.LevFinCong.exists_finCong_lev <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

theorem _root_.GlobalTheory.T.stepDatum_bounded_at_typePrime : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (i : ℕ) (P : rowSG Pr sel mu), i + 2 ≤ R.m → P.1 ∈ Pr.vGs → ∀ (hal : AutY X R i) (h : AutY X R (i + 1)), hal ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) i P.1) → h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) (i + 1) P.1) → HomBdd P.1 R.m (omPhi Ch sel mu cst i P hal h) ∧ ∀ x, omPhi Ch sel mu cst i P hal h x ≠ 0 → IntAt P.1 ((qOf P.1 : X.E) * Loc.chArg x) := by
  first | exact @GlobalTheory.Mem.Col2.BddG.omPhi_bdd_type | exact GlobalTheory.Mem.Col2.BddG.omPhi_bdd_type | (intros; apply GlobalTheory.Mem.Col2.BddG.omPhi_bdd_type <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts


theorem _root_.GlobalTheory.T.dictionary_rational_element_analytic_point : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (W : HSp D) (r : ℕ) (hr : W.rank = r) (U : Unf Xo c σ r) (dict : GA D W → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (g₀ : ℕ) (e₀ : Fin g₀ ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)) (F : ReciprocityTheory.ChartRestriction.G.Geo.Tor.FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e₀ j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (θ : InfFam D) (Z₀ : Fam W), GoodEmb c σ → IsUnf U → 1 ≤ r → IsInfFam θ → (∀ k τ, IsInfEmb τ.1 (th k τ)) → DictLat U W hr dict ι e₀ F ik φ th x₀ → (∀ ρ, x₀ (tauE D ρ) = Matrix.reindex (finCongr hr) (finCongr hr) (Z₀ ρ)) → ∀ h : GA D W, ∃ γ ∈ GQ W, MarkBy U W hr dict ι F ik φ h γ ∧ latW hr (U.X (dict h).1).Λ = latG W (γ * h) ∧ (∀ eT : D.what₂.Tau ≃ (U.X (dict h).1).Ψ, (∀ ρ, (eT ρ).1 = tauE D ρ) → (dict h).2 = frOf hr eT (mvZ θ (γ * h) Z₀)) ∧ ∀ (hx : (dict h).2 ∈ (U.X (dict h).1).dom) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X (dict h).1).Λ) (idx : Fin g ≃ (U.X (dict h).1).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw), IsSympl (U.X (dict h).1) bas → Matched c σ (U.X (dict h).1) idx e → letI : Algebra c.F ℂ := σ.toAlgebra; ∀ (A : AnFib (U.X (dict h).1) bas idx e (dict h).2 (U.X (dict h).1).Λ (ptC U (dict h).1 ⟨(dict h).2, hx⟩)) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)), (∀ a, mk a ∈ (U.X (dict h).1).Λ) → MarkAd hr l ι (γ * h) mk → A.Marked mk := by
  first | exact @GlobalTheory.OneMapRef.DictPt.dict_point | exact GlobalTheory.OneMapRef.DictPt.dict_point | (intros; apply GlobalTheory.OneMapRef.DictPt.dict_point <;> assumption)
end
