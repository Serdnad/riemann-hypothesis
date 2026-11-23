module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle297
public import GroundTheory.GlobalFields.TateThesis.AdeleIdealMeasure
public import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle324
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle313
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicFrobeniusSystemContinuationOpenDisc
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle013
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle338
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle312
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle100
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle189
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle213
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle325
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle263
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle326
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle337
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle308
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel
open GlobalTheory.TwistDet GlobalTheory.AntiRamConj
open scoped Pointwise

namespace GlobalTheory.ResUnr

theorem cocycle_conj {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (rho : Representation R G M) (x : Z1 rho)
    (h σ : G) (hσ : x.1 σ = 0) : x.1 (h * σ * h⁻¹) = rho (h * σ * h⁻¹) (-x.1 h) - (-x.1 h) := by
  have e1 := x.2.2 (h * σ * h⁻¹) h
  have e2 := x.2.2 h σ
  rw [inv_mul_cancel_right, e2, hσ, map_zero, add_zero] at e1
  rw [map_neg, sub_neg_eq_add, eq_neg_add_iff_add_eq, add_comm]
  exact e1.symm

theorem res_mem_unrAt {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (rho : Representation R (G F Ω) M) (x : Z1 rho)
    (A : ValuationSubring Ω) (m : M) (hm : ∀ σ ∈ Ine (F := F) A, x.1 σ = rho σ m - m) :
    ReciprocityTheory.Gal.resH1 rho (Dec (F := F) A).subtype continuous_subtype_val (Submodule.Quotient.mk x) ∈ Formalism.GaloisCohomology.unrAt rho A := by
  unfold Formalism.GaloisCohomology.unrAt H1ur
  rw [LinearMap.mem_ker]
  unfold ReciprocityTheory.Gal.resH1
  rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
  exact (mem_coboundaries1 _ _).2 ⟨m, fun g => hm g.1.1 (Subgroup.mem_subgroupOf.1 g.2)⟩

theorem mem_of_subsingleton {R M : Type} [Ring R] [AddCommGroup M] [Module R M] (h : Subsingleton M) (S : Submodule R M) (y : M) :
    y ∈ S := by
  rw [Subsingleton.elim y 0]
  exact S.zero_mem

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}

theorem mem_ine_iff_isFrob {B : ValuationSubring N.Om} {σ : GE N} : σ ∈ Ine (F := D.host.E) B ↔ IsFrob B 1 σ := by
  constructor
  · intro h
    exact ⟨h.1, fun x hx => by rw [pow_one]; exact h.2 x hx⟩
  · intro h
    exact ⟨h.1, fun x hx => by have := h.2 x hx; rwa [pow_one] at this⟩

theorem ine_smul {B : ValuationSubring N.Om} {σ : GE N} (hσ : σ ∈ Ine (F := D.host.E) B) (g : GE N) :
    g * σ * g⁻¹ ∈ Ine (F := D.host.E) (g • B) :=
  mem_ine_iff_isFrob.2 (isFrob_smul (mem_ine_iff_isFrob.1 hσ) g)

theorem exists_ine_of_conj (X : NTw D.R D.host D.what₂ D.LL0 N) {P P' : PlE D.host} (h : IsConjPl D.host P P') :
    ∃ k : GE N, ∀ σ ∈ Ine (F := D.host.E) (N.plOm.1 P'), ∃ σ₀ ∈ Ine (F := D.host.E) (N.plOm.1 P),
      σ = k * cConj X σ₀ * k⁻¹ := by
  have h2 := isPlaceOver_moveVal_cc X (isConjPl_symm h) (N.plOm.2 P')
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := D.host.E) h2 (N.plOm.2 P)
  refine ⟨(cConj X g)⁻¹, fun σ hσ => ?_⟩
  have h3 := ine_smul (cConj_mem_ine X hσ) g
  rw [hg] at h3
  refine ⟨_, h3, ?_⟩
  rw [map_mul, map_mul, map_inv, cConj_cConj]
  group

theorem res_mem_unrAt_of_conj (X : NTw D.R D.host D.what₂ D.LL0 N) {P P' : PlE D.host} (h : IsConjPl D.host P P')
    {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (rho : Representation R (GE N) M) (x : Z1 rho)
    (hz : ∀ σ ∈ Ine (F := D.host.E) (N.plOm.1 P), x.1 (cConj X σ) = 0) :
    ReciprocityTheory.Gal.resH1 rho (Dec (F := D.host.E) (N.plOm.1 P')).subtype continuous_subtype_val (Submodule.Quotient.mk x) ∈
      Formalism.GaloisCohomology.unrAt rho (N.plOm.1 P') := by
  obtain ⟨k, hk⟩ := exists_ine_of_conj X h
  refine res_mem_unrAt rho x (N.plOm.1 P') (-x.1 k) fun σ hσ => ?_
  obtain ⟨σ₀, h3, rfl⟩ := hk σ hσ
  exact cocycle_conj rho x k _ (hz _ h3)



theorem unrelax : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), FirstHalf i s → ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K → ∀ (M R : ℕ) (P : Fin R ⊕ Fin R → PlE D.host) d φ φ' (Q : Finset (PlE D.host)), 1 ≤ M → Position i s M P d φ φ' → IsQ P Q → ∀ x : Z1 (red i K (Tgl i s)), cl x ∈ selOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K Q → (∀ a, ∀ σ ∈ Ine (F := D.host.E) (N.plOm.1 (P (.inr a))), x.1 σ = 0 ∧ x.1 (GlobalTheory.TwistDet.cConj X σ) = 0) → cl x ∈ selOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K ∅ := by
  intro D N X bkP i s hF K _ _ _ _ hK M R P d φ φ' Q hM hpos hQ x hx hz
  unfold selOn Formalism.GaloisCohomology.SelAll at hx ⊢
  refine (mem_Sel _ _ _ _ _).2 fun v => ?_
  have hv := (mem_Sel _ _ _ _ _).1 hx v
  unfold Formalism.GaloisCohomology.bkCond at hv ⊢
  by_cases h1 : ((X.l i : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal
  · rw [if_pos h1] at hv ⊢
    exact hv
  rw [if_neg h1] at hv ⊢
  by_cases h2 : v ∈ Spl i
  · rw [if_pos (Set.mem_union_left _ h2)]
    exact Submodule.mem_top
  rw [if_neg (by simpa using h2)]
  by_cases h3 : v ∈ Q
  swap
  · rw [if_neg (by simp [h2, h3])] at hv
    exact hv
  obtain ⟨q, hq⟩ := (hQ v).1 h3
  rcases q with a | a
  · haveI : IsLocalHom (algebraMap (X.O0 i) K) := ⟨fun y hy => by
      by_contra hn
      exact hy.ne_zero (hK y ((IsLocalRing.mem_maximalIdeal y).2 hn))⟩
    have hT : Tors K K := fun b => ⟨1, fun y hy => by
      rw [pow_one, IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at hy
      rw [hy, zero_smul]⟩
    have hs := (hF M R P d φ φ' hM hpos K (1 : GE N →* Kˣ) (by rw [MonoidHom.ker_one, Subgroup.coe_top]; exact isOpen_univ) (fun g => ⟨0, by simp⟩) K hT (Tgl i s) (Or.inl rfl)
      a v hq).2.1
    exact mem_of_subsingleton hs _ _
  · rcases hq with rfl | hq
    · refine res_mem_unrAt (red i K (Tgl i s)) x (N.plOm.1 (P (.inr a))) 0 fun σ hσ => ?_
      rw [(hz a σ hσ).1, map_zero, sub_zero]
    · exact res_mem_unrAt_of_conj X hq (red i K (Tgl i s)) x fun σ hσ => (hz a σ hσ).2

end GlobalTheory.ResUnr

end
end

section

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.RSJ

open IsDedekindDomain.HeightOneSpectrum WithZero

theorem valued_natCast_apply (E : Type) [Field E] [NumberField E] (N : ℕ)
    (v : HeightOneSpectrum (𝓞 E)) :
    Valued.v ((N : FiniteAdeleRing (𝓞 E) E) v) = v.valuation E (N : E) := by
  rw [← map_natCast (algebraMap E (FiniteAdeleRing (𝓞 E) E)) N]
  exact valuedAdicCompletion_eq_valuation' v (N : E)

theorem natLat_iff_mem_idealFiniteAdeles : ∀ (E : Type) [Field E] [NumberField E] (N : ℕ), 0 < N →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ),
      (J : FractionalIdeal (𝓞 E)⁰ E) = FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E) →
      ∀ z : FiniteAdeleRing (𝓞 E) E, z ∈ GlobalTheory.RSJ.natLat E N ↔ z ∈ GroundTheory.Global.idealFiniteAdeles J := by
  intro E _ _ N hN J hJ x
  have hN0 : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hc0 : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E (N : E) ≠ 0 :=
    fun v => (Valuation.ne_zero_iff _).2 hN0
  have hc : ∀ v : HeightOneSpectrum (𝓞 E),
      exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) = v.valuation E (N : E) := by
    intro v
    rw [hJ, GroundTheory.Global.count_spanSingleton v hN0, neg_neg, exp_log (hc0 v)]
  rw [GroundTheory.Global.mem_idealFiniteAdeles]
  simp only [hc]
  have hunit : (N : FiniteAdeleRing (𝓞 E) E) * algebraMap E (FiniteAdeleRing (𝓞 E) E) (N : E)⁻¹ = 1 := by
    rw [← map_natCast (algebraMap E (FiniteAdeleRing (𝓞 E) E)) N, ← map_mul, mul_inv_cancel₀ hN0,
      map_one]
  constructor
  · rintro ⟨z, hz, rfl⟩ v
    change Valued.v ((N : FiniteAdeleRing (𝓞 E) E) v * z v) ≤ _
    rw [map_mul, valued_natCast_apply]
    have : Valued.v (z v) ≤ 1 := by
      have h := hz v
      rwa [mem_adicCompletionIntegers] at h
    calc v.valuation E (N : E) * Valued.v (z v) ≤ v.valuation E (N : E) * 1 := by gcongr
      _ = _ := mul_one _
  · intro hx
    refine ⟨algebraMap E (FiniteAdeleRing (𝓞 E) E) (N : E)⁻¹ * x, fun v => ?_, ?_⟩
    · rw [mem_adicCompletionIntegers]
      change Valued.v ((algebraMap E (FiniteAdeleRing (𝓞 E) E) (N : E)⁻¹) v * x v) ≤ 1
      rw [map_mul]
      change Valued.v (((N : E)⁻¹ : E) : v.adicCompletion E) * Valued.v (x v) ≤ 1
      rw [valuedAdicCompletion_eq_valuation' v, map_inv₀]
      exact (GroundTheory.Global.inv_mul_le_one_iff_withZero (hc0 v)).2 (hx v)
    · rw [← mul_assoc, hunit, one_mul]

end GlobalTheory.RSJ
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

theorem _root_.GlobalTheory.T.one_le_kap_and_lam0_hasInf : ∀ (D : D7) (Z : LamDat D), Z.Ok → ∀ (l : ℕ) (j a : Fin D.R.m) (s : ℕ), (s : ℤ) ≤ (BlochKatoReduction.Gen.NFun D.R : ℤ) + 1 → (∀ g, 1 ≤ Z.kap j a s g) ∧ GlobalTheory.CMVal.HasInf (Z.lam0 l j a) (phi D.host) (fun g => (Z.kap j a s g : ℤ) + s) := by
  first | exact @GlobalTheory.LamTie.InfType.toricLam0_hasInfinityType_conjRatio | exact GlobalTheory.LamTie.InfType.toricLam0_hasInfinityType_conjRatio | (intros; apply GlobalTheory.LamTie.InfType.toricLam0_hasInfinityType_conjRatio <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem mu0_del_tame {D : D7} (C : CharFrame D) (l : ℕ) (j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    (C.mu0 j * C.delAt l).LevelLe w 1 := by
  have hd : (C.delAt l).TameAt w := by
    unfold CharFrame.delAt; split_ifs
    · exact C.isDel'.tame w
    · exact C.isDel.tame w
  exact HChar.LevelLe.mul ((C.isMu0 j).tame w) hd

theorem mu0_del_unr {D : D7} (C : CharFrame D) (l : ℕ) (j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : ¬ Over4 D.host w) : (C.mu0 j * C.delAt l).UnrAt w := by
  have h1 : ∀ k, ¬ OverP D.host (D.host.g k) w := fun k hk => hw (Or.inl ⟨k, hk⟩)
  have hd : (C.delAt l).UnrAt w := by
    unfold CharFrame.delAt; split_ifs
    · exact C.isDel'.unr w (fun h => hw (Or.inr (Or.inr h)))
    · exact C.isDel.unr w (fun h => hw (Or.inr (Or.inl h)))
  exact HChar.UnrAt.mul ((C.isMu0 j).unr w h1) hd

theorem lam0_expAt : ∀ (D : D7) (Z : LamDat D), Z.Ok → ∀ (l : ℕ) (j a : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)),
    ExpAt (Z.lam0 l j a) w (expIn (cond0 D.host Z.w0) (below w)) := by
  intro D Z hZ l j a w
  obtain ⟨h4, h0, hO⟩ := expIn_cond0 D.R D.host Z.q0 Z.w0 hZ.places w
  have hA := hZ.aux a
  unfold LamDat.lam0
  by_cases hw : Over4 D.host w
  · rw [h4 hw]
    exact expAt_mul_inv _ (Z.chi a) _ w 2 (by norm_num) (hA.two w hw) (mu0_del_tame Z.C l j w)
  · by_cases hb : below w = below Z.w0
    · rw [(h0 hb).2]
      have hu := mu0_del_unr Z.C l j w hw
      exact expAt_mul_inv _ (Z.chi a) _ w 1 le_rfl (hA.one w hb) ((HChar.unrAt_iff _ _).1 hu)
    · rw [hO hw hb]
      have hu := HChar.UnrAt.mul (mu0_del_unr Z.C l j w hw) (HChar.UnrAt.inv (hA.unr w hw hb))
      intro m
      exact ⟨fun _ => Nat.zero_le m, fun _ => HChar.UnrAt.levelLe hu m⟩

end GlobalTheory.LamTie
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.cyclotomicFrobenius_system_continuation_open_disc : ∀ (l : ℕ) [Fact l.Prime], ∀ (LL : FinExt l) (s r n M : ℕ) [NeZero n], 1 ≤ s → ∀ (t τ : PowerSeries ↥LL.1), PowerSeries.constantCoeff t = 0 → (1 + PowerSeries.X) * PowerSeries.derivative t = 1 → XX l ↥LL.1 s * τ = t → ∀ (U : ZMod n → Matrix (Fin r) (Fin r) (PowerSeries ↥LL.1)) (Pm : ZMod n → Matrix (Fin r) (Fin r) (PowerSeries ↥(OL LL))) (Cm : ZMod n → Matrix (Fin r) (Fin r) ↥LL.1) (ρ : ℝ), 0 < ρ → (∀ i, QQ l ↥LL.1 s ^ M • U i = (Pm i).map (PowerSeries.map (algebraMap ↥(OL LL) ↥LL.1)) * (U (i - 1)).map (phi l ↥LL.1) * (Cm i).map PowerSeries.C) → (∀ i a b, (∀ r : ℝ, 0 < r → r < ρ → Filter.Tendsto (fun k : ℕ => ‖((PowerSeries.coeff k (U i a b) : ↥LL.1) : Om l)‖ * r ^ k) Filter.atTop (nhds 0))) → ∀ i a b, (∀ r : ℝ, 0 < r → r < 1 → Filter.Tendsto (fun k : ℕ => ‖((PowerSeries.coeff k (τ ^ M * U i a b) : ↥LL.1) : Om l)‖ * r ^ k) Filter.atTop (nhds 0)) := by
  first | exact @GlobalTheory.Cyc.continuation_to_open_disc | exact GlobalTheory.Cyc.continuation_to_open_disc | (intros; apply GlobalTheory.Cyc.continuation_to_open_disc <;> assumption)
end

section



open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

noncomputable section
namespace GlobalTheory.UseLoc.Cases.AdmW

open GlobalTheory.AdmLoc

section Ext
variable {G : Type} [Group G] [TopologicalSpace G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
  (L : Lattice (O := O) ρ) (X : Type) [AddCommGroup X] [Module O X] (χ₁ : G →* Oˣ) (z : G → ↥L.T ⊗[O] X)

def actExtL (g : G) : ((↥L.T ⊗[O] X) × O) →ₗ[O] ((↥L.T ⊗[O] X) × O) :=
  LinearMap.prod ((actT L g).rTensor X ∘ₗ LinearMap.fst O _ O +
      (LinearMap.id : O →ₗ[O] O).smulRight (((χ₁ g : Oˣ) : O) • z g) ∘ₗ LinearMap.snd O _ O)
    ((((χ₁ g : Oˣ) : O) • (LinearMap.id : O →ₗ[O] O)) ∘ₗ LinearMap.snd O _ O)

theorem actExtL_apply (g : G) (p : (↥L.T ⊗[O] X) × O) : actExtL L X χ₁ z g p = tableLineDegreeTwo.actExt L X χ₁ z g p := by
  simp [actExtL, tableLineDegreeTwo.actExt, mul_comm]

variable {L X χ₁ z}

variable (L X χ₁ z)

theorem actExtL_ker (lam : O) (a : ℕ) (hX : ∀ x : X, lam ^ a • x = 0) (g : G) :
    tableLineDegreeTwo.kerExt L X lam a ≤ (tableLineDegreeTwo.kerExt L X lam a).comap (actExtL L X χ₁ z g) := by
  have hT : ∀ m : ↥L.T ⊗[O] X, lam ^ a • m = 0 := by
    intro m
    induction m using TensorProduct.induction_on with
    | zero => simp
    | tmul t x => rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul, hX, TensorProduct.tmul_zero]
    | add u v hu hv => rw [smul_add, hu, hv, add_zero]
  rintro ⟨m, y⟩ ⟨hm, hy⟩
  simp only [Submodule.mem_bot] at hm
  subst hm
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  rw [Submodule.mem_comap, actExtL_apply]
  refine ⟨?_, ?_⟩
  · show _ ∈ (⊥ : Submodule O (↥L.T ⊗[O] X))
    rw [Submodule.mem_bot]
    simp only [tableLineDegreeTwo.actExt, map_zero, zero_add]
    rw [mul_smul, hT, smul_zero]
  · show _ ∈ Ideal.span {lam ^ a}
    simp only [tableLineDegreeTwo.actExt]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))

theorem kerExt_kill (lam : O) (a : ℕ) (hX : ∀ x : X, lam ^ a • x = 0)
    (m : ((↥L.T ⊗[O] X) × O) ⧸ tableLineDegreeTwo.kerExt L X lam a) : lam ^ a • m = 0 := by
  have hT : ∀ m : ↥L.T ⊗[O] X, lam ^ a • m = 0 := by
    intro m
    induction m using TensorProduct.induction_on with
    | zero => simp
    | tmul t x => rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul, hX, TensorProduct.tmul_zero]
    | add u v hu hv => rw [smul_add, hu, hv, add_zero]
  obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  refine ⟨?_, ?_⟩
  · show _ ∈ (⊥ : Submodule O (↥L.T ⊗[O] X))
    rw [Submodule.mem_bot]
    exact hT p.1
  · show _ ∈ Ideal.span {lam ^ a}
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

end Ext
end GlobalTheory.UseLoc.Cases.AdmW
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism

theorem _root_.GlobalTheory.T.prismaticFCrystal_value_localPrism_ainf_wittTensor : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (PS PW : Obj l ↥(OL K)) (ev : Hom PS PW) (ioH : Hom PS (ainfObj K)) (gH : ↥(GK K) → Hom PS PS) (π Q : PS.A) (ψ : PS.A →+* WCb l), (∀ x, ψ x = inclW l (ainfId K (ioH.f x))) → (∀ g, ioH.comp (gH g) = (ainfHom K g).comp ioH) → (∀ g, ev.comp (gH g) = ev) → RingHom.ker ev.f = Ideal.span {π} → Q ∈ PS.I → IsLocalRing PS.A → ψ Q ≠ 0 → ∀ (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)) (E : FCrys l ↥(OL K)) (j : E.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T)), Realises K E (ainfObj K) (ainfId K) T ρ j → ∃ (q : ℕ) (b : Module.Basis (Fin q) PS.A (E.M PS)) (c : Module.Basis (Fin q) (WCb l) (WCb l ⊗[ℤ_[l]] T)), (∀ i, c i = j (E.tr ioH (b i))) ∧ (∀ x, ∃ (k : ℕ) (m : E.M PS), ψ Q ^ k • TensorProduct.map (frobW l).toLinearMap LinearMap.id (j (E.tr ioH x)) = j (E.tr ioH m)) ∧ (∀ x, ∃ (k : ℕ) (s : Fin q → PS.A), ψ Q ^ k • j (E.tr ioH x) = ∑ i, ψ (s i) • TensorProduct.map (frobW l).toLinearMap LinearMap.id (c i)) ∧ (∀ (g : ↥(GK K)) x, TensorProduct.map (galW l (g : GQ l)).toLinearMap (ρ g) (j (E.tr ioH x)) = j (E.tr ioH (E.tr (gH g) x))) ∧ (∀ g x, ∃ y, E.tr (gH g) x - x = π • y) := by
  first | exact @GlobalTheory.Prism.LocalValue.main | exact GlobalTheory.Prism.LocalValue.main | (intros; apply GlobalTheory.Prism.LocalValue.main <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.IntSup

open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
open scoped TensorProduct

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (Y : NExp D.R D.host D.what₂ D.LL0 N X)

theorem mall_map_le (i : X.Tw) (j : ℕ) (b : Bool) (φ : Module.End (FractionRing (X.O i)) (Y.Fm i j b))
    (hφ : ∀ f ∈ Y.Bsup i j b, φ f ∈ Y.Bsup i j b)
    (hc : ∀ g, (Y.actG i j b g).toLinearMap ∘ₗ φ = φ ∘ₗ (Y.actG i j b g).toLinearMap) :
    (IntegralHeckeForms.Mall Y i j b).map (φ.restrictScalars (X.O i)) ≤ IntegralHeckeForms.Mall Y i j b := by
  rintro _ ⟨f, ⟨hf, hf0⟩, rfl⟩
  refine ⟨hφ f hf, ?_⟩
  change φ f ∈ IntegralHeckeForms.Fm0 Y i j b
  replace hf0 : f ∈ IntegralHeckeForms.Fm0 Y i j b := hf0
  simp only [IntegralHeckeForms.Fm0, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero] at hf0 ⊢
  intro u
  have h := LinearMap.congr_fun (hc u) f
  simp only [LinearMap.comp_apply] at h
  rw [h, hf0 u, map_smul]

theorem admInt_of_sup : ∀ (D : D7) (E : IntegralHeckeForms.XD D), SupG D → SupFull D → SupHk D → UnivSup D E → TypeKept E → CommG D →
    IntegralHeckeForms.IsotypicPartsInternalDirectSum D.nexp E := by
  intro D E hG hF hH hU hT hC i hi j hj b
  obtain ⟨hfg, hsp⟩ := hF i hi j hj b
  refine ⟨fun g => ?_, ?_,
    GlobalTheory.IntRestBall.span_inf_of_span_top _ hsp _ _ (fun _ => Iff.rfl),
    fun k P hk => mall_map_le D.nexp i j b _ (hH i hi j hj b k P hk) (fun g => hC i hi b j hj g k P hk),
    ?_, hT i hi j hj b⟩
  · rintro _ ⟨f, hf, rfl⟩
    exact hG i hi j hj b g f hf
  · exact hfg.of_le (fun f hf => hf.1)
  · intro a ha
    obtain ⟨c, hc⟩ := hU i hi j hj b a ha
    refine ⟨c, fun Q M h1 h2 h3 h4 => ?_⟩
    obtain ⟨Xi, hXi, hδ⟩ := hc Q M h1 h2 h3 h4
    rw [hXi, Finsupp.sum, Finset.smul_sum]
    refine Submodule.sum_mem _ fun δ _ => ?_
    have hm : ((D.ntw.l i : D.ntw.O i) ^ c) • Xi δ ∈ IntegralHeckeForms.Mall D.nexp i j b :=
      ⟨(hδ δ).2, ((IntegralHeckeForms.Fm0 D.nexp i j b).restrictScalars (D.ntw.O i)).smul_mem _ (hδ δ).1⟩
    exact ⟨(⟨_, hm⟩ : IntegralHeckeForms.Mall D.nexp i j b) ⊗ₜ AddMonoidAlgebra.single δ (1 : D.ntw.O i), by
      simp [TensorProduct.smul_tmul']⟩

end GlobalTheory.IntSup
end
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.senMultiplicity_subquotient_lattice_le : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) (B A₁ A : Ob k G) (j : (Fin A₁.m → k) →ₗ[k] (Fin B.m → k)) (p : (Fin A₁.m → k) →ₗ[k] (Fin A.m → k)) (w w' : ZMod n → ℤ) (N : Lats k n B.m), F.Obj B → IsHom A₁ B j → Function.Injective j → IsHom A₁ A p → Function.Surjective p → ABC (F.D B) w w' N → ∀ i x, sen ((F.D A).γ i) (F.push A₁ A p (F.pre A₁ B j N) i) x ≤ sen ((F.D B).γ i) (N i) x := by
  first | exact @GlobalTheory.Models.sen_push_pre_le | exact GlobalTheory.Models.sen_push_pre_le | (intros; apply GlobalTheory.Models.sen_push_pre_le <;> assumption)
end

section

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilQuad

theorem absK_units_neg_one {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] (A : Et F E) : A.absK ((-1 : A.Kˣ) : A.K) = 1 := by
  have hu : IsUnit ((-1 : A.Kˣ) : A.K) := Units.isUnit _
  have he : hu.unit = -1 := Units.ext rfl
  unfold Et.absK
  rw [dite_eq_left hu, he]
  have h2 : (distribHaarChar A.K (-1 : A.Kˣ)) ^ 2 = 1 := by
    rw [← map_pow]; simp
  have h3 : distribHaarChar A.K (-1 : A.Kˣ) = 1 :=
    (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 h2
  rw [h3]; simp

theorem stableGauss_neg_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ)
    (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ G₁ : ℂ, IsStableGauss A ψ x μ 1 G₁ →
    IsStableGauss A ψ x μ (-1) G₁ := by
  intro F E _ _ _ _ _ A ψ x μ ω h G₁ h1
  obtain ⟨G, hG⟩ := GlobalTheory.T.exists_stable_quadraticGaussIntegral F E A ψ x μ ω h (-1)
  have hω := (GlobalTheory.T.normGroupSign_mul_and_neg_one F E A ψ x μ ω h).2
  have h1' : IsStableGauss A ψ x μ ((1 : A.Kˣ) : A.K) G₁ := by simpa using h1
  have key := GlobalTheory.T.stableQuadraticGaussIntegral_transform_weil F E A ψ x μ ω h (-1) G G₁ hG h1'
  rw [hω, absK_units_neg_one] at key
  simp at key
  subst key
  simpa using hG

end GlobalTheory.JR.WeilQuad
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.isAcrisLogOneAdd_add_of_mul : ∀ (l : ℕ) [Fact l.Prime] (a b : Per.Ainf l) (y y' : Per.Acris l), GlobalTheory.LogU.InJ a → GlobalTheory.LogU.InJ b → GlobalTheory.LogU.IsLogJ a y → GlobalTheory.LogU.IsLogJ b y' → GlobalTheory.LogU.IsLogJ (a + b + a * b) (y + y') := by
  first | (exact @GlobalTheory.LogU.isLogJ_add) | (exact GlobalTheory.LogU.isLogJ_add) | (intros; apply GlobalTheory.LogU.isLogJ_add  <;> assumption)
end
