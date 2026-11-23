module

public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle298
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle217
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle197
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle232
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle252
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle219
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1274
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1242
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2024
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle246
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle403
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle477
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle410
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryPart
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAdelicIdentification
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2093
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2077
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle010
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1349

@[expose] public section

section

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar GlobalTheory.ResLine
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ResLine

theorem exists_real_idele_flow (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) :
    ∃ l : ℝ → (AF F ⊗[F] E)ˣ, Continuous l ∧ (∀ s t, l (s + t) = l s * l t) ∧
      (∀ t, sigR (AF F) σ (l t).1 = (l t).1) ∧ ∀ t, (absE F E (l t) : ℝ) = Real.exp t := by
  have := h.1
  let e := fun w : InfinitePlace F => InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)
  let ρ : ℝ →* AF F :=
    { toFun := fun x => ((fun w => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm x :
        Ainf F), (1 : Af F))
      map_one' := Prod.ext (funext fun w => map_one _) rfl
      map_mul' := fun x y => Prod.ext (funext fun w => map_mul _ _ _) (mul_one _).symm }
  have hρ : Continuous ρ := (continuous_pi fun w => (e w).symm.continuous).prodMk continuous_const
  have hn : ∀ w x, ‖evInf F w (ρ x)‖ = ‖x‖ := fun w x =>
    (e w).symm.isometry.norm_map_of_map_zero
      (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm) x
  let ι : AF F →* AF F ⊗[F] E := (algebraMap (AF F) (AF F ⊗[F] E)).toMonoidHom
  have hι : Continuous ι := by
    haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
    haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
    exact IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AF F ⊗[F] E))
  let d : ℕ := Fintype.card (InfinitePlace F)
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  let u : ℝ → ℝˣ := fun t => Units.mk0 (Real.exp (t / (2 * d))) (Real.exp_ne_zero _)
  have hu : Continuous u := Units.continuous_iff.2
    ⟨show Continuous fun t : ℝ => Real.exp (t / (2 * d)) by fun_prop,
      show Continuous fun t : ℝ => (Real.exp (t / (2 * d)))⁻¹ from
        Continuous.inv₀ (by fun_prop) fun _ => Real.exp_ne_zero _⟩
  refine ⟨fun t => Units.map (ι.comp ρ) (u t), (Continuous.units_map (ι.comp ρ) (show Continuous (ι ∘ ρ) from hι.comp hρ)).comp hu, fun s t => ?_,
    fun t => congrArg (ρ (u t) ⊗ₜ[F] ·) (map_one σ), fun t => ?_⟩
  · rw [← map_mul]
    exact congrArg _ (Units.ext (show Real.exp _ = Real.exp _ * Real.exp _ by rw [← Real.exp_add, add_div]))
  · have h1 : Algebra.norm (AF F) (Units.map (ι.comp ρ) (u t)).1 = ρ (u t) ^ 2 := by
      change Algebra.norm (AF F) (algebraMap (AF F) (AF F ⊗[F] E) (ρ (u t))) = _
      haveI : Nontrivial (AF F) := (evInf F (Classical.arbitrary _)).toRingHom.domain_nontrivial
      rw [Algebra.norm_algebraMap, Module.finrank_baseChange, h.2.2.1]
    have h2 : ∀ v, evFin F v (ρ (u t)) = 1 := fun v => rfl
    have h3 : ∀ w : InfinitePlace F, w.mult = 1 := fun w => if_pos (IsTotallyReal.isReal w)
    simp only [GlobalTheory.Doubling.absE_apply, GlobalTheory.Doubling.absEv_unitFin, GlobalTheory.Doubling.absEw_unitInf, h1, map_pow, h2, h3,
      one_pow, nnnorm_one, finprod_one, mul_one, pow_one, NNReal.coe_prod, coe_nnnorm, norm_pow, hn,
      Finset.prod_const, Finset.card_univ]
    change (‖Real.exp (t / (2 * d))‖ ^ 2) ^ d = _
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, ← pow_mul, ← Real.exp_nat_mul]
    congr 1
    push_cast
    field_simp

end GlobalTheory.ResLine
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.UpSystem

theorem flatMap_cast (l : List ℕ) : List.flatMap (fun a : ℕ => [(a : ℤ)]) l = List.map (fun a : ℕ => (a : ℤ)) l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem labIn_eq (n : ℕ) (s : List ℕ) : Formalism.IndefR.Links.labIn n s =
    List.map (fun a : ℕ => (a : ℤ)) s ++ List.replicate (n - 2 * s.length) 0 ++ List.map (fun a : ℕ => -(a : ℤ)) s.reverse := by
  unfold Formalism.IndefR.Links.labIn
  simp only [List.bind_eq_flatMap, List.pure_def, flatMap_cast, List.map_map]
  rfl

theorem labIn_pairwise {n : ℕ} {s : List ℕ} (h : Formalism.L2.Col.InertTypeOk n s) :
    (Formalism.IndefR.Links.labIn n s).Pairwise (fun a b : ℤ => b ≤ a) := by
  obtain ⟨h1, -, -⟩ := h
  rw [labIn_eq]
  refine List.pairwise_append.2 ⟨List.pairwise_append.2 ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · exact List.pairwise_map.2 (h1.imp fun h => by exact_mod_cast h)
  · exact List.pairwise_replicate.2 (Or.inr le_rfl)
  · intro a ha b hb
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 ha
    rw [List.eq_of_mem_replicate hb]
    exact Int.natCast_nonneg x
  · rw [List.pairwise_map, List.pairwise_reverse]
    exact h1.imp fun h => by omega
  · intro a ha b hb
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hb
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨y, -, rfl⟩ := List.mem_map.1 ha
      omega
    · rw [List.eq_of_mem_replicate ha]
      omega

end GlobalTheory.UpSystem

namespace GlobalTheory.UpSystem



theorem up_sys : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ P, Good R.toRealDat A3.A.μ0 P → _root_.Formalism.DivisionValues.conjPl P = P → TwoSided R.toRealDat A3.A.μ0 P) → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → ∃ Tc : (A3.rowI A3.A.μ0).OpIx → Module.End ℂ (R.HX A3.A.μ0).H, (∀ i f, R.jX A3.A.μ0 ((A3.rowI A3.A.μ0).opAll i f) = Tc i (R.jX A3.A.μ0 f)) ∧ ∀ c, ∃ x : (A3.rowI A3.A.μ0).OpIx → ℂ, ∀ w ∈ R.EEc c, ∀ i, Tc i (LinearMap.adjoint (R.Th A3.A.μ0) w) = x i • LinearMap.adjoint (R.Th A3.A.μ0) w := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hI hOk hW hEx hS hTS hInert
  have h1 := GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hW
  have hC := h1.1 hEx
  have hSF := h1.2.1
  have hIn := h1.2.2.1
  have hEE := h1.2.2.2.2.1
  choose hX hXo _ using (GlobalTheory.T.realization_family_normal_operators R.toRealDat F.lv2 hC.lev hC.fam hC.models).1 A3.A.μ0
  have hf := GlobalTheory.AdjBlock.model_form (W := R.cX.W) (ι := Bridge.ratF D.sp.X') (ρ := R.cX.coef.ρ)
    (J := (levEnv _ R.βX (R.datXt A3.A.μ0)).J) (χ := (levEnv _ R.βX (R.datXt A3.A.μ0)).χ) (R.B.R A3.A.μ0).pres
    (R.HX A3.A.μ0) (hC.models.HX A3.A.μ0) (hC.models.jX A3.A.μ0)
  choose Tc hTc using fun i => GlobalTheory.AdjBlock.exists_cx hf.1 hf.2.1 ((A3.rowI A3.A.μ0).opAll i)
  refine ⟨Tc, fun i f => (hTc i f).symm, fun c => ?_⟩
  have hext : ∀ i (U : Module.End ℂ (R.HX A3.A.μ0).H),
      (∀ f, R.jX A3.A.μ0 ((A3.rowI A3.A.μ0).opAll i f) = U (R.jX A3.A.μ0 f)) → Tc i = U :=
    fun i U hU => GlobalTheory.AdjBlock.ext_of_span hf.2.1 fun f => (hTc i f).trans (hU f)
  have hzero : ∀ i, (A3.rowI A3.A.μ0).opAll i = 0 → Tc i = 0 := by
    intro i h0
    refine hext i 0 (fun f => ?_)
    have e1 : (A3.rowI A3.A.μ0).opAll i f = 0 := by rw [h0]; rfl
    exact (congrArg (R.jX A3.A.μ0) e1).trans ((map_zero _).trans (LinearMap.zero_apply _).symm)
  have hsys : ∀ P, Good R.toRealDat A3.A.μ0 P → ∀ cX c0, GlobalTheory.Hk3.MatchE R.toRealDat A3.A.μ0 P cX c0 → ∀ i,
      Tc i = hX P cX → ∃ a : ℂ, ∀ w ∈ R.EEc c,
        Tc i (LinearMap.adjoint (R.Th A3.A.μ0) w) = a • LinearMap.adjoint (R.Th A3.A.μ0) w := by
    intro P hP cX c0 hm i hi
    have h10 := (GlobalTheory.T.matched_spherical_pairs_commute_composite_lift R.toRealDat F.lv2 hC hS R.SF hSF A3.A.μ0 P hP cX c0 hm hX hXo).2 c
    refine ⟨_, fun w hw => (congrArg (fun U : Module.End ℂ (R.HX A3.A.μ0).H => U (LinearMap.adjoint (R.Th A3.A.μ0) w)) hi).trans
      (h10 w ((hEE c).symm ▸ hw))⟩
  have hev0 : ∀ i, Tc i = 0 → ∃ a : ℂ, ∀ w ∈ R.EEc c,
      Tc i (LinearMap.adjoint (R.Th A3.A.μ0) w) = a • LinearMap.adjoint (R.Th A3.A.μ0) w := fun i h0 =>
    ⟨0, fun w _ => (congrArg (fun U : Module.End ℂ (R.HX A3.A.μ0).H => U (LinearMap.adjoint (R.Th A3.A.μ0) w)) h0).trans
      ((LinearMap.zero_apply _).trans (zero_smul ℂ _).symm)⟩
  have key : ∀ i, ∃ a : ℂ, ∀ w ∈ R.EEc c,
      Tc i (LinearMap.adjoint (R.Th A3.A.μ0) w) = a • LinearMap.adjoint (R.Th A3.A.μ0) w := by
    rintro (⟨P, k⟩ | ⟨Q, y⟩)
    · by_cases hk : k ≤ D.sp.X'.rank
      · have hgood := ((GlobalTheory.GoodPrimes.good_primes R.toRealDat F.lv2 hC.lev).2.2.2 hC.fam A3.A.μ0 P.1 P.2).1
        have h99 := GlobalTheory.T.exists_splitPrime_heckeTransfer_compositeLift R.toRealDat F.lv2 hI hC hS A3.A.μ0 (P : A3.A.ok A3.A.μ0)
        have hso := (GlobalTheory.SplitHeckeLabel.split_ops R.toRealDat F.lv2 hC.lev hC.fam hC.models).1 A3.A.μ0 hX hXo
          (P : A3.A.ok A3.A.μ0) k hk
        exact hsys _ hgood _ _ (h99.choose_spec.1 k hk) _ (hext _ _ hso)
      · exact hev0 _ (hzero _ ((hC.fam.degR A3.A.μ0 P).2 k (not_le.1 hk)))
    · refine Or.elim (hInert.1 A3.A.μ0 ((Q : A3.okI A3.A.μ0), y)) (fun h0 => ?_) (fun hy => ?_)
      · exact hev0 (Sum.inr (Q, y)) (hzero (Sum.inr (Q, y)) h0)
      · have hgc := hIn A3.A.μ0 Q.1 Q.2
        have tie := (hW.inert.hR A3.A.μ0).some
        have hy'' : Formalism.L2.Col.InertTypeOk D.sp.X'.rank hy.choose := R.B.rankR ▸ hy.choose_spec.1
        have h78 := GlobalTheory.T.inertHeckeOperators_rows_rational_selfAdjoint_labels R.toRealDat F.lv2 hC.lev hC.fam hC.models A3.A.μ0 (A3.okI A3.A.μ0 × List ℕ)
          (fun i => R.plI i.1) (fun i => Formalism.IndefR.Links.labIn D.sp.X'.rank i.2) (A3.heckeRI A3.A.μ0)
          (fun i => Formalism.L2.Col.InertTypeOk D.sp.X'.rank i.2)
          (fun i hi => ⟨(hIn A3.A.μ0 i.1.1 i.1.2).1, (hIn A3.A.μ0 i.1.1 i.1.2).2, labIn_pairwise hi⟩) tie (Q, hy.choose) hy''
        have hm := (hTS _ hgc.1 hgc.2).1.1 (Finsupp.single (Formalism.IndefR.Links.labIn D.sp.X'.rank hy.choose) 1)
        refine hsys _ hgc.1 _ _ hm.choose_spec (Sum.inr (Q, y)) (hext _ _ fun f => ?_)
        exact (congrArg (R.jX A3.A.μ0) (LinearMap.congr_fun hy.choose_spec.2 f)).trans (h78.2.2.2 hX hXo f)
  exact ⟨fun i => (key i).choose, fun w hw i => (key i).choose_spec w hw⟩

end GlobalTheory.UpSystem
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory

theorem exists_passage_of_labels {Ix C α β L : Type} [Infinite L] (S : Finset (α → L)) (r : β → α) (hr : Function.Injective r)
    (e : Ix → α → L) (hS : ∀ p, e p ∈ S) (Car : Ix → C → Prop) (Sys : C → (β → L) → Prop) (Lab : C → C → Prop)
    (hE : ∀ p p' c c', Car p c → Car p' c' → ((∀ k, e p (r k) = e p' (r k)) ↔ Lab c c'))
    (hW : ∀ c c' f f', Sys c f → Sys c' f' → ((∀ k, f k = f' k) ↔ Lab c c')) :
    ∃ t : (α → L) → α → L, (∀ p c, Car p c → ∀ f, Sys c f → ∀ k, f k = t (e p) (r k)) ∧
      ∀ a ∈ S, ∀ b ∈ S, (∃ k, a (r k) ≠ b (r k)) → ∃ k, t a (r k) ≠ t b (r k) := by
  obtain ⟨t, h1, h2⟩ := exists_separating_extension_of_rel S r
    (fun a f => ∃ p, e p = a ∧ ∃ c, Car p c ∧ Sys c f) hr (by
      rintro a - b - f f' ⟨p, rfl, c, hc, hf⟩ ⟨p', rfl, c', hc', hf'⟩
      constructor
      · intro h
        funext k
        exact (hW c c' f f' hf hf').2 ((hE p p' c c' hc hc').1 fun k => congrFun h k) k
      · intro h
        funext k
        exact (hE p p' c c' hc hc').2 ((hW c c' f f' hf hf').1 fun k => congrFun h k) k)
  exact ⟨t, fun p c hc f hf k => h1 (e p) (hS p) f ⟨p, rfl, c, hc, hf⟩ k, h2⟩

theorem exists_inert_passage_separating : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ P, Good R.toRealDat A3.A.μ0 P → _root_.Formalism.DivisionValues.conjPl P = P → TwoSided R.toRealDat A3.A.μ0 P) → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → (∀ p, ∀ w ∈ R.EEp3 p, LinearMap.adjoint (R.Th A3.A.μ0) w = 0 → w = 0) → ∃ tr, R.TrISem F tr ∧ ∀ (j : Fin D.R.m), ∀ p ∈ (A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X, ∀ p' ∈ (A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X, (∃ k : A3.okI A3.A.μ0 × List ℕ, p.2 (k.1.1, k.2) ≠ p'.2 (k.1.1, k.2)) → ∃ k : A3.okI A3.A.μ0 × List ℕ, tr j p.2 (k.1.1, k.2) ≠ tr j p'.2 (k.1.1, k.2) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hL hO hC hE hS hT hJ hI
  classical
  haveI : Infinite D.what₂.LL := Infinite.of_injective (Nat.cast : ℕ → D.what₂.LL) Nat.cast_injective
  have hr : Function.Injective (fun k : A3.okI A3.A.μ0 × List ℕ => ((k.1.1, k.2) : I0 × List ℕ)) := by
    rintro ⟨⟨a, ha⟩, b⟩ ⟨⟨a', ha'⟩, b'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  have key : ∀ j : Fin D.R.m, ∃ t : (I0 × List ℕ → D.what₂.LL) → I0 × List ℕ → D.what₂.LL,
      (∀ (p : A3.fam3.base3.Ix) (c : Pl D.host.E → List ℤ → ℂ), R.Carries p c → ∀ f : A3.okI A3.A.μ0 × List ℕ → D.what₂.LL,
        (∃ (u : (A3.liftI j A3.A.μ0).OpIx → D.what₂.LL) (x : (A3.A.fam.L j A3.A.μ0).S.Forms), (∀ k, f k = u (Sum.inr k)) ∧
          (∀ i, (A3.liftI j A3.A.μ0).opAll i x = u i • x) ∧
          R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ∈ R.Wc' j c ∧ R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ≠ 0) →
        ∀ k, f k = t p.1.2 (k.1.1, k.2)) ∧
      ∀ a ∈ ((A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X).image Prod.snd,
      ∀ b ∈ ((A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X).image Prod.snd,
        (∃ k : A3.okI A3.A.μ0 × List ℕ, a (k.1.1, k.2) ≠ b (k.1.1, k.2)) →
        ∃ k : A3.okI A3.A.μ0 × List ℕ, t a (k.1.1, k.2) ≠ t b (k.1.1, k.2) := by
    intro j
    have hE' : ∀ (p p' : A3.fam3.base3.Ix) (c c' : Pl D.host.E → List ℤ → ℂ), R.Carries p c → R.Carries p' c' →
        ((∀ k : A3.okI A3.A.μ0 × List ℕ, p.1.2 (k.1.1, k.2) = p'.1.2 (k.1.1, k.2)) ↔
          (∀ P d, Good R.toRealDat A3.A.μ0 P → _root_.Formalism.DivisionValues.conjPl P = P → IsLab (Wc D j) P d → c P d = c' P d)) :=
      fun p p' c c' hc hc' => GlobalTheory.T.inertValues_iff_inertLabels_carriedEigensystems R F hL hO hC hE hS hT hJ hI j p p' c c' hc hc'
    have hW' : ∀ (c c' : Pl D.host.E → List ℤ → ℂ) (f f' : A3.okI A3.A.μ0 × List ℕ → D.what₂.LL),
        (∃ (u : (A3.liftI j A3.A.μ0).OpIx → D.what₂.LL) (x : (A3.A.fam.L j A3.A.μ0).S.Forms), (∀ k, f k = u (Sum.inr k)) ∧
          (∀ i, (A3.liftI j A3.A.μ0).opAll i x = u i • x) ∧
          R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ∈ R.Wc' j c ∧ R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ≠ 0) →
        (∃ (u : (A3.liftI j A3.A.μ0).OpIx → D.what₂.LL) (x : (A3.A.fam.L j A3.A.μ0).S.Forms), (∀ k, f' k = u (Sum.inr k)) ∧
          (∀ i, (A3.liftI j A3.A.μ0).opAll i x = u i • x) ∧
          R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ∈ R.Wc' j c' ∧ R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ≠ 0) →
        ((∀ k, f k = f' k) ↔
          (∀ P d, Good R.toRealDat A3.A.μ0 P → _root_.Formalism.DivisionValues.conjPl P = P → IsLab (Wc D j) P d → c P d = c' P d)) := by
      rintro c c' f f' ⟨u, x, hf, a1, a2, a3⟩ ⟨u', x', hf', b1, b2, b3⟩
      have V := GlobalTheory.T.inertEigenvalues_iff_thetaLift_inertLabels R F hL hO hC hE hS hT hJ j c c' u u' x x' a1 b1 a2 b2 a3 b3
      refine Iff.trans ?_ V
      exact forall_congr' fun k => by rw [hf k, hf' k]
    exact exists_passage_of_labels (Ix := A3.fam3.base3.Ix) (C := Pl D.host.E → List ℤ → ℂ) (L := D.what₂.LL)
      (((A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X).image Prod.snd)
      (fun k : A3.okI A3.A.μ0 × List ℕ => ((k.1.1, k.2) : I0 × List ℕ)) hr (fun p => p.1.2)
      (fun p => Finset.mem_image.2 ⟨p.1, p.2, rfl⟩) (fun p c => R.Carries p c)
      (fun c f => ∃ (u : (A3.liftI j A3.A.μ0).OpIx → D.what₂.LL) (x : (A3.A.fam.L j A3.A.μ0).S.Forms), (∀ k, f k = u (Sum.inr k)) ∧
          (∀ i, (A3.liftI j A3.A.μ0).opAll i x = u i • x) ∧
          R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ∈ R.Wc' j c ∧ R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ≠ 0)
      (fun c c' => ∀ P d, Good R.toRealDat A3.A.μ0 P → _root_.Formalism.DivisionValues.conjPl P = P → IsLab (Wc D j) P d → c P d = c' P d) hE' hW'
  choose tr h1 h2 using key
  refine ⟨tr, ?_, ?_⟩
  · rintro j p c hc u ⟨x, -, a1, a2, a3⟩ k
    exact h1 j p c hc (fun k => u (Sum.inr k)) ⟨u, x, fun _ => rfl, a1, a2, a3⟩ k
  · intro j p hp p' hp' h
    exact h2 j p.2 (Finset.mem_image.2 ⟨p, hp, rfl⟩) p'.2 (Finset.mem_image.2 ⟨p', hp', rfl⟩) h

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
namespace GlobalTheory.SpanW

theorem iSup_wp3_eq_range_eH : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → GoodStable A3.A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R.toRealDat → (∀ c, R.EEc c ≠ ⊥ → ∃ p, R.Carries p c) → ∀ i, (⨆ p, R.Wp3 i p) = LinearMap.range (eH R.toRealDat i) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hW hEx hS hGS hCD hME hcar i
  obtain ⟨hCore, hSF, hE, hWc⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hW hEx
  have hOk2 : A3.A.fam.Ok s := hOk.ok2
  have hirr : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk2.irr
  obtain ⟨h, -, -, -, hsum, -⟩ := GlobalTheory.T.sphericalOperators_forms_on_rank_space_normal R.toRealDat F.lv2 hCore hS hirr R.SF hSF i
  rw [← hsum]
  apply le_antisymm
  · refine iSup_le fun p => iSup₂_le fun c _ => ?_
    rw [hWc]
    exact le_iSup (fun c => Wcc R.toRealDat R.SF i c) c
  · refine iSup_le fun c => ?_
    by_cases h0 : Wcc R.toRealDat R.SF i c = ⊥
    · rw [h0]; exact bot_le
    · have hE0 : EEc R.toRealDat R.SF c ≠ ⊥ :=
        GlobalTheory.T.eigensystem_goodForms_thetaTarget_occurs_on_rows R.toRealDat F.lv2 hOk2 hCore hS hGS hCD hME R.SF hSF i c h0
      obtain ⟨p, hp⟩ := hcar c (by rw [hE]; exact hE0)
      rw [← hWc]
      exact le_trans (le_iSup₂ (f := fun c (_ : R.Carries p c) => R.Wc' i c) c hp) (le_iSup (fun p => R.Wp3 i p) p)

end GlobalTheory.SpanW
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam

theorem _root_.GlobalTheory.T.exists_periodTorus_complexPoint_siegelFamily : ∀ (h k : ℕ) (K : Type) [Field K] (ζ : K) (σ : K →+* ℂ) (F : SFam h k ζ), 1 ≤ h → 3 ≤ k → Odd k → σ ζ = Complex.exp (-(2 * Real.pi * Complex.I) / k) → ∀ p : Sp ℂ ⟶ F.X, p ≫ F.s = spMap σ → ∃ τ : Matrix (Fin h) (Fin h) ℂ, PtAt F.univ p τ := by
  first | exact @GlobalTheory.SiegelPtAt.exists_ptAt | exact GlobalTheory.SiegelPtAt.exists_ptAt | (intros; apply GlobalTheory.SiegelPtAt.exists_ptAt <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.FinIsoLocal

theorem bij_of_frame {A : Type} [CommRing A] {m n : ℕ} (h : n = m) (j : Matrix (Fin m) (Fin n) A) (β : GL (Fin n) A)
    (M : GL (Fin m) A) (hj : j * β.val = M.val.submatrix id (Fin.cast h)) : Function.Bijective j.mulVec := by
  subst h
  have hj' : j = M.val * (β⁻¹).val := by
    have e : M.val.submatrix id (Fin.cast rfl) = M.val := by ext a b; rfl
    rw [e] at hj
    rw [← hj, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  refine GlobalTheory.FinAdIdent.bij_of_inv (j' := β.val * (M⁻¹).val) ?_ ?_
  · rw [hj', Matrix.mul_assoc, ← Matrix.mul_assoc (β⁻¹).val, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  · rw [hj', Matrix.mul_assoc, ← Matrix.mul_assoc (M⁻¹).val, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]

end GlobalTheory.FinIsoLocal

theorem GlobalTheory.FinIsoLocal.exists_local_inner : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → ∀ (i : Fin D.R.m) (j : Matrix (Fin (Wc D i).rank) (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)) (Φ : GfC (Yc D 0) ≃ₜ* GfC (Wc D i)), GlobalTheory.CuspMult.IsFinIso (Yc D 0) (Wc D i) (R.βY 0) (R.βW i) R.Pg j Φ → ∃ (jl : ∀ v, GLoc D.sp.cm.sig (Yc D 0).gram v ≃ₜ* GLoc D.sp.cm.sig (Wc D i).gram v) (Φ₀ : GfC (Yc D 0) ≃ₜ* GfC (Wc D i)) (b : GfC (Yc D 0)), (∀ v, IsLatticeConj (frameLat (Yc D 0)) (frameLat (Wc D i)) (jl v)) ∧ (∀ v g, Φ₀ (locFin (Yc D 0) v g) = locFin (Wc D i) v (jl v g)) ∧ ∀ g, Φ g = Φ₀ (b * g * b⁻¹) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _ i j Φ hΦ
  obtain ⟨h, u, hu, -⟩ := hΦ.frame
  have hbij := GlobalTheory.FinIsoLocal.bij_of_frame h j (R.βY 0) (R.βW i * intGL D.host.F D.host.E (Wc D i).rank u) hu
  have hIs : GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.IsIsom (Yc D 0) (Wc D i) (Formalism.L2.Herm.Af D.host.F) j := ⟨hbij, hΦ.isom⟩
  have hC : GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.IsConjBy (Yc D 0) (Wc D i) j Φ := hΦ.conj
  obtain ⟨β₀, hβ₀, -⟩ := GlobalTheory.T.exists_baseFrame_selfDual_hermitianFrameLattice D (Yc D 0)
  obtain ⟨β₀', hβ₀', -⟩ := GlobalTheory.T.exists_baseFrame_selfDual_hermitianFrameLattice D (Wc D i)
  have hT : GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.OnePlaceOver (D := D) (∅ : Set (Formalism.L2.DIV.Pl D.host.E)) := by
    intro PP hPP; exact absurd hPP (Set.notMem_empty PP)
  obtain ⟨j₀, hL, hM⟩ := GlobalTheory.FinAdIdent.globalIsometry D (Yc D 0) (Wc D i) h (frameLat (Yc D 0)) (frameLat (Wc D i))
    β₀ β₀' 1 1 hβ₀ hβ₀' ∅ hT
  obtain ⟨Φ₀, hC₀, -⟩ := GlobalTheory.FinAdIdent.inducedIso D (Yc D 0) (Wc D i) h (frameLat (Yc D 0)) (frameLat (Wc D i))
    β₀ β₀' 1 1 hβ₀ hβ₀' ∅ j₀ hL hM
  obtain ⟨jl, h1, h2⟩ := GlobalTheory.T.adelicLatticeIsometry_eq_prod_localComponents D (Yc D 0) (Wc D i) j₀ Φ₀ hL hC₀
  obtain ⟨b, hb⟩ := GlobalTheory.T.adelicIsometryConj_differ_by_innerAutomorphism D (Yc D 0) (Wc D i) j j₀ Φ Φ₀ hIs hL.1 hC hC₀
  exact ⟨jl, Φ₀, b, h1, h2, hb⟩
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

theorem _root_.GlobalTheory.T.exists_symmetric_thetaElement_level_four_square : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (x : TFK (R := R) F ⟶ A.A), x ^ 4 = 1 → ∀ σ : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(ι[A.A]).left, 𝟙 A.A.left] ![1, -1]), σ.IsGen → LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ σ (eSec A.A)) (LB.oneGen A.L) → ∃ θ : ThetaGrp A.A A.L ((4 : ℕ) : ℤ) (TFK (R := R) F), θ.pt = x ∧ (∃ nu : LB.Gen (negLB A.A A.L ((4 : ℕ) : ℤ) (TFK (R := R) F)), nu.IsGen ∧ LB.Gen.Corr A.L _ _ _ _ (symGen A.A A.L ((4 : ℕ) : ℤ) θ nu) (LB.oneGen A.L)) ∧ ∃ c : F, (∀ z J, Good A.L z J → (val σ (x ^ 2).left z J).val = @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c)) ∧ ∀ (ψ : TFK (R := R) F ⊗ A.A ⟶ TFK (R := R) F ⊗ A.A) (m : TFK (R := R) F ⊗ A.A ⟶ A.A) (hm : ψ ≫ snd _ _ = m), ψ ≫ fst _ _ = fst _ _ → m = snd _ _ ^ 2 → ∀ α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, m.left] ![((4 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]), α.IsGen → ∀ (t : SecA A F 1) (t₁ t₂ t₃ : SecA A F 4), IsTwistPull A.A A.L ψ m hm ((4 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α t t₁ → IsActOf A.A A.L ((4 : ℕ) : ℤ) θ t₁ t₂ → IsActOf A.A A.L ((4 : ℕ) : ℤ) θ t₂ t₃ → ∀ j, t₃.f j = liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * t₁.f j := by
  first | exact @GlobalTheory.ThetaSquare.exists_symmetric_square | exact GlobalTheory.ThetaSquare.exists_symmetric_square | (intros; apply GlobalTheory.ThetaSquare.exists_symmetric_square <;> assumption)
end

section

open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal

namespace GlobalTheory.ResLine

def conjNormalEquiv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (N : Subgroup G) (b : G) (h : ∀ u, u ∈ N ↔ b * u * b⁻¹ ∈ N) : N ≃ₜ* N := GlobalTheory.ConjugationEquiv.conjEquiv N b h

end GlobalTheory.ResLine
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.splitPlaceCharacterComponent_smooth_unitary_conductor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : Chr F E), IsHecke F E χ →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v), IsSmU (chrW χ t) ∧ (∃ e, GlobalTheory.SplitFlip.CondLE (unifAt v) e (chrW χ t)) ∧
      (GlobalTheory.SplitWeil.IsUnram (chrW χ t) ↔ UnrAt χ (splitPrime t)) := by
  first | exact @GlobalTheory.ChrWLocal.chrW_local | exact GlobalTheory.ChrWLocal.chrW_local | (intros; apply GlobalTheory.ChrWLocal.chrW_local <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.lagrangianColumns_linear_parametrisation_finitePlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (v : Pl (F := F))
    (m : ℕ) (C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), IsLagrAt σ W v C →
    d = 2 * m ∧ ∃ (N : ℕ) (j : (Fin N → Fv F v) →ₗ[Fv F v] (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v))
      (ζ : (Fin N → Fv F v) → Matrix (Fin n) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), Function.Injective j ∧
      (∀ y, At (evFin F v) (ζ y) ∧ locCo M.co v (ζ y * Cᵀ) = j y) ∧
      (∀ z : Matrix (Fin n) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z → ∃ y, ζ y = z) ∧
      ∀ s : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), ∃ T : GL (Fin N) (Fv F v), (∀ y, ζ (T.val *ᵥ y) = s.val * ζ y) ∧
        T.val.det = Algebra.norm (Fv F v) (compFin F E v s.val.det) ^ m := by
  first | exact @GlobalTheory.InertLagParam.param | exact GlobalTheory.InertLagParam.param | (intros; apply GlobalTheory.InertLagParam.param <;> assumption)
end
