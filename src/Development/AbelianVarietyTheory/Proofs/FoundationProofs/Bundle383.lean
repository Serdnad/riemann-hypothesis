module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle015
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle042
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle056
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle350
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle334
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle326
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle318
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Definitions.Foundations.ThNSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ShiftedCocycleLimitIntegral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle381
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle382
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle018
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

theorem _root_.GlobalTheory.T.shifted_cocycle_limit_integral : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (η : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (y : G ℚ Ω → Fin 2 → Qbar l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ r x i, Continuous fun s => Y r s x i) → (∀ r s x i, Y r s x i ∈ c.O) → (∀ r, ShCoc (mat W) (cycMod ℚ Ω l r)⁻¹ (Y r)) → (∀ r s, Y r s = push (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) (Y (r + 1)) s) → (∀ r x, η r x ∈ c.O) → (∀ r s i, ‖y s i - spec (η r) (Y r) s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → ∀ q : Pl, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧ ∃ v : Fin 2 → Qbar l, ∀ s ∈ Ine (F := ℚ) B, y s = mat W s *ᵥ v - v := by
  first | exact @GlobalTheory.InertCoh.unr_of_limit_spec | exact GlobalTheory.InertCoh.unr_of_limit_spec | (intros; apply GlobalTheory.InertCoh.unr_of_limit_spec ; all_goals assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.Mem.Th GlobalTheory.Cusp
open GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspLie

theorem hasDerivAt_constTermOn {G : Type} [Group G] [TopologicalSpace G] {Γ N : Subgroup G} [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [DiscreteTopology Γ] [LocallyCompactSpace N]
    (hc : Cocompact Γ N) {φ ψ : G → ℂ} (hφ : LeftInv Γ φ) (hφc : Continuous φ) (hψ : LeftInv Γ ψ) (hψc : Continuous ψ)
    {u : ℝ → G} (hu : Continuous u) (hd : ∀ g t, HasDerivAt (fun s => φ (g * u s)) (ψ (g * u t)) t) (x : G) :
    HasDerivAt (fun s => constTermOn Γ N φ (x * u s)) (constTermOn Γ N ψ (x * u 0)) 0 := by
  have := hc.isProbabilityMeasure
  obtain ⟨K, hK, hs⟩ := id hc
  obtain ⟨C, hC⟩ := (hK.prod (isCompact_closedBall (0 : ℝ) 1)).exists_bound_of_continuousOn
    (f := fun p : N × ℝ => ψ (p.1 * (x * u p.2))) (by fun_prop)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := probMeasure Γ N) (bound := fun _ => C)
    (F := fun s q => φ ((q.out : N) * (x * u s))) (F' := fun s q => ψ ((q.out : N) * (x * u s)))
    (Metric.ball_mem_nhds (0 : ℝ) one_pos) (.of_forall fun s => (hc.integrable hφ hφc _).1) (hc.integrable hφ hφc _)
    (hc.integrable hψ hψc _).1 (.of_forall fun q s hs' => ?_) (integrable_const C) (.of_forall fun q s _ => ?_)).2
  · obtain ⟨γ, hγ, hk⟩ := hs q.out
    exact (congrArg norm (leftInv_integrand hψ (x * u s) γ hγ q.out)).ge.trans
      (hC (_, s) ⟨hk, Metric.ball_subset_closedBall hs'⟩)
  · simpa only [mul_assoc] using hd ((q.out : N) * x) s

variable {D : D7} {θ : InfF D} {V : HSp D} {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} {φ : GA D V → ℂ}

theorem gelf_Rder (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) (hφ : φ ∈ SmFun θ V) (τ' : D.what₂.Tau) (k : ℕ) :
    gelf θ V τ' k (Rder θ V τ X φ) = Rder θ V τ X (gelf θ V τ' k φ) := by
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  obtain ⟨c, hc, hg⟩ := GlobalTheory.SmoothForms.exists_gelf R τ'
  let ψ : GlobalTheory.SmoothForms.SmF θ V := ⟨φ, (GlobalTheory.SmoothForms.smooth_iff R φ).1 hφ⟩
  let X' : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ := ⟨X, hX⟩
  have e : ∀ f : GlobalTheory.SmoothForms.SmF θ V, Rder θ V τ X f.1 =
      (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ X') f).1 := fun f => GlobalTheory.SmoothForms.Rder_eq R τ X' f.1
  have hcomm : Commute (GlobalTheory.SmoothForms.envRep R τ' (c k))
      (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ X')) := by
    rw [← GlobalTheory.SmoothForms.envRep_ι]
    by_cases h : τ' = τ
    · subst h
      have hm : c k ∈ Subalgebra.center ℂ _ := hc ▸ Algebra.subset_adjoin ⟨k, rfl⟩
      exact Commute.map (Subalgebra.mem_center_iff.1 hm _).symm _
    · exact GlobalTheory.SmoothForms.envRep_comm R h _ _
  change gelf θ V τ' k (Rder θ V τ X ψ.1) = Rder θ V τ X (gelf θ V τ' k ψ.1)
  rw [e ψ, hg, hg, e]
  exact congrArg (fun S : Module.End ℂ (GlobalTheory.SmoothForms.SmF θ V) => (S ψ).1) hcomm.eq

theorem fg_comap {W : Submodule ℂ (GA D V → ℂ)} (hW : FiniteDimensional ℂ W) :
    (W.comap (SmFun θ V).subtype).FG :=
  Module.Finite.iff_fg.1 (FiniteDimensional.of_injective ((SmFun θ V).subtype.restrict (q := W) fun _ hx => hx)
    fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun z : W => z.1) h)))

theorem derEnd_coe (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) (f : SmFun θ V) : (derEnd hθ τ X f).1 = Rder θ V τ X f.1 :=
  GlobalTheory.SmoothAutCheck.RderC_eq θ V τ hX f.1

theorem isAutFunSm_Rder (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) (h : IsAutFunSm θ V φ) :
    IsAutFunSm θ V (Rder θ V τ X φ) := by
  refine { left := fun γ hγ => GlobalTheory.Mem.Lift.Rder_left (h.left γ hγ) τ X, level := ?_, cont := ?_,
           smooth := Rder_mem h.smooth hX, zfin := ?_, growth := ?_ }
  · obtain ⟨U, hU, e⟩ := h.level
    refine ⟨U, hU, fun k hk hf g => ?_⟩
    have := congrFun (GlobalTheory.Mem.FinTranslate.Rder_rTr (θ := θ) hf τ X φ) g
    rw [show rTr V k φ = φ from funext (e k hk hf)] at this
    exact this.symm
  · exact GlobalTheory.Size.continuous_rWord hθ h.smooth h.cont (GlobalTheory.Grow.unifModGrowth_of_isAutFunSm hθ h) (l := [(τ, X)])
      fun p hp => by rw [List.mem_singleton.1 hp]; exact hX
  · obtain ⟨W, hW, m, s⟩ := h.zfin
    refine ⟨((W.comap (SmFun θ V).subtype).map (derEnd hθ τ X)).map (SmFun θ V).subtype,
      Module.Finite.iff_fg.2 (((fg_comap hW).map _).map _),
      ⟨_, ⟨⟨φ, h.smooth⟩, m, rfl⟩, derEnd_coe hθ hX _⟩, ?_⟩
    rintro τ' k _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    refine ⟨_, ⟨⟨_, (linOnSm_gelf τ' k).mem _ f.2⟩, s τ' k _ hf, rfl⟩, ?_⟩
    rw [Submodule.subtype_apply, Submodule.subtype_apply, derEnd_coe hθ hX, derEnd_coe hθ hX, gelf_Rder hθ hX f.2]
  · obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun l hl x => ?_⟩
    simpa only [List.foldr_append, List.foldr_cons, List.foldr_nil] using
      hN (l ++ [(τ, X)]) (GlobalTheory.Mem.Lift.append_mem_lie hl hX) x

theorem isKFinite_Rder (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) {K : Subgroup (GA D V)} (hK : K ≤ GinfC V)
    (hs : φ ∈ SmFun θ V) (h : GlobalTheory.Doubling.IsKFinite K φ) : GlobalTheory.Doubling.IsKFinite K (Rder θ V τ X φ) := by
  obtain ⟨W, hW, m⟩ := GlobalTheory.Doubling.isKFinite_iff.1 h
  refine GlobalTheory.Doubling.isKFinite_iff.2
    ⟨(Submodule.map₂ (derEnd hθ τ) ⊤ (W.comap (SmFun θ V).subtype)).map (SmFun θ V).subtype,
      Module.Finite.iff_fg.2 ((Submodule.FG.map₂ _ Module.Finite.fg_top (fg_comap hW)).map _), fun k hk => ?_⟩
  have hr : ∀ k ∈ K, IsRealPt θ k := fun k hk => ⟨hK hk, FockCompare.RealAction.infMat_mem_UH hθ V k⟩
  have hi := hr _ (inv_mem hk)
  refine ⟨_, Submodule.apply_mem_map₂ _ (Submodule.mem_top (x := adAt θ k⁻¹ τ X))
    (n := ⟨rTr V k φ, rTr_mem hθ (hr k hk) hs⟩) (m k hk), ?_⟩
  rw [Submodule.subtype_apply, derEnd_coe hθ (adAt_mem hi hX)]
  funext g
  have := congrFun (Rder_rTr hθ hi hX (rTr V k φ)) (g * k)
  rw [show rTr V k⁻¹ (rTr V k φ) = φ from funext fun y => by simp [rTr]] at this
  rw [this, rTr, mul_inv_cancel_right]

theorem isCuspFun_Rder (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) (h : IsAutFunSm θ V φ) (hc : IsCuspFun V φ) :
    IsCuspFun V (Rder θ V τ X φ) := by
  have h' := isAutFunSm_Rder hθ hX h
  refine (isCuspFun_iff h'.left).2 fun W hW => funext fun x => ?_
  have h0 : constTermOn (GQ V) (NA (.single hW)) φ = 0 := (isCuspFun_iff h.left).1 hc W hW
  have := hasDerivAt_constTermOn (cocompact_single hW) h.left h.cont h'.left h'.cont (GlobalTheory.Mem.Lift.continuous_oneP hθ hX)
    (GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (GlobalTheory.Mem.Lift.hasDerivAt_Rder h.smooth hX)) x
  rw [h0, GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one] at this
  exact this.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))

end GlobalTheory.CuspLie

end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_ker_rep_cyclotomic_ne_one_normalForm : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∃ z ∈ W.ker, eps l z ≠ 1 := by
  first | exact @GlobalTheory.Ord2.exists_ker_eps_ne_one | exact GlobalTheory.Ord2.exists_ker_eps_ne_one | (intros; apply GlobalTheory.Ord2.exists_ker_eps_ne_one <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.tame_cochain_cocycle_extension : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (w : Pl) (B : ValuationSubring Ω) (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n))) (h : G ℚ Ω → Qbar l) (σ : G ℚ Ω), 1 ≤ n → IsPlaceOver B w → l ^ n ∣ normV w - 1 → (∃ τ ∈ Ine (F := ℚ) B, (ψ τ).toAdd = 1) → (∀ s, h s ∈ c.O) → (∀ s ∈ Dec (F := ℚ) B, ∀ t ∈ Dec (F := ℚ) B, Cg n (h (s * t)) (h s + h t)) → (∀ s ∈ Ine (F := ℚ) B, Cg n (h s) 0) → Cob2 c n (Dec (F := ℚ) B) (fun s t => (((ψ s).toAdd.val : ℕ) : Qbar l) * h t) → σ ∈ Dec (F := ℚ) B → Cg n (h σ) 0 := by
  first | exact @GlobalTheory.br_tame | exact GlobalTheory.br_tame | (intros; apply GlobalTheory.br_tame <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.Mem.Th GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Cusp

theorem constTerm_eq_zero_of_mem_cuspCont (D : D7) (V : HSp D) (φ : GA D V → ℂ) (h : φ ∈ cuspCont V) (𝔉 : IsoFlag V)
    (h𝔉 : 𝔉.Proper) : constTerm 𝔉 φ = 0 := by
  have hi : (⟨1, Nat.succ_lt_succ h𝔉⟩ : Fin (𝔉.k + 1)) ≠ 0 := Fin.ne_of_val_ne one_ne_zero
  have h0 : constTermOn (GQ V) (NA (.single (𝔉.isIsotropic hi))) φ = 0 :=
    (isCuspFun_iff h.2.1).1 h.2.2 _ (𝔉.isIsotropic hi)
  funext x
  refine (Stages.constTermOn_stages (GA D V) (GQ V) (NA 𝔉) (NA (.single (𝔉.isIsotropic hi)))
    (𝔉.unip_single_le D.sp.cm _ hi) (fun p hp n hn => IsoFlag.conj_mem_unip ?_ hn) (cocompact_flag D V 𝔉)
    (cocompact_single _) φ h.2.1 h.1 x).trans ?_
  · rw [IsoFlag.par_single]
    exact 𝔉.par_le_parab D.sp.cm _ _ (𝔉.unip_le_par D.sp.cm _ hp)
  · rw [h0]
    exact (cocompact_flag D V 𝔉).constTermOn_const 0 x

end GlobalTheory.Cusp
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.cmThetaNormBoundHypotheses_satisfied : ∀ D, Inp D := by
  first | exact @GlobalTheory.NormSum.inp_all | exact GlobalTheory.NormSum.inp_all | (intros; apply GlobalTheory.NormSum.inp_all <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.testVector_adelicPair_translates_movedLatticeVacuum : ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ) (Q : ℕ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (P : Pair D cc δ t0 Q), ∀ (g : GA D P.a) (g' : GA D P.d) L₁ L₁', Moves D (g : GL (Fin P.a) (AE D)) L₁ → Moves D (g' : GL (Fin P.d) (AE D)) L₁' → ∃ (c : ℂ) (k : ℕ) (r : Fin k → Qbar) (y : Fin k → VC D P.a P.d), 0 < Q → (Mod1All c ∧ (∀ i, Q • y i ∈ La D (tor0 D cc δ) L₁ L₁') ∧ (∀ i, IsIntegral ℤ ((Q : Qbar) ^ (P.a * P.d) * r i)) ∧ (∀ ρ : Qbar →+* ℂ, (∑ i, ‖ρ (r i)‖) ^ 2 ≤ (Q : ℝ) ^ (P.a * P.d)) ∧ (P.W.Om g g' P.F = fun z => c * ∑ i, (r i : ℂ) * U D (tor0 D cc δ) (y i) (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) P.a P.d) (La D (tor0 D cc δ) L₁ L₁') P.e0) z) ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (k' : GA D P.d), k' ∈ intG D P.d → TrivAt D p (g : GL (Fin P.a) (AE D)) → TrivAt D p ((g' * k' : GA D P.d) : GL (Fin P.d) (AE D)) → ‖lamC lam c‖ = 1) := by
  first | exact @GlobalTheory.ArchFree.expand.om_expand | exact GlobalTheory.ArchFree.expand.om_expand | (intros; apply GlobalTheory.ArchFree.expand.om_expand <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.cuspFunctionalModPrimePow_commutes_hecke_diamond : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime], (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → l ≠ 2 → ¬ l ∣ N → 5 ≤ N → ((l : Ω) ∈ A.nonunits) → ∀ (n w d : ℕ), Odd w → d.Coprime N → ∀ b : X.Fn l, b ∈ X.B N l w →
  (∀ q : ℕ, q.Prime → ¬ q ∣ N * l → ∀ r, CgA A l n ((thN X A N l n d (X.heckeT N l q b)).coeff r)
      ((hq ε q (thN X A N l n d b) + ((q : Ω) ^ (w + 1)) • vq q (thN X A N l n (d * q) b)).coeff r)) ∧
  (∀ r, CgA A l n ((thN X A N l n d (X.heckeU l b)).coeff r) ((uq l (thN X A N l (n + 1) d b)).coeff r)) ∧
  (∀ a : ℕ, a.Coprime N → ∀ r, CgA A l n ((thN X A N l n d (X.diam N l a b)).coeff r) ((thN X A N l n (d * a) b).coeff r)) := by
  first | exact @GlobalTheory.CyclotomicQExpansion.thN_hecke | exact GlobalTheory.CyclotomicQExpansion.thN_hecke | (intros; apply GlobalTheory.CyclotomicQExpansion.thN_hecke <;> assumption)
end
