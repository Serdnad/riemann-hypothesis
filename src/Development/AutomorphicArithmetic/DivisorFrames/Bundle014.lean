module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle002
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
public import Formalism.SatakeDualWeyl.DualWeylRepApply
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle289
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.DetSplit
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.Valuation.Integral
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2429
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open Formalism.CohomologicalDescent.DepthNonnegative (NablaT)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem UpperTheory.good_place_of_twist_place_dividing :
    ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
        {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W →
        ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → ∀ v : HeightOneSpectrum (𝓞 D.host.E),
          ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal → GlobalTheory.Hk3.Good p.R.toRealDat (p.R.mu w) v := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j P W hD w hw hW v hv
  have hL := p.charW.base.lev
  have hl := Formalism.EigenvalueLevelCeiling.plc_prime w
  have key : ∀ q : ℕ, q.Prime → q ≠ Formalism.EigenvalueLevelCeiling.plc w → ((q : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := by
    intro q hq hne hqv
    have hc : IsCoprime ((q : ℕ) : 𝓞 D.host.E) ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) :=
      Nat.Coprime.cast ((Nat.coprime_primes hq hl).2 hne)
    obtain ⟨a, b, hab⟩ := hc
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ v.asIdeal.add_mem (v.asIdeal.mul_mem_left a hqv) (v.asIdeal.mul_mem_left b hv)))
  have hsp : Formalism.EigenvalueLevelCeiling.plc w ∉ Formalism.MainNotions.JumpSetsAlt.excSet D := hD.special ▸ hW.2.2.2
  have hunr : (p.R.xiH (p.R.mu w)).UnrAt v := by
    obtain ⟨ψ, Q, hψ, e⟩ := p.charW.tup.mu_on w hw
    have e' : p.R.xiH (p.R.mu w) = p.R.C.delAt (Formalism.EigenvalueLevelCeiling.plc w) * ψ := e
    have hd : (p.R.C.delAt (Formalism.EigenvalueLevelCeiling.plc w)).UnrAt v := by
      unfold Formalism.L2.Host.CharFrame.delAt
      split_ifs
      · refine p.R.C.isDel'.unr v (key _ D.host.pde'_prime fun h => hsp ?_)
        rw [← h]
        simp [Formalism.MainNotions.JumpSetsAlt.excSet]
      · refine p.R.C.isDel.unr v (key _ D.host.pde_prime fun h => hsp ?_)
        rw [← h]
        simp [Formalism.MainNotions.JumpSetsAlt.excSet]
    intro x hx
    have a1 := hd x hx
    have a2 := hψ.atl v hv x
    rw [e']
    change (p.R.C.delAt (Formalism.EigenvalueLevelCeiling.plc w)).loc v x * ψ.loc v x = 1
    rw [a1, a2, mul_one]
  intro PP hPP
  rcases hPP with hPP | hPP
  · obtain ⟨k, hk⟩ := (hL.Pg PP).1 hPP
    have hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
      have h1 := p.R.C.P.pb_over k
      have hk' : PP.under (𝓞 D.host.K) = p.R.C.P.pb k := hk
      rw [← hk'] at h1
      have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal := h1
      rwa [map_natCast] at h2
    have hn : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := by
      refine key _ (D.host.g_prime k) fun h => ?_
      have h1 := hD.big k
      have h2 := hW.2.1
      rw [h] at h1
      exact absurd h1 (not_lt.2 h2)
    refine ⟨fun e => hn (e ▸ hg), fun hc => hn ?_⟩
    obtain ⟨c', h1, h2⟩ := hc _ hg
    have : c' = ((D.host.g k : ℕ) : 𝓞 D.host.E) := by
      apply RingOfIntegers.ext
      have e1 : (((D.host.g k : ℕ) : 𝓞 D.host.E) : D.host.E) = ((D.host.g k : ℕ) : D.host.E) := map_natCast (algebraMap (𝓞 D.host.E) D.host.E) _
      have h3 : (c' : D.host.E) = star (((D.host.g k : ℕ) : 𝓞 D.host.E) : D.host.E) := h2
      rw [e1, star_natCast, ← e1] at h3
      exact h3
    exact this ▸ h1
  · exact ⟨fun e => (hL.Q_ram (p.R.mu w) v).2 (Or.inl (e ▸ hPP)) hunr,
      fun hc => (hL.Q_ram (p.R.mu w) v).2 (Or.inr ⟨PP, hPP, hc⟩) hunr⟩
end

section

open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open Formalism.CohomologicalDescent.DepthNonnegative (NablaT)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem UpperTheory.hecke_offprime_preimage {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (hβ : ∃ c : ℕ, Formalism.IndefR.Lev.IsBaseFrame V β Λ (1 ^ c)) (v : HeightOneSpectrum (𝓞 D.host.E))
    (hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ v ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP v) :
    ∀ k ∈ GlobalTheory.Hk3.hyp V v, ∃ h : (Formalism.L2.Theta.finHom V).rangeRestrict k ∈ (levEnv V β L).J,
      (levEnv V β L).χ ⟨_, h⟩ = 1 := by
  refine hβ.elim fun c hc => ?_
  have hc' : Formalism.IndefR.Lev.IsBaseFrame V β Λ 1 := (one_pow c : (1 : ℕ) ^ c = 1) ▸ hc
  have h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top
  have hl := fun e f' he => (GlobalTheory.LevSplit.lev_split V β Λ 1 (Formalism.IndefR.Lev.flag1L L) hc').2 v e f' he h1 hoff
  rintro a ⟨ha, e, f', he, hs⟩
  have hm := ((hl e f' he).1 a hs).2 ha
  exact ⟨hm.2, Units.ext ((hl e f' he).2.1 a hm hs)⟩

theorem UpperTheory.levChi_eq_one_of_good_place :
    ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
        {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m) (t : p.P.T) (v : HeightOneSpectrum (𝓞 D.host.E)), GlobalTheory.Hk3.Good p.R.toRealDat t v →
        ∀ k ∈ GlobalTheory.Hk3.hyp (Vc D j) v, ∃ h : (Formalism.L2.Theta.finHom (Vc D j)).rangeRestrict k ∈ levJ p j t, levChi p j t ⟨_, h⟩ = 1 := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j t v hv
  exact UpperTheory.hecke_offprime_preimage (Vc D j) (p.R.βV j) (p.R.ΛV j) (p.R.datVt j t) (p.charW.base.lev.βV j) v hv
end

section

open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR GlobalTheory.UnitaryBC GlobalTheory.FrameAut Formalism.CohomologicalDescent.DepthNonnegative
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem norm_int_le_one {E : Type} [Field E] {l : ℕ} [Fact l.Prime] (j : E →+* PadicAlgCl l) (x : 𝓞 E) :
    ‖j (x : E)‖ ≤ 1 := by
  have h1 : IsIntegral ℤ (j (x : E)) := x.isIntegral_coe.map j.toIntAlgHom
  have h2 : IsIntegral (PadicAlgCl.valued l).v.integer (j (x : E)) := h1.tower_top
  have h3 := (Valuation.integer.integers (PadicAlgCl.valued l).v).mem_of_integral h2
  rw [Valuation.mem_integer_iff, PadicAlgCl.valuation_def] at h3
  exact_mod_cast h3

private theorem norm_le_of_int {D : D7} {l : ℕ} [Fact l.Prime]
    (ev : (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl l)
    (h : ∀ a : FiniteAdeleRing (𝓞 D.host.F) D.host.F, (∀ v, a v ∈ v.adicCompletionIntegers D.host.F) →
      ‖ev (a ⊗ₜ[D.host.F] 1)‖ ≤ 1) (z) (hz : z ∈ intAE D) : ‖ev z‖ ≤ 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, rfl⟩ := hy
    have e : a ⊗ₜ[D.host.F] (x : D.host.E) = (a ⊗ₜ[D.host.F] (1 : D.host.E)) * (1 ⊗ₜ[D.host.F] (x : D.host.E)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e, RingHom.map_mul, norm_mul]
    have h2 := norm_int_le_one (ev.comp (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := D.host.F)
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) x
    exact mul_le_one₀ (h a ha) (norm_nonneg _) h2
  | zero => rw [RingHom.map_zero, norm_zero]; exact zero_le_one
  | add x y _ _ hx hy =>
    rw [RingHom.map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  | neg x _ hx => rw [RingHom.map_neg, norm_neg]; exact hx

private theorem ev_idem {D : D7} {l : ℕ} [Fact l.Prime]
    (ev : (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl l)
    (h : ∀ a : FiniteAdeleRing (𝓞 D.host.F) D.host.F, (∀ v, a v ∈ v.adicCompletionIntegers D.host.F) →
      ‖ev (a ⊗ₜ[D.host.F] 1)‖ ≤ 1) (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : ((l : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (e : AE D) (he : e * e = e)
    (hx : ∀ x : 𝓞 D.host.E, x ≠ 0 → (x ∈ P.asIdeal ↔ finPart D (e * incA D ((x : D.host.E)⁻¹)) ∉ intAE D)) :
    ev (finPart D e) = 0 := by
  have hl : l.Prime := Fact.out
  have hcO : ((l : ℕ) : 𝓞 D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have h1 := (hx _ hcO).not.1 hP
  rw [not_not] at h1
  have h2 := norm_le_of_int ev h _ h1
  by_contra hne
  have h3 : ev (finPart D e) * ev (finPart D e) = ev (finPart D e) := by
    rw [← RingHom.map_mul, ← RingHom.map_mul, he]
  have h4 : ev (finPart D e) = 1 := mul_left_cancel₀ hne (h3.trans (mul_one _).symm)
  rw [RingHom.map_mul, RingHom.map_mul, h4, one_mul] at h2
  have h5 : ev (finPart D (incA D ((((l : ℕ) : 𝓞 D.host.E) : D.host.E)⁻¹))) = ((l : ℕ) : PadicAlgCl l)⁻¹ := by
    change (ev.comp ((finPart D).comp (incA D))) _ = _
    rw [map_inv₀]
    congr 1
    simp only [map_natCast]
  rw [h5, norm_inv] at h2
  have h6 : ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)) l, PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  have h7 : 0 < ‖((l : ℕ) : PadicAlgCl l)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hl.ne_zero)
  exact absurd h2 (not_le.2 ((one_lt_inv₀ h7).2 h6))

private theorem finPart_cA {D : D7} (w : AE D) :
    finPart D (cA D w) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig (finPart D w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul a e => rfl

private theorem placeIdem {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F}
    (h : IsPlaceIdem D v ε) : ε * ε = ε := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  have : α * α = α := by
    refine DFunLike.ext _ _ fun w => ?_
    change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w (α * α) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w α
    rw [map_mul]
    by_cases hw : w = v
    · subst hw; rw [h1, mul_one]
    · rw [h0 w hw, mul_zero]
  exact Prod.ext (mul_zero _) this

private theorem finPart_sub_one {D : D7} (V : HSp D) (h : GA D V) (i j : Fin V.rank) :
    finPart D ((Formalism.L2.Theta.mt V h - 1) i j) = ((finHom V h).1 - 1) i j := by
  rw [Matrix.sub_apply, Matrix.sub_apply, RingHom.map_sub]
  congr 1
  by_cases e : i = j
  · subst e; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
  · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, RingHom.map_zero]

theorem UpperTheory.eval_localElement_matrix_eq_one_of_prime_not_dvd :
    ∀ (D : D7) (V : HSp D) (l : ℕ) [Fact l.Prime]
        (ev : (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl l),
        (∀ a : FiniteAdeleRing (𝓞 D.host.F) D.host.F, (∀ v, a v ∈ v.adicCompletionIntegers D.host.F) → ‖ev (a ⊗ₜ[D.host.F] 1)‖ ≤ 1) →
        ∀ P : HeightOneSpectrum (𝓞 D.host.E), ((l : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ∀ x : Bridge.Gf V, GlobalTheory.Hk3.IsLocElt V P x →
          Matrix.map x.1.val ev = 1 := by
  intro D V l _ ev h P hP x ⟨e, f, g, hef, _, hx, hs⟩
  have hf : ev (finPart D f) = 0 := by
    rcases hef with ⟨⟨⟨h1, -⟩, h2⟩, rfl⟩ | ⟨rfl, ⟨v, ε, hε, h1⟩, h2⟩
    · have a1 := ev_idem ev h P hP e h1 h2
      have a2 := ev_idem (ev.comp (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig))
        (fun a ha => by
          change ‖ev (a ⊗ₜ[D.host.F] D.sp.cm.sig 1)‖ ≤ 1
          rw [map_one]; exact h a ha) P hP e h1 h2
      rw [RingHom.map_add (f := _), RingHom.map_add (f := _), a1, finPart_cA, zero_add]
      exact a2
    · refine ev_idem ev h P hP f ?_ h2
      rw [h1, ← RingHom.map_mul, placeIdem hε]
  ext i j
  have h1 := congrArg (fun z => ev (finPart D z)) (hs i j)
  simp only [RingHom.map_mul, hf, zero_mul] at h1
  rw [finPart_sub_one, ← hx, Matrix.sub_apply, RingHom.map_sub, eq_comm, sub_eq_zero] at h1
  rw [Matrix.map_apply, h1]
  by_cases e : i = j
  · subst e; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
  · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, RingHom.map_zero]
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.BasicNotions GlobalTheory.DefU GlobalTheory.FrameAut Formalism.CohomologicalDescent.DepthNonnegative

section SlopeTestRemainingChoices

open MvPolynomial Formalism.GradedWeylDivisibility
open Formalism.REAL (fockF)
open scoped Matrix

private theorem fock_add_right {σ : Type} (f g g' : MvPolynomial σ ℂ) :
    fockF f (g + g') = fockF f g + fockF f g' := by
  simp only [fockF, MvPolynomial.coeff_add, star_add, mul_add, add_mul, Finset.sum_add_distrib]

private theorem fock_smul_right {σ : Type} (c : ℂ) (f g : MvPolynomial σ ℂ) :
    fockF f (c • g) = star c * fockF f g := by
  simp only [fockF, MvPolynomial.coeff_smul, smul_eq_mul, star_mul', Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring

private noncomputable def fischer (σ : Type) : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun f h => fockF f (map (starRingEnd ℂ) h))
    (fun f f' h => by
      rw [Formalism.GradedWeylDivisibility.fockHerm σ _ (f + f'), fock_add_right, star_add, ← Formalism.GradedWeylDivisibility.fockHerm, ← Formalism.GradedWeylDivisibility.fockHerm])
    (fun c f h => by
      rw [Formalism.GradedWeylDivisibility.fockHerm σ _ (c • f), fock_smul_right, star_mul', star_star, ← Formalism.GradedWeylDivisibility.fockHerm, smul_eq_mul])
    (fun f h h' => by rw [map_add (f := _), fock_add_right])
    (fun c f h => by
      rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul, fock_smul_right, smul_eq_mul]
      simp)

private theorem fischer_apply {σ : Type} (f h : MvPolynomial σ ℂ) :
    fischer σ f h = fockF f (map (starRingEnd ℂ) h) := rfl

private theorem map_rowAct {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (h : MvPolynomial (Fin n × Fin n) ℂ) :
    map (starRingEnd ℂ) (rowAct ℂ A h) = rowAct ℂ (Aᵀ)ᴴ (map (starRingEnd ℂ) h) := by
  induction h using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp]
    congr 1
    simp [rowAct]

private theorem fischer_adj {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (f h : MvPolynomial (Fin n × Fin n) ℂ) :
    fischer _ (rowAct ℂ Aᵀ f) h = fischer _ f (rowAct ℂ A h) := by
  rw [fischer_apply, fischer_apply, Formalism.GradedWeylDivisibility.fockRowAdj, map_rowAct]

private theorem rowAct_rowAct {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hAB : B * A = 1)
    (h : MvPolynomial (Fin n × Fin n) ℂ) : rowAct ℂ A (rowAct ℂ B h) = h := by
  have : (rowAct ℂ (n := n) A).comp (rowAct ℂ B) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro v

    simp only [AlgHom.comp_apply, rowAct, aeval_X, map_sum, map_mul, algHom_C, AlgHom.id_apply]
    simp only [algebraMap_eq, Finset.mul_sum, ← mul_assoc, ← C_mul]
    rw [Finset.sum_comm]

    simp only [← Finset.sum_mul, ← map_sum, ← Matrix.mul_apply, hAB, Matrix.one_apply]
    rw [Finset.sum_eq_single v.1]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  exact DFunLike.congr_fun this h

private theorem lp_ne (n : ℕ) : lpMinor ℂ n (le_refl n) (le_refl n) ≠ 0 := by
  intro h
  have h1 := GlobalTheory.Branching.genericDet_pow_mul_hw ℂ n 1 (fun _ => 0)
  rw [h, pow_one, zero_mul] at h1
  exact hwNe ℂ n n le_rfl _ h1.symm

private theorem exists_j (n : ℕ) (ν : Fin n → ℕ) (s : ℤ) (lam : DomWeight n) (hl : ∀ a, lam.w a = (ν a : ℤ) + s) :
    ∃ j : nablaSq ℂ n lam →ₗ[ℂ] dualWeyl ℂ n n ν, Function.Bijective j ∧
      ∀ (g : GL (Fin n) ℂ) v, (j (GlobalTheory.Branching.sqRep ℂ n lam g v) : MvPolynomial (Fin n × Fin n) ℂ) =
        ((Matrix.GeneralLinearGroup.det g ^ s : ℂˣ) : ℂ) • rowAct ℂ (g : Matrix (Fin n) (Fin n) ℂ)ᵀ (j v) := by
  obtain ⟨c, hc, hdet⟩ : ∃ c : ℕ, (fun a => lam.natW a + c) = ν ∧ ∀ g : GL (Fin n) ℂ,
      detPow ℂ n g lam.detShift = detPow ℂ n g s * (g : Matrix (Fin n) (Fin n) ℂ).det ^ c := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      refine ⟨0, funext fun a => a.elim0, fun g => ?_⟩
      have : Matrix.GeneralLinearGroup.det g = 1 := Units.ext (by simp)
      simp [detPow, this]
    · have h3 : lam.detShift = lam.w ⟨n - 1, by omega⟩ := by simp [DomWeight.detShift, hn]
      refine ⟨ν ⟨n - 1, by omega⟩, funext fun a => ?_, fun g => ?_⟩
      · have h1 : lam.w ⟨n - 1, by omega⟩ ≤ lam.w a := lam.anti (by
          have := a.2
          rw [Fin.le_def]
          simp only
          omega)
        simp only [DomWeight.natW, h3]
        rw [hl, hl] at h1
        rw [hl, hl]
        omega
      · rw [h3, hl, add_comm, detPow, detPow, zpow_add, zpow_natCast]
        simp
  subst hc
  obtain ⟨dm, de, -⟩ := GlobalTheory.Branching.genericDet_pow_mul n c lam.natW
  let D : nablaSq ℂ n lam →ₗ[ℂ] dualWeyl ℂ n n (fun i => lam.natW i + c) :=
    { toFun := fun f => ⟨lpMinor ℂ n le_rfl le_rfl ^ c * f, dm f f.2⟩
      map_add' := fun f f' => Subtype.ext (by simp [mul_add])
      map_smul' := fun a f => Subtype.ext (by simp) }
  refine ⟨D, ⟨fun f f' e => Subtype.ext ?_, fun f => ?_⟩, fun g f => ?_⟩
  · exact mul_left_cancel₀ (pow_ne_zero c (lp_ne n)) (congrArg Subtype.val e)
  · obtain ⟨f', hf', e⟩ := PI.WMI.determinant_splitting_formula n lam.natW c
      (fun h => by simp [DomWeight.natW, DomWeight.detShift, h]) f f.2
    exact ⟨⟨f', hf'⟩, Subtype.ext e.symm⟩
  · change lpMinor ℂ n le_rfl le_rfl ^ c * sqAct ℂ n lam g f =
      detPow ℂ n g s • rowAct ℂ (g : Matrix (Fin n) (Fin n) ℂ)ᵀ
        (lpMinor ℂ n le_rfl le_rfl ^ c * (f : MvPolynomial (Fin n × Fin n) ℂ))
    rw [de, sqAct, hdet, Matrix.det_transpose, mul_smul_comm, smul_smul]

end SlopeTestRemainingChoices

theorem UpperTheory.exists_invariant_perfect_pairing_nablaSq_dualWeyl :
    ∀ (n : ℕ) (ν : Fin n → ℕ) (s : ℤ) (lam : DomWeight n), (∀ a, lam.w a = (ν a : ℤ) + s) →
        ∃ P : nablaSq ℂ n lam →ₗ[ℂ] Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν →ₗ[ℂ] ℂ, Function.Bijective P.flip ∧
          ∀ (g : GL (Fin n) ℂ) v u, P (GlobalTheory.Branching.sqRep ℂ n lam g v) (Formalism.UG.dualWeylRep ℂ n n ν g u) =
            ((Matrix.GeneralLinearGroup.det g ^ s : ℂˣ) : ℂ) * P v u := by
  intro n ν s lam hl
  obtain ⟨j, hj, he⟩ := exists_j n ν s lam hl
  let P : nablaSq ℂ n lam →ₗ[ℂ] Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν →ₗ[ℂ] ℂ :=
    (fischer _).compl₁₂ ((Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν).subtype ∘ₗ j) (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν).subtype
  have hP : ∀ v u, P v u = fischer _ (j v : MvPolynomial (Fin n × Fin n) ℂ) u := fun _ _ => rfl
  let e := LinearEquiv.ofBijective j hj
  haveI : FiniteDimensional ℂ (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν) := e.finiteDimensional
  have hinj : Function.Injective P.flip := by
    refine (injective_iff_map_eq_zero _).2 fun u hu => ?_
    obtain ⟨v, hv⟩ := hj.2 ⟨_, Formalism.GradedWeylDivisibility.dualWeylMap ℂ ℂ (starRingEnd ℂ) n n ν u u.2⟩
    have h0 : P v u = 0 := LinearMap.congr_fun hu v
    rw [hP, hv, fischer_apply] at h0
    by_contra hne
    have hne' : MvPolynomial.map (starRingEnd ℂ) (u : MvPolynomial (Fin n × Fin n) ℂ) ≠ 0 := fun h =>
      hne (Subtype.ext (MvPolynomial.map_injective _ (starRingEnd ℂ).injective (h.trans (map_zero _).symm)))
    have := (Formalism.GradedWeylDivisibility.fockPos _ _ hne').1
    rw [h0] at this
    simp at this
  refine ⟨P, ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hinj⟩, fun g v u => ?_⟩
  · rw [← e.finrank_eq]
    exact (Subspace.dual_finrank_eq).symm
  · rw [hP, hP, he, map_smul, LinearMap.smul_apply, fischer_adj, Formalism.UG.dualWeylRep_apply, Formalism.UG.dwAct,
      rowAct_rowAct _ _ (by simp), smul_eq_mul]
end
