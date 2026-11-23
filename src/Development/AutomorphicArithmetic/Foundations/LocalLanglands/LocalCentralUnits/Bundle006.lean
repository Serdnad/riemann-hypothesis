module

public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToZModPowKummerEqIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle474
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle466
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle417
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyMemTwKerOfNormalizer
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle008
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle360
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle345
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle344
import GroundTheory.LocalFields.PadicLogSeries
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Artinian.Instances
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC.AbC

section LinAlg

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]

private theorem stable_eq_top {ρ : Representation ℂ G V} (hρ : ρ.IsIrreducible) (S : Submodule ℂ V)
    (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S) (h0 : S ≠ ⊥) : S = ⊤ := by
  rcases hρ.eq_bot_or_eq_top ⟨S, fun g v hv => hS g v hv⟩ with h | h
  · exact absurd (congrArg Subrepresentation.toSubmodule h) h0
  · exact congrArg Subrepresentation.toSubmodule h

private theorem nontrivial_of_irr {ρ : Representation ℂ G V} (hρ : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  obtain ⟨x, y, hxy⟩ := hρ.toNontrivial.exists_pair_ne
  exact hxy (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

private theorem eq_one_of_dvd [FiniteDimensional ℂ V] (f : Module.End ℂ V) (hf : f.IsSemisimple) (m : ℕ)
    (hd : f.charpoly ∣ (X - 1 : ℂ[X]) ^ m) : f = 1 := by
  have hsq : Squarefree (minpoly ℂ f) := hf.minpoly_squarefree
  have h1 : minpoly ℂ f ∣ (X - 1 : ℂ[X]) ^ (m + 1) :=
    (LinearMap.minpoly_dvd_charpoly f).trans (hd.trans (pow_dvd_pow _ (Nat.le_succ m)))
  obtain ⟨q, hq⟩ := (hsq.dvd_pow_iff_dvd (Nat.succ_ne_zero m)).1 h1
  have h2 : aeval f (X - 1 : ℂ[X]) = 0 := by rw [hq, map_mul, minpoly.aeval, zero_mul]
  simpa [sub_eq_zero] using h2

private theorem scalar_of_commute [FiniteDimensional ℂ V] {ρ : Representation ℂ G V} (hρ : ρ.IsIrreducible)
    (f : Module.End ℂ V) (hf : ∀ g, Commute (ρ g) f) : ∃ c : ℂ, ∀ v, f v = c • v := by
  haveI := nontrivial_of_irr hρ
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue f
  have hS : f.eigenspace μ = ⊤ := stable_eq_top hρ _ (fun g v hv => by
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    have h1 : f (ρ g v) = ρ g (f v) := LinearMap.congr_fun (hf g).eq.symm v
    rw [h1, hv, map_smul]) hμ
  refine ⟨μ, fun v => ?_⟩
  have hv : v ∈ f.eigenspace μ := hS ▸ Submodule.mem_top
  exact Module.End.mem_eigenspace_iff.1 hv

end LinAlg

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem dim_one {d : ℕ} (b : WDRep h (Fin d → ℂ)) (hb : b.ρ.IsIrreducible)
    (hu : ∀ (σ : Weil h) (t : Ine (F := E) A), ∃ m : ℕ,
      (b.ρ (σ * ineIncl h t * σ⁻¹ * (ineIncl h t)⁻¹)).charpoly ∣ (X - 1 : ℂ[X]) ^ m) : d = 1 := by
  haveI := nontrivial_of_irr hb
  have h1 : ∀ (σ : Weil h) (t : Ine (F := E) A), b.ρ (σ * ineIncl h t * σ⁻¹ * (ineIncl h t)⁻¹) = 1 := fun σ t => by
    obtain ⟨m, hm⟩ := hu σ t
    exact eq_one_of_dvd _ (b.semisimple _) m hm
  have h2 : ∀ (σ : Weil h) (t : Ine (F := E) A), Commute (b.ρ σ) (b.ρ (ineIncl h t)) := fun σ t => by
    have e : σ * ineIncl h t = (σ * ineIncl h t * σ⁻¹ * (ineIncl h t)⁻¹) * (ineIncl h t * σ) := by group
    show b.ρ σ * b.ρ _ = b.ρ _ * b.ρ σ
    rw [← map_mul, ← map_mul, e, map_mul, h1, one_mul]
  have h3 : ∀ t : Ine (F := E) A, ∃ c : ℂ, ∀ v, b.ρ (ineIncl h t) v = c • v :=
    fun t => scalar_of_commute hb _ fun g => h2 g t
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (b.ρ (frob h))
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  have hφ : b.ρ (frob h) v = μ • v := Module.End.mem_eigenspace_iff.1 hv.1
  let K : Subgroup (Weil h) :=
    { carrier := {σ | ∃ c : ℂ, b.ρ σ v = c • v}
      one_mem' := ⟨1, by simp⟩
      mul_mem' := by
        rintro σ τ ⟨c, hc⟩ ⟨c', hc'⟩
        exact ⟨c * c', by rw [map_mul, Module.End.mul_apply, hc', map_smul, hc, smul_smul, mul_comm]⟩
      inv_mem' := by
        rintro σ ⟨c, hc⟩
        have hinv : b.ρ σ⁻¹ (b.ρ σ v) = v := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
          rfl
        rw [hc, map_smul] at hinv
        have hc0 : c ≠ 0 := by
          rintro rfl
          rw [zero_smul] at hinv
          exact hv0 hinv.symm
        exact ⟨c⁻¹, by rw [eq_inv_smul_iff₀ hc0]; exact hinv⟩ }
  have hK : ∀ σ, σ ∈ K := fun σ => by
    obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) σ
    rw [hτ]
    refine K.mul_mem (K.zpow_mem ⟨μ, hφ⟩ _) ?_
    obtain ⟨c, hc⟩ := h3 τ
    exact ⟨c, hc v⟩
  have hL : (ℂ ∙ v) = ⊤ := stable_eq_top hb _ (fun g u hu => by
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hu
    obtain ⟨c, hc⟩ := hK g
    rw [map_smul, hc]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)))
    (by simpa using hv0)
  have hf := finrank_span_singleton (K := ℂ) hv0
  rw [hL, finrank_top, Module.finrank_fin_fun] at hf
  exact hf

private theorem charPol_first_dvd (rc : IrrGL (k := w.adicCompletion E) → WD h) (Δ : Segment (w.adicCompletion E)) (σ : Weil h) :
    (rc Δ.first).charPol σ ∣ (((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len)).charPol σ := by
  rw [(GlobalTheory.WeilDeligne.charPol_lpTw_lpChar_lpSp E Ω A w h (rc Δ.first)).2 Δ.len σ]
  have h0 : ((rc Δ.first).lpTw ((0 : ℕ) : ℝ)).charPol σ = (rc Δ.first).charPol σ := by
    obtain ⟨n, b, hb⟩ := (rc Δ.first).exists_rep
    rw [← hb, WD.lpTw_mk, WD.charPol_mk, WD.charPol_mk, WDRep.tw_ρ]
    simp
  rw [← h0]
  exact Multiset.dvd_prod (Multiset.mem_map.2 ⟨0, Multiset.mem_range.2 Δ.len_pos, rfl⟩)

end UpperTheory.Zero.LLC.AbC

open UpperTheory.Zero.LLC.AbC in
theorem UpperTheory.Zero.LLC.abConv :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), UpperTheory.Zero.LLC.IsRecT h rc → ∀ x, UpperTheory.Zero.LLC.AbConverse (rc x) x := by
  rintro E Ω _ _ _ _ _ A w h rc ⟨a, ha, H⟩ x ξ hξ
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨𝔪, hm⟩ := Pr.exh (w.adicCompletion E) x
  have hs : HasSupport x.rep (msupp 𝔪) := GlobalTheory.LocGL.hasSupport_msupp_of_isL Pr.zel _ 𝔪 x hm
  have hrc : rc x = segSum rc 𝔪.toList := H.langlands _ x (by rw [Multiset.coe_toList]; exact hm)
  refine ⟨_, hs, fun y hy => ?_⟩
  obtain ⟨Δ, hΔ, hy⟩ := Multiset.mem_bind.1 hy
  obtain ⟨j, -, rfl⟩ := Segment.mem_carrier.1 (Segment.mem_ms.1 hy)
  have hd : ∀ σ, (rc Δ.first).charPol σ ∣ (rc x).charPol σ := fun σ => by
    rw [hrc, segSum, CuspExt.charPol_sumList, List.map_map]
    refine (charPol_first_dvd rc Δ σ).trans (List.dvd_prod (List.mem_map.2 ⟨Δ, Multiset.mem_toList.2 hΔ, rfl⟩))
  obtain ⟨n, b, hb, hirr⟩ := H.cusp _ Δ.isCusp_first
  have hdim : n = Δ.first.1 := by
    have := H.dim Δ.first
    rw [← hb, WD.lpDim_mk] at this
    simpa using this
  have hn : n = 1 := dim_one b hirr fun σ t => ⟨x.1, by
    have e : σ * ineIncl h t * σ⁻¹ * (ineIncl h t)⁻¹ = ineIncl h (ineConj σ t * t⁻¹) := by
      rw [map_mul, ineIncl_ineConj, map_inv]
    have h1 : ∀ j, ξ j (ineIncl h (ineConj σ t * t⁻¹)) = 1 := fun j => by
      rw [← e, map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm (ξ j σ), mul_inv_cancel_right, mul_inv_cancel]
    rw [← WD.charPol_mk, hb, e]
    refine (hd _).trans ?_
    rw [hξ]
    simp [h1]⟩
  exact hdim.symm.trans hn
end

section

noncomputable section

open ValuativeRel Matrix
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands

namespace UpperTheory.Zero.LLC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem dualCl_fst' (x : IrrGL (k := k)) : (Zc.dualCl x).1 = x.1 := by
  rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_eq Pr.adm x]
  rfl

private theorem dualCl_iff (x y : IrrGL (k := k)) : DualCl x y ↔ y = Zc.dualCl x := by
  constructor
  · rintro ⟨n, π, π', rfl, rfl, ⟨e⟩⟩
    have ψ := GlobalTheory.ContraRefl.contraEquiv (equivRep π)
    rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_eq Pr.adm (cls π)]
    exact IrrGL.of_eq_of.2 ⟨e.trans ψ.symm⟩
  · rintro rfl
    exact ⟨x.1, x.2.rep, ⟨_, contra x.rep, isSmooth_contra _,
      GlobalTheory.CompanionTheory.ZcDual.isIrreducible_contra Pr.adm _ x.2.rep.smooth x.2.rep.irr⟩,
      congrArg (Sigma.mk x.1) x.2.cl_rep.symm, GlobalTheory.CompanionTheory.ZcDual.dualCl_eq Pr.adm x, ⟨.refl _⟩⟩

private theorem dualCl_tw (x : IrrGL (k := k)) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (hχ' : IsSmoothChar χ⁻¹) :
    Zc.dualCl (x.tw χ hχ) = (Zc.dualCl x).tw χ⁻¹ hχ' := by
  obtain ⟨e⟩ := GlobalTheory.CompanionTheory.ZcDual.nonempty_equiv_contra_twist Pr.adm x.rep x.2.rep.smooth x.2.rep.irr hχ hχ'
    (mul_inv_cancel χ)
  have φ := GlobalTheory.ContraRefl.contraEquiv (x.twEquiv χ hχ)
  rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_eq Pr.adm x, GlobalTheory.CompanionTheory.ZcDual.dualCl_eq Pr.adm (x.tw χ hχ), IrrGL.tw_of]
  exact IrrGL.of_eq_of.2 ⟨φ.trans e.symm⟩

private theorem fixed_ne_of_equiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ G V} {σ : Representation ℂ G W} (φ : π.Equiv σ) {K : Subgroup G}
    (h : fixed π K ≠ ⊥) : fixed σ K ≠ ⊥ := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  refine fun hb => hv0 (φ.toLinearEquiv.map_eq_zero_iff.1 ?_)
  have hm : φ.toLinearEquiv v ∈ fixed σ K := GlobalTheory.Parabolic.mem_fixed.2 fun g hg => by
    show σ g (φ.toIntertwiningMap v) = φ.toIntertwiningMap v
    rw [← φ.toIntertwiningMap.isIntertwining, GlobalTheory.Parabolic.mem_fixed.1 hv g hg]
  rw [hb] at hm
  exact hm

private theorem fixed_contra_ne {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) (hs : IsSmooth π) (h : fixed π (KOne k (Fin n)) ≠ ⊥) :
    fixed (contra π) (KOne k (Fin n)) ≠ ⊥ := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  have hv' : (⟨v, hv⟩ : fixed π (KOne k (Fin n))) ≠ 0 := fun e => hv0 (congrArg Subtype.val e)
  obtain ⟨m, hm⟩ : ∃ m : Module.Dual ℂ (fixed π (KOne k (Fin n))), m ⟨v, hv⟩ ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hv' ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hn)
  obtain ⟨l, hl, hlm⟩ := GlobalTheory.ContraRefl.exists_fixed_contra hs GlobalTheory.StepData.isOpen_KOne GlobalTheory.DepthZeroJac.isCompact_KOne m
  intro hb
  have hlf : l ∈ fixed (contra π) (KOne k (Fin n)) := GlobalTheory.Parabolic.mem_fixed.2 hl
  rw [hb] at hlf
  have hl0 : l = 0 := hlf
  have := hlm ⟨v, hv⟩
  rw [hl0] at this
  exact hm (by simpa using this.symm)

private theorem dz_dualCl {x : IrrGL (k := k)} (h : DZ x) : DZ (Zc.dualCl x) := by
  unfold DZ
  rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_eq Pr.adm x]
  exact fixed_ne_of_equiv (IrrGL.equivOf _ _ _) (fixed_contra_ne x.rep x.2.rep.smooth h)

private theorem central_dualCl {x : IrrGL (k := k)} {ω : kˣ →* ℂˣ} (h : HasCentralChar x.rep ω) :
    HasCentralChar (Zc.dualCl x).rep ω⁻¹ := by
  rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_eq Pr.adm x]
  refine hasCentralChar_of_equiv (IrrGL.equivOf _ _ _) fun z l => Subtype.ext (LinearMap.ext fun v => ?_)
  have h1 : (GeneralLinearGroup.scalar (Fin x.1) z)⁻¹ = GeneralLinearGroup.scalar (Fin x.1) z⁻¹ :=
    (map_inv _ z).symm
  rw [contra_apply, h1, h z⁻¹ v, map_smul, Submodule.coe_smul, LinearMap.smul_apply, MonoidHom.inv_apply, map_inv]

private theorem tw_tw_inv (y : IrrGL (k := k)) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (hχ' : IsSmoothChar χ⁻¹) :
    (y.tw χ hχ).tw χ⁻¹ hχ' = y := by
  simp only [IrrGL.tw_tw, mul_inv_cancel, IrrGL.tw_one]

private theorem goodCusp_tw {y : IrrGL (k := k)} (h : GoodCusp y) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    GoodCusp (y.tw χ hχ) := by
  rcases h with h | ⟨hg, y₀, χ₀, h₀, hd, rfl⟩
  · exact .inl h
  · exact .inr ⟨hg, y₀, χ₀ * χ, h₀.mul hχ, hd, IrrGL.tw_tw _ _ _ _ _⟩

private theorem goodCusp_dualCl {y : IrrGL (k := k)} (h : GoodCusp y) : GoodCusp (Zc.dualCl y) := by
  rcases h with h | ⟨hg, y₀, χ₀, h₀, hd, rfl⟩
  · exact .inl ((dualCl_fst' y).trans h)
  · exact .inr ⟨hg, Zc.dualCl y₀, χ₀⁻¹, h₀.inv, dz_dualCl hd, dualCl_tw _ _ _ _⟩

private theorem deg_one (c : IrrCl (GL (Fin 1) k)) :
    IrrGL.IsCusp (⟨1, c⟩ : IrrGL (k := k)) ∧ ∃ χ hχ, (⟨1, c⟩ : IrrGL (k := k)) = IrrGL.ofChar χ hχ := by
  refine ⟨⟨one_pos, c.rep.smooth, fun s d e he => absurd (exh_unipRad_one e) he⟩, ?_⟩
  obtain ⟨ω, hω, hc⟩ := exists_smooth_hasCentralChar c.rep.smooth c.rep.irr
  refine ⟨ω, hω, ?_⟩
  have hact : ∀ (g : GL (Fin 1) k) v, c.rep.ρ g v = (ω (GeneralLinearGroup.det g) : ℂ) • v := fun g v => by
    have hg : GeneralLinearGroup.scalar (Fin 1) (GeneralLinearGroup.det g) = g := by
      ext i j
      rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
      simp [GeneralLinearGroup.scalar]
    conv_lhs => rw [← hg]
    exact hc _ v
  haveI := c.rep.irr
  have := Model.nontrivial_of_isIrreducible c.rep.irr
  obtain ⟨v, hv⟩ := exists_ne (0 : c.rep.V)
  let S : Subrepresentation c.rep.ρ := ⟨Submodule.span ℂ {v}, fun g w hw => by
    rw [hact]; exact Submodule.smul_mem _ _ hw⟩
  have hS : S = ⊤ := (eq_bot_or_eq_top S).resolve_left fun h => hv (by
    have : v ∈ S := Submodule.mem_span_singleton_self v
    rw [h] at this; exact this)
  let f : (GlobalTheory.SmGL.ofChar (detChar (Fin 1) ω)).IntertwiningMap c.rep.ρ :=
    { toFun := fun a : ℂ => a • v
      map_add' := fun a b => add_smul a b v
      map_smul' := fun a b => mul_smul a b v
      isIntertwining' := fun g => LinearMap.ext fun a => by
        show ((ω (GeneralLinearGroup.det g) : ℂ) * a) • v = c.rep.ρ g (a • v)
        rw [map_smul, hact, smul_smul, mul_comm] }
  have hb : Function.Bijective f := by
    refine ⟨fun a b h => smul_left_injective ℂ hv h, fun w => ?_⟩
    have : w ∈ S := by rw [hS]; trivial
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 this
    exact ⟨a, ha⟩
  exact (IrrGL.of_rep ⟨1, c⟩).symm.trans ((IrrGL.of_eq_of (π := c.rep.ρ) (σ := GlobalTheory.SmGL.ofChar (detChar (Fin 1) ω))
    (hs := c.rep.smooth) (hi := c.rep.irr) (hs' := (IrrRep.det (Fin 1) ω hω).smooth)
    (hi' := (IrrRep.det (Fin 1) ω hω).irr)).2 ⟨(equivOfBijective f hb).symm⟩)

theorem clBasic : ClBasic := by
  intro k _ _ _ _ _ y
  have hnt := Model.nontrivial_of_isIrreducible y.2.rep.irr
  refine ⟨?_, fun χ hχ => ⟨rfl, ?_, ?_, fun χ' hχ' h'' => IrrGL.tw_tw _ _ _ _ _, fun ω hω => ?_⟩,
    fun h1 => IrrGL.tw_one _ _, fun h => h.1, fun h => ?_, ⟨_, (dualCl_iff y _).2 rfl⟩, fun y' hy' => ?_⟩
  · obtain ⟨ω, hs, hω⟩ := exists_smooth_hasCentralChar y.2.rep.smooth y.2.rep.irr
    exact ⟨ω, hs, hω, fun ω' hω' => centralChar_unique hω' hω⟩
  · exact ⟨fun h => tw_tw_inv y χ hχ hχ.inv ▸ h.tw χ⁻¹ hχ.inv, fun h => h.tw χ hχ⟩
  · exact ⟨fun h => tw_tw_inv y χ hχ hχ.inv ▸ goodCusp_tw h χ⁻¹ hχ.inv, fun h => goodCusp_tw h χ hχ⟩
  · have h1 := hasCentralChar_twist hω χ
    rw [Fintype.card_fin] at h1
    exact hasCentralChar_of_equiv (y.twEquiv _ _) h1
  · obtain ⟨n, c⟩ := y
    obtain rfl : n = 1 := h
    exact deg_one c
  · obtain rfl := (dualCl_iff y y').1 hy'
    have hdd := GlobalTheory.CompanionTheory.Zcore.dualCl_dualCl Pr.adm y
    refine ⟨dualCl_fst' y, ⟨fun h => ?_, fun h => (GlobalTheory.T.dual_class_cuspidal Pr.adm y h).1⟩, ⟨fun h => ?_, dz_dualCl⟩,
      ⟨fun h => ?_, goodCusp_dualCl⟩, fun y'' h => (dualCl_iff y y'').1 h,
      fun χ hχ hχ' => (dualCl_iff _ _).2 (dualCl_tw y χ hχ hχ').symm, fun ω hω => central_dualCl hω⟩
    · exact hdd ▸ (GlobalTheory.T.dual_class_cuspidal Pr.adm _ h).1
    · exact hdd ▸ dz_dualCl h
    · exact hdd ▸ goodCusp_dualCl h

end UpperTheory.Zero.LLC

end
end
