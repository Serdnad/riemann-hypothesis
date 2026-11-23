module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle247
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle383
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1911
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockEmbeddingArchimedeanComponents
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle064
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbelianizationEqOfForallAbRestrictEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle199
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle378
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle607
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsAnalyticUniformizationOfIsAnalyticIso
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle327
public import GroundTheory.GlobalFields.ComplexMultiplication.MainTheorem
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle296
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle055
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle084
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle066
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle065
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle319
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle002
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle053

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct Topology InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.HCCusp

open GlobalTheory.Cusp GlobalTheory.Mem.AutSpace

variable {D : D7} {θ : GlobalTheory.Mem.Th.InfF D} {V : HSp D}


variable (θ V) in
abbrev Mc : Submodule ℂ (GA D V → ℂ) := GlobalTheory.Cusp.cuspForms θ V ⊥

theorem mem_Mc_iff {φ : GA D V → ℂ} : φ ∈ Mc θ V ↔ IsAutFunSm θ V φ ∧ IsCuspFun V φ := by
  refine ⟨fun h => (mem_cuspForms.1 h).1, fun h => mem_cuspForms.2 ⟨h, ?_⟩⟩
  refine GlobalTheory.Doubling.isKFinite_iff.2 ⟨Submodule.span ℂ {φ}, inferInstance, fun k hk => ?_⟩
  rw [Subgroup.mem_bot.1 hk]
  exact Submodule.subset_span (by simp)

def der (hθ : IsInfFam θ) (τ : D.what₂.Tau) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    Module.End ℂ (Mc θ V) where
  toFun φ := ⟨Rder θ V τ X φ.1, mem_Mc_iff.2
    ⟨GlobalTheory.CuspLie.isAutFunSm_Rder hθ hX (mem_Mc_iff.1 φ.2).1,
      GlobalTheory.CuspLie.isCuspFun_Rder hθ hX (mem_Mc_iff.1 φ.2).1 (mem_Mc_iff.1 φ.2).2⟩⟩
  map_add' f g := Subtype.ext (Rder_add (mem_Mc_iff.1 f.2).1.smooth (mem_Mc_iff.1 g.2).1.smooth hX)
  map_smul' c f := Subtype.ext (Rder_smul c f.1 τ X)

def io (μ : Measure (GA D V)) [μ.IsHaarMeasure] (hθ : IsInfFam θ) : Mc θ V →ₗ[ℂ] L2cusp V μ :=
  GlobalTheory.Cusp.cuspToL2 ⊥ μ
    (GlobalTheory.Grow.cuspRapidDecay_of_bound GlobalTheory.CuspGeo.cuspDecayBound) hθ

theorem io_injective (μ : Measure (GA D V)) [μ.IsHaarMeasure] (hθ : IsInfFam θ) :
    Function.Injective (io (V := V) μ hθ) := cusp_form_toL2_injective _ hθ

def derInf (hθ : IsInfFam θ) (X : GlobalTheory.SmoothForms.LieN V) : Module.End ℂ (Mc θ V) :=
  ∑ τ, der hθ τ (X := (X τ).1) (X τ).2

def IsKLie {n : ℕ} (e : Fin n → Bool) (y : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  yᴴ = -y ∧ y * Formalism.REAL.Jm e = Formalism.REAL.Jm e * y

end GlobalTheory.CompanionTheory.HCCusp
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.GoodPos

theorem exists_conj_mem_majCpt_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ c : (∀ w : InfinitePlace F, GL (Fin n) (w.Completion ⊗[F] E)), (∀ w, ∃ ε : Fin n → Bool, Formalism.UG.cT (sigR _ σ) (c w).1 * JR w.Completion J * (c w).1 =
        Matrix.diagonal fun i => if ε i then 1 else -1) →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      1 ≤ d → (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∃ u ∈ GlobalTheory.StdPar.unip σ J Xf S, u ∈ infPts σ J ∧ ∃ y : GL (Fin d) (GlobalTheory.CuspRep.Cinf E),
        ∀ k : GlobalTheory.CuspRep.Kinf E d, (u * ι (GlobalTheory.CuspRep.infGL E d y)) * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) *
          (u * ι (GlobalTheory.CuspRep.infGL E d y))⁻¹ ∈ majCpt σ J c := by
  intro F E _ _ _ _ _ _ σ hCM n J hJ r Xf Yf hW c hc S l d h ι hι hd hS1 hS2 hS3
  obtain ⟨ρ, hρs, hρlift, hρι⟩ := GlobalTheory.BlockForms.exists_archComp_of_isBlockEmb F E σ hCM n J r Xf Yf l d h ι hι
  have loc := fun w => stab_of_frame F E σ hCM n J hJ r Xf Yf hW w (c w) (hc w) l d h
  choose uw N hN hNX hNv y₀ hy₀ using loc
  set u : GAd σ J := ofInf σ J (embArchPi σ J uw) with hu
  have hu_arch : ∀ w, projArch σ J w u = uw w := fun w => by
    rw [hu, projArch_ofInf, projInfArch_embArchPi]
  have hu_inf : u ∈ infPts σ J := mem_infPts.2 (projFin_ofInf _ _ _)
  obtain ⟨y, hy⟩ := hρlift y₀
  obtain ⟨k₀, hk₀S, hk₀⟩ := hS2
  refine ⟨u, mem_unip_of_arch_frame F E σ n J r Xf S u hu_inf fun w => ⟨N w, by rw [hu_arch]; exact hN w, fun i j hij => ?_,
    fun v hv => ?_⟩, hu_inf, y, fun k => ?_⟩
  · rcases hNX w i j hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases hS3 with h0 | ⟨p, hpS, hp⟩
      · omega
      · exact ⟨p, hpS, by rw [Fin.le_def]; omega, by rw [Fin.lt_def]; omega⟩
    · exact ⟨k₀, hk₀S, by rw [Fin.le_def]; omega, by rw [Fin.lt_def]; omega⟩
  · obtain ⟨a, ha, hav⟩ := hNv w v fun i hi => hv i ⟨k₀, hk₀S, by rw [Fin.le_def]; omega⟩
    exact ⟨a, fun i hi => ⟨k₀, hk₀S, by have := ha i hi; rw [Fin.le_def]; omega⟩, by rw [hu_arch]; exact hav⟩
  · have e : (u * ι (GlobalTheory.CuspRep.infGL E d y)) * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) *
        (u * ι (GlobalTheory.CuspRep.infGL E d y))⁻¹ = u * ι (GlobalTheory.CuspRep.infGL E d (y * Unitary.toUnits k * y⁻¹)) * u⁻¹ := by
      simp only [map_mul, map_inv]; group
    rw [e, mem_majCpt]
    refine ⟨mul_mem (mul_mem hu_inf (hρι _).1) (inv_mem hu_inf), fun w => ?_⟩
    rw [map_mul, map_mul, map_inv, hu_arch]
    refine hy₀ w (Matrix.GeneralLinearGroup.map (ρ w) (Unitary.toUnits k)) ?_ _ ?_
    · have hk : star (k : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf E)) * (k : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf E)) = 1 :=
        Unitary.star_mul_self_of_mem k.2
      have e1 : Formalism.UG.cT (sigR w.Completion σ) ((Matrix.GeneralLinearGroup.map (ρ w) (Unitary.toUnits k)).1) =
          (star (k : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf E))).map (ρ w) := by
        ext i j
        simp [Formalism.UG.cT, Matrix.star_apply, hρs]
      rw [e1]
      change _ * (k : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf E)).map (ρ w) = 1
      rw [← Matrix.map_mul, hk, Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [(hρι _).2 w]
      simp only [map_mul, map_inv, hy w]

end GlobalTheory.CompanionTheory.GoodPos
end
end

section

open NumberField
open scoped nonZeroDivisors GlobalTheory.Idele

namespace GlobalTheory.CompanionTheory.Hypotheses₂

theorem ellipticMainTheoremCM : GlobalTheory.Published.EllipticMainTheoremCM := by
  classical
  intro K _ _ _ _ h2 Art hArt σ s hs X _ 𝔞 h𝔞 ξ hξ
  obtain ⟨Art₀, hArt₀, hlink⟩ := GlobalTheory.CompanionTheory.EllipticCM.exists_globalArtinMap_tied K h2
  have hEq : Art = Art₀ := MonoidHom.ext fun c =>
    GlobalTheory.CompanionTheory.GaloisAb.abelianization_eq_of_forall_abRestrict_eq K _ _ fun L h =>
      GlobalTheory.T.artin_map_abelian_unique K Art Art₀ hArt hArt₀ L h c
  subst hEq
  have hfound := hlink σ s hs
  let 𝔞u : (FractionalIdeal (𝓞 K)⁰ K)ˣ := Units.mk0 𝔞 h𝔞
  have hf := GlobalTheory.CompanionTheory.EllipticCM.isAnalyticUniformization_of_isAnalyticIso h2 X 𝔞 h𝔞 ξ hξ
  obtain ⟨f', ⟨hf', hrel⟩, -⟩ :=
    GroundTheory.Global.Elliptic.main_theorem_complexMultiplication h2 σ s hfound 𝔞u hf
  have hid : ((s⁻¹ • 𝔞u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      (GlobalTheory.EllipticCM.finitePart (K := K) s)⁻¹ • 𝔞 :=
    GlobalTheory.CompanionTheory.EllipticCM.inv_smul_eq_finitePart_inv_smul s 𝔞u
  rw [hid] at hf'
  have hex := GlobalTheory.CompanionTheory.EllipticUniformization.exists_analyticIso_of_isAnalyticUniformization _ _ f' hf'
  rw [GlobalTheory.CompanionTheory.EllipticDict.idealLattice_toAddSubgroup_eq_idealSub] at hex
  obtain ⟨ξ', hξ', hξf⟩ := hex
  refine GlobalTheory.EllipticCM.transports_of_exists h𝔞 rfl hξ' fun x => ?_
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _
    (GlobalTheory.Idele.mulEquiv (GlobalTheory.EllipticCM.finitePart (K := K) s)⁻¹ h𝔞 rfl (Submodule.Quotient.mk t))
  rw [← hy]
  have hq := (GlobalTheory.CompanionTheory.IdeleQuot.smulQuotient_inv_mk_eq_mk_iff_mulEquiv s 𝔞u t y).2 hy.symm
  have h3 := hrel t y hq
  rw [GlobalTheory.CompanionTheory.ConjPointDict.mapPoint_eq_pointMapRing, GlobalTheory.EllipticCM.torsionIncl_mk,
    GlobalTheory.EllipticCM.torsionIncl_mk, hξf, h3]
  rfl

end GlobalTheory.CompanionTheory.Hypotheses₂
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.TD

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Published GlobalTheory.LocGL.SupportUnique GlobalTheory.SplitRead

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem exists_hasSupport (hBZ : BernsteinZelevinskyFiniteness) (hG : GeometricLemma) (x : IrrGL (k := k)) :
    ∃ s, HasSupport x.rep s := by
  obtain ⟨s, d, σ, h⟩ := GlobalTheory.CuspSupportExist.main hBZ hG k x.1 (Irr.ofIrrRep x.2.rep)
  exact ⟨_, hasSupport_of_isCuspSupport h⟩

theorem map_univ_eq_sum {α : Type} {β : Type*} [Fintype α] (f : α → β) :
    Finset.univ.val.map f = ∑ a, ({f a} : Multiset β) := by
  rw [Finset.sum, ← Multiset.sum_map_singleton (Finset.univ.val.map f), Multiset.map_map]
  rfl

theorem hasSupport_of_isSubquotient_prodIrr {c N : ℕ} {y : Fin c → IrrGL (k := k)}
    {hd : ∑ a, (y a).1 = N} {t : Fin c → Multiset (IrrGL (k := k))} (ht : ∀ a, HasSupport (y a).rep (t a))
    {π : Representation ℂ (GL (Fin N) k) V} (hi : π.IsIrreducible) (h : IsSubquotient π (prodIrr y hd)) :
    HasSupport π (∑ a, t a) := by
  choose T u hu hc using ht
  have h3 := fun a => (hc a).2.2
  choose e' he' using h3
  let e := stdBlocks (fun a => (y a).1) hd
  have step1 : IsSubquotient (multiProd e fun a => (y a).rep)
      (multiProd e fun a => multiProd (e' a) fun b => (u a b).rep) :=
    GlobalTheory.CuspSupportExist.L_ind k _ _ _ e _ _ _ _ (isSmooth_piTensor fun a => isSmooth_parInd _ _)
      (GlobalTheory.CuspSupportExist.L_pit _ _ _ _ _ _ he')
  obtain ⟨E, hE⟩ := GlobalTheory.CuspSupportExist.L_stage k c N (fun a => (y a).1) e T (fun a b => (u a b).1) e' _
    (fun a b => (u a b).rep) fun a b => (u a b).2.rep.smooth
  refine ⟨∑ a, T a, fun c => u (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2, ?_, hi,
    fun c => (hc _).2.1 _, E, h.trans (step1.trans hE)⟩
  rw [map_univ_eq_sum, Equiv.sum_comp finSigmaFinEquiv.symm (fun p : (Σ a, Fin (T a)) => ({u p.1 p.2} : Multiset _)),
    Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← hu a, map_univ_eq_sum]

theorem exists_sum_of_jac (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness) {N : ℕ}
    {π : Representation ℂ (GL (Fin N) k) V} {s : Multiset (IrrGL (k := k))} (hs : HasSupport π s) {r : ℕ} {d : Fin r → ℕ}
    (e' : (Σ j, Fin (d j)) ≃ Fin N) {τ : Representation ℂ (Levi k fun j => Fin (d j)) W} (hτ : τ.IsIrreducible)
    (hτs : IsSubquotient τ (_root_.GlobalTheory.SmGL.jac e' π)) (y : ∀ j, IrrRep (GL (Fin (d j)) k))
    (hy : ∀ j, IsSubquotient (y j).ρ (τ.comp (MonoidHom.mulSingle (fun j => GL (Fin (d j)) k) j) :
      Representation ℂ (GL (Fin (d j)) k) W)) :
    ∃ t : Fin r → Multiset (IrrGL (k := k)), (∀ j, HasSupport (y j).ρ (t j)) ∧ s = ∑ j, t j := by
  obtain ⟨h, x, rfl, hi, hc, e, hsub⟩ := hs
  have hx : ∀ i, (x i).IsCusp := fun i => ⟨(hc i).1, (hc i).2.2⟩
  obtain ⟨b, f, g, c, hrow, hcol⟩ := exists_cell_of_isSubquotient (hG k).1 (hG k).2 e e'
    (fun i => (x i).2.rep.smooth) (fun i => (x i).2.rep.hasFiniteLength) hτ
    (hτs.trans (GlobalTheory.JacquetExact.isSubquotient_jac e' (isSmooth_parInd _ _) hsub))
  choose J hJ0 hJ using fun i => exists_block_of_isCusp (hx i) (f i) (c i) (hrow i)
  let u : Fin h → Fin r → Multiset (IrrGL (k := k)) := fun i j => if j = J i then {x i} else 0
  have hu : ∀ i j, HasSupport (IrrGL.of (c i j).ρ (c i j).smooth (c i j).irr).rep (u i j) := by
    intro i j
    by_cases hj : j = J i
    · subst hj
      simp only [u, if_true]
      rw [hJ i]
      exact hasSupport_self (hx i)
    · obtain ⟨s', hs'⟩ := exists_hasSupport hBZ hG (IrrGL.of (c i j).ρ (c i j).smooth (c i j).irr)
      simp only [u, if_neg hj]
      rwa [eq_zero_of_hasSupport (hJ0 i j hj) hs'] at hs'
  refine ⟨fun j => ∑ i, u i j, fun j => ?_, ?_⟩
  · have hd : ∑ i, b.1 i j = d j := by simpa using b.2.2 j
    have h1 := isSubquotient_factor (fun j => multiProd (g j) fun i => (c i j).ρ) j (y j).irr
      ((hy j).trans (isSubquotient_comp hcol _))
    obtain ⟨φ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ (g j) (stdBlocks (fun i => b.1 i j) hd) _).1
      (piTensor fun i => (c i j).ρ)
    let ψ := φ.trans (prodIrrEquiv hd (fun i => (c i j).ρ) (fun i => (c i j).smooth) fun i => (c i j).irr)
    exact hasSupport_of_isSubquotient_prodIrr
      (y := fun i => IrrGL.of (c i j).ρ (c i j).smooth (c i j).irr) (fun i => hu i j) (y j).irr
      (h1.trans (.of_injective ψ.toIntertwiningMap ψ.toLinearEquiv.injective))
  · rw [Finset.sum_comm]
    simp only [u, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Multiset.sum_map_singleton (Finset.univ.val.map x), Multiset.map_map]
    rfl

theorem eq_of_hasSupport (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness) (N : ℕ) :
    ∀ (x : IrrGL (k := k)), x.1 = N → ∀ s t : Multiset (IrrGL (k := k)), HasSupport x.rep s → HasSupport x.rep t → s = t := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rintro x rfl s t hs ht
    rcases Nat.eq_zero_or_pos x.1 with h0 | hpos
    · rw [eq_zero_of_hasSupport h0 hs, eq_zero_of_hasSupport h0 ht]
    by_cases hc : IsCuspidal x.rep
    · rw [eq_singleton_of_isCusp ⟨hpos, hc⟩ hs, eq_singleton_of_isCusp ⟨hpos, hc⟩ ht]
    obtain ⟨r, d, e, hU, hJ⟩ : ∃ (r : ℕ) (d : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin x.1), unipRad k e ≠ ⊥ ∧
        ¬ Subsingleton (Jacquet x.rep (unipRad k e)) := by
      by_contra! hn
      exact hc ⟨x.2.rep.smooth, hn⟩
    obtain ⟨Y, _, _, τ, hτ, hτs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _ (_root_.GlobalTheory.SmGL.jac e x.rep)
      (not_subsingleton_iff_nontrivial.1 hJ)
    have hτsm : IsSmooth τ := hτs.isSmooth (isSmooth_jac e x.2.rep.smooth)
    have hy : ∀ j, ∃ y : IrrRep (GL (Fin (d j)) k), IsSubquotient y.ρ
        (τ.comp (MonoidHom.mulSingle (fun j => GL (Fin (d j)) k) j) : Representation ℂ (GL (Fin (d j)) k) Y) := by
      intro j
      obtain ⟨X, _, _, υ, hυ, hυs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _
        (τ.comp (MonoidHom.mulSingle (fun j => GL (Fin (d j)) k) j))
        (GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hτ)
      exact ⟨⟨X, υ, hυs.isSmooth (isSmooth_comp hτsm _
        (continuous_mulSingle (A := fun j => GL (Fin (d j)) k) j)), hυ⟩, hυs⟩
    choose y hy using hy
    obtain ⟨u, hu, rfl⟩ := exists_sum_of_jac hG hBZ hs e hτ hτs y hy
    obtain ⟨u', hu', rfl⟩ := exists_sum_of_jac hG hBZ ht e hτ hτs y hy
    refine Finset.sum_congr rfl fun j _ => ?_
    have hlt : d j < x.1 := by
      have hN : ∑ a, d a = x.1 := by simpa using Fintype.card_congr e
      obtain ⟨a, ha, hda⟩ : ∃ a, a ≠ j ∧ 0 < d a := by
        obtain ⟨p, q, hpq⟩ := GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff.1 hU
        obtain ⟨⟨a, p⟩, rfl⟩ := e.surjective p
        obtain ⟨⟨b, q⟩, rfl⟩ := e.surjective q
        rw [blk_apply, blk_apply] at hpq
        by_cases haj : a = j
        · exact ⟨b, fun hb => hpq.ne (haj.trans hb.symm), q.pos⟩
        · exact ⟨a, haj, p.pos⟩
      have h1 := Finset.add_le_sum (s := Finset.univ) (f := d) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
        (Finset.mem_univ j) ha
      omega
    exact ih (d j) hlt (IrrGL.of (y j).ρ (y j).smooth (y j).irr) rfl _ _
      ((hu j).of_equiv (IrrGL.equivOf _ _ _)) ((hu' j).of_equiv (IrrGL.equivOf _ _ _))

theorem hasSupport_unique (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness) {N : ℕ}
    {π : Representation ℂ (GL (Fin N) k) V} {s t : Multiset (IrrGL (k := k))} (hs : HasSupport π s)
    (ht : HasSupport π t) : s = t := by
  have φ := IrrGL.equivOf π hs.isSmooth hs.isIrreducible
  exact eq_of_hasSupport hG hBZ N (IrrGL.of π hs.isSmooth hs.isIrreducible) rfl s t (hs.of_equiv φ) (ht.of_equiv φ)

end GlobalTheory.CompanionTheory.Hypotheses₂.TD
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test

variable {F : Type} [Field F] [NumberField F]

theorem singleV_apply_self' (v : HeightOneSpectrum (𝓞 F)) (s : Fv F v) : (singleV F v s) v = s := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v s

theorem singleV_apply_ne' (v w : HeightOneSpectrum (𝓞 F)) (s : Fv F v) (h : w ≠ v) :
    (singleV F v s) w = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) s h

theorem singleV_mul_box (v : HeightOneSpectrum (𝓞 F)) (s : Fv F v) (b : Af F) :
    singleV F v s * b = singleV F v (s * b v) := by
  refine RestrictedProduct.ext _ _ fun w => ?_
  change (singleV F v s) w * b w = (singleV F v (s * b v)) w
  by_cases h : w = v
  · subst h
    rw [singleV_apply_self', singleV_apply_self']
  · rw [singleV_apply_ne' v w _ h, singleV_apply_ne' v w _ h, zero_mul]

open Classical in
theorem sum_singleV_apply (T : Finset (HeightOneSpectrum (𝓞 F))) (c : Af F) (w : HeightOneSpectrum (𝓞 F)) :
    (∑ v ∈ T, singleV F v (c v)) w = if w ∈ T then c w else 0 := by
  classical
  have h1 : (∑ v ∈ T, singleV F v (c v)) w = ∑ v ∈ T, (singleV F v (c v)) w :=
    map_sum (evalV F w) _ T
  rw [h1]
  split_ifs with hw
  · rw [Finset.sum_eq_single w (fun v _ hv => singleV_apply_ne' v w _ (Ne.symm hv))
      (fun h => absurd hw h), singleV_apply_self']
  · exact Finset.sum_eq_zero fun v hv => singleV_apply_ne' v w _ (fun h => hw (h ▸ hv))

theorem singleV_mem_boxA (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v))
    (hU : ∀ v, (0 : Fv F v) ∈ U v) (v : HeightOneSpectrum (𝓞 F)) (s : Fv F v)
    (hS : v ∈ S → s ∈ U v) (hO : v ∉ S → s ∈ v.adicCompletionIntegers F) :
    singleV F v s ∈ Coef.boxA S U := by
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · by_cases h : w = v
    · subst h; rw [singleV_apply_self']; exact hS hw
    · rw [singleV_apply_ne' v w _ h]; exact hU w
  · by_cases h : w = v
    · subst h; rw [singleV_apply_self']; exact hO hw
    · rw [singleV_apply_ne' v w _ h]; exact zero_mem _

theorem annF_boxA : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ S : Finset (HeightOneSpectrum (𝓞 F)), (∀ v, v ∉ S → annV ψ v (v.adicCompletionIntegers F : Set (Fv F v)) = (v.adicCompletionIntegers F : Set (Fv F v))) → ∀ U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v), (∀ v, (0 : Fv F v) ∈ U v) → annF ψ (Coef.boxA S U) = Coef.boxA S (fun v => annV ψ v (U v)) := by
  intro F _ _ ψ hψ S hS U hU
  classical
  ext b
  constructor
  · intro hb
    have key : ∀ v (s : Fv F v), (v ∈ S → s ∈ U v) → (v ∉ S → s ∈ v.adicCompletionIntegers F) →
        psiV F ψ v (s * b v) = 1 := by
      intro v s h1 h2
      have := hb _ (singleV_mem_boxA S U hU v s h1 h2)
      rwa [singleV_mul_box, psiF_singleV] at this
    refine ⟨fun v hv s hs => key v s (fun _ => hs) (fun h => absurd hv h), fun v hv => ?_⟩
    have hmem : b v ∈ annV ψ v (v.adicCompletionIntegers F : Set (Fv F v)) :=
      fun s hs => key v s (fun h => absurd h hv) (fun _ => hs)
    rw [hS v hv] at hmem
    exact hmem
  · rintro ⟨hb1, hb2⟩ y ⟨hy1, hy2⟩
    obtain ⟨T, hT⟩ := GlobalTheory.T.adelic_character_trivial_almost_everywhere F ψ hψ
    set c := y * b with hc
    have hcv : ∀ v, c v = y v * b v := fun v => rfl
    set T' := T ∪ S with hT'
    set e : Af F := ∑ v ∈ T', singleV F v (c v) with he
    have hcint : ∀ v, v ∉ S → c v ∈ v.adicCompletionIntegers F := fun v hv => by
      rw [hcv]; exact mul_mem (hy2 v hv) (hb2 v hv)
    have hd : psiF ψ (c - e) = 1 := by
      have happ : ∀ w, (c - e) w = c w - (if w ∈ T' then c w else 0) := fun w => by
        rw [← sum_singleV_apply T' c w]; rfl
      refine hT _ (fun w => ?_) (fun w hw => ?_)
      · rw [happ]
        split_ifs with h
        · rw [sub_self]; exact zero_mem _
        · rw [sub_zero]
          exact hcint w (fun hw => h (Finset.mem_union_right _ hw))
      · rw [happ, if_pos (Finset.mem_union_left _ hw), sub_self]
    have hsum : psiF ψ e = 1 := by
      rw [he]
      refine Finset.sum_induction _ (fun x => psiF ψ x = 1) (fun a b ha hb => by rw [psiF_add, ha, hb, one_mul])
        (psiF_zero ψ) (fun v _ => ?_)
      rw [psiF_singleV]
      by_cases hv : v ∈ S
      · rw [hcv]; exact hb1 v hv (y v) (hy1 v hv)
      · have h1 : c v ∈ annV ψ v (v.adicCompletionIntegers F : Set (Fv F v)) := by
          rw [hS v hv]; exact hcint v hv
        have := h1 1 (one_mem _)
        rwa [one_mul] at this
    have : c = (c - e) + e := by abel
    change psiF ψ c = 1
    rw [this, psiF_add, hd, hsum, one_mul]

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
end
