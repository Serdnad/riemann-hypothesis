module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle002
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle009
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.TensorProductVectors
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivPiExteriorTensorBlockLevi
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle028
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle031
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.CornerStable
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.RelKill
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle010
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section




section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix UpperTheory.TNZ
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.NonzeroTypeTheory
abbrev _root_.UpperTheory.NonzeroTypeTheory.typeData_of_s_ty : Prop := ∀ (P : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (a1 : ArtinTransferDecompositionCharacter) (a3 : LocalArtinCharacterProduct) (a4 : FiniteDimensionalTranslationCoordinates) (a5 : TwistedSphericalRepresentative) (a6 : DistinctOnUnitsDistinctOnInertia)
    (a7 : SmoothVectorsFixedByCongruence) (gm : _root_.UpperTheory.TNZ.GMainAlt) (ge : GEmb) (gi : ArtinInertiaProp) (cm : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → Need_CMain) (cp : Need_CProps) (gr : Need_Grp),
    _root_.UpperTheory.NonzeroTypeTheory.TypeDataAlt
end UpperTheory.NonzeroTypeTheory
end
end
end

section




section
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.TNZ
theorem gMain_alt (h1 : DeterminantVectorProp) (h2 : UnramifiedTwistProp) (h3 : SumOverListProp) (h4a : IsotypicComponentProp)
    (h4b : ScalarOnInertiaProp) (h5 : SphericalOfUnramifiedProp) (h5' : SphericalUnramifiedProp) (h6 : TwistRestrictionProp) (h6' : UntwistRestrictionProp)
    (h7 : ProductRestrictionProp) (h8a : _root_.UpperTheory.TNZ.Step_cuspSupp_alt) (h8b : _root_.UpperTheory.TNZ.Step_prodIrr_alt) (h9 : ArtinInertiaProp) : _root_.UpperTheory.TNZ.GMainAlt := by
  intro E Ω _ _ _ _ _ A w h a ha ε rc hL hLit s d η hη hdist x hd
  have hψ : ∀ b, IsSmooth ((η b).comp a) := fun b => ha.smooth (hη b)
  constructor
  · rintro ⟨h0, hc⟩
    obtain ⟨v, hv, hsum⟩ := h4a E Ω A w h (rc x) s d (fun b => (η b).comp a) hψ hdist h0 hc
    have hv' : ∀ b, ∃ v' : WD h, v'.unr ∧ v'.lpDim = d b ∧
        v b = v'.lpChar (WD.lpOfChar h ((η b).comp a) (hψ b)) := by
      intro b
      obtain ⟨v', hu, hdim, he⟩ := h4b E Ω A w h (v b) ((η b).comp a) (hψ b) (hv b).1
        (fun t => by rw [(hv b).2.1]; exact (hv b).2.2 t)
      exact ⟨v', hu, hdim.trans (hv b).2.1, he⟩
    choose v' hu hdim he using hv'
    choose Xs instA instM σ hs hi hsph hrc using fun b => h5 E Ω A w h a ha ε rc hL (d b) (v' b) (hu b) (hdim b)
    letI := instA
    letI := instM
    choose hs' hi' hrc' using fun b => h6 E Ω A w h a ha ε rc hL (d b) (Xs b) (σ b) (hs b) (hi b) (η b) (hη b)
    have hdet : ∀ b, HasDetVec (twist (σ b) (detChar (Fin (d b)) (η b))) (η b) :=
      fun b => (h1 _ (d b) (Xs b) (σ b) (η b)).1 (hsph b)
    have hdistU : ∀ b c, b ≠ c → ∃ u : (w.adicCompletion E)ˣ,
        valuation (w.adicCompletion E) (u : w.adicCompletion E) = 1 ∧ η b u ≠ η c u := by
      intro b c hbc
      obtain ⟨t, ht⟩ := hdist b c hbc
      exact ⟨a (ineIncl h t), (h9 E Ω A w h a ha).1 t, ht⟩
    have hI := h8b h8a hLit _ s x.1 d hd Xs (fun b => twist (σ b) (detChar (Fin (d b)) (η b))) hs' hi' η hη hdet hdistU
    have hrcP := h7 E Ω A w h a ha ε rc hL s x.1 d hd Xs (fun b => twist (σ b) (detChar (Fin (d b)) (η b))) hs' hi' hI
    have heq : rc (IrrGL.of (multiProd (stdBlocks d hd) fun b => twist (σ b) (detChar (Fin (d b)) (η b)))
        (isSmooth_parInd _ _) hI) = rc x := by
      rw [hrcP, hsum]
      congr 1
      refine List.ofFn_inj.2 (funext fun b => ?_)
      rw [hrc' b, hrc b, he b]
    have e2 := (hL.bij.1 heq).trans (IrrGL.of_rep x).symm
    obtain ⟨e⟩ := IrrGL.of_eq_of.1 e2
    exact ⟨Xs, instA, instM, fun b => twist (σ b) (detChar (Fin (d b)) (η b)), hs', hi', hdet, ⟨e.symm⟩⟩
  · rintro ⟨Xs, instA, instM, σ, hs, hi, hdet, ⟨e⟩⟩
    letI := instA
    letI := instM
    have hI : (multiProd (stdBlocks d hd) σ).IsIrreducible := GlobalTheory.Parabolic.isIrreducible_of_equiv e x.2.rep.irr
    have hx : x = IrrGL.of (multiProd (stdBlocks d hd) σ) (isSmooth_parInd _ _) hI :=
      (IrrGL.of_rep x).symm.trans (IrrGL.of_eq_of.2 ⟨e⟩)
    have hfac : ∀ b, ∃ u : WD h, u.unr ∧ u.lpDim = d b ∧
        rc (IrrGL.of (σ b) (hs b) (hi b)) = u.lpChar (WD.lpOfChar h ((η b).comp a) (hψ b)) := by
      intro b
      obtain ⟨hs', hi', hr⟩ := h6' E Ω A w h a ha ε rc hL (d b) (Xs b) (σ b) (hs b) (hi b) (η b) (hη b)
      exact ⟨_, h5' E Ω A w h a ha ε rc hL (d b) (Xs b) _ hs' hi' ((h1 _ (d b) (Xs b) (σ b) (η b)).2 (hdet b)),
        hL.dim _, hr⟩
    choose u hu hud hur using hfac
    have hl := h3 E Ω A w h (List.ofFn fun b => rc (IrrGL.of (σ b) (hs b) (hi b)))
    have hP := h7 E Ω A w h a ha ε rc hL s x.1 d hd Xs σ hs hi hI
    rw [← hx] at hP
    rw [hP]
    refine ⟨hl.1.2 fun y hy => ?_, fun t => ?_⟩
    · simp only [List.mem_ofFn, Set.mem_range] at hy
      obtain ⟨b, rfl⟩ := hy
      rw [hur b]
      exact (h2 E Ω A w h (u b) _ (hψ b) (hu b)).1
    · rw [hl.2, List.map_ofFn, List.prod_ofFn]
      refine Finset.prod_congr rfl fun b _ => ?_
      simp only [Function.comp_apply]
      rw [hur b, (h2 E Ω A w h (u b) _ (hψ b) (hu b)).2 t, hud b]
      rfl
end UpperTheory.TNZ
end
end
end

section




section
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace Grp
namespace JacquetFiniteLength₂
variable {n : ℕ} (G : Grp k n)
end JacquetFiniteLength₂
theorem step_jacFin_alt {n : ℕ} (G : Grp k n) : G.Step_jacFin_alt := by
  intro L V _ _ π hπ hirr
  exact ⟨isSmooth_jacU G.e hπ,
    JacquetFiniteLength₂.hasFiniteLength_jacU G L.loc.bz π hπ (hasFiniteLength_of_isIrreducible hirr)⟩
end Grp
end UpperTheory.TNZ
end
end
end

section




section
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
open scoped TensorProduct
open Module
namespace UpperTheory.TNZ.Grp.Tensor₂
section Contr
variable {ι : Type} [Fintype ι] [hd : DecidableEq ι] {Y : ι → Type} [∀ b, AddCommGroup (Y b)]
  [∀ b, Module ℂ (Y b)]
end Contr
end UpperTheory.TNZ.Grp.Tensor₂
namespace UpperTheory.TNZ.Grp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
theorem step_tensor_alt {n : ℕ} (G : Grp k n) : G.Step_tensor_alt := by
  intro hN X _ _ σ hs hirr hη
  obtain ⟨y, hy0, hy⟩ := hη
  obtain ⟨s, ⟨E⟩⟩ := GlobalTheory.LeviFactor.exists_equiv_piTensor_levi hN.loc.bz k (Fin G.s)
    (fun a => Fin (G.d a)) { V := X, ρ := σ, smooth := hs, irr := hirr }
  refine ⟨fun a => (s a).V, fun a => inferInstance, fun a => inferInstance, fun a => (s a).ρ,
    fun a => (s a).smooth, fun a => (s a).irr, fun a => ?_, ⟨E⟩⟩
  have hE : ∀ m, E (σ m y) = piTensor (fun b => (s b).ρ) m (E y) := fun m =>
    LinearMap.congr_fun (E.toIntertwiningMap.isIntertwining' m) y
  have hEy : E y ≠ 0 := (map_ne_zero_iff E (EquivLike.injective E)).2 hy0
  have hK : ∀ g ∈ (KO k (Fin (G.d a)) : Set (GL (Fin (G.d a)) k)),
      piTensor (fun b => (s b).ρ) (Pi.mulSingle a g) (E y) =
        ((G.μ a (GeneralLinearGroup.det g) : ℂˣ) : ℂ) • E y := by
    intro g hg
    have hm : (Pi.mulSingle a g : Levi k fun b : Fin G.s => Fin (G.d b)) ∈
        leviK k (m := fun b : Fin G.s => Fin (G.d b)) := by
      rw [leviK, Subgroup.mem_pi]
      intro b _
      by_cases hb : b = a
      · subst hb
        rw [Pi.mulSingle_eq_same]
        exact hg
      · rw [Pi.mulSingle_eq_of_ne hb]
        exact one_mem _
    rw [← hE, hy _ hm, map_smul]
    congr 1
    rw [eta, Finset.prod_eq_single a]
    · rw [Pi.mulSingle_eq_same]
    · intro b _ hb
      rw [Pi.mulSingle_eq_of_ne hb, map_one, map_one, Units.val_one]
    · intro h
      exact absurd (Finset.mem_univ a) h
  exact Tensor₂.exists_factor_vec (fun b => (s b).ρ) a (E y) hEy _ _ hK
end UpperTheory.TNZ.Grp
end
end
end

section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th
private theorem adL_conj {C G V : Type} [CommRing C] [Group G] [AddCommGroup V] [Module C V] (ρ : Representation C G V)
    (c : G → V) (hc : ∀ g h, c (g * h) = c g + ρ g (c h)) (γ g : G) :
    c g = ρ γ (c (γ⁻¹ * g * γ)) + c γ - ρ g (c γ) := by
  have h1 := hc γ (γ⁻¹ * g * γ)
  rw [← mul_assoc, mul_inv_cancel_left, hc] at h1
  rw [eq_sub_iff_add_eq, h1, add_comm]
private theorem adL_rho {C G V : Type} [CommRing C] [Group G] [AddCommGroup V] [Module C V] (ρ : Representation C G V)
    (γ g : G) (x : V) : ρ γ (ρ (γ⁻¹ * g * γ) x) = ρ g (ρ γ x) := by
  rw [← Module.End.mul_apply, ← map_mul, ← mul_assoc, mul_inv_cancel_left, map_mul, Module.End.mul_apply]
private theorem adL_emb {F Ω K : Type} [Field F] [Field Ω] [Field K] [CharZero F] [Algebra F Ω] [IsAlgClosure F Ω]
    (j j₀ : Ω →+* K) (h : j₀.comp (algebraMap F Ω) = j.comp (algebraMap F Ω)) :
    ∃ γ : Ω ≃ₐ[F] Ω, ∀ y, j (γ y) = j₀ y := by
  letI : Algebra F K := (j.comp (algebraMap F Ω)).toAlgebra
  letI : Algebra Ω K := j.toAlgebra
  haveI : IsScalarTower F Ω K := IsScalarTower.of_algebraMap_eq' rfl
  let f : Ω →ₐ[F] K := { j₀ with commutes' := fun x => RingHom.congr_fun h x }
  exact ⟨f.restrictNormal' Ω, fun y => f.restrictNormal_commutes Ω y⟩
private theorem adL_above {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] (j : Ω →+* Formalism.BasicNotions.Loc.Om l) {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (φ : H →* Formalism.BasicNotions.Loc.GQ l) (ψ : H →* G F Ω) (hφ : Topology.IsOpenEmbedding φ) (hψ : Continuous ψ)
    (hj : ∀ h y, φ h (j y) = j (ψ h y))
    {C V : Type} [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] C V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V] (ρ : Representation C (G F Ω) V)
    (c : G F Ω → V) (hc : c ∈ Z1 ρ) (hb : Af.IsBK l ρ c) : (fun h => c (ψ h)) ∈ Loc.finiteCocycles φ (ρ.comp ψ) := by
  obtain ⟨j₀, hj₀, h0⟩ := hb.above (j.comp (algebraMap F Ω))
  obtain ⟨γ, hγ⟩ := adL_emb j j₀ hj₀
  let ψ' : H →* G F Ω := (MulAut.conj (γ⁻¹ : G F Ω)).toMonoidHom.comp ψ
  have hψ' : ∀ h, ψ' h = γ⁻¹ * ψ h * γ := fun h => by simp [ψ']
  obtain ⟨-, x, hx⟩ := (Loc.bkAbove (F := F) j₀ φ ψ' hφ (fun h y => by
    rw [← hγ, hj, ← hγ, hψ']
    simp) ρ c hc).2 h0
  refine ⟨⟨hc.1.comp hψ, fun g h => (congrArg c (map_mul ψ g h)).trans (hc.2 _ _)⟩,
    TensorProduct.AlgebraTensorModule.map (ρ γ) LinearMap.id x - c γ ⊗ₜ[ℚ_[l]] 1, fun h => ?_⟩
  have e : ∀ w, TensorProduct.AlgebraTensorModule.map (ρ γ) LinearMap.id (Loc.actC φ (ρ.comp ψ') h w) =
      Loc.actC φ (ρ.comp ψ) h (TensorProduct.AlgebraTensorModule.map (ρ γ) LinearMap.id w) := fun w => by
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      simp only [Loc.actC, TensorProduct.AlgebraTensorModule.map_tmul, MonoidHom.comp_apply, hψ', adL_rho, LinearMap.id_apply]
    | add u v hu hv => simp only [map_add (f := _), hu, hv]
  have h2 := congrArg (TensorProduct.AlgebraTensorModule.map (ρ γ) LinearMap.id) (hx h)
  rw [map_sub, e, TensorProduct.AlgebraTensorModule.map_tmul] at h2
  have h3 : Loc.actC φ (ρ.comp ψ) h (c γ ⊗ₜ[ℚ_[l]] 1) = ρ (ψ h) (c γ) ⊗ₜ[ℚ_[l]] 1 := by simp [Loc.actC]
  change c (ψ h) ⊗ₜ[ℚ_[l]] _ = _
  rw [adL_conj ρ c hc.2 γ (ψ h), TensorProduct.sub_tmul, TensorProduct.add_tmul, map_sub, h3]
  simp only [LinearMap.id_apply, hψ'] at h2
  rw [h2]
  abel
open scoped Pointwise in
private theorem adL_ine {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A : ValuationSubring Ω} (γ : G F Ω)
    {g : G F Ω} (hg : g ∈ Ine (F := F) (γ • A)) : γ⁻¹ * g * γ ∈ Ine (F := F) A := by
  have m : ∀ y : Ω, γ y ∈ γ • A ↔ y ∈ A := fun y => ValuationSubring.smul_mem_pointwise_smul_iff (g := γ)
  refine ⟨?_, fun x hx => ?_⟩
  · have h1 : g • γ • A = γ • A := hg.1
    change (γ⁻¹ * g * γ) • A = A
    rw [mul_smul, mul_smul, h1, inv_smul_smul]
  · have h2 := hg.2 (γ x) (by rwa [ValuationSubring.valuation_le_one_iff, m, ← ValuationSubring.valuation_le_one_iff])
    have e : g (γ x) - γ x = γ ((γ⁻¹ * g * γ) x - x) := by simp
    rwa [e, valuation_lt_one_iff', m, ← map_inv₀, m, map_eq_zero_iff _ γ.injective, ← valuation_lt_one_iff'] at h2
private theorem adL_away {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime]
    {C V : Type} [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] C V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V] (ρ : Representation C (G F Ω) V)
    (c : G F Ω → V) (hc : c ∈ Z1 ρ) (hb : Af.IsBK l ρ c) (w : HeightOneSpectrum (𝓞 F)) (hw : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal)
    (A : ValuationSubring Ω) (hA : IsPlaceOver A w) : ∃ x : V, ∀ g ∈ Ine (F := F) A, c g = ρ g x - x := by
  obtain ⟨A₀, hA₀, x, hx⟩ := hb.away w hw
  obtain ⟨γ, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) hA₀ hA
  refine ⟨ρ γ x - c γ, fun g hg => ?_⟩
  rw [adL_conj ρ c hc.2 γ g, hx _ (adL_ine γ hg), map_sub, adL_rho, map_sub]
  abel
private theorem adL_pr {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev) : Function.Surjective V.pr := fun g => by
  obtain ⟨τ, hτ⟩ : ∃ τ, toGS Ω V.S' τ = g.1 := QuotientGroup.mk_surjective g.1
  obtain ⟨σ, rfl⟩ := (V.hη τ).1 (by rw [hτ]; exact g.2)
  exact ⟨σ, Subtype.ext hτ⟩
private theorem adL_desc {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : W.GDet n A G) (φ : H →* G)
    (hφ : Function.Surjective φ) (ρ : G →* GL (Fin n) A) (hD : D.comap φ = W.GDet.ofRep (W.mat (ρ.comp φ))) :
    D = W.GDet.ofRep (W.mat ρ) := by
  refine CA.d_gext _ _ fun g i _ _ => ?_
  obtain ⟨h, rfl⟩ := hφ g
  have e : (D.comap φ).chi (MonoidAlgebra.single h 1) = D.chi (MonoidAlgebra.single (φ h) 1) := by
    change D.D A[X] (MonoidAlgebra.mapDomainRingHom A[X] φ _) = D.D A[X] _
    congr 1
    rw [map_sub]
    simp
  unfold W.GDet.lam
  rw [← e, hD, (AlgebraTools.Det.repApi _).2.1, (AlgebraTools.Det.repApi _).2.1]
  rfl
private theorem adL_triv {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : W.Resid V.frame c.O n} {B : W.UniversalOrdinaryDeterminantRing r}
    {ι : Qbar l ≃+* ℂ} {x : B.Pt} {ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)} (H : _root_.UpperTheory.V.Th.AutomorphicPointLocallyGeneric ι x ρ) :
    ∀ u, ∀ g ∈ r.Ip u, ρ g = 1 :=
  (Ws.Eb.relKill B x ρ ((AlgebraTools.Det.irrIffSpan (W.mat ρ)).1 fun N hN => H.irr N fun g _ v hv => hN g v hv)
    (adL_desc x.D V.pr (adL_pr V) ρ H.rep)).2
theorem UpperTheory.V.Th.adjointLiftingTheorem_of_locPrints_of_core :
    Loc.LocalPublishedTheorems → _root_.UpperTheory.V.Th.DenseThresholdMainCase → _root_.UpperTheory.V.Th.AdjointLiftingTheorem := by
  intro hP hC l _ L Ω _ _ _ _ _ _ s V hS hζ c hL n hn hn' r hr B ι x ρ H hpar P R hform hR z hz hb
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  have hz' : (fun g => z (toGS Ω V.S' g)) ∈ Z1 (R.comp (toGS Ω V.S') :
      Representation (Qbar l) (G (W.Lp L) Ω) (Matrix (Fin n) (Fin n) (Qbar l))) :=
    ⟨hz.1.comp (continuous_toGS Ω _), fun g h => (congrArg z (map_mul _ g h)).trans (hz.2 _ _)⟩
  have he : V.frame.eps c.O (Qbar l) = V.frame.eps ℤ_[l] (Qbar l) := by
    unfold W.GFrame.eps
    rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  refine hC l L Ω s V hS hζ c hL n hn hn' r hr B ι x ρ H P R (fun g => he ▸ hform g) hR z hz ⟨fun u g hg => ?_, fun v => ?_⟩
  · obtain ⟨X, hX⟩ := adL_away _ _ hz' hb u.1 (s.St_l u.1 u.2) (s.A u.1) (s.hA u.1)
    have h1 := adL_triv H u g hg
    obtain ⟨g', hg', rfl⟩ := hg.1
    have h2 := hX (W.resP L Ω g') hg'
    have h3 : ∀ g : V.frame.G₀, ρ g = 1 → Loc.adGL ρ g X = X := fun g h => by simp [Loc.adGL, h]
    exact h2.trans (sub_eq_zero.2 ((hR.ad (V.pr g') X).trans (h3 _ h1)))
  · obtain ⟨j, hj⟩ := (Loc.decEmb (F := W.Lp L) (Ω := Ω) (v := l)).1 (s.A v.1) v.1 (s.hA v.1) v.2
    have key : ∃ φ : ↥(Dec (F := L) (s.A v.1)) →* Formalism.BasicNotions.Loc.GQ l, Topology.IsOpenEmbedding φ ∧
        (∀ g y, φ g (j y) = j ((g : G L Ω) y)) ∧ (∀ g, φ g ∈ Loc.Iq l ↔ (g : G L Ω) ∈ Ine (F := L) (s.A v.1)) ∧
        (∀ g, Loc.cyc l l (φ g) = cycZ L Ω l (g : G L Ω)) := by
      rw [← hj]
      obtain ⟨φ, a, b, -, c, d, -⟩ := ((Loc.decEmb (F := L) (Ω := Ω) (v := l)).2 j).2
      exact ⟨φ, a, b, c, d l⟩
    obtain ⟨φ, a, b, hi, d⟩ := key
    have d' : ∀ g, Loc.cycA l l (Qbar l) (φ g) = cycBar L Ω l (g : G L Ω) := fun g => congrArg (Units.map _) (d g)
    have h3 := adL_above (F := W.Lp L) j φ ((W.resP L Ω).comp (Dec (F := L) (s.A v.1)).subtype) a
      (W.continuous_resP.comp continuous_subtype_val) b _ _ hz' hb
    have e : ((R.comp (toGS Ω V.S')).comp ((W.resP L Ω).comp (Dec (F := L) (s.A v.1)).subtype) :
        Representation (Qbar l) (Dec (F := L) (s.A v.1)) (Matrix (Fin n) (Fin n) (Qbar l))) =
        Loc.adGL (ρ.comp (V.frame.φ v)) :=
      MonoidHom.ext fun g => LinearMap.ext fun X => hR.ad (V.frame.φ v g) X
    rw [e] at h3
    obtain ⟨m, k, hm, hk, hψ⟩ := hpar v
    obtain ⟨g₀, hg₀, hf⟩ := H.free v
    have hI : V.frame.Iv v = (Loc.Iq l).comap φ := Subgroup.ext fun g => (hi g).symm
    rw [hI]
    haveI : CompactSpace (Dec (F := L) (s.A v.1)) := V.frame.cv v
    refine bkOrd hP l (Dec (F := L) (s.A v.1)) φ a n _ _ m k (H.cont.comp (V.frame.φ_cont v)) (H.flag v) hm hk
      (fun i i' g hg => ?_) ⟨g₀, ?_, hf⟩ _ h3
    · rw [d']
      exact hψ i i' g ((hi g).1 hg)
    · have h4 : cycZ (W.Lp L) Ω l (W.resP L Ω g₀.1) = 1 := by
        rw [← V.hε]
        exact hg₀
      have h5 : Loc.cyc l l (φ g₀) = 1 := (d g₀).trans h4
      exact (congrArg (Units.map _) h5).trans (map_one _)
end
end
