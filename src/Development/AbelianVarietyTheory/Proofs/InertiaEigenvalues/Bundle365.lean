module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Formalism.LocalToGlobal.Divisibility.RowSideTie
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Mathlib.RepresentationTheory.Coinduced
public import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.NotAdmissibleWithAmbientTop
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle177
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.Bundle001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle013
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.MemTypeSubspaceIffUnipotentCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLatInOfIndexLe
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle345
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle346
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.MvPolynomial.Ideal
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
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Formalism.LocalRingCardinality.Bundle003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod

@[expose] public section

section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin Formalism.DivisionValues

noncomputable section

namespace GlobalTheory.EtaJoin

section Gen

variable {K : Type} [Field K] [StarRing K] {n d : ℕ}

theorem hform_eq_dot (H : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    hform H x y = star x ⬝ᵥ H.mulVec y := by
  simp only [hform, Matrix.toLinearMapₛₗ₂'_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, RingHom.id_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [starRingEnd_apply, Pi.star_apply]; ring

theorem hform_orthProj (H : Matrix (Fin n) (Fin n) K) (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K)
    (h : IsOrthProj H E Pr) (u : Fin d → K) (x : Fin n → K) :
    hform H (E.mulVec u) (x - E.mulVec (Pr.mulVec x)) = 0 := by
  have e : x - E.mulVec (Pr.mulVec x) = (1 - E * Pr).mulVec x := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec]
  rw [hform_eq_dot, e, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    h.2, Matrix.zero_mulVec, dotProduct_zero]

variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (σ : K →+* ℂ) (J : (Fin n → K) →ₛₗ[σ] W)

theorem semi_expand (y : Fin n → K) : J y = ∑ i, σ (y i) • J (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single y]

  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (Pi.single i (y i) : Fin n → K) = y i • Pi.single i 1 := by
    ext k; by_cases hk : k = i
    · subst hk; simp
    · simp [Pi.single_apply, hk]
  rw [this, LinearMap.map_smulₛₗ]

theorem semi_injective (hli : LinearIndependent ℂ fun i => J (Pi.single i 1)) : Function.Injective J := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro y hy
  rw [semi_expand σ J y] at hy
  have h0 := (Fintype.linearIndependent_iff.1 hli) (fun i => σ (y i)) hy
  funext i
  exact σ.injective (by rw [h0 i]; simp)

theorem semi_mulVec_mem (E : Matrix (Fin n) (Fin d) K) (c : Fin d → K) :
    J (E.mulVec c) ∈ Submodule.span ℂ (Set.range fun k => J (E.mulVec (Pi.single k 1))) := by
  have e : E.mulVec c = ∑ k, c k • E.mulVec (Pi.single k 1) := by
    conv_lhs => rw [← Finset.univ_sum_single c]
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Matrix.mulVec_smul]
    congr 1
    ext a; by_cases ha : a = k
    · subst ha; simp
    · simp [Pi.single_apply, ha]

  rw [e, map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [LinearMap.map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

end Gen

end GlobalTheory.EtaJoin

namespace GlobalTheory.EtaJoin

section Gen2

variable {K : Type} [Field K] [NumberField K] [StarRing K] {n d : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {σ : K →+* ℂ} {V : Type} [AddCommGroup V] [Module K V]

theorem tied_orthProj (e : (Fin n → K) ≃ₗ[K] V) (jV : V →ₛₗ[σ] W) (H Eop : Matrix (Fin n) (Fin n) K) (op : W →ₗ[ℂ] W)
    (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K) (hP : IsOrthProj H E Pr)
    (hF : FormsTie σ (jV.comp e.toLinearMap) H Eop op) (Z : Submodule ℂ W)
    (hZ : Z = Submodule.span ℂ (Set.range fun k => jV (e (E.mulVec (Pi.single k 1))))) :
    Function.Injective (e.toLinearMap ∘ₗ E.mulVecLin) ∧ Z.comap jV = LinearMap.range (e.toLinearMap ∘ₗ E.mulVecLin) ∧
      ∀ x, e x - (e.toLinearMap ∘ₗ E.mulVecLin) (Pr.mulVec x) ∈ (Zᗮ).comap jV := by
  have hin : ∀ x y, inner ℂ (jV (e x)) (jV (e y)) = σ (hform H x y) := hF.inner
  have hJinj : Function.Injective fun x => jV (e x) := fun a b h => semi_injective σ (jV.comp e.toLinearMap) hF.li h
  have hgen : ∀ c, jV (e (E.mulVec c)) ∈ Z := by
    intro c; rw [hZ]; exact semi_mulVec_mem σ (jV.comp e.toLinearMap) E c
  have horth : ∀ x, jV (e (x - E.mulVec (Pr.mulVec x))) ∈ Zᗮ := by
    intro x
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [hZ] at hu
    induction hu using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨k, rfl⟩ := hv
      show inner ℂ (jV (e (E.mulVec (Pi.single k 1)))) _ = 0
      rw [hin, hform_orthProj _ _ _ hP, map_zero]
    | zero => exact inner_zero_left _
    | add a b _ _ ha hb => rw [inner_add_left, ha, hb, add_zero]
    | smul c a _ ha => rw [inner_smul_left, ha, mul_zero]
  have hEinj : Function.Injective E.mulVec := by
    intro a b hab
    have := congrArg Pr.mulVec hab
    simp only [Matrix.mulVec_mulVec, hP.1, Matrix.one_mulVec] at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · exact e.injective.comp hEinj
  · ext y
    constructor
    · intro hy
      rw [Submodule.mem_comap] at hy
      obtain ⟨x, rfl⟩ := e.surjective y
      have hw1 : jV (e (x - E.mulVec (Pr.mulVec x))) ∈ Z := by
        rw [map_sub, map_sub]; exact Submodule.sub_mem _ hy (hgen _)
      have hw0 : jV (e (x - E.mulVec (Pr.mulVec x))) = 0 :=
        inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 (horth x) _ hw1)
      have hw : x = E.mulVec (Pr.mulVec x) := by
        refine sub_eq_zero.1 (hJinj ?_)
        simp only [map_zero]; exact hw0
      exact ⟨Pr.mulVec x, by simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, LinearEquiv.coe_coe]; rw [← hw]⟩
    · rintro ⟨c, rfl⟩
      exact hgen c
  · intro x
    rw [Submodule.mem_comap]
    have e1 : e x - (e.toLinearMap ∘ₗ E.mulVecLin) (Pr.mulVec x) = e (x - E.mulVec (Pr.mulVec x)) := by
      simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, LinearEquiv.coe_coe, map_sub]
    rw [e1]; exact horth x

end Gen2

theorem concreteProj_orth : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin m) (t : T), (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (s : ℕ), A.fam.Ok s → ∀ (i : Fin m) (t : T), FormsTie D.what₂.embLL ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lH D A P ψ i t) (lE D A P ψ i t) (D.what₂.eMt (tup t) ((i : ℕ) + 1)) → Idx.Z0 D (tup t) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => (D.what₂.jMt (tup t) ((i : ℕ) + 1)) (eMt i t ((lZ0 D A P ψ Zs i t).mulVec (Pi.single k 1)))) → Function.Injective ((eMt i t).toLinearMap ∘ₗ (lZ0 D A P ψ Zs i t).mulVecLin) ∧ ratSub D (tup t) ((i : ℕ) + 1) (Idx.Z0 D (tup t) ((i : ℕ) + 1)) = LinearMap.range ((eMt i t).toLinearMap ∘ₗ (lZ0 D A P ψ Zs i t).mulVecLin) ∧ ∀ x, eMt i t x - ((eMt i t).toLinearMap ∘ₗ (lZ0 D A P ψ Zs i t).mulVecLin) ((lPrj D A P ψ Zs i t).mulVec x) ∈ ratSub D (tup t) ((i : ℕ) + 1) (Idx.Z0 D (tup t) ((i : ℕ) + 1))ᗮ := by
  intro D G _ _ Pl0 T m A P ψ Zs tup eMt s hOk i t hF hZ
  have hB : BlockHyp (A.fam.L i t) (A.fam.lvlA P ψ) A.fam.v0 s := ⟨hOk.conj, fun χ hχ => hOk.irr χ hχ, hOk.lifts i t⟩
  have hP : IsOrthProj (lH D A P ψ i t) (lZ0 D A P ψ Zs i t) (lPrj D A P ψ Zs i t) :=
    BlockDat.lf_l_proj (Z := Zs.Zl i t) hB
  exact tied_orthProj (eMt i t) (D.what₂.jMt (tup t) ((i : ℕ) + 1)) _ _ _ _ _ hP hF _ hZ

end GlobalTheory.EtaJoin
end
end

section

noncomputable section

namespace GlobalTheory.GoodTypes

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.MainNotions.PrimeDegreeVariant
open scoped Classical

section Local

variable {g : ℕ} [Fact g.Prime] {n : ℕ} {G V U : Type} [Group G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup U] [Module ℂ U]

def ConjIn (ρ : Representation ℂ G V) (W : Submodule ℂ V) (j : Gn g n →* G)
    (π : Representation ℂ (GL (Fin n) ℚ_[g]) U) : Prop :=
  ∀ y ∈ W, y ≠ 0 → ∃ Λ : V →ₛₗ[starRingEnd ℂ] U, Λ y ≠ 0 ∧
    ∀ z ∈ W, Λ z ∈ fixK1 π ∧ ∀ h, Λ (ρ (j h) z) = π (lift g n h) (Λ z)

theorem ConjIn.act_ne {ρ : Representation ℂ G V} {W : Submodule ℂ V} {j : Gn g n →* G}
    {π : Representation ℂ (GL (Fin n) ℚ_[g]) U} (h : ConjIn ρ W j π) (a a' : MonoidAlgebra ℂ (Gn g n))
    (ha : ∀ x, starRingEnd ℂ (a.coeff x) = a'.coeff x) {y : V} (hy : y ∈ W) (h0 : y ≠ 0)
    (hfix : ∑ x, a.coeff x • ρ (j x) y = y) : ∃ u ∈ fixK1 π, actK π a' u ≠ 0 := by
  obtain ⟨Λ, h1, h2⟩ := h y hy h0
  refine ⟨Λ y, (h2 y hy).1, ?_⟩
  have : actK π a' (Λ y) = Λ y := by
    conv_rhs => rw [← hfix]

    rw [map_sum, actK, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [LinearMap.smul_apply, map_smulₛₗ, ha, (h2 y hy).2]
  rwa [this]

theorem eq_of_teich (τ : Formalism.CyclotomicNorms.Fbar g →* ℂ) (hτ : Function.Injective τ) {f f' : (ZMod g)[X]} (hf : f.Monic)
    (hf' : f'.Monic) (h : ((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (τ x)).prod =
      ((Formalism.CyclotomicNorms.rootsBar f').map fun x => X - C (τ x)).prod) : f = f' := by
  have h3 := congrArg Polynomial.roots h
  have e : ∀ m : Multiset (Formalism.CyclotomicNorms.Fbar g), ((m.map fun x => X - C (τ x)).prod).roots = m.map τ := fun m => by
    rw [← roots_multiset_prod_X_sub_C (m.map τ), Multiset.map_map]; rfl
  rw [e, e] at h3
  apply Polynomial.map_injective (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)) (RingHom.injective _)
  rw [(IsAlgClosed.splits _).eq_prod_roots_of_monic (hf.map _),
    (IsAlgClosed.splits (f'.map _)).eq_prod_roots_of_monic (hf'.map _)]
  exact congrArg (fun m => (Multiset.map (fun x => X - C x) m).prod) (Multiset.map_injective hτ h3)

end Local

local instance factPrime (D : D7) (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

local instance neZeroPrime (D : D7) (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩

def facHom (D : D7) (k : Fin 2) (v : D.nd.PlG k) : Gn (D.host.g k) D.R.r →* G0g D.nd :=
  MonoidHom.mulSingle (fun kv : (Σ k : Fin 2, D.nd.PlG k) => GL (Fin D.R.r) (ZMod (D.host.g kv.1))) ⟨k, v⟩

abbrev LocRep (D : D7) (k : Fin 2) : Type 1 := Rep.{0} ℂ (GL (Fin D.R.r) ℚ_[D.host.g k])

abbrev Comp (D : D7) : Type 1 := D.what₂.FT → ∀ k : Fin 2, D.nd.PlG k → LocRep D k

def SeriesConj (D : D7) : Prop :=
  ∀ (k : Fin 2) (f : (ZMod (D.host.g k))[X]), IsLabel D k f →
    (D.ntypes.eSer k f).coeff.mapRange (starRingAut : ℂ ≃+* ℂ) (map_zero _) =
      (D.ntypes.eSer k (labAct D starRingAut k f)).coeff

theorem labAct_conj (D : D7) (k : Fin 2) {f : (ZMod (D.host.g k))[X]} (hf : IsLabel D k f) :
    labAct D starRingAut k f = dualLab D k f := by
  obtain ⟨h1, h2⟩ := GlobalTheory.Compare.TeichmullerRoots.dual_spec hf.1 hf.2.2
  refine GlobalTheory.Compare.TeichmullerRoots.labAct_eq D k _ (-1) (fun ζ hζ => ?_) hf h1 h2
  have hn : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζ
    (GlobalTheory.IndefiniteRowSideFullHecke.FactorSeriesSupport.rootExp_ne_zero D.R.r _ (D.host.g_prime k).two_le)
  rw [zpow_neg_one, Complex.inv_eq_conj hn]
  rfl

theorem act_atPlace (D : D7) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (G0g D.nd) V)
    (k : Fin 2) (v : D.nd.PlG k) (a : MonoidAlgebra ℂ (Gn (D.host.g k) D.R.r)) (y : V) :
    ρ.asAlgebraHom (atPlace D k v a) y = ∑ x, a.coeff x • ρ (facHom D k v x) y := by
  rw [GlobalTheory.SeriesSupportTest.atPlace_eq]
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb, add_smul, Finset.sum_add_distrib]
  | single h c =>
    have : GlobalTheory.SeriesSupportTest.plHom D k v (MonoidAlgebra.single h c) =
        MonoidAlgebra.single (facHom D k v h) c := MonoidAlgebra.mapDomain_single
    rw [this, Representation.asAlgebraHom_single]
    simp [Finsupp.single_apply]

theorem exists_good (D : D7) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (G0g D.nd) V) {x : V}
    (hx : x ≠ 0) (he : ρ.asAlgebraHom D.ntypes.e0 x = x) :
    ∃ (t : Tup2 D) (a : MonoidAlgebra ℂ (G0g D.nd)), D.ntypes.goodTuple t ∧ ρ.asAlgebraHom a x ≠ 0 ∧
      ∀ k v, ρ.asAlgebraHom (atPlace D k v (D.ntypes.eSer k (t k v))) (ρ.asAlgebraHom a x) = ρ.asAlgebraHom a x := by

  rw [Ten.e0_eq, Ten.eGood, map_sum, LinearMap.sum_apply] at he
  obtain ⟨p, -, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero (he.trans_ne hx)
  by_cases hg : Ten.goodVec D p
  · rw [if_pos hg] at hp
    refine ⟨_, _, hg, hp, fun k v => ?_⟩
    rw [← Module.End.mul_apply, ← map_mul,
      ← Subalgebra.mem_center_iff.1 (GlobalTheory.SeriesSupportTest.atPlace_central D k v _ (D.ntypes.eSer_central k _)),
      Ten.atPlace_eq, Ten.tens_mul_plc]
    congr 3
    exact Function.update_eq_self_iff.2 (D.ntypes.eSer_idem _ _)
  · rw [if_neg hg] at hp
    simp at hp

variable {D : D7} {X : BaseLevelRowSide D}

end GlobalTheory.GoodTypes
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo

namespace GlobalTheory.StepTwo.LowCoeff

def genChar {T ι : Type} [CommMonoid T] [Fintype ι] (n : ℕ) [NeZero n] (u : ι → T) (hu : ∀ q, u q ^ n = 1) :
    Multiplicative (ι → ZMod n) →* T where
  toFun g := ∏ q, u q ^ (g.toAdd q).val
  map_one' := by simp
  map_mul' g h := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [toAdd_mul, Pi.add_apply, ZMod.val_add, ← pow_eq_pow_mod _ (hu q), pow_add]

open Classical in
theorem genChar_single {T ι : Type} [CommMonoid T] [Fintype ι] (n : ℕ) [NeZero n] [Fact (1 < n)] (u : ι → T)
    (hu : ∀ q, u q ^ n = 1) (q : ι) : genChar n u hu (Multiplicative.ofAdd (Pi.single q 1)) = u q := by
  change ∏ p, u p ^ ((Pi.single q (1 : ZMod n) : ι → ZMod n) p).val = u q
  rw [Finset.prod_eq_single q]
  · simp [ZMod.val_one]
  · intro p _ hp
    simp [Pi.single_eq_of_ne hp]
  · simp

theorem coeff_mem_of_toLam_mem : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] (I : Ideal (X.O0 i)), 0 < nu X i → nu X i + 1 ≤ M → (X.l i : X.O0 i) ^ (nu X i + 1) ∈ I → ∀ F : MvPolynomial ι (X.O0 i), toLam X i M ι F ∈ I.map (algebraMap (X.O0 i) (abelian₂ X i M ι)) → ∀ m : ι →₀ ℕ, m.degree < X.l i ^ (M - nu X i - 1) → F.coeff m ∈ I := by
  intro D N X i M ι _ I _ hM h4 F hF m hm
  classical
  have hp : (X.l i).Prime := (X.lPrime i).out
  let J : Ideal (MvPolynomial ι (X.O0 i)) :=
    I.map (MvPolynomial.C : X.O0 i →+* MvPolynomial ι (X.O0 i)) ⊔ MvPolynomial.idealOfVars ι (X.O0 i) ^ (X.l i ^ (M - nu X i - 1))
  let π : MvPolynomial ι (X.O0 i) →ₐ[X.O0 i] (MvPolynomial ι (X.O0 i) ⧸ J) := Ideal.Quotient.mkₐ (X.O0 i) J
  have hI : ∀ a ∈ I, algebraMap (X.O0 i) (MvPolynomial ι (X.O0 i) ⧸ J) a = 0 := by
    intro a ha
    rw [← π.commutes]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha))
  have h4' : ((X.l i : ℕ) : MvPolynomial ι (X.O0 i) ⧸ J) ^ (nu X i + 1) = 0 := by
    have := hI _ h4
    rwa [map_pow, map_natCast] at this
  have h1 : 1 < X.l i ^ M := Nat.one_lt_pow (by omega) hp.one_lt
  haveI : Fact (1 < X.l i ^ M) := ⟨h1⟩
  haveI : NeZero (X.l i ^ M) := ⟨by omega⟩
  have hu : ∀ q, (1 + π (MvPolynomial.X q)) ^ (X.l i ^ M) = 1 := by
    intro q
    refine KStar.Tree.one_add_pow_prime_pow_eq_one hp h4' hM ?_
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.mem_sup_right (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self q)) _))
  let L := MonoidAlgebra.lift (X.O0 i) (MvPolynomial ι (X.O0 i) ⧸ J) (Del X i M ι)
    (genChar (X.l i ^ M) (fun q => 1 + π (MvPolynomial.X q)) hu)
  have hc : L.comp (toLam X i M ι) = π := by
    refine MvPolynomial.algHom_ext fun q => ?_
    rw [AlgHom.comp_apply, toLam, MvPolynomial.aeval_X, map_sub, map_one, MonoidAlgebra.lift_of]
    have := genChar_single (X.l i ^ M) (fun q => 1 + π (MvPolynomial.X q)) hu q
    rw [sub_eq_iff_eq_add']
    convert this
  have hker : I.map (algebraMap (X.O0 i) (abelian₂ X i M ι)) ≤ RingHom.ker L := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, L.commutes]
    exact hI a ha
  have hFJ : F ∈ J := by
    have h0 : L (toLam X i M ι F) = 0 := hker hF
    have : π F = 0 := by rw [← hc]; exact h0
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hFJ
  have hb0 : b.coeff m = 0 := (MvPolynomial.mem_pow_idealOfVars_iff' _ b).1 hb m hm
  rw [MvPolynomial.coeff_add, hb0, add_zero]
  exact MvPolynomial.mem_map_C_iff.1 ha m

end GlobalTheory.StepTwo.LowCoeff

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen Formalism.MainNotions.IntegralHeckeForms
open scoped TensorProduct

namespace GlobalTheory.ExportFromInputs

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

open GlobalTheory.TwistInputsTest GlobalTheory.TwAll

theorem twistModule_all_character_powers_of_admissible (bkP : BKPh X) (E : ExpDat Y) (N0 : X.Tw → ℕ) (h2 : TwAll.admissibleIndexBoundAllPowers Y bkP N0) (h3 : IsotypicPartsInternalDirectSum Y E)
    (h5 : GroupAlgebraIntegrality Y) (h7 : admT4 Y E) (h10 : TwistedSeriesSpecialisation Y) (h11 : GoodLatticePoints Y) (i : X.Tw) (hi : X.NonzeroIndexPlace i) :
    TwAll.goodTwistExistsAllCoprimePowers Y bkP E N0 i := by
  classical
  intro hs eps' he hF S hS A
  choose z hz using fun b => (h5 i hi b).1
  have hAB := fun j hj b => abHyp_fam Y E i hi j hj b z (hz b) S h3 h5 h11 (hF j hj b) (hS j hj b)
  obtain ⟨Q, k, ψ₀, hall⟩ := h2 i hi hs eps' he (fam Y i z S) hAB (levs Y i S ∪ A)
  refine ⟨Q, k, ψ₀, fun n hn => ?_⟩
  have hn' := hall n hn
  generalize ψ₀ ^ n = ψ' at hn' ⊢
  obtain ⟨hok, ha, hc, hd, M, χ, hχ, epsB, h0, hsum, H⟩ := hn'
  have key : ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, _ := fun j hj b => by
    obtain ⟨htw, hu, hdis⟩ := twOK_of_psiOk i _ Q k ψ' hok b
    refine export_at Y E i hi j hj b (S j b) h3 h7 (hF j hj b) (hS j hj b) k Q _ htw hu (epsB j b) ?_
    intro T hT hle
    obtain ⟨-, hfg, hsp, -⟩ := h3 i hi j hj b
    have hA : (fam Y i z S).A j b = AO Y i j b := zO_eq Y i j b _ (hz b)
    have hTh : (fam Y i z S).Th j b = (Th Y i j b (SgJ Y E i j b)).map (AO Y i j b) := by
      rw [← (hS j hj b).2.2, RFam.Th, hA]; rfl
    rw [← hTh]
    refine H j hj b T ?_ fun a ha => ?_
    · have : Submodule.span (FractionRing (X.O i)) ((fam Y i z S).B j b : Set (Y.Fm i j b)) = V0 Y i j b :=
        span_of_isLatIn (isLatIn_B Y i j b hfg hsp)
      rw [this]; exact hT
    · have ha' : a ∈ S j b := ha
      rw [hχ, psiAt_comp] at htw hle
      have hlev : Disjoint Q (Y.lev i j b a) := by
        refine hdis.mono_right (le_trans ?_ Finset.subset_union_left)
        intro v hv
        simp only [levs, Finset.mem_biUnion]
        exact ⟨j, hj, b, Finset.mem_univ _, a, ha', hv⟩
      rw [hA]
      refine hle ⟨_, ?_, rfl⟩
      refine Submodule.span_mono ?_ (h10 i hi j hj b k Q M _ htw a hlev)
      exact Set.biUnion_subset_biUnion_left (Set.singleton_subset_iff.2 ((hS j hj b).1 ha'))
  exact ⟨hok, ⟨epsB, h0, hsum, fun j hj b => (key j hj b).1⟩, fun j hj b => (key j hj b).2, ha, hc, hd⟩

end GlobalTheory.ExportFromInputs


end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

theorem _root_.GlobalTheory.T.lam_conductor_exponent : ∀ (D : D7) (Z : LamDat D), Z.Ok → ∀ (l : ℕ) (j a : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)), ExpAt (Z.lam0 l j a) w (expIn (cond0 D.host Z.w0) (below w)) := by
  first | exact @GlobalTheory.LamTie.lam0_expAt | exact GlobalTheory.LamTie.lam0_expAt | (intros; apply GlobalTheory.LamTie.lam0_expAt <;> assumption)
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.Models

theorem model_sen_mem : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A : Ob k G) (N : Lats k n A.m), M.Model A N → ∀ i x, sen ((F.D A).γ i) (N i) x ≠ 0 → ∃ u ∈ Dt.Ut i, ((u - Dt.w i : ℤ) : k) = x := by
  intro k G _ _ l n _ _ _ R F r Dt M A N hN i x hx
  obtain ⟨B, Nb, A₁, j, p, hB, hj, hji, hp, hps, rfl⟩ := hN
  have hle := GlobalTheory.T.senMultiplicity_subquotient_lattice_le F B A₁ A j p Dt.w Dt.wst Nb (M.base_obj B Nb hB) hj hji hp hps
    (M.base_abc B Nb hB) i x
  obtain ⟨μ, -, hs⟩ := M.base_sen B Nb hB
  rw [hs i x] at hle
  have h0 : resCount (Dt.Ut i) (Dt.w i) x ≠ 0 := by
    intro h
    rw [h] at hle
    apply hx
    simpa using hle
  unfold resCount at h0
  obtain ⟨u, hu⟩ := Multiset.card_pos_iff_exists_mem.1 (Nat.pos_of_ne_zero h0)
  classical
  rw [Multiset.mem_filter] at hu
  exact ⟨u, hu.1, hu.2⟩

end GlobalTheory.Models
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.exists_simple_pieces_sen_sum : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (B : Ob k G) (N : Lats k n B.m), M.Model B N → ∃ (s : ℕ) (C : Fin s → Ob k G) (L : ∀ a, Lats k n (C a).m), (∀ a, M.Model (C a) (L a)) ∧ (∀ a, IsSimpleModule (MonoidAlgebra k G) (C a).ρ.asModule) ∧ SameSS B.ρ (piRep fun a => (C a).ρ) ∧ ∀ i x, sen ((F.D B).γ i) (N i) x = ∑ a, sen ((F.D (C a)).γ i) (L a i) x := by
  first | exact @GlobalTheory.Models.ModTh.exists_simple_pieces | exact GlobalTheory.Models.ModTh.exists_simple_pieces | (intros; apply GlobalTheory.Models.ModTh.exists_simple_pieces <;> assumption)
end
