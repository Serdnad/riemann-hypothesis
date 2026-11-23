module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsInvariantLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle314
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle783
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeylConjugateOfUnitarySatakeDiagDoubleCosets
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle006
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeC
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle234
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle255
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle308
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle040
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle313
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle265
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle315
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010

@[expose] public section

section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory.ThEx

theorem T_mem_Gamma1 (M : ℕ) : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 M := by
  rw [CongruenceSubgroup.Gamma1_mem]
  simp [ModularGroup.T]

theorem of_lift (hlift : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ l ∣ N → 1 ≤ N → ∀ (n w : ℕ), Odd w → ∀ b : X.Fn l, b ∈ X.B N l w → ∃ f : X.Kˣ, Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) (f : X.K) ∧ AdicCompletion.eval (idl l) (X.Kl l) n (b ![1, 0]) = X.cls l n f ∧ (∀ δ ∈ CongruenceSubgroup.Gamma1 N, -δ ∈ CongruenceSubgroup.Gamma (l ^ n) → ∃ g : X.K, Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g ∧ (f : X.K) * X.sl (ofSL δ) f = g ^ (l ^ n))) : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime], Algebra.IsAlgebraic ℚ Ω → (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → l ≠ 2 → ¬ l ∣ N → 1 ≤ N → ((l : Ω) ∈ A.nonunits) → ∀ (n w : ℕ), Odd w → ∀ b : X.Fn l, b ∈ X.B N l w → ∃ φ : HahnSeries ℚ Ω, IsThB X A N l n b φ ∧ IsLat 1 φ := by
  intro Ω _ _ _ ε X A N l _ halg han hl2 hlN hN hA n w hw b hb
  have : IsAlgClosure ℚ Ω := ⟨inferInstance, halg⟩
  obtain ⟨f, hfinv, hfcls, hfsq⟩ := hlift Ω ε X N l hl2 hlN hN n w hw b hb
  obtain ⟨ψ, hψan, hψd⟩ := han
  have hT : (f : X.K) ∈ GlobalTheory.Glue.KT X 1 := by
    rw [GlobalTheory.Glue.KT.mem_def, pow_one]
    exact hfinv _ (T_mem_Gamma1 _)
  obtain ⟨φ, hdl, hden⟩ := GlobalTheory.dl_exists ε X ⟨ψ, hψd, hψan⟩ l A hA n 1 (f : X.K) one_pos f.ne_zero hT
  refine ⟨φ, ⟨f, hfinv, hfcls, hfsq, by simpa using hdl⟩, fun r hr => ?_⟩
  simpa using hden r hr

theorem thex : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime], Algebra.IsAlgebraic ℚ Ω → (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → l ≠ 2 → ¬ l ∣ N → 5 ≤ N → ((l : Ω) ∈ A.nonunits) → ∀ (n w : ℕ), Odd w → ∀ b : X.Fn l, b ∈ X.B N l w → ∃ φ : HahnSeries ℚ Ω, IsThB X A N l n b φ ∧ IsLat 1 φ := by
  intro Ω _ _ _ ε X A N l _ halg han hl2 hlN hN hA n w hw b hb
  exact of_lift (GlobalTheory.ThLift.exists_invariant_lift) Ω ε X A N l halg han hl2 hlN (by omega) hA n w hw b hb

end GlobalTheory.ThEx
end

section

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

theorem _root_.GlobalTheory.T.commutative_hecke_acts_by_scalar_on_fixed_vectors : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (K : Subgroup G), IsCompact (K : Set G) → IsCommensurated K → (∀ f₁ ∈ Hecke ℂ K, ∀ f₂ ∈ Hecke ℂ K, conv K f₁ f₂ = conv K f₂ f₁) → GlobalTheory.LGrp.IsIrrSmooth π → FiniteDimensional ℂ (fixed π K) → ∀ h ∈ Hecke ℂ K, ∃ c : ℂ, ∀ x ∈ fixed π K, heckeVec π K h x = c • x := by
  first | exact @GlobalTheory.LFun.HeckeScalar.exists_scalar | exact GlobalTheory.LFun.HeckeScalar.exists_scalar | (intros; apply GlobalTheory.LFun.HeckeScalar.exists_scalar <;> assumption)
end

section

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

theorem _root_.GlobalTheory.T.isSubquotient_of_same_spherical_hecke_eigenvalues : ∀ (G V W : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G V) (ρ : Representation ℂ G W) (K : Subgroup G), IsCompact (K : Set G) → IsCommensurated K → GlobalTheory.LGrp.IsIrrSmooth π → IsSmooth ρ → ∀ x ∈ fixed π K, x ≠ 0 → ∀ y ∈ fixed ρ K, y ≠ 0 → (∀ h ∈ Hecke ℂ K, ∃ c : ℂ, heckeVec π K h x = c • x ∧ heckeVec ρ K h y = c • y) → GlobalTheory.LGrp.IsSubquot π ρ := by
  first | exact @GlobalTheory.LGrp.Zonal.isSubquot_of_hecke_eigenvalues | exact GlobalTheory.LGrp.Zonal.isSubquot_of_hecke_eigenvalues | (intros; apply GlobalTheory.LGrp.Zonal.isSubquot_of_hecke_eigenvalues <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.unitaryDoubleCosetClasses_finite_card_le : ∀ (D : D7) (N : ℕ), Finite (Cls D N (intG D N)) ∧ (Nat.card (Cls D N (intG D N)) : ℝ) ≤ (12 * (fF D : ℝ) ^ 2 * (N : ℝ) ^ 4 * D.host.rdE ^ 2) ^ (6 * fF D * N ^ 2) ∧ ∀ J : Subgroup (GA D N), J ≤ intG D N → J.relIndex (intG D N) ≠ 0 → Finite (Cls D N J) ∧ Nat.card (Cls D N J) ≤ Nat.card (Cls D N (intG D N)) * J.relIndex (intG D N) := by
  first | exact @GlobalTheory.NormSum.cls_finite_card_le | exact GlobalTheory.NormSum.cls_finite_card_le | (intros; apply GlobalTheory.NormSum.cls_finite_card_le <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.LFun.SplitTie

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.LFun.SplitChart
open Formalism.MainNotions.SchurIrreducible (IsSplit)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
  {n : ℕ} {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} {V : Type} [AddCommGroup V] [Module ℂ V]

section Transport

def glEquiv {A B : Type} [CommRing A] [CommRing B] (n : ℕ) (ψ : A ≃+* B) : GL (Fin n) A ≃* GL (Fin n) B :=
  Units.mapEquiv ψ.mapMatrix.toMulEquiv

variable {ψ : Fv F v ≃+* w.adicCompletion E}

theorem mem_KGL_iff (h3 : ∀ a, Valued.v (ψ a) = Valued.v a) (x : GL (Fin n) (Fv F v)) :
    x ∈ KGL v (n := n) ↔ glEquiv n ψ x ∈ KGL w (n := n) := (bc_mem_KGL_iff h3).symm

theorem Tj_comp (h3 : ∀ a, Valued.v (ψ a) = Valued.v a) (ϖ : Fv F v) (j : ℕ) :
    Tj ℂ n (Ov E w) (ψ ϖ) j ∘ glEquiv n ψ = Tj ℂ n (Ov F v) ϖ j := by
  have hd : diagJ n (ψ ϖ) j = ψ.mapMatrix (diagJ n ϖ j) := by
    rw [RingEquiv.mapMatrix_apply, diagJ, diagJ, Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    split_ifs <;> simp
  have hv : ∀ x : GL (Fin n) (Fv F v), (glEquiv n ψ x).1 = ψ.mapMatrix x.1 := fun _ => rfl
  refine (funext fun g => (Set.indicator_comp_right (g := 1) (glEquiv n ψ)).symm).trans (congrArg (Set.indicator · 1) ?_)
  ext g
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, (glEquiv n ψ).surjective.exists, ← mem_KGL_iff h3, hd, hv, ← map_mul,
    EmbeddingLike.apply_eq_iff_eq]

theorem isSatVecGL_comp_symm (h3 : ∀ a, Valued.v (ψ a) = Valued.v a) (hq : qV E w = qV F v)
    (ρ : Representation ℂ (GL (Fin n) (Fv F v)) V) (x : V) (B : Multiset ℂˣ) :
    IsSatVecGL w (ρ.comp (glEquiv n ψ).symm.toMonoidHom) x B ↔ IsSatVecGL v ρ x B := by
  unfold IsSatVecGL
  rw [mem_fixed_comp_symm (glEquiv n ψ) (mem_KGL_iff h3), hq, ψ.surjective.forall]
  refine and_congr_right fun _ => and_congr_right fun hx => and_congr_right fun _ => forall_congr' fun ϖ => ?_
  have hu : IsUnifV E w (ψ ϖ) ↔ IsUnifV F v ϖ := by unfold IsUnifV; rw [h3]
  rw [hu]
  refine forall_congr' fun hϖ => forall₂_congr fun j _ => ?_
  rw [heckeVec_comp_symm (glEquiv n ψ) (mem_KGL_iff h3) (Tj_mem_hecke (hu.2 hϖ) j).1 hx, Tj_comp h3]

end Transport

variable [Algebra F E] {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}

section Compl

variable (τ : E →ₐ[F] Fv F v) (hw : (splitPrime τ).under (𝓞 F) = v)

theorem complMap_bijective : Function.Bijective (complMap hw) := by
  obtain ⟨ψ, h1, -⟩ := exists_equiv_complMap τ hw
  exact (funext h1 : ⇑ψ = complMap hw) ▸ ψ.bijective

theorem valued_complMap (a : Fv F v) : Valued.v (complMap hw a) = Valued.v a := by
  obtain ⟨ψ, h1, -, h3, -⟩ := exists_equiv_complMap τ hw
  rw [← h1, h3]

theorem complMap_apply_emb (x : E) : complMap hw (τ x) = algebraMap E _ x := by
  obtain ⟨ψ, h1, h2, -⟩ := exists_equiv_complMap τ hw
  rw [← h1, h2]

def complEquiv : Fv F v ≃+* (splitPrime τ).adicCompletion E :=
  RingEquiv.ofBijective (complMap hw) (complMap_bijective τ hw)

theorem complEquiv_apply (a : Fv F v) : complEquiv τ hw a = complMap hw a := rfl

theorem toCompl_eq_complMap (y : Fv F v ⊗[F] E) : toCompl hw y = complMap hw (splitProj τ y) :=
  toCompl_eq (ψ := complEquiv τ hw) (fun _ => rfl) (complMap_apply_emb τ hw) y

theorem qV_splitPrime : qV E (splitPrime τ) = qV F v := absNorm_splitPrime τ

end Compl

variable (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : E →ₐ[F] Fv F v) (hw : (splitPrime τ).under (𝓞 F) = v)
  (β : GL (Fin n) (Fv F v))

variable {τ β}

variable (hL : IsSelfDualAt σ J L v) (hβ : IsSplitBasis τ L β)
include hL hβ

end GlobalTheory.LFun.SplitTie

end
end

section

noncomputable section

namespace GlobalTheory.LFun

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun.Orbit
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (WeylConjU bcParam bcParam_of_weylConj)

section Local

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n q : ℕ} {ϖ ϖ' : L}

theorem exists_dosetInd_eq (hU : IsUnramInv ϖ σ q) (hU' : IsUnramInv ϖ' σ q) {d : Fin n → ℤ} {t : GU σ n}
    (ht : t.1.1 = Matrix.diagonal fun i => ϖ ^ d i) :
    ∃ t' : GU σ n, t'.1.1 = Matrix.diagonal (fun i => ϖ' ^ d i) ∧ dosetInd ℂ (KU σ n) t' = dosetInd ℂ (KU σ n) t := by
  have h0 := GlobalTheory.InertThetaCompare.unif_ne_zero hU
  have h0' := GlobalTheory.InertThetaCompare.unif_ne_zero hU'
  have hv : ∀ a : ℤ, Valued.v (ϖ ^ a) = WithZero.exp (-a) := fun a => by
    simpa using GlobalTheory.InertThetaCompare.val_prod_zpow (ϖ := ϖ) hU.2.2.2.1 (Finset.univ : Finset Unit) fun _ => a
  have hd : ∀ i, d i + d i.rev = 0 := fun i => by
    have h1 := P.fSatake_unit_diag (P.fSatake_borel_of_diag ht) i
    rw [ht, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, map_zpow₀, hU.2.2.1, ← zpow_add₀ h0] at h1
    have h2 := hv (d i + d i.rev)
    rw [h1, map_one, eq_comm, WithZero.exp_eq_one] at h2
    omega
  obtain ⟨k, hk, hk'⟩ := P.fSatake_diag_exists (σ := σ) (fun i : Fin n => (ϖ' / ϖ) ^ d i) fun i => by
    rw [map_zpow₀, map_div₀, hU.2.2.1, hU'.2.2.1, ← zpow_add₀ (div_ne_zero h0' h0), hd, zpow_zero]
  have hK : k ∈ KU σ n := P.fSatake_diag_mem_K hk hk' fun i => by
    rw [map_zpow₀, map_div₀, hU.2.2.2.1, hU'.2.2.2.1, div_self WithZero.coe_ne_zero, one_zpow]
  refine ⟨t * k, ?_, ?_⟩
  · rw [Subgroup.coe_mul, Units.val_mul, ht, hk, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← mul_zpow, mul_div_cancel₀ _ h0]
  · rw [dosetInd, dosetInd, DoubleCoset.doubleCoset_eq_of_mem
      (DoubleCoset.mem_doubleCoset.2 ⟨1, one_mem _, k, hK, by rw [one_mul]⟩)]

variable [CompleteSpace L] {V : Type} [AddCommGroup V] [Module ℂ V] {α β : Fin (n / 2) → ℂˣ}

theorem satU_of_weylConj (hU : IsUnramInv ϖ σ q) {h : GU σ n → ℂ} (hh : h ∈ Hecke ℂ (KU σ n)) (e : WeylConjU α β) :
    SatU ϖ q h (fun i => (α i : ℂ)) = SatU ϖ q h (fun i => (β i : ℂ)) :=
  unitarySatakeTransform_weylConjugate_invariant GlobalTheory.T.unitarySatake_weylInvariant hU hh e

theorem weylConj_of_dosetInd (hU : IsUnramInv ϖ σ q)
    (h : ∀ (d : Fin n → ℤ) (t : GU σ n), Antitone d → t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) →
      SatU ϖ q (dosetInd ℂ (KU σ n) t) (fun i => (α i : ℂ)) = SatU ϖ q (dosetInd ℂ (KU σ n) t) fun i => (β i : ℂ)) :
    WeylConjU α β := weylConjugate_of_unitarySatake_diagDoubleCosets GlobalTheory.T.unitarySatake_weylInvariant hU h

theorem satU_eq_iff_weylConj (hU : IsUnramInv ϖ σ q) :
    (∀ h ∈ Hecke ℂ (KU σ n), SatU ϖ q h (fun i => (α i : ℂ)) = SatU ϖ q h fun i => (β i : ℂ)) ↔ WeylConjU α β :=
  ⟨fun h => weylConj_of_dosetInd hU fun _ _ _ _ => h _ (Final.DosetIndMem _ _ _ _),
    fun e _ hh => satU_of_weylConj hU hh e⟩

theorem bcParam_eq_of_satU_eq (hU : IsUnramInv ϖ σ q)
    (h : ∀ h ∈ Hecke ℂ (KU σ n), SatU ϖ q h (fun i => (α i : ℂ)) = SatU ϖ q h fun i => (β i : ℂ)) :
    bcParam n α = bcParam n β := bcParam_of_weylConj ((satU_eq_iff_weylConj hU).1 h)

variable {ρ : Representation ℂ (GU σ n) V} {x : V}

theorem IsSatVecU.unique (hU : IsUnramInv ϖ σ q) (h : IsSatVecU ϖ q ρ x α) (h' : IsSatVecU ϖ q ρ x β) :
    WeylConjU α β :=
  (satU_eq_iff_weylConj hU).1 fun t ht => smul_left_injective ℂ h.1 ((h.2.2 t ht).symm.trans (h'.2.2 t ht))

end Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Place

variable {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}

theorem toCompl_surjective (h : w.under (𝓞 F) = v) : Function.Surjective (toCompl h) := fun y => by
  obtain ⟨a, ha⟩ := (finAdEquiv F E).surjective (Neutral.B1.finiteSingle E w y)
  refine ⟨_, (finAdEquiv_apply h a).symm.trans ?_⟩
  rw [ha]
  classical exact Pi.mulSingle_eq_same (M := fun u : HeightOneSpectrum (𝓞 E) => u.adicCompletion E) w y

variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
  {V : Type} [AddCommGroup V] [Module ℂ V] {h : w.under (𝓞 F) = v}

theorem IsConjAt.unique {c c' : w.adicCompletion E →+* w.adicCompletion E} (hc : IsConjAt σ h c)
    (hc' : IsConjAt σ h c') : c = c' := RingHom.ext fun y => by
  obtain ⟨z, rfl⟩ := toCompl_surjective h y
  rw [hc, hc']

variable {ρ : Representation ℂ (GLoc σ J v) V} {x : V} {B B' : Multiset ℂˣ}

theorem IsParamVec.unique (hx : IsParamVec σ J L h ρ x B) (hx' : IsParamVec σ J L h ρ x B') : B = B' := by
  by_cases hv : IsSplit (E := E) v
  · exact hx.unique_of_isSplit hv hx'
  obtain ⟨-, c, ϖ, e, α, hU, he, hα, rfl⟩ := hx.resolve_left fun h => hv h.1
  obtain ⟨-, c', ϖ', e', β, hU', he', hβ, rfl⟩ := hx'.resolve_left fun h => hv h.1
  obtain rfl := he.1.unique he'.1
  exact bcParam_of_weylConj (((hα.of_chart he he').of_unif hU hU').unique hU' hβ)

theorem HasParam.unique (hρ : HasParam σ J L h ρ B) (hρ' : HasParam σ J L h ρ B') : B = B' := by
  obtain ⟨x, hx⟩ := hρ.exists_vec
  exact hx.unique (hρ'.isParamVec hx.mem_fixed hx.ne_zero)

theorem IsSysParam.unique {c : List ℤ → ℂ} (hc : IsSysParam σ n h c B) (hc' : IsSysParam σ n h c B') : B = B' := by
  rcases hc with ⟨hv, hB, hc⟩ | ⟨hw, τ, ϖ, α, hU, hτ, rfl, hc⟩ <;>
    rcases hc' with ⟨hv', hB', hc'⟩ | ⟨hw', τ', ϖ', β, hU', hτ', rfl, hc'⟩
  · exact eq_of_satEig_eq (qV_ne_zero w) hB hB' fun j hj => (hc j hj).symm.trans (hc' j hj)
  · exact absurd hv (not_isSplit_of_isInertAt hw')
  · exact absurd hv' (not_isSplit_of_isInertAt hw)
  · obtain rfl := hτ.unique hτ'
    refine bcParam_of_weylConj (weylConj_of_dosetInd hU fun d t hd ht => ?_)
    obtain ⟨t', ht', e⟩ := exists_dosetInd_eq hU hU' ht
    rw [← hc d t hd ht, hc' d t' hd ht', e, satU_indep hU hU' (Final.DosetIndMem _ _ _ _)]

end Place

section Global

variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
  {S : Set (HeightOneSpectrum (𝓞 F))} {V : Type} [AddCommGroup V] [Module ℂ V]
  {Vl : HeightOneSpectrum (𝓞 F) → Type} [∀ v, AddCommGroup (Vl v)] [∀ v, Module ℂ (Vl v)]
  {π : ∀ v, Representation ℂ (GLoc σ J v) (Vl v)} {c c' : Fam E} {w : HeightOneSpectrum (𝓞 E)}

theorem IsParamVecOff.unique {ρ : Representation ℂ (GAd σ J) V} {x : V} (h : IsParamVecOff σ J L S ρ x c)
    (h' : IsParamVecOff σ J L S ρ x c') (hw : w ∉ above E S) : c w = c' w :=
  (h _ hw w rfl).unique (h' _ hw w rfl)

theorem IsSysParamOff.unique {s : HeightOneSpectrum (𝓞 E) → List ℤ → ℂ} (h : IsSysParamOff σ n S s c)
    (h' : IsSysParamOff σ n S s c') (hw : w ∉ above E S) : c w = c' w :=
  (h _ hw w rfl).unique (h' _ hw w rfl)

theorem LSTw_congr (h : ∀ w ∉ above E S, c w = c' w) (m : HeightOneSpectrum (𝓞 E) → ℂˣ) (s : ℂ) :
    LSTw S c m s = LSTw S c' m s := eulerProd_congr (fun w hw => by rw [twist, twist, h w hw]) s

end Global

end GlobalTheory.LFun

end
end

section

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil.Model

theorem conjE_conjE (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [Formalism.HC.HostAx.conjE_apply, Formalism.HC.HostAx.conjE_apply]
  simp

theorem sgA_incE (D : D7) (x : D.host.E) : sgA D (inc D x) = inc D (D.host.conj x) := by
  simp [sgA, inc, Formalism.UG.sigR, Formalism.UG.inclE]

theorem wd_at_zero (D : D7) (T : Tor D) {a d : ℕ} (G : VC D a d → ℂ) : Wd D T 0 G = G := by
  funext z
  simp [Wd, wdPh, ee, qH, U, Hf]

theorem pt_zero (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} :
    pt D (tor0 D cc δ) δ (0 : Matrix (Fin N') (Fin N) D.host.E) = 0 := by
  funext τ i j
  simp [pt, embV, tor0]

theorem pt_nsmul (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (m : ℕ) (z : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (m • z) = m • pt D (tor0 D cc δ) δ z := by
  funext τ i j
  simp only [pt, embV, tor0, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast]
  ring

def incM (D : D7) (N N' : ℕ) : Matrix (Fin N') (Fin N) D.host.E →+ XA D N N' :=
  (inc D).toAddMonoidHom.mapMatrix

theorem incM_apply (D : D7) (N N' : ℕ) (z : Matrix (Fin N') (Fin N) D.host.E) : incM D N N' z = z.map (inc D) := rfl

theorem exists_div (D : D7) {N N' : ℕ} {m : ℕ} (hm : 0 < m) (z : Matrix (Fin N') (Fin N) D.host.E) (a : XA D N N')
    (h : z.map (inc D) = m • a) : ∃ z' : Matrix (Fin N') (Fin N) D.host.E, z = m • z' ∧ z'.map (inc D) = a := by
  have hm' : (m : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  refine ⟨Matrix.of fun i j => (m : D.host.E)⁻¹ * z i j, ?_, ?_⟩
  · ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul]
    field_simp
  · ext i j
    have h1 := congrFun (congrFun h i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, nsmul_eq_mul] at h1
    simp only [Matrix.map_apply, Matrix.of_apply, map_mul, h1]
    rw [← mul_assoc, ← map_natCast (inc D) m, ← map_mul, inv_mul_cancel₀ hm', map_one, one_mul]

theorem mul_nsmul_left {X : Type} [AddCommGroup X] (f : X → ℂ) (h0 : f 0 = 1) (h : ∀ x y, f (x + y) = f x * f y)
    (m : ℕ) (x : X) : f (m • x) = f x ^ m := by
  induction m with
  | zero => simp [h0]
  | succ n ih => rw [succ_nsmul, h, ih, pow_succ]

theorem exists_isModel (D : D7) (hD : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : Crv D cc δ) (N N' : ℕ) :
    ∃ w γ WA, GlobalTheory.FinWeil.IsModel D cc δ N N' w γ WA := by
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_finiteAdeleExtendedCharacter_of_curve D hD cc δ hc
  obtain ⟨w, hw, hwd⟩ := GlobalTheory.T.theta_point_additive_form D hD cc δ hc
  obtain ⟨hinv, halt, hadj, hl, hr⟩ := GlobalTheory.T.adelicHermitianCharacterPairing_properties D hD cc δ hc ψ hψ N N'
  have hsd := GlobalTheory.T.completedStandardAdelicLattice_selfDual D hD cc δ hc ψ hψ N N'
  obtain ⟨hrat, -, hdense, hden, -, -⟩ := GlobalTheory.T.completedStandardAdelicLattice_properties D hD cc δ hc N N'
  have htt := GlobalTheory.T.weilOperator_rationalTranslate_mem_thetaFunctions D hD cc δ hc N N'
  let W₀ : Matrix (Fin N') (Fin N) D.host.E → TTs D (tor0 D cc δ) N N' →ₗ[ℂ] TTs D (tor0 D cc δ) N N' := fun z =>
    { toFun := fun F => ⟨Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) F, htt z F F.2⟩
      map_add' := fun F G => Subtype.ext (wd_add _ _ _)
      map_smul' := fun c F => Subtype.ext (wd_smul _ _ _) }
  have hz1 : ∀ y : XA D N N', gamA ψ 0 y = 1 := fun y => by simp [gamA, hψ.2.1]
  have hz2 : ∀ y : XA D N N', gamA ψ y 0 = 1 := fun y => by simp [gamA, hψ.2.1]
  have hn1 : ∀ (m : ℕ) (x y : XA D N N'), gamA ψ (m • x) y = gamA ψ x y ^ m := fun m x y =>
    mul_nsmul_left (fun x => gamA ψ x y) (hz1 y) (fun a b => hl a b y) m x
  have hn2 : ∀ (m : ℕ) (x y : XA D N N'), gamA ψ x (m • y) = gamA ψ x y ^ m := fun m x y =>
    mul_nsmul_left (fun y => gamA ψ x y) (hz2 x) (fun a b => hr x a b) m y
  have hiso : ∀ a ∈ latA D cc N N', ∀ b ∈ latA D cc N N', gamA ψ (w • a) b = 1 := fun a ha b hb =>
    (hsd _).1 ((latA D cc N N').smul_mem w ha) b hb
  obtain ⟨WA, h1, h2, h3⟩ := GlobalTheory.FinWeil.exists_extension_of_dense (incM D N N') (latA D cc N N').toAddSubgroup
    (fun x y => gamA ψ (w • x) y) W₀
    (fun x y z => by simp only [smul_add, hl]) (fun x y z => hr _ _ _) hiso
    (fun x => by
      obtain ⟨m, hm, hx⟩ := hden x
      refine ⟨m, hm, fun a ha => ⟨?_, ?_⟩⟩
      · have := hiso _ hx a ha
        rw [smul_comm, hn1] at this
        simp only [hn2, this]
      · have := hiso a ha _ hx
        rw [hn2] at this
        show gamA ψ (w • m • a) x = 1
        rw [smul_comm, hn1, this])
    (fun x y v => by
      apply Subtype.ext
      have h := (hwd N N' x y).2.2 v
      have h' : gamA ψ (w • incM D N N' x) (incM D N N' y) =
          psi0 D cc δ (∑ i, ∑ j, (w : D.host.E) * x i j * D.host.conj (y i j)) := by
        rw [← hψ.2.2.1]

        simp only [gamA, incM_apply, Matrix.smul_apply, Matrix.map_apply, smul_AE, sgA_incE, map_sum, map_mul]
      show Wd D _ _ (Wd D _ _ _) = gamA ψ (w • incM D N N' x) (incM D N N' y) • Wd D _ _ _
      rw [h', h])
    (fun x m hm => hdense x m hm)
    (fun v => by
      obtain ⟨m, hm, hv⟩ := v.2.2
      refine ⟨m, hm, ?_⟩
      rintro z ⟨a, ha, hz⟩
      obtain ⟨z', rfl, rfl⟩ := exists_div D hm z a hz
      apply Subtype.ext
      show Wd D _ (pt D _ δ (m • z')) _ = _
      rw [pt_nsmul]
      exact hv _ ((hrat z').1 ha))
  refine ⟨w, gamA ψ, WA, ⟨fun r => ?_, hw, hl, hr, halt, hadj, fun v => ?_, h2⟩, hsd, hinv, fun z F => ?_, h3⟩
  · apply RingOfIntegers.ext
    rw [coe_sgO, coe_sgO, conjE_conjE]
  · have := h1 0
    rw [map_zero] at this
    rw [this]
    apply Subtype.ext
    show Wd D _ (pt D _ δ 0) _ = _
    rw [pt_zero, wd_at_zero]
  · rw [← incM_apply, h1]
    rfl

end GlobalTheory.FinWeil.Model
end
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB

theorem _root_.GlobalTheory.T.exists_betti_cocycle_kummer_relation : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ b ∈ X.BSet N l w, ∃ c ∈ Z1 N l w, BtZ X N l b c := by
  first | exact @GlobalTheory.KZ.BettiEx.exists_betti_cocycle | exact GlobalTheory.KZ.BettiEx.exists_betti_cocycle | (intros; apply GlobalTheory.KZ.BettiEx.exists_betti_cocycle <;> assumption)
end
