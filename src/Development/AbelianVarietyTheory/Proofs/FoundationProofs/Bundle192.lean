module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle023
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle182
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle183
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle184
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle004
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EllipticPointsStabilizer
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle186
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
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.GaloisCohomology.StatementLoc
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.KmapA

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem val_eq_one_iff {K : Type} [Field K] (A : ValuationSubring K) {y : K} (hy : y ≠ 0) :
    A.valuation y = 1 ↔ y ∈ A ∧ y⁻¹ ∈ A := by
  constructor
  · intro h
    refine ⟨(A.valuation_le_one_iff y).1 h.le, (A.valuation_le_one_iff _).1 ?_⟩
    rw [map_inv₀, h, inv_one]
  · rintro ⟨h1, h2⟩
    have hu : IsUnit (⟨y, h1⟩ : A) :=
      isUnit_iff_exists_inv.2 ⟨⟨y⁻¹, h2⟩, Subtype.ext (by simp [hy])⟩
    exact (A.valuation_eq_one_iff _).1 hu

theorem un_map (X : Tower Ω ε) (φ : X.K ≃+* X.K)
    (hφ : ∀ W : ValuationSubring X.K, X.OverY W → X.OverY (W.comap φ.toRingHom)) (m : ℕ) (f : X.Kˣ)
    (hf : f ∈ X.Un m) : Units.map φ.toMonoidHom f ∈ X.Un m := by
  intro W hW
  obtain ⟨g, hg⟩ := hf _ (hφ W hW)
  refine ⟨Units.map φ.toMonoidHom g, ?_⟩
  have hx : ((f : X.K) / (g : X.K) ^ m) ≠ 0 := div_ne_zero f.ne_zero (pow_ne_zero _ g.ne_zero)
  rw [val_eq_one_iff _ hx] at hg
  have hx' : φ ((f : X.K) / (g : X.K) ^ m) ≠ 0 := (map_ne_zero φ).2 hx
  have e : ((Units.map φ.toMonoidHom f : X.Kˣ) : X.K) / ((Units.map φ.toMonoidHom g : X.Kˣ) : X.K) ^ m =
      φ ((f : X.K) / (g : X.K) ^ m) := by
    simp [map_div₀, map_pow]
  rw [e, val_eq_one_iff _ hx']
  refine ⟨ValuationSubring.mem_comap.1 hg.1, ?_⟩
  rw [← map_inv₀]
  exact ValuationSubring.mem_comap.1 hg.2

theorem eval_kmap (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ : X.K ≃+* X.K) (n : ℕ) (a : X.Khat l) (f : X.Kˣ)
    (he : AdicCompletion.eval (idl l) (X.Kl l) n a = X.cls l n f) :
    AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ a) = X.cls l n (Units.map φ.toMonoidHom f) := by
  rw [AdicCompletion.eval_apply] at he ⊢
  have h2 := AdicCompletion.map_val_apply (idl l) (LinearMap.baseChange ℤ_[l]
    (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map φ.toMonoidHom)))) (n := n) a
  refine Eq.trans h2 ?_
  rw [he]
  rfl

theorem kmap_mem_A (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ : X.K ≃+* X.K)
    (hφ : ∀ W : ValuationSubring X.K, X.OverY W → X.OverY (W.comap φ.toRingHom)) :
    ∀ a ∈ X.A l, X.kmap l φ a ∈ X.A l := by
  have h : X.A l ≤ (X.A l).comap (X.kmap l φ) := by
    refine Submodule.span_le.2 (fun x hx => ?_)
    refine Submodule.subset_span (fun n => ?_)
    obtain ⟨f, hf, he⟩ := hx n
    exact ⟨_, un_map X φ hφ (l ^ n) f hf, eval_kmap X l φ n x f he⟩
  intro a ha
  exact h ha

end GlobalTheory.KZ.KmapA


open GlobalTheory.KZ.KmapA in
theorem GlobalTheory.KZ.kmap_A_stable : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
    ∀ (l : ℕ) [Fact l.Prime], (∀ (g : GQ), ∀ a ∈ X.A l, X.kmap l (X.sl g).toRingEquiv a ∈ X.A l) ∧
      ∀ (s : Ω ≃ₐ[ℚ] Ω), ∀ a ∈ X.A l, X.kmap l (X.gal s) a ∈ X.A l := by
  intro Ω _ _ _ ε X hinj hhol l _
  have hY := GlobalTheory.T.overAffineJLine_comap_sl_gal ε X hinj hhol
  exact ⟨fun g => kmap_mem_A X l _ (fun W hW => (hY W hW).1 g),
    fun s => kmap_mem_A X l _ (fun W hW => (hY W hW).2 s)⟩
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ


theorem _root_.GlobalTheory.T.modularFunctionTower_unitGroup_stable_slash_galois : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (m : ℕ) (f : X.Kˣ), f ∈ X.Un m → (∀ (g : GQ) (u : X.Kˣ), (u : X.K) = X.sl g (f : X.K) → u ∈ X.Un m) ∧ ∀ (s : Ω ≃ₐ[ℚ] Ω) (u : X.Kˣ), (u : X.K) = X.gal s (f : X.K) → u ∈ X.Un m := by
  first | exact @GlobalTheory.KZ.Tower.Un_sl_gal | exact GlobalTheory.KZ.Tower.Un_sl_gal | (intros; apply GlobalTheory.KZ.Tower.Un_sl_gal <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

theorem _root_.GlobalTheory.T.gaussValuation_unique_on_lthRoot_level_fields : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l M₀ : ℕ), l.Prime → 0 < M₀ → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring Ω, ((q : ℕ) : Ω) ∈ V.nonunits → ∀ W₁ W₂ : ValuationSubring (AlgebraicClosure X.K), Gauss (algebraMap X.K (AlgebraicClosure X.K) X.jK) V W₁ → Gauss (algebraMap X.K (AlgebraicClosure X.K) X.jK) V W₂ → ∀ (θ : AlgebraicClosure X.K) (f : X.Kˣ), f ∈ X.Un l → Lev X M₀ f → θ ^ l = algebraMap X.K (AlgebraicClosure X.K) (f : X.K) → ∀ x ∈ IntermediateField.adjoin (levF X M₀) {θ}, x ∈ W₁ ↔ x ∈ W₂ := by
  first | exact @GlobalTheory.KZ.ES.UniqRoot.gauss_unique_root | exact GlobalTheory.KZ.ES.UniqRoot.gauss_unique_root | (intros; apply GlobalTheory.KZ.ES.UniqRoot.gauss_unique_root <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction
open scoped ENNReal nonZeroDivisors

namespace GlobalTheory.SelBaseChange

section Coord

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [Algebra R R']

end Coord

section Coh

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
  {G : Type} [Group G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
  {M' : Type} [AddCommGroup M'] [Module R' M'] [TopologicalSpace M']
  [IsTopologicalAddGroup M'] [ContinuousConstSMul R' M'] [Module R M'] [IsScalarTower R R' M']
  (ρ : Representation R G M) (ρ' : Representation R' G M') (u : M' →ₗ[R] M) (hu : Continuous u)
  (he : ∀ g m, u (ρ' g m) = ρ g (u m))

def cZ : Z1 ρ' →ₗ[R] Z1 ρ where
  toFun f := ⟨u ∘ f.1, hu.comp f.2.1, fun g h => by
    simp only [Function.comp_apply, f.2.2 g h, map_add (f := _), he]⟩
  map_add' f f' := Subtype.ext (funext fun g => map_add u _ _)
  map_smul' r f := Subtype.ext (funext fun g => map_smul u _ _)

def cH : H1 ρ' →ₗ[R] H1 ρ :=
  Submodule.mapQ (((B1 ρ').comap (Z1 ρ').subtype).restrictScalars R) _ (cZ ρ ρ' u hu he)
    (fun f hf => by
      obtain ⟨m, hm⟩ := (mem_coboundaries1 ρ' _).1 hf
      refine (mem_coboundaries1 _ _).2 ⟨u m, fun g => ?_⟩
      have e := hm g
      simp only [Submodule.coe_subtype] at e
      change u (f.1 g) = _
      rw [e, map_sub, he]) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv R ((B1 ρ').comap (Z1 ρ').subtype)).symm.toLinearMap

theorem cH_mk (z : Z1 ρ') :
    cH ρ ρ' u hu he (Submodule.Quotient.mk z) = Submodule.Quotient.mk (cZ ρ ρ' u hu he z) := rfl

theorem res_cH {H : Type} [Group H] [TopologicalSpace H] (φ : H →* G) (hφ : Continuous φ)
    (x : H1 ρ') :
    resH1 ρ φ hφ (cH ρ ρ' u hu he x) =
      cH (ρ.comp φ) (ρ'.comp φ) u hu (fun _ _ => he _ _) (resH1 ρ' φ hφ x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem cH_mem_H1ur (J : Subgroup G) (x : H1 ρ') (hx : x ∈ H1ur ρ' J) :
    cH ρ ρ' u hu he x ∈ H1ur ρ J := by
  unfold H1ur at hx ⊢
  rw [LinearMap.mem_ker] at hx ⊢
  exact (res_cH ρ ρ' u hu he J.subtype continuous_subtype_val x).trans
    ((congrArg _ hx).trans (map_zero _))

theorem cH_mem_Sel {I : Type} {Dc : I → Type} [∀ v, Group (Dc v)] [∀ v, TopologicalSpace (Dc v)]
    (φ : ∀ v, Dc v →* G) (hφ : ∀ v, Continuous (φ v)) (L : LocCond ρ φ) (L' : LocCond ρ' φ)
    (h : ∀ v, ∀ x ∈ L' v, cH (ρ.comp (φ v)) (ρ'.comp (φ v)) u hu (fun _ _ => he _ _) x ∈ L v)
    (x : H1 ρ') (hx : x ∈ Sel ρ' φ hφ L') : cH ρ ρ' u hu he x ∈ Sel ρ φ hφ L := by
  rw [mem_Sel] at hx ⊢
  intro v
  rw [res_cH]
  exact h v _ (hx v)

theorem eq_zero_of_cH {ι : Type} (u : ι → (M' →ₗ[R] M)) (hu : ∀ i, Continuous (u i))
    (he : ∀ i g m, u i (ρ' g m) = ρ g (u i m))
    (hb : Function.Bijective fun (m : M') (i : ι) => u i m) (x : H1 ρ')
    (hx : ∀ i, cH ρ ρ' (u i) (hu i) (he i) x = 0) : x = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  simp only [cH_mk, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, mem_coboundaries1] at hx ⊢
  choose m hm using hx
  obtain ⟨m', hm'⟩ := hb.2 m
  refine ⟨m', fun g => hb.1 (funext fun i => ?_)⟩
  have := hm i g
  rw [← congrFun hm' i] at this
  show u i _ = u i _
  rw [map_sub, he]
  exact this

end Coh

section Main

open Formalism.MainNotions.BlochKatoReduction.Gen

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) (k k' : ℕ)

theorem trep_one_apply (g : Gen.GE N) (m : Fin D.R.r → KmodO (X.Ok i k)) (a : Fin D.R.r) :
    Trep i s k 1 g m a = ∑ j, phiK X i k (Tmat i s g a j) • m j := by
  simp [Trep, twRep, matAct, Tmat, Finset.smul_sum, smul_smul]

variable [Algebra (X.Ok i k) (X.Ok i k')] [IsScalarTower (X.O i) (X.Ok i k) (X.Ok i k')]

theorem phiK_eq (a : X.O0 i) :
    phiK X i k' a = algebraMap (X.Ok i k) (X.Ok i k') (phiK X i k a) :=
  IsScalarTower.algebraMap_apply (X.O i) (X.Ok i k) (X.Ok i k') _

variable (p : KmodO (X.Ok i k') →ₗ[X.Ok i k] KmodO (X.Ok i k))

theorem equivariant (g : Gen.GE N) (m : Fin D.R.r → KmodO (X.Ok i k')) :
    p.compLeft (Fin D.R.r) (Trep i s k' 1 g m) = Trep i s k 1 g (p.compLeft (Fin D.R.r) m) := by
  funext a
  show p (Trep i s k' 1 g m a) = _

  rw [trep_one_apply, trep_one_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [phiK_eq i k k', algebraMap_smul, map_smul]
  rfl

end Main

end GlobalTheory.SelBaseChange
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles

namespace GlobalTheory.BKIntegralToRational

theorem exists_mul_pow_eq {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {p : A}
    (hu : ¬ IsUnit p) (a : FractionRing A) :
    ∃ (x : A) (N : ℕ), a * algebraMap A (FractionRing A) p ^ N = algebraMap A (FractionRing A) x := by
  obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := A) a
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨N, hN⟩ := IsDiscreteValuationRing.associated_pow_irreducible hd0 hϖ
  have h1 : ϖ ∣ p := by
    rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq]
    exact hu
  obtain ⟨c, hc⟩ : d ∣ p ^ N := hN.dvd.trans (pow_dvd_pow_of_dvd h1 N)
  refine ⟨n * c, N, ?_⟩
  have hd1 : algebraMap A (FractionRing A) d ≠ 0 := by
    simpa using hd0
  rw [← map_pow, hc, map_mul, map_mul]
  field_simp

theorem continuous_div_mk {O₀ O' : Type} [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀]
    [TopologicalSpace O₀] [IsTopologicalRing O₀] (had : IsAdic (IsLocalRing.maximalIdeal O₀))
    [CommRing O'] [IsDomain O'] (ι : O₀ →+* O') {d : O₀} (hd : d ≠ 0) (hd' : ι d ≠ 0) :
    Continuous fun x : O₀ => (Submodule.Quotient.mk (algebraMap O' (FractionRing O') (ι x) /
      algebraMap O' (FractionRing O') (ι d)) : KmodO O') := by
  have hd1 : algebraMap O' (FractionRing O') (ι d) ≠ 0 := by simpa using hd'
  have hop : IsOpen ((Ideal.span {d} : Ideal O₀) : Set O₀) := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O₀
    obtain ⟨N, hN⟩ := IsDiscreteValuationRing.associated_pow_irreducible hd hϖ
    have := (isAdic_iff.1 had).1 N
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow] at this
    rwa [Ideal.span_singleton_eq_span_singleton.2 hN]
  refine IsLocallyConstant.continuous ?_
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => y - x) ⁻¹' ((Ideal.span {d} : Ideal O₀) : Set O₀),
    hop.preimage (by fun_prop), by simp, fun y hy => ?_⟩
  obtain ⟨c, hc⟩ : d ∣ y - x := Ideal.mem_span_singleton.1 hy
  rw [Submodule.Quotient.eq]
  refine ⟨ι c, ?_⟩
  rw [← sub_div, ← map_sub, ← map_sub, hc, map_mul, map_mul]
  simp only [Algebra.linearMap_apply]
  field_simp

section Bridge

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O₀ : Type} [CommRing O₀] [Algebra ℤ_[l] O₀] [TopologicalSpace O₀]
  (Bw : LocBridge l E Ω Gw O₀) (P : LocPrime l) {m : ℕ}

theorem toLL_injective : Function.Injective Bw.toLL :=
  Subtype.val_injective.comp Bw.eO.injective

theorem continuous_of_toLL {X : Type} [TopologicalSpace X] (f : X → O₀)
    (h : Continuous fun x => Bw.toLL (f x)) : Continuous f := by
  have h1 : Continuous fun x => Bw.eO (f x) := continuous_induced_rng.2 h
  simpa [Function.comp_def] using Bw.eO_symm_cont.comp h1

theorem continuous_of_crys {T : (Ω ≃ₐ[E] Ω) →* GL (Fin m) O₀} {f : ↥Gw → Fin m → O₀}
    (hf : IsCrysCocycle Bw P T f) (j : Fin m) : Continuous fun g => f g j := by
  apply continuous_of_toLL Bw
  have := ((continuous_apply j).comp hf.1.1).comp Bw.e_cont
  simpa [Function.comp_def] using this

theorem cocycle_of_crys {T : (Ω ≃ₐ[E] Ω) →* GL (Fin m) O₀} {f : ↥Gw → Fin m → O₀}
    (hf : IsCrysCocycle Bw P T f) (g h : ↥Gw) (j : Fin m) :
    f (g * h) j = f g j + ∑ b, ((T g : GL (Fin m) O₀) : Matrix (Fin m) (Fin m) O₀) j b * f h b := by
  apply toLL_injective Bw
  have := congrFun (hf.1.2 (Bw.e g) (Bw.e h)) j
  simpa [← map_mul, LocBridge.rep, Matrix.mulVec, dotProduct, Matrix.toLinAlgEquiv'_apply] using this

end Bridge

section Main

variable (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i) (k : ℕ)

variable (ψ : GE D →* (D.ntw.Ok i k)ˣ) (v : PlE D.host) (hv : v ∈ placesOver D.host.E (D.ntw.l i))
  (hψ : ∀ σ ∈ decAt D v, ψ σ = 1)


end Main

end GlobalTheory.BKIntegralToRational
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles
open Formalism.MainNotions.N
open scoped Matrix Pointwise

namespace GlobalTheory.InertiaTypePrimes

section General

variable {Γ R : Type} [Group Γ] [CommRing R] {r : ℕ}

theorem mem_ker_mapRep_iff (J : Ideal R) (ρ : Γ →* GL (Fin r) R) (g : Γ) :
    g ∈ (mapRep (Ideal.Quotient.mk J) ρ).ker ↔
      ∀ a b, (((ρ g : GL (Fin r) R) : Matrix (Fin r) (Fin r) R) - 1) a b ∈ J := by
  rw [MonoidHom.mem_ker, Units.ext_iff]
  change (Ideal.Quotient.mk J).mapMatrix ((ρ g : GL (Fin r) R) : Matrix (Fin r) (Fin r) R) = 1 ↔ _
  rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk J).mapMatrix, ← map_sub, ← Matrix.ext_iff]
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply,
    Ideal.Quotient.eq_zero_iff_mem]

theorem isOpen_ker_mapRep [TopologicalSpace Γ] [TopologicalSpace R] [IsTopologicalRing R]
    (J : Ideal R) (hJ : IsOpen (J : Set R)) (ρ : Γ →* GL (Fin r) R)
    (hρ : Continuous fun g => ((ρ g : GL (Fin r) R) : Matrix (Fin r) (Fin r) R)) :
    IsOpen ((mapRep (Ideal.Quotient.mk J) ρ).ker : Set Γ) := by
  have : ((mapRep (Ideal.Quotient.mk J) ρ).ker : Set Γ) = ⋂ a, ⋂ b,
      (fun g => (((ρ g : GL (Fin r) R) : Matrix (Fin r) (Fin r) R) - 1) a b) ⁻¹' (J : Set R) := by
    ext g
    simp only [SetLike.mem_coe, mem_ker_mapRep_iff, Set.mem_iInter, Set.mem_preimage]
  rw [this]
  refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => hJ.preimage ?_
  exact (hρ.sub continuous_const).matrix_elem a b

end General

theorem isWild_of_isWildAt {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (σ : G E Ω) (h : IsWildAt A σ) : IsWild A σ := by
  have h1 : ∀ x : Ω, x ≠ 0 → A.valuation (σ x - x) < A.valuation x := fun x hx => by
    have e : σ x - x = (σ x / x - 1) * x := by field_simp
    have h0 : 0 < A.valuation x := zero_lt_iff.mpr (by simpa using hx)
    rw [e, map_mul]
    exact mul_lt_of_lt_one_left h0 (h x hx)
  have h2 : ∀ x : Ω, A.valuation (σ x) = A.valuation x := fun x => by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · exact Valuation.map_eq_of_sub_lt _ (h1 x hx)
  refine ⟨⟨?_, fun x hx => ?_⟩, h1⟩
  · change σ • A = A
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← A.valuation_le_one_iff,
      ← A.valuation_le_one_iff, ← h2, AlgEquiv.smul_def, mul_inv_apply]
  · rcases eq_or_ne x 0 with rfl | hx0
    · simp
    · exact (h1 x hx0).trans_le hx

section Wild

variable {E Ω R : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [TopologicalSpace R] [IsTopologicalRing R]
  {r : ℕ} {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 E)}

end Wild

end GlobalTheory.InertiaTypePrimes
end

section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

theorem _root_.GlobalTheory.T.elliptic_points_stabilizer : ∀ τ₀ : ℍ, (E₆ τ₀ = 0 → ∃ u : SL(2, ℤ), u • τ₀ = τ₀ ∧ IsPrimitiveRoot (denom (u : GL (Fin 2) ℝ) τ₀) 4) ∧ (E₄ τ₀ = 0 → ∃ u : SL(2, ℤ), u • τ₀ = τ₀ ∧ IsPrimitiveRoot (denom (u : GL (Fin 2) ℝ) τ₀) 6) := by
  first | exact @GlobalTheory.EllipticZero.elliptic_of_zero | exact GlobalTheory.EllipticZero.elliptic_of_zero | (intros; apply GlobalTheory.EllipticZero.elliptic_of_zero <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

theorem _root_.GlobalTheory.T.padicInt_module_finite_of_separated : ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X], Finite (X ⧸ LinearMap.range (LinearMap.lsmul ℤ_[l] X ((l : ℤ_[l]) ^ 1))) → (∀ x : X, (∀ r : ℕ, ∃ y, (l : ℤ_[l]) ^ r • y = x) → x = 0) → Module.Finite ℤ_[l] X := by
  first | exact @GlobalTheory.padicInt_module_finite_of_separated_of_finite_quotient | exact GlobalTheory.padicInt_module_finite_of_separated_of_finite_quotient | (intros; apply GlobalTheory.padicInt_module_finite_of_separated_of_finite_quotient <;> assumption)
end
