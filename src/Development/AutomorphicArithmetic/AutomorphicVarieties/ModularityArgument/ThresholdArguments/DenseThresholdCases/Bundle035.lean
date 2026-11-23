module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.PromodularityCaseThree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle033
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.HiComm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HeckeOperatorPreservesPart
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle010
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle119
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle226
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ConjSep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle026
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.HidaOrdinaryHecke.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.HidaOrdinaryHecke.HeckePolCoeffMem
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.NewformOfAdmissibleTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.PowEqOneOfKills
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.QuadBC2
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section




section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
namespace UpperTheory.V.Cu
section
variable {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) {R : Type} [CommRing R] (a : O →+* R)
end
section
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}
end
def SeedIVAlt : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T₀ : Tower D),
    Ctx3 D → T₀.Ok → Four T₀ → ∀ (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l),
    ∃ (w : ℕ) (s : PD T₀.ι (G T₀.F Ω) 𝔞.k), w.Prime ∧ T₀.Splits w ∧ (T₀.fr {w}).IsRes (𝔞.red c) s ∧ Supp nM s.r ∧
      ∀ (T : Tower D) (hT : T₀.Le T), T.Ok → Dies l w T.F →
        ∃ (c₁ : Coef l) (h : c.O ≤ c₁.O) (Q : PD T.ι (G T.F Ω) c₁.O), T.SeedPairAlt ι h Q ∧ T₀.OverT hT s (Q.map (𝔞.red c₁)) ∧
          InA (Q.map (𝔞.red c₁)) ∧ Ent (Q.map (𝔞.red c₁)).r (-wBe) ∧ Ent (Q.map (𝔞.red c₁)).r (-wTh)
def ChainRankFour : Prop :=
  CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (ι : PadicAlgCl l ≃+* ℂ) (c' : Coef l) (h : c.O ≤ c'.O)
    (X : Space (T.fr ∅) (inc h)) (J : Ideal X.B), T.PotentialModularityTower ι X J → ∀ C : ℕ, (T.fr ∅).Bounds ((residue c'.O).comp (inc h)) T.d C →
    30 * (C + 1) * (C + 1) ≤ T.d → ∀ x : X.A →ₐ[c'.O] ResidueField c'.O,
      (T.fr ∅).IsRes ((residue c'.O).comp (inc h)) (X.P.map (x : X.A →+* _)) →
      Good4 (T.fr ∅) ((residue c'.O).comp (inc h)) (X.P.map (x : X.A →+* _)) →
      X.SomeIn J (RingHom.ker x) → X.AllIn J (RingHom.ker x)
def RankFourChainReductionDense : Prop :=
  CohomologyHyp → HFit → _root_.UpperTheory.V.Cu.SeedIVAlt → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T₀ : Tower D), Ctx3 D → T₀.Ok → Four T₀ → TameL l T₀.F →
    ∀ (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l) (c₀ : PD Unit (G ℚ Ω) 𝔞.k), LatShape D T₀.pr (resQ T₀.F T₀.g0) (𝔞.red c) c₀ →
      ∃ T₁ : Tower D, T₀.Le T₁ ∧ TameL l T₁.F ∧ ∀ T : Tower D, T₁.Le T → T.Deep →
        ∃ (c₁ : Coef l) (h : c.O ≤ c₁.O) (Q : PD T.ι (G T.F Ω) c₁.O), T.SeedPairAlt ι h Q ∧
          ∀ c₀' : PD T.ι (G T.F Ω) 𝔞.k, T.OverQ c₀ c₀' → (T.fr ∅).IsRes (𝔞.red c) c₀' →
            Chain4 (T.fr ∅) (𝔞.red c) c₀' (Q.map (𝔞.red c₁))
def PromodularityCaseThreeDense : Prop :=
  CohomologyHyp → UpperTheory.V.Published.FerreroWashington → HFit → _root_.UpperTheory.V.Cu.SeedIVAlt → _root_.UpperTheory.V.Ws.PMExAlt → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), Ctx3 D →
    ∀ (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l) r u, KPair D 𝔞 r u → Star (mapRep 𝔞.toK r) → _root_.UpperTheory.V.Ws.ProModAlt D ι 𝔞 r
def AutomorphyRankFourDense : Prop :=
  CohomologyHyp → UpperTheory.V.Published.FerreroWashington → HFit → _root_.UpperTheory.V.Ws.SeedIIAlt → _root_.UpperTheory.V.Cu.SeedIVAlt → _root_.UpperTheory.V.Ws.PMExAlt → _root_.UpperTheory.V.Aut.SymplecticFourImageDense
end UpperTheory.V.Cu
end
end
end

section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem coreSep_coord {A M N κ : Type} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module ℂ N]
    (Y : Submodule A M) (φ : A →+* ℂ) (sp : M → N) (hadd : ∀ f ∈ Y, ∀ f' ∈ Y, sp (f + f') = sp f + sp f')
    (hsmul : ∀ f ∈ Y, ∀ b : A, sp (b • f) = φ b • sp f) (b : Module.Basis κ A Y)
    (hind : LinearIndependent ℂ fun i => sp (b i)) (g : Y) (hg : sp g = 0) (i : κ) : φ (b.repr g i) = 0 := by
  classical
  let s : Y →ₛₗ[φ] N :=
    { toFun := fun f => sp f
      map_add' := fun f f' => hadd _ f.2 _ f'.2
      map_smul' := fun r f => hsmul _ f.2 r }
  have h1 : s g = ∑ j ∈ (b.repr g).support, φ (b.repr g j) • sp (b j) := by

    conv_lhs => rw [← b.linearCombination_repr g, Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    exact Finset.sum_congr rfl fun j _ => s.map_smulₛₗ _ _
  by_cases hi : i ∈ (b.repr g).support
  · exact linearIndependent_iff'.1 hind _ (fun j => φ (b.repr g j)) (h1.symm.trans hg) i hi
  · rw [Finsupp.notMem_support_iff.1 hi, map_zero]
private theorem coreSep_kill {N J : Type*} [AddCommGroup N] [Module ℂ N] (E : Submodule ℂ N) (Y : J → Submodule ℂ N)
    (hE : E = ⨆ j, Y j ⊓ E) (T : Module.End ℂ E) (h : ∀ j, ∀ F : E, (F : N) ∈ Y j → T F = 0) (F : E) : T F = 0 := by
  have hle : E ≤ (LinearMap.ker T).map E.subtype := by
    conv_lhs => rw [hE]
    exact iSup_le fun j G hG => ⟨⟨G, hG.2⟩, h j ⟨G, hG.2⟩ hG.1, rfl⟩
  obtain ⟨G, hG, hGF⟩ := hle F.2
  have : G = F := Subtype.ext hGF
  exact this ▸ hG
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete in
theorem UpperTheory.V.Hi.eq_zero_of_vanish_at_good_points_dense_weight :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop), H.AutomorphicHeckeSet ι P →
    ∀ (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))], ∀ lam ∈ H.admitted, H.DenseWt θ lam → ∀ t : H.TK θ a K, (∀ x : H.TK θ a K →ₐ[c.O] Qbar l, H.Good θ (x.toRingHom.comp (algebraMap A _)) lam → x t = 0) → t = 0 := by
  intro hLit L Ω _ _ _ _ _ l _ n c H hAx A _ _ _ θ hθ ι P hP a K _ lam hlam hD t ht
  obtain ⟨-, -, hfree, -⟩ := hiComm L Ω l n c H hAx A θ hθ K
  let b := Module.Free.chooseBasis A (H.X.Ord (H.τA A) θ (H.lev K))
  refine Subtype.ext (LinearMap.ext fun f => ?_)
  let g : H.X.Ord (H.τA A) θ (H.lev K) :=
    ⟨((t : Module.End A (H.MK θ a K)) f : H.MK θ a K), ((t : Module.End A (H.MK θ a K)) f).2.1⟩
  have hg : g = 0 := by
    refine b.repr.injective (Finsupp.ext fun i => ?_)
    rw [map_zero, Finsupp.zero_apply]
    refine hD _ fun x hx => ?_
    obtain ⟨d, ξ, c0, sp, hsp⟩ := spec L Ω l n c H hAx A θ hθ ι x lam hx.2.1
    obtain ⟨h1, act, h2, -, -, -, h3⟩ := _root_.UpperTheory.V.Hi.partAct0_alt hLit L Ω l n c H hAx A θ hθ ι P hP x lam d ξ c0 sp hsp hlam a K _ rfl
    have hE := h1.resolve_right (not_not.2 hx)
    have h0 := coreSep_kill _ _ hE (act t) (fun Y F hF => by
      by_cases hb : Y.1.Y ⊓ Submodule.span ℂ (sp '' H.MK θ a K) = ⊥
      · have : F = 0 := Subtype.ext ((Submodule.eq_bot_iff _).1 hb _ ⟨hF, F.2⟩)
        rw [this, map_zero]
      · obtain ⟨y, hy, hact⟩ := h3 hx Y.1 hb
        rw [hact t F hF, ht y (hy ▸ hx), map_zero, zero_smul])
      ⟨sp f, Submodule.subset_span ⟨f, f.2, rfl⟩⟩
    have h4 := h2 t f ⟨sp f, Submodule.subset_span ⟨f, f.2, rfl⟩⟩ rfl
    rw [h0] at h4
    have h5 := coreSep_coord _ (ι.toRingHom.comp x.toRingHom) sp (hsp.add K) (hsp.smul K) b (hsp.indep K _ b) g h4.symm i
    exact ι.injective (h5.trans (map_zero ι).symm)
  exact Subtype.ext (congrArg (fun z : H.X.Ord (H.τA A) θ (H.lev K) => (z : H.X.Fn A H.m)) hg)
end
end

section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem lam_map {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (D : W.GDet n A G) (f : A →+* B)
    (g : G) (i : ℕ) : (D.map f).lam i (MonoidAlgebra.single g 1) = f (D.lam i (MonoidAlgebra.single g 1)) := by
  have h0 : (D.map f).chi (MonoidAlgebra.single g 1) = (D.chi (MonoidAlgebra.single g 1)).map f := by
    letI : Algebra A (Polynomial B) := ((algebraMap B (Polynomial B)).comp f).toAlgebra
    let φ : Polynomial A →ₐ[A] Polynomial B :=
      { Polynomial.mapRingHom f with commutes' := fun a => Polynomial.map_C f }
    have h := D.nat (Polynomial A) (Polynomial B) φ
      (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom G Polynomial.C (MonoidAlgebra.single g 1))
    refine Eq.trans ?_ h
    change D.D (Polynomial B) _ = D.D (Polynomial B) (MonoidAlgebra.mapRingHom G (Polynomial.mapRingHom f) _)
    congr 1
    simp [map_sub, MonoidAlgebra.mapRingHom_single]
  simp [W.GDet.lam, h0]
private theorem red_abs {O R T : Type} [CommRing O] [CommRing R] [CommRing T] [Algebra O R] [Algebra O T] (f : R →ₐ[O] T)
    (I : Ideal T) (S : Subalgebra O T) (hS : ∀ s ∈ S, ∀ k : ℕ, s ^ k ∈ I → s ∈ I) (U : Set R)
    (hU : ∀ u ∈ U, ∃ s ∈ S, f u - s ∈ I) (t : R) (ht : t ∈ Algebra.adjoin O U) (k : ℕ) (hk : f (t ^ k) ∈ I) : f t ∈ I := by
  have key : ∃ s ∈ S, f t - s ∈ I := by
    clear hk
    induction ht using Algebra.adjoin_induction with
    | mem x hx => exact hU x hx
    | algebraMap b => exact ⟨_, S.algebraMap_mem b, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs, h1⟩ := hx
      obtain ⟨s', hs', h2⟩ := hy
      refine ⟨s + s', add_mem hs hs', ?_⟩
      have := I.add_mem h1 h2
      rw [map_add (f := _)]; convert this using 1; ring
    | mul x y _ _ hx hy =>
      obtain ⟨s, hs, h1⟩ := hx
      obtain ⟨s', hs', h2⟩ := hy
      refine ⟨s * s', mul_mem hs hs', ?_⟩
      have := I.add_mem (I.mul_mem_left (f x) h2) (I.mul_mem_left s' h1)
      rw [map_mul]; convert this using 1; ring
  obtain ⟨s, hs, h1⟩ := key
  have e : Ideal.Quotient.mk I (f t) = Ideal.Quotient.mk I s := Ideal.Quotient.eq.2 h1
  have h2 : s ^ k ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow, ← e, ← map_pow, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact hk
  have := I.add_mem h1 (hS s hs k h2)
  simpa using this
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete in
theorem UpperTheory.V.Th.AnnihilatorQuotientFinite.ctrlMu_of_arith_weight :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
∀ (ι : Qbar l ≃+* ℂ) (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop), H.AutomorphicHeckeSet ι P →
    ∀ (x : A →ₐ[c.O] c.O) (lam : Wt L l n), lam ∈ H.admitted → H.Arith θ ((Algebra.ofId c.O (Qbar l)).comp x).toRingHom lam →
    ∀ (a : H.Op → c.O) (K : H.Lev) [Module.Finite A (H.MK θ a K)] (R : Type) [CommRing R] [Algebra c.O R] (D₀ : W.GDet n R H.Gq)
      (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Rˣ) (μ : R →+* Module.End A (H.MK θ a K)),
      (H.MK θ a K = ⊥ ∨ ∃ (_ : Fact (CommOn (H.MK θ a K) (H.op A))) (_ : Alg.IsCO c.O (H.TK θ a K)) (f : R →ₐ[c.O] H.TK θ a K),
        H.IsMap θ a K D₀ ψ₀ f ∧ ∀ t, μ t = (f t : Module.End A (H.MK θ a K))) →
      ∀ t ∈ Algebra.adjoin c.O {b : R | ∃ i g, b = D₀.lam i (MonoidAlgebra.single g 1)}, ∀ k : ℕ,
        (∀ y, μ (t ^ k) y ∈ (RingHom.ker x • ⊤ : Submodule A (H.MK θ a K))) →
        ∀ y, μ t y ∈ (RingHom.ker x • ⊤ : Submodule A (H.MK θ a K)) := by
  intro L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ ι P hP x lam hl har a K _ R _ _ D₀ ψ₀ μ hμ t ht k hk y
  rcases hμ with h0 | ⟨_, _, f, hf, hμ⟩
  · have : μ t y = 0 := Subtype.ext ((Submodule.mem_bot A).1 (h0 ▸ (μ t y).2))
    rw [this]
    exact zero_mem _
  haveI := c.dvr
  have hker : RingHom.ker ((Algebra.ofId c.O (Qbar l)).comp x) = RingHom.ker x := by
    ext b
    rw [RingHom.mem_ker, RingHom.mem_ker]
    exact map_eq_zero_iff (algebraMap c.O (Qbar l)) Subtype.val_injective
  obtain ⟨I, hI, hfin⟩ := Th.AnnihilatorQuotientFinite.annFin x (heckeAlg (H.MK θ a K) (H.op A)).val.toRingHom fun o y => by
    rw [IsScalarTower.algebraMap_apply c.O A (H.TK θ a K)]
    rfl
  have h1 := red_abs f I (Algebra.adjoin c.O (Set.range fun p : H.Wp × Fin n => H.gen θ a K (.inl p)))
    (fun s hs k hk => (hI s).2 (by
      have := _root_.UpperTheory.V.Th.AnnihilatorQuotientFinite.sphRed_alt L Ω l n c H hH A θ hθ ι P hP _ lam hl har a K s hs k
      rw [hker] at this
      exact this ((hI _).1 hk))) _ (by
      rintro _ ⟨i, g, rfl⟩
      refine Th.AnnihilatorQuotientFinite.closedSub I _ _ fun N => ?_
      have := Th.AnnihilatorQuotientFinite.frobS L Ω l n c H hH A θ a K _ _ _ hf i g N
      rwa [lam_map] at this) t ht k ((hI _).2 fun y => by
      have := hk y
      rwa [hμ] at this)
  rw [hμ]
  exact (hI _).1 h1 y
end
end

section




open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep

noncomputable section

namespace TConjKDualProof

open Matrix GlobalTheory.ContraPair

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {a : ℕ}

private def phiOp (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) : Module.End ℂ (Sm L a) :=
  act (.fin (PhiU a (Af L))) * act (.cpt (PhiK L a))

private theorem barK_barK (k : Kinf L a) : barK (barK k) = k := Subtype.ext (by
  ext i j : 1
  exact star_star _)

private theorem fin_cpt (k : GL (Fin a) (Af L)) (u : Kinf L a) :
    act (.cpt u) * act (.fin k) = act (.fin k) * act (Op.cpt u : Op L a) := by
  change rt L a _ * rt L a _ = rt L a _ * rt L a _
  rw [← map_mul, ← map_mul]
  exact congrArg _ (infGL_comm _ _)

private theorem phiOp_mul (o : Op L a) : phiOp L a * act (invTOp (conjOp o)) = act (thetaOp o) * phiOp L a := by
  cases o with
  | fin k =>
    simp only [phiOp, conjOp, invTOp, thetaOp]
    rw [mul_assoc, fin_cpt, ← mul_assoc, ← mul_assoc]
    congr 1
    change finRep L a _ * finRep L a _ = finRep L a _ * finRep L a _
    rw [← map_mul, ← map_mul]
    congr 1
    change _ = PhiU a (Af L) * _ * (PhiU a (Af L))⁻¹ * _
    rw [inv_mul_cancel_right]
    rfl
  | cpt k =>
    simp only [phiOp, conjOp, invTOp, thetaOp, barK_barK]
    rw [← mul_assoc, fin_cpt, mul_assoc, mul_assoc]
    congr 1
    change cptRep L a _ * cptRep L a _ = cptRep L a _ * cptRep L a _
    rw [← map_mul, ← map_mul, inv_mul_cancel_right]
  | lie X =>
    simp only [phiOp, conjOp, invTOp, thetaOp]
    have h1 := GlobalTheory.CapAdInv.rt_lie (Unitary.toUnits (PhiK L a)) (-(Matrix.of X)ᴴ)
    have h2 := lie_rt_fin (E := L) (toL (-(GlobalTheory.Tw.Phi a (Cinf L) * (Matrix.of X)ᴴ * (GlobalTheory.Tw.Phi a (Cinf L))ᵀ)))
      (PhiU a (Af L))
    have e : Unitary.toUnits (PhiK L a) = PhiU a (Cinf L) := Units.ext rfl
    have e2 : (Unitary.toUnits (PhiK L a)).val * (-(Matrix.of X)ᴴ) * ((Unitary.toUnits (PhiK L a))⁻¹).val =
        -(GlobalTheory.Tw.Phi a (Cinf L) * (Matrix.of X)ᴴ * (GlobalTheory.Tw.Phi a (Cinf L))ᵀ) := by
      rw [e, mul_neg, neg_mul]; rfl
    rw [e2] at h1
    rw [mul_assoc, ← mul_assoc (act (Op.lie _))]
    exact (congrArg (act (.fin (PhiU a (Af L))) * ·) h1).trans ((mul_assoc _ _ _).symm.trans
      (congrArg (· * _) h2.symm))

private theorem dualIsConj_of_isCsd {π : CuspSub L a} (h : Paired π π invTOp) (hc : π.IsCsd) : DualIsConj π := by
  obtain ⟨B, h1, h2, h3, h4, h5⟩ := h
  obtain ⟨T, hT⟩ := hc
  let P : Module.End ℂ π.V := π.op (.fin (PhiU a (Af L))) * π.op (.cpt (PhiK L a))
  let Q : Module.End ℂ π.V := π.op (.cpt (PhiK L a)⁻¹) * π.op (.fin (PhiU a (Af L))⁻¹)
  have f1 : ∀ k k' : GL (Fin a) (Af L), k * k' = 1 → ∀ φ, π.op (.fin k) (π.op (.fin k') φ) = φ := fun k k' e φ =>
    Subtype.ext (by
      change (finRep L a k * finRep L a k') φ.1 = φ.1
      rw [← map_mul, e, map_one]; rfl)
  have f2 : ∀ k k' : Kinf L a, k * k' = 1 → ∀ φ, π.op (.cpt k) (π.op (.cpt k') φ) = φ := fun k k' e φ =>
    Subtype.ext (by
      change (cptRep L a k * cptRep L a k') φ.1 = φ.1
      rw [← map_mul, e, map_one]; rfl)
  let Pe : π.V ≃ₗ[ℂ] π.V := LinearEquiv.ofLinear P Q
    (LinearMap.ext fun φ => by simp [P, Q, f1, f2]) (LinearMap.ext fun φ => by simp [P, Q, f1, f2])
  let S := Pe.trans T
  have hS : ∀ o φ, S (π.op (invTOp (conjOp o)) φ) = π.op o (S φ) := fun o φ => by
    change T _ = π.op o (T _)
    rw [← hT]
    exact congrArg T (Subtype.ext (LinearMap.congr_fun (phiOp_mul o) φ.1))
  have hS' : ∀ o φ, S.symm (π.op o φ) = π.op (invTOp (conjOp o)) (S.symm φ) := fun o φ => by
    rw [LinearEquiv.symm_apply_eq, hS, LinearEquiv.apply_symm_apply]
  refine ⟨B.flip ∘ₗ S.symm.toLinearMap, fun φ h => ?_, fun ψ h => h1 ψ fun x => ?_, fun k φ ψ => ?_, fun k φ ψ => ?_,
    fun X φ ψ => ?_⟩
  · exact (map_eq_zero_iff _ S.symm.injective).1 (h2 _ h)
  · simpa using h (S x)
  · change B _ (S.symm _) = B _ (S.symm _)
    rw [hS']; exact h3 _ _ _
  · change B _ (S.symm _) = B _ (S.symm _)
    rw [hS']; exact h4 _ _ _
  · change B _ (S.symm _) + B _ (S.symm _) = 0
    rw [hS', add_comm]; exact h5 _ _ _

end TConjKDualProof

section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.ThetaPull
namespace UpperTheory.V.Af
private theorem regAlg_of_infOf {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {n : ℕ} {m : Fin n → ℤ}
    (hm : StrictAnti m) {π : CuspSub K n} (h : ∀ τ, π.HasInfChar τ (infOf m)) : (CG.mk π).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
  rw [CG.HasInfChar.infChar_eq (π := CG.mk π) (h τ)]
  refine ⟨Multiset.Nodup.map (fun i j e => hm.injective ?_) Finset.univ.nodup, fun z hz => ?_⟩
  · exact_mod_cast add_left_cancel e
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
    exact ⟨m i, add_comm _ _⟩
private theorem eventually_notMem {K : Type} [Field K] [NumberField K] {M : ℕ} (hM : 1 ≤ M) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite, (M : 𝓞 K) ∉ w.asIdeal := by
  have h0 : Ideal.span {(M : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 (by omega)
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  exact Ideal.dvd_span_singleton.2 (not_not.1 hw)
private theorem sep_theta {K : Type} [Field K] [NumberField K] [IsCMField K] {n : ℕ} {π π' : CuspSub K n} {σ : ℂ ≃+* ℂ}
    (hc : π.IsCsd) (h : Sep σ π.finPart π'.finPart) (h' : Sep σ.symm π'.finPart π.finPart) :
    Sep (RingEquiv.refl ℂ) π'.finPart (thetaSub π').finPart ∧ Sep (RingEquiv.refl ℂ) (thetaSub π').finPart π'.finPart := by
  obtain ⟨T, hT⟩ := hc
  have h1 := Sep.of_equiv (ρ := π.finPart.comp (thetaGL n (cFin K))) (ρ' := π.finPart) T fun g v => hT (.fin g) v
  have h2 := Sep.of_equiv (ρ := π'.finPart.comp (thetaGL n (cFin K))) (ρ' := (thetaSub π').finPart)
    ((pull K n).submoduleMap π'.V) fun g v => Subtype.ext (act_pull (.fin g) v.1).symm
  have e : σ.symm.trans σ = RingEquiv.refl ℂ := σ.symm_trans_self
  exact ⟨e ▸ ((h'.trans h1.2).trans (h.comp _)).trans h2.1, e ▸ ((h2.2.trans (h'.comp _)).trans h1.1).trans h⟩
end UpperTheory.V.Af
open UpperTheory.V.Af in
theorem UpperTheory.V.Af.conjK_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.ConjK := by
  intro P K _ _ _ n hn m hm M hM σ π ⟨hinf, hdual, hfix⟩
  obtain ⟨π', τ, τ', h1, h2, h3, h4⟩ := P.conjC K n (by omega) π (regAlg_of_infOf hm hinf) σ
  obtain ⟨hs, hs'⟩ := sep_of_conj h1 h2 h3
  have hfix' := hs.hasFixed hfix
  refine ⟨π', ⟨fun φ => ?_, ?_, hfix'⟩, fun w B hB => (hs.comp _).exists_hasSatGL (hs'.comp _) hB⟩
  · have e : σ.toRingHom.comp (σ.symm.toRingHom.comp φ) = φ := RingHom.ext fun x => σ.apply_symm_apply _
    exact e ▸ h4 _ _ (hinf _)
  · obtain ⟨ht, ht'⟩ := sep_theta (GlobalTheory.CsdBack.isCsd_of_paired P.litN.aut.fin K n π (P.litN.aut.gk K n π) hdual) hs hs'
    refine TConjKDualProof.dualIsConj_of_isCsd (P.litN.aut.gk K n π') (isCsd_of_iso (Quotient.exact
      (P.litN.aut.js.1.strong_multiplicity_one (by omega) (CG.mk (thetaSub π')) (CG.mk π') (by
        refine (eventually_notMem hM).mono fun w hw => ?_
        obtain ⟨B, hB⟩ := _root_.UpperTheory.V.Af.satake_k_of_printed_results P K n M π' hfix' w hw
        exact ⟨B, (ht.comp _).hasSatGL_refl (ht'.comp _) hB, hB⟩))))
end

end
end

section




section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
noncomputable section
open Polynomial Pointwise
namespace GlobalTheory.Ord2.SrcForm
open TwDet
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]
theorem exists_rep_alt (P : _root_.UpperTheory.V.Af.Hypotheses') [IsAlgClosure ℚ Ω] {k : ℕ} (hk : 2 ≤ k) (f : Newform k) (ι : Qbar l ≃+* ℂ) (W : R2 Ω l) (j : ℤ)
    (hf : f.Att ι (tw W (cycBar ℚ Ω l ^ j))) :
    ∃ π : TR.CuspSub ℚ 2, π.IsRegAlg ∧ AttR ι W π ∧ ∀ᶠ w : Pl in Filter.cofinite, ∃ Bs, π.HasSat w Bs ∧
      ((algSat 2 (normV w) Bs).map fun b => X - C ((normV w : ℂ) ^ (-j) * b)).prod = f.heckePoly (normV w) := by
  have hl : Fact l.Prime := inferInstance
  obtain ⟨π, hinf, hsat⟩ := P.newform k hk f (-j)
  refine ⟨π, fun v => ⟨_, hinf v, ?_, ?_⟩, ⟨ss_of_tw _ _ hf.1, ?_⟩, ?_⟩
  · simp only [Multiset.insert_eq_cons, Multiset.nodup_cons, Multiset.mem_singleton, Multiset.nodup_singleton, and_true]
    intro h
    have h1 : (k : ℂ) = 1 := by linear_combination h
    have h2 : k = 1 := by exact_mod_cast h1
    omega
  · intro z hz
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact ⟨-j, by push_cast; ring⟩
    · exact ⟨1 - k - j, by push_cast; ring⟩
  · filter_upwards [hf.2, ev_not_mem l hl.out.ne_zero, ev_not_mem f.M f.pos.ne'] with w hw hwl hwM
    obtain ⟨B, hB, hpoly⟩ := hsat w (not_dvd_of_not_mem hwM)
    refine ⟨B, hB, fun A hA => ⟨fun s hs => ?_, fun σ hσ => ?_⟩⟩
    · have h1 := (hw A hA).1 s hs
      have h2 : cycZ ℚ Ω l s = 1 := by
        refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
        rw [cycZ_toZModPow_eq (v := w) (σ := s) hwl hA (q := 1) (fun x hx => by simpa only [pow_one] using hs.2 x hx) n]
        simp
      have h3 : (cycBar ℚ Ω l ^ j) s = 1 := by
        rw [MonoidHom.zpow_apply, cycBar, MonoidHom.comp_apply, h2, map_one, one_zpow]
      apply Units.ext
      have h4 := congrArg Units.val h1
      rwa [tw_val, h3, Units.val_one, one_smul] at h4
    · have h1 := (hw A hA).2 σ hσ
      rw [tw_val, ← hpoly] at h1
      refine scale_charpoly ι.toRingHom _ _ (Units.ne_zero ((cycBar ℚ Ω l ^ j) σ⁻¹)) _ ?_
      rw [h1]
      have h2 : ((cycBar ℚ Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ) := by
        change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _
        rw [cycZ_of_isFrob hwl hA hσ, map_natCast, map_natCast]
      have h3 : ι.toRingHom (((cycBar ℚ Ω l ^ j) σ⁻¹ : (Qbar l)ˣ) : Qbar l) = (normV w : ℂ) ^ (-j) := by
        rw [MonoidHom.zpow_apply, map_inv, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, h2, map_zpow₀,
          map_inv₀, map_natCast, inv_zpow']
      rw [h3]
  · filter_upwards [ev_not_mem f.M f.pos.ne'] with w hwM
    exact hsat w (not_dvd_of_not_mem hwM)
end GlobalTheory.Ord2.SrcForm
namespace GlobalTheory.Ord2
open TwDet SrcForm
end GlobalTheory.Ord2
end
end
end
end

section




section
open NumberField UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
theorem UpperTheory.Gal.SV.quad_base_change_w_of_printed_results (_P : _root_.UpperTheory.V.Af.Hypotheses') : UpperTheory.V.Br.QuadBCw := by
  intro F E _ _ _ _ _ _ _ h2 a ha2 _ π hr
  obtain rfl := ha2.out
  exact (UpperTheory.ConvolutionTheory.R2.quadBC2 F E h2 π hr).imp_right fun ⟨P, hP⟩ => ⟨P, UpperTheory.V.Br.IsBCw.of_isBC hP⟩
end
end
