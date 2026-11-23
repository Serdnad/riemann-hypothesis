module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1434
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1435
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1432
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1433
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralEqSumSmallerLevel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import GroundTheory.GlobalFields.Bundle001
public import GroundTheory.LocalFields.PadicLogSeries
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1436
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1464
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle093
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle077
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open scoped Classical TensorProduct

namespace GlobalTheory.BCT

theorem exists_ne_zero_of_avg_ne_zero {H : Type} [Group H] (u : H → ℂ) (h : avg u ≠ 0) : ∃ k, u k ≠ 0 := by
  by_contra hc
  push Not at hc
  exact h (by simp [avg, hc])

theorem exists_ne_zero_of_twOrb_ne_zero {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G)
    (f : G → ℂ) (h : twOrb θ K δ f ≠ 0) : ∃ x, f (x⁻¹ * δ * θ x) ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h
  unfold twOrb
  simp only [hc]
  simp [avg]

theorem exists_ne_zero_of_clSum_ne_zero {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G)
    (S : Set G) (wt f : G → ℂ) (h : clSum θ K S wt f ≠ 0) : ∃ δ ∈ S, ∃ x, f (x⁻¹ * δ * θ x) ≠ 0 := by
  by_contra hc
  apply h
  unfold clSum
  refine finsum_eq_zero_of_forall_eq_zero fun c => ?_
  split_ifs with hS
  · by_contra hne
    exact hc ⟨c.rep, hS, exists_ne_zero_of_twOrb_ne_zero θ K c.rep f (right_ne_zero_of_mul hne)⟩
  · rfl

theorem nrmL_twConj {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (δ x : GLw n w) :
    nrmL n w (x⁻¹ * δ * thL n w x) = x⁻¹ * nrmL n w δ * x := by
  have hinv := TwistInvol.thL_involutive E n w x
  unfold nrmL
  unfold thL at hinv ⊢
  split_ifs at hinv ⊢ with hs
  · simp
  · simp only [map_mul, map_inv, hinv]
    group

end GlobalTheory.BCT
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.compactPart_centralizer_le_conj_integralUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E)
    (P₀ : (w.adicCompletionIntegers E)[X]), IsCoprime P₀ (derivative P₀) →
    ∀ γ : UL n w, γ.1.val.charpoly = P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) →
    ∀ g : UL n w, g⁻¹ * γ * g ∈ KL n w →
    cptPart (twCent (MonoidHom.id (UL n w)) γ) ≤ (KL n w).map (MulAut.conj g).toMonoidHom := by
  first | exact @GlobalTheory.CptCent.cptPart_le_conj_KL | exact GlobalTheory.CptCent.cptPart_le_conj_KL | (intros; apply GlobalTheory.CptCent.cptPart_le_conj_KL <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.SplitConj

theorem exists_conj_of_isSplitAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∀ P ∈ Ell E n,
    ∀ w : Pl E, IsSplitAt w → ∀ γ γ' : UL n w, γ.1.val.charpoly = atPl w P → γ'.1.val.charpoly = atPl w P →
      ∃ g : UL n w, γ' = g⁻¹ * γ * g := by
  intro E _ _ _ n P hP w hw γ γ' h h'
  have hs : (atPl w P).Separable := hP.2.2.1.map
  obtain ⟨g, hg⟩ := GlobalTheory.BCT.ClsFin.conj_of_charpoly γ.1 γ'.1 (by rw [h]; exact hs) (h.trans h'.symm)
  have hmem : g ∈ UL n w := by
    rw [UL, if_pos hw]
    exact Subgroup.mem_top g
  exact ⟨⟨g, hmem⟩, Subtype.ext hg⟩

end GlobalTheory.BCT.SplitConj
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

theorem _root_.GlobalTheory.T.twistedOrbitalIntegral_eq_sum_smallerLevel : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G) (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → (∀ k ∈ K, θ k ∈ K) → ∀ K' : Subgroup G, IsLevel θ K K' → ∀ (δ : G) (f : G → ℂ), IsHecke K' f → (∀ x : G, twCent θ δ ⊓ K.map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent θ δ) ∧ (twCent θ δ ⊓ K'.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent θ δ)) ≠ 0) → {q : DoubleCoset.Quotient (twCent θ δ : Set G) (K' : Set G) | f ((Quotient.out q)⁻¹ * δ * θ (Quotient.out q)) ≠ 0}.Finite → twOrb θ K δ f = ((K'.relIndex K : ℕ) : ℂ)⁻¹ * twOrb θ K' δ f ∧ twOrb θ K' δ f = ∑ᶠ q : DoubleCoset.Quotient (twCent θ δ : Set G) (K' : Set G), (((twCent θ δ ⊓ K'.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex (cptPart (twCent θ δ)) : ℕ) : ℂ) * f ((Quotient.out q)⁻¹ * δ * θ (Quotient.out q)) := by
  first | exact @GlobalTheory.BCT.OrbLev.twOrb_eq_sum_smallerLevel | exact GlobalTheory.BCT.OrbLev.twOrb_eq_sum_smallerLevel | (intros; apply GlobalTheory.BCT.OrbLev.twOrb_eq_sum_smallerLevel <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open scoped Classical TensorProduct
open GlobalTheory.BCT

noncomputable section

namespace GlobalTheory.BCT.StTw2Add

section Generic

variable {G : Type} [Group G]

theorem twRel_equiv (θ : G →* G) : Equivalence fun x y : G => ∃ g, y = g⁻¹ * x * θ g := by
  refine ⟨fun x => ⟨1, by simp⟩, ?_, ?_⟩
  · rintro x y ⟨g, rfl⟩
    exact ⟨g⁻¹, by simp only [map_inv, inv_inv]; group⟩
  · rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
    exact ⟨g * h, by simp only [map_mul, mul_inv_rev]; group⟩

theorem twCl_eq_iff (θ : G →* G) (x y : G) :
    (Quot.mk _ x : TwCl θ) = Quot.mk _ y ↔ ∃ g, y = g⁻¹ * x * θ g :=
  ⟨fun h => (twRel_equiv θ).eqvGen_iff.1 (Quot.eqvGen_exact h), fun h => Quot.sound h⟩

theorem mk_rep (θ : G →* G) (c : TwCl θ) : (Quot.mk _ c.rep : TwCl θ) = c := Quot.out_eq c

theorem rep_mk_iff (θ : G →* G) (P : G → Prop) (hP : ∀ x g, P (g⁻¹ * x * θ g) ↔ P x) (x : G) :
    P (TwCl.rep (θ := θ) (Quot.mk _ x)) ↔ P x := by
  obtain ⟨g, hg⟩ := (twCl_eq_iff θ _ _).1 (mk_rep θ (Quot.mk _ x : TwCl θ))
  have h := hP (TwCl.rep (θ := θ) (Quot.mk _ x)) g
  rw [← hg] at h
  exact h.symm

variable [TopologicalSpace G]

variable {G₁ G₂ : Type} [Group G₁] [Group G₂]

theorem finite_prod (θ₁ : G₁ →* G₁) (θ₂ : G₂ →* G₂) (P₁ : G₁ → Prop) (P₂ : G₂ → Prop)
    (h₁ : ∀ x g, P₁ (g⁻¹ * x * θ₁ g) ↔ P₁ x) (h₂ : ∀ x g, P₂ (g⁻¹ * x * θ₂ g) ↔ P₂ x)
    (f₁ : {c : TwCl θ₁ | P₁ c.rep}.Finite) (f₂ : {c : TwCl θ₂ | P₂ c.rep}.Finite) :
    {c : TwCl (θ₁.prodMap θ₂) | P₁ c.rep.1 ∧ P₂ c.rep.2}.Finite := by
  refine Set.Finite.of_finite_image (f := fun c : TwCl (θ₁.prodMap θ₂) =>
    ((Quot.mk _ c.rep.1 : TwCl θ₁), (Quot.mk _ c.rep.2 : TwCl θ₂))) ((f₁.prod f₂).subset ?_) ?_
  · rintro _ ⟨c, hc, rfl⟩
    exact ⟨(rep_mk_iff θ₁ P₁ h₁ _).2 hc.1, (rep_mk_iff θ₂ P₂ h₂ _).2 hc.2⟩
  · intro c _ d _ hcd
    obtain ⟨g₁, hg₁⟩ := (twCl_eq_iff θ₁ _ _).1 (congrArg Prod.fst hcd)
    obtain ⟨g₂, hg₂⟩ := (twCl_eq_iff θ₂ _ _).1 (congrArg Prod.snd hcd)
    rw [← mk_rep _ c, ← mk_rep _ d]
    exact Quot.sound ⟨(g₁, g₂), Prod.ext hg₁ hg₂⟩

end Generic

section Local

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isOpen_isCompact_KK (a b : ℕ) (w : Pl E) :
    IsOpen (((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)) : Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w)) ∧
    IsCompact (((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)) : Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w)) := by
  rw [Subgroup.coe_prod]
  exact ⟨(GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1,
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2⟩

end Local

end GlobalTheory.BCT.StTw2Add
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ModAbs

theorem ordL_eq_ord {E : Type} [Field E] [NumberField E] (w : Pl E) {x : w.adicCompletion E} (hx : x ≠ 0) :
    ordL x = GroundTheory.LocalField.ord x := by
  have h2 := GroundTheory.Global.valued_eq_exp_neg_ord hx
  have hv : Valued.v x ≠ 0 := (Valued.v).ne_zero_iff.2 hx
  unfold ordL
  rw [dite_eq_right hv]
  have : WithZero.unzero hv = Multiplicative.ofAdd (-GroundTheory.LocalField.ord x) := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, h2]
    rfl
  rw [this, toAdd_ofAdd, neg_neg]

theorem haar_eq_absHalf_sq : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (x : w.adicCompletion E) (hx : x ≠ 0), (((MeasureTheory.distribHaarChar (w.adicCompletion E) (Units.mk0 x hx) : NNReal) : ℝ) : ℂ) = absHalf w x ^ 2 := by
  intro E _ _ w x hx
  have h1 := GroundTheory.LocalField.distribHaarChar_eq_modulus (K := w.adicCompletion E) (Units.mk0 x hx)
  have h3 : (GroundTheory.LocalField.residueCard (w.adicCompletion E)) = Ideal.absNorm w.asIdeal :=
    GroundTheory.Global.residueCard_adicCompletion
  rw [h1, Units.val_mk0, GroundTheory.LocalField.modulus_of_ne_zero hx, h3]
  unfold absHalf
  rw [ordL_eq_ord w hx]
  have hq : (0 : ℝ) ≤ ((qV E w : ℕ) : ℝ) ^ (-GroundTheory.LocalField.ord x) := zpow_nonneg (Nat.cast_nonneg _) _
  rw [← Complex.ofReal_pow, Real.sq_sqrt hq]
  simp [qV]

end GlobalTheory.ModAbs
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.adelicCongruence_selfDual_of_principalLattice : ∀ {D : D7} (V : HSp D) (K : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA D.host.F D.host.E)) (I : Ideal (𝓞 D.host.E)), (∀ z ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.Pj.latG V 1 : Set (Fin V.rank → D.host.E)), K *ᵥ z - z ∈ GlobalTheory.AdLat.hat D.host.F ((I • Formalism.L2.Pj.latG V 1 : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E))) → ∀ z ∈ GlobalTheory.AdLat.hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)), K *ᵥ z - z ∈ GlobalTheory.AdLat.hat D.host.F ((I • GlobalTheory.Member.latC V : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E)) := by
  first | exact @GlobalTheory.CovolCong.cong_latC_of_cong_latG | exact GlobalTheory.CovolCong.cong_latC_of_cong_latG | (intros; apply GlobalTheory.CovolCong.cong_latC_of_cong_latG <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.cocompact_normal_subgroup_descent_invariants : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [T2Space G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] (Γ N N' : Subgroup G) [DiscreteTopology Γ]
    [LocallyCompactSpace N] [LocallyCompactSpace N'], N' ≤ N → (∀ p ∈ N, ∀ m ∈ N', p * m * p⁻¹ ∈ N') →
    GlobalTheory.Cusp.Cocompact Γ N → GlobalTheory.Cusp.Cocompact Γ N' →
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V]
      [MeasurableSpace V] [BorelSpace V] (Λ : AddSubgroup V) (s : V → G) (π : N → V),
      Continuous s → (∀ v w, s (v + w) = s v * s w) → (∀ v, s v ∈ N) → Continuous π →
      (∀ a b : N, π (a * b) = π a + π b) → (∀ (a : N) (v : V), (a : G) = s v → π a = v) →
      (∀ a : N, π a = 0 ↔ (a : G) ∈ N') → (∀ v ∈ Λ, s v ∈ Γ) → (∀ a : N, (a : G) ∈ Γ → π a ∈ Λ) →
      ∀ φ : G → ℂ, GlobalTheory.AutomorphicL2Unitary.LeftInv Γ φ → Continuous φ → (∀ m ∈ N', ∀ g, φ (m * g) = φ g) →
      ∀ (μ : MeasureTheory.Measure V) (𝓕 : Set V), μ.IsAddHaarMeasure → MeasureTheory.IsAddFundamentalDomain Λ 𝓕 μ →
        ∀ x : G, ∫ v in 𝓕, φ (s v * x) ∂μ = μ.real 𝓕 • GlobalTheory.Cusp.constTermOn Γ N φ x := by
  first | exact @GlobalTheory.Cusp.Shear.integral_section_eq_constTermOn | exact GlobalTheory.Cusp.Shear.integral_section_eq_constTermOn | (intros; apply GlobalTheory.Cusp.Shear.integral_section_eq_constTermOn <;> assumption)
end

section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ResAniso.ResProp
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect

theorem absAU_ne_zero {D : D7} (u : (AE D)ˣ) : absA D u ≠ 0 := by
  intro h0
  have := congrArg (absA D) (mul_inv_cancel u)
  rw [map_mul, h0, zero_mul, map_one] at this
  exact zero_ne_one this

end GlobalTheory.ResAniso.ResProp
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

theorem _root_.GlobalTheory.T.principalFormsSubspace_eq_good_forms : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ i, (⨆ p, R.Wp3 i p) = LinearMap.range (eH R.toRealDat i)) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmA → Formalism.IndefR.Rat.LiftTest (R.toCx3 F) → (R.toCx3 F).zs.InBlock → ∀ i, principalFormsSubspace A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) i = Tw.sub (twAt D.what₂.embLL A3.A.v0) (LinearMap.range (eH R.toRealDat i)) := by
  first | exact @GlobalTheory.WgLift.principal_lift_forms_eq_good_forms | exact GlobalTheory.WgLift.principal_lift_forms_eq_good_forms | (intros; apply GlobalTheory.WgLift.principal_lift_forms_eq_good_forms <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.twistedConjugacyClasses_equiv_unitsModNorms_nonsplit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (a : ℕ) (Q : (w.adicCompletion E)[X]), Q.Monic → Q.natDegree = a → Q.Separable → ∀ (B : GlobalTheory.UnitLemma.InvAlg K), B.g * B.σ B.g = 1 → B.P = Q.map e.symm.toRingHom → ∀ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * ((-1) ^ (a - 1) * B.g) → ∃ F : B.Cl ≃ {c : TwCl (thL a w) // (nrmL a w c.rep).val.charpoly = Q}, ∀ k : B.Cl, ∃ b : Module.Basis (Fin a) K.E B.A, ∀ i j, (((F k).1.rep.val * GlobalTheory.Tw.Phi a (w.adicCompletion E))⁻¹)ᵀ i j = e (B.herm ((β₀ : B.A) * k.rep) (b i) (b j)) := by
  first | exact @GlobalTheory.TwClassForms.twCl_equiv_cl | exact GlobalTheory.TwClassForms.twCl_equiv_cl | (intros; apply GlobalTheory.TwClassForms.twCl_equiv_cl <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.unitLemma_unitary_group_every_residue_of_lie : UnitLemmaLie → ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → InvAlg.Identity B₁ B₂ := by
  first | exact @GlobalTheory.UnitLemma.OrbitAll.identity_of_lie | exact GlobalTheory.UnitLemma.OrbitAll.identity_of_lie | (intros; apply GlobalTheory.UnitLemma.OrbitAll.identity_of_lie <;> assumption)
end
