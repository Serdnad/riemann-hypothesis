module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle056
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle281
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueLevelCharacterArgumentAtTypePlace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle223
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle003
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.MixPer.semiMeas_isMulLeftInvariant {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (N : Subgroup G) (s : H →* G) (hN : IsClosed (N : Set G)) (hs : Continuous s)
    (hnorm : ∀ n ∈ N, ∀ h, s h * n * (s h)⁻¹ ∈ N)
    (_hp : ∃ p : (N ⊔ s.range : Subgroup G) → H, Continuous p ∧ ∀ (h : H) (n : N),
      p ⟨n.1 * s h, mul_mem (Subgroup.mem_sup_left n.2) (Subgroup.mem_sup_right ⟨h, rfl⟩)⟩ = h)
    (μ : Measure H) (ν : Measure N) (hμ : μ.IsHaarMeasure) (hν : ν.IsHaarMeasure)
    (hc : ∀ h, ν.map (fun n : N => s h * n.1 * (s h)⁻¹) = ν.map Subtype.val) :
    (semiMeas N s μ ν).IsMulLeftInvariant := by
  have := hμ
  have := hν
  have : LocallyCompactSpace N := hN.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set G)
  have : SigmaCompactSpace N := sigmaCompactSpace_of_locallyCompact_secondCountable
  have : SigmaFinite ν := inferInstance
  have : SigmaFinite μ := inferInstance
  have hemb : MeasurableEmbedding (Subtype.val : N → G) :=
    MeasurableEmbedding.subtype_coe hN.measurableSet

  let φ : H × N → (N ⊔ s.range : Subgroup G) := fun p =>
    ⟨p.2.1 * s p.1, mul_mem (Subgroup.mem_sup_left p.2.2) (Subgroup.mem_sup_right ⟨p.1, rfl⟩)⟩
  have hφ : Measurable φ :=
    (Continuous.subtype_mk ((continuous_subtype_val.comp continuous_snd).mul
      (hs.comp continuous_fst)) _).measurable
  have hm : semiMeas N s μ ν = (μ.prod ν).map φ := rfl

  let T : Subgroup G :=
    { carrier := {g | ∃ hg : g ∈ N ⊔ s.range,
        (semiMeas N s μ ν).map (fun x => (⟨g, hg⟩ : (N ⊔ s.range : Subgroup G)) * x) =
          semiMeas N s μ ν}
      one_mem' := by
        refine ⟨one_mem _, ?_⟩
        have e : (fun x : (N ⊔ s.range : Subgroup G) =>
            (⟨1, one_mem _⟩ : (N ⊔ s.range : Subgroup G)) * x) = id := funext fun x => one_mul x
        rw [e, Measure.map_id]
      mul_mem' := by
        rintro a b ⟨ha, ea⟩ ⟨hb, eb⟩
        refine ⟨mul_mem ha hb, ?_⟩
        have e : (fun x : (N ⊔ s.range : Subgroup G) =>
            (⟨a * b, mul_mem ha hb⟩ : (N ⊔ s.range : Subgroup G)) * x) =
            (fun x => (⟨a, ha⟩ : (N ⊔ s.range : Subgroup G)) * x) ∘
              (fun x => (⟨b, hb⟩ : (N ⊔ s.range : Subgroup G)) * x) :=
          funext fun x => mul_assoc (⟨a, ha⟩ : (N ⊔ s.range : Subgroup G)) ⟨b, hb⟩ x
        rw [e, ← Measure.map_map (measurable_const_mul _) (measurable_const_mul _), eb, ea]
      inv_mem' := by
        rintro a ⟨ha, ea⟩
        refine ⟨inv_mem ha, ?_⟩
        conv_lhs => rw [← ea]
        rw [Measure.map_map (measurable_const_mul _) (measurable_const_mul _)]
        have e : ((fun x : (N ⊔ s.range : Subgroup G) =>
            (⟨a⁻¹, inv_mem ha⟩ : (N ⊔ s.range : Subgroup G)) * x) ∘
              (fun x => (⟨a, ha⟩ : (N ⊔ s.range : Subgroup G)) * x)) = id :=
          funext fun x => inv_mul_cancel_left (⟨a, ha⟩ : (N ⊔ s.range : Subgroup G)) x
        rw [e, Measure.map_id] }

  have hNT : N ≤ T := by
    intro n hn
    refine ⟨Subgroup.mem_sup_left hn, ?_⟩
    have e : (fun x : (N ⊔ s.range : Subgroup G) =>
        (⟨n, Subgroup.mem_sup_left hn⟩ : (N ⊔ s.range : Subgroup G)) * x) ∘ φ =
        φ ∘ Prod.map id (fun m : N => (⟨n, hn⟩ : N) * m) := by
      funext p
      apply Subtype.ext
      simp [φ, mul_assoc]
    rw [hm, Measure.map_map (measurable_const_mul _) hφ, e,
      ← Measure.map_map hφ (measurable_id.prodMap (measurable_const_mul _)),
      ← Measure.map_prod_map μ ν measurable_id (measurable_const_mul _), Measure.map_id,
      map_mul_left_eq_self]

  have hST : s.range ≤ T := by
    rintro _ ⟨h₀, rfl⟩
    refine ⟨Subgroup.mem_sup_right ⟨h₀, rfl⟩, ?_⟩
    let c : N → N := fun m => ⟨s h₀ * m.1 * (s h₀)⁻¹, hnorm m.1 m.2 h₀⟩
    have hcm : Measurable c :=
      (Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const)
        _).measurable
    have hcν : ν.map c = ν := by
      rw [← hemb.comap_map (ν.map c), Measure.map_map hemb.measurable hcm]
      have e : (Subtype.val ∘ c) = (fun m : N => s h₀ * m.1 * (s h₀)⁻¹) := rfl
      rw [e, hc h₀, hemb.comap_map]
    have e : (fun x : (N ⊔ s.range : Subgroup G) =>
        (⟨s h₀, Subgroup.mem_sup_right ⟨h₀, rfl⟩⟩ : (N ⊔ s.range : Subgroup G)) * x) ∘ φ =
        φ ∘ Prod.map (fun h => h₀ * h) c := by
      funext p
      apply Subtype.ext
      simp [φ, c, mul_assoc]
    rw [hm, Measure.map_map (measurable_const_mul _) hφ, e,
      ← Measure.map_map hφ ((measurable_const_mul _).prodMap hcm),
      ← Measure.map_prod_map μ ν (measurable_const_mul _) hcm, hcν, map_mul_left_eq_self]
  have hT : N ⊔ s.range ≤ T := sup_le hNT hST
  exact ⟨fun k => by
    obtain ⟨hk, ek⟩ := hT k.2
    exact ek⟩
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CosToCoset

open GlobalTheory.FunObj.Comparison₂ GlobalTheory.StdFrames

variable {D : D7}

theorem prod_eq_inf (P : Finset (Pl D.host.E)) (d : Pl D.host.E → ℕ) :
    (∏ w ∈ P, w.asIdeal ^ d w) = P.inf fun w => w.asIdeal ^ d w :=
  (HeightOneSpectrum.inf_pow_eq_prod _ _ _ fun _ _ _ _ hne h => hne h).symm

theorem prod_ne_bot (P : Finset (Pl D.host.E)) (d : Pl D.host.E → ℕ) :
    (∏ w ∈ P, w.asIdeal ^ d w) ≠ ⊥ := by
  rw [← Ideal.zero_eq_bot]
  exact Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact w.ne_bot)

theorem idem_mem_OA {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) : toEAf D e ∈ OA D := by
  obtain ⟨-, e1, e2⟩ := cpt_idemSum he
  refine (mem_OA_iff _).2 fun w => ?_
  by_cases hw : w ∈ P
  · rw [e1 w hw]; exact one_mem _
  · rw [e2 w hw]; exact zero_mem _

theorem one_sub_idem_mem {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) (d : Pl D.host.E → ℕ) :
    (1 - ⟨toEAf D e, idem_mem_OA he⟩ : OA D) ∈ idS D.host.F (∏ w ∈ P, w.asIdeal ^ d w) := by
  obtain ⟨-, e1, -⟩ := cpt_idemSum he
  refine mem_idS_of_v_le (w := fun w => w) (prod_ne_bot P d) (prod_eq_inf P d) fun w hw => ?_
  show Valued.v (cpt (D := D) w (1 - toEAf D e)) ≤ _
  rw [RingHom.map_sub, RingHom.map_one, e1 w hw, sub_self, Valuation.map_zero]
  exact zero_le'

end GlobalTheory.CosToCoset

namespace GlobalTheory.CosToCoset

open GlobalTheory.FunObj.Comparison₂ GlobalTheory.StdFrames

variable {D : D7} {S T : GlobalTheory.Grid.Node D} {e : AE D} {x : WO S.V T.V}

theorem half_map (hx : IsHalf e x) : x.map (toEAf D) = toEAf D e • x.map (toEAf D) :=
  Matrix.ext fun i j => by
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← RingHom.map_mul, hx i j]

theorem fr_half (hx : IsHalf e x) (i : Fin T.V.rank) (j : Fin S.V.rank) :
    fr T.β S.β (x.map (toEAf D)) i j = toEAf D e * fr T.β S.β (x.map (toEAf D)) i j := by
  have h1 : fr T.β S.β (x.map (toEAf D)) i j = fr T.β S.β (toEAf D e • x.map (toEAf D)) i j := by
    rw [← half_map hx]
  rw [fr_smul, Matrix.smul_apply, smul_eq_mul] at h1
  exact h1

variable {S T : GlobalTheory.Grid.Node D}

theorem frMapO_eq_fr (x : WO S.V T.V) : frMapO S.V T.V S.β T.β x = fr T.β S.β (x.map (toEAf D)) := by
  unfold frMapO fr
  rfl

end GlobalTheory.CosToCoset

namespace GlobalTheory.CosToCoset

theorem alg_one {R : Type} [CommRing R] {s t A A' X Y E eS : R} (hs : s = E * (X - Y)) (ht : t = Y - A') (ha : A = A')
    (he : eS = E) (hx : X = E * X) : s + eS * t - (1 - eS) * A + A = X := by
  subst hs ht ha he
  linear_combination -hx

theorem alg_two {R : Type} [CommRing R] {s t A X eS : R} (h : s + eS * t - (1 - eS) * A + A = X) :
    X - A = s + eS * t - (1 - eS) * A := by
  rw [← h]; ring

end GlobalTheory.CosToCoset

namespace GlobalTheory.CosToCoset

open GlobalTheory.FunObj.Comparison₂ GlobalTheory.StdFrames

variable {D : D7} {S T : GlobalTheory.Grid.Node D} {e : AE D} {x : WO S.V T.V}

theorem half_sub (hx : IsHalf e x) (y : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E) (i : Fin T.V.rank)
    (j : Fin S.V.rank) : (x - e • y.map (incA D)) i j = e * (x i j - incA D (y i j)) := by
  rw [mul_sub, hx]; rfl

theorem fr_half_sub (hx : IsHalf e x) (y : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E) (i : Fin T.V.rank)
    (j : Fin S.V.rank) : fr T.β S.β ((x - e • y.map (incA D)).map (toEAf D)) i j =
      toEAf D e * (fr T.β S.β (x.map (toEAf D)) i j - fr T.β S.β (y.map (eToEAf D)) i j) := by
  have h : (x - e • y.map (incA D)).map (toEAf D) = toEAf D e • (x.map (toEAf D) - y.map (eToEAf D)) :=
    Matrix.ext fun i j => by rw [Matrix.map_apply, half_sub hx, RingHom.map_mul, RingHom.map_sub]; rfl
  rw [h, fr_smul, fr_sub]; rfl

theorem sub_mem_hatMx {P : Finset (Pl D.host.E)} {I : Ideal (𝓞 D.host.E)} (hS : IsFrame S.β S.Λ) (hT : IsFrame T.β T.Λ)
    (he : IsIdemSum e P) (x₀ : homLat S.Λ T.Λ) (a : Fin T.V.rank → Fin S.V.rank → OA D)
    (ha : ∀ i j, (a i j).1 = fr T.β S.β (x₀.1.map (eToEAf D)) i j) (hx : IsHalf e x)
    (h : ∀ i j, ∃ hX : frMapO S.V T.V S.β T.β x i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      (⟨_, hX⟩ : OA D) - a i j ∈ idS D.host.F I) :
    x - e • (x₀.1 : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E).map (incA D) ∈ hatMx (I • homLat S.Λ T.Λ) := by
  obtain ⟨e0, -, -⟩ := cpt_idemSum he
  refine (mem_hatMx_iff hS hT _ _).2 ⟨fun i j => by rw [half_sub hx, RingHom.map_mul, e0, zero_mul], fun i j => ?_⟩
  obtain ⟨hX, h'⟩ := h i j
  refine ⟨⟨toEAf D e, idem_mem_OA he⟩ * (⟨_, hX⟩ - a i j), Ideal.mul_mem_left _ _ h', ?_⟩
  refine Eq.trans ?_ (fr_half_sub hx x₀.1 i j).symm
  exact congrArg (toEAf D e * ·) (congrArg₂ (· - ·) rfl (ha i j))

end GlobalTheory.CosToCoset

namespace GlobalTheory.CosToCoset

open GlobalTheory.FunObj.Comparison₂ GlobalTheory.StdFrames

variable {D : D7} {S T : GlobalTheory.Grid.Node D} {e : AE D} {x : WO S.V T.V}



theorem frMapO_sub_mem {I : Ideal (𝓞 D.host.E)} (hS : IsFrame S.β S.Λ) (hT : IsFrame T.β T.Λ) (eS : OA D)
    (heS : eS.1 = toEAf D e) (he1 : 1 - eS ∈ idS D.host.F I)
    (x₀ : homLat S.Λ T.Λ) (a : Fin T.V.rank → Fin S.V.rank → OA D)
    (ha : ∀ i j, (a i j).1 = fr T.β S.β (x₀.1.map (eToEAf D)) i j) (hx : IsHalf e x) (y : homLat S.Λ T.Λ)
    (hyx : y.1 - x₀.1 ∈ I • homLat S.Λ T.Λ)
    (hz : x - e • (y.1 : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E).map (incA D) ∈ hatMx (I • homLat S.Λ T.Λ))
    (i : Fin T.V.rank) (j : Fin S.V.rank) : ∃ hX : frMapO S.V T.V S.β T.β x i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      (⟨_, hX⟩ : OA D) - a i j ∈ idS D.host.F I := by
  obtain ⟨s, hs, hs'⟩ := ((mem_hatMx_iff hS hT _ _).1 hz).2 i j
  obtain ⟨t, ht, ht'⟩ := fr_mem_idS hS hT hyx i j
  have hs'' := hs'.trans (fr_half_sub hx y.1 i j)
  have hyA : t.1 = fr T.β S.β (y.1.map (eToEAf D)) i j - fr T.β S.β (x₀.1.map (eToEAf D)) i j := by
    rw [ht', Matrix.map_sub _ (RingHom.map_sub _), fr_sub, Matrix.sub_apply]
  have hz0 : s.1 + eS.1 * t.1 - (1 - eS.1) * (a i j).1 + (a i j).1 = fr T.β S.β (x.map (toEAf D)) i j :=
    alg_one hs'' hyA (ha i j) heS (fr_half hx i j)
  have hX : frMapO S.V T.V S.β T.β x i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    have hz1 : ((s + eS * t - (1 - eS) * a i j + a i j : OA D) : EAf D) = fr T.β S.β (x.map (toEAf D)) i j := by
      simp only [AddSubgroupClass.coe_sub, AddMemClass.coe_add, MulMemClass.coe_mul, OneMemClass.coe_one]
      exact hz0
    rw [frMapO_eq_fr, ← hz1]
    exact (s + eS * t - (1 - eS) * a i j + a i j).2
  refine ⟨hX, ?_⟩
  have : (⟨_, hX⟩ : OA D) - a i j = s + eS * t - (1 - eS) * a i j := by
    apply Subtype.ext
    simp only [AddSubgroupClass.coe_sub, AddMemClass.coe_add, MulMemClass.coe_mul, OneMemClass.coe_one]
    rw [frMapO_eq_fr]
    exact alg_two hz0
  rw [this]
  exact sub_mem (add_mem hs (Ideal.mul_mem_left _ _ ht)) (Ideal.mul_mem_right _ _ he1)

end GlobalTheory.CosToCoset

namespace GlobalTheory.CosToCoset

open GlobalTheory.FunObj.Comparison₂ GlobalTheory.StdFrames

variable {D : D7} {S T : GlobalTheory.Grid.Node D} {e : AE D}



theorem cosetInd_eq_of {P : Finset (Pl D.host.E)} {I : Ideal (𝓞 D.host.E)} (hS : IsFrame S.β S.Λ)
    (hT : IsFrame T.β T.Λ) (he : IsIdemSum e P) (he1 : (1 - ⟨toEAf D e, idem_mem_OA he⟩ : OA D) ∈ idS D.host.F I)
    (κ : Cos S.Λ T.Λ I) (x₀ : homLat S.Λ T.Λ) (hx₀ : Cos.mk I x₀ = κ) (a : Fin T.V.rank → Fin S.V.rank → OA D)
    (ha : ∀ i j, (a i j).1 = fr T.β S.β (x₀.1.map (eToEAf D)) i j) (c : Coset S T I)
    (hc : ∀ i j, cmpS D.host.F I (c i j) = Ideal.Quotient.mk (idS D.host.F I) (a i j)) :
    cosetInd S T e I c = cosInd e κ := by
  funext x
  have key : IsHalf e x → (InCosetOf S T I c x ↔ ∃ y : homLat S.Λ T.Λ, Cos.mk I y = κ ∧
      x - e • (y.1 : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E).map (incA D) ∈ hatMx (I • homLat S.Λ T.Λ)) := by
    intro hx
    have hq : ∀ i j (hX : frMapO S.V T.V S.β T.β x i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E),
        Ideal.Quotient.mk (idS D.host.F I) ⟨_, hX⟩ = cmpS D.host.F I (c i j) ↔ (⟨_, hX⟩ : OA D) - a i j ∈ idS D.host.F I :=
      fun i j hX => by rw [hc i j, Ideal.Quotient.eq]
    constructor
    · intro h
      exact ⟨x₀, hx₀, sub_mem_hatMx hS hT he x₀ a ha hx fun i j => ⟨(h i j).1, (hq i j _).1 (h i j).2⟩⟩
    · rintro ⟨y, hy, hz⟩ i j
      obtain ⟨hX, h'⟩ := frMapO_sub_mem hS hT _ rfl he1 x₀ a ha hx y (sub_mem_of_mk_eq (hy.trans hx₀.symm)) hz i j
      exact ⟨hX, (hq i j hX).2 h'⟩
  have hiff : (IsHalf e x ∧ InCosetOf S T I c x) ↔ x ∈ cosSet e κ :=
    ⟨fun ⟨h1, h2⟩ => ⟨h1, (key h1).1 h2⟩, fun ⟨h1, h2⟩ => ⟨h1, (key h1).2 h2⟩⟩
  unfold GlobalTheory.Grid.cosetInd GlobalTheory.ChiGrid.cosInd
  by_cases h : x ∈ cosSet e κ
  · rw [if_pos (hiff.2 h), Set.indicator_of_mem h]; rfl
  · rw [if_neg (fun h' => h (hiff.1 h')), Set.indicator_of_notMem h]

theorem cosInd_eq_cosetInd : ∀ {D : D7} (S T : GlobalTheory.Grid.Node D) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (d : Formalism.L2.DIV.Pl D.host.E → ℕ), Formalism.L2.DIV.IsFrame S.β S.Λ → Formalism.L2.DIV.IsFrame T.β T.Λ → IsIdemSum e P → ∀ κ : GlobalTheory.ChiGrid.Cos S.Λ T.Λ (∏ w ∈ P, w.asIdeal ^ d w), ∃ c : GlobalTheory.Grid.Coset S T (∏ w ∈ P, w.asIdeal ^ d w), GlobalTheory.Grid.cosetInd S T e (∏ w ∈ P, w.asIdeal ^ d w) c = GlobalTheory.ChiGrid.cosInd e κ := by
  intro D S T e P d hS hT he κ
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : homLat S.Λ T.Λ, Cos.mk (∏ w ∈ P, w.asIdeal ^ d w) x₀ = κ :=
    Submodule.Quotient.mk_surjective _ κ
  have hA : ∀ i j, ∃ s : OA D, s.1 = fr T.β S.β (x₀.1.map (eToEAf D)) i j := fun i j => by
    obtain ⟨s, -, hs⟩ := fr_mem_idS hS hT (𝔪 := ⊤) (y := x₀.1) (by rw [Submodule.top_smul]; exact x₀.2) i j
    exact ⟨s, hs⟩
  choose a ha using hA
  choose c hc using fun i j => cmpS_surj (F := D.host.F) _ (prod_ne_bot P d)
    (Ideal.Quotient.mk (idS D.host.F (∏ w ∈ P, w.asIdeal ^ d w)) (a i j))
  exact ⟨fun i j => c i j, cosetInd_eq_of hS hT he (one_sub_idem_mem he d) κ x₀ hx₀ a ha _ fun i j => hc i j⟩

end GlobalTheory.CosToCoset
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DerBracket

open GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem bracket_mem_lieAt {τ : D.what₂.Tau} {X Y : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (hY : Y ∈ lieAt V τ) : X * Y - Y * X ∈ lieAt V τ := by

  have hX0 : Xᴴ * gramAt D V τ + gramAt D V τ * X = 0 := hX
  have hY0 : Yᴴ * gramAt D V τ + gramAt D V τ * Y = 0 := hY
  have hX' : Xᴴ * gramAt D V τ = -(gramAt D V τ * X) := eq_neg_of_add_eq_zero_left hX0
  have hY' : Yᴴ * gramAt D V τ = -(gramAt D V τ * Y) := eq_neg_of_add_eq_zero_left hY0
  have e1 : Yᴴ * Xᴴ * gramAt D V τ = gramAt D V τ * Y * X := by
    rw [Matrix.mul_assoc Yᴴ Xᴴ, hX', Matrix.mul_neg, ← Matrix.mul_assoc Yᴴ, hY', Matrix.neg_mul, neg_neg]
  have e2 : Xᴴ * Yᴴ * gramAt D V τ = gramAt D V τ * X * Y := by
    rw [Matrix.mul_assoc Xᴴ Yᴴ, hY', Matrix.mul_neg, ← Matrix.mul_assoc Xᴴ, hX', Matrix.neg_mul, neg_neg]
  show (X * Y - Y * X)ᴴ * gramAt D V τ + gramAt D V τ * (X * Y - Y * X) = 0
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, Matrix.sub_mul, e1, e2]
  noncomm_ring

private theorem mem_smF_of_mem_smFun (R : GlobalTheory.SmoothForms.RealPoints θ V) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) :
    φ ∈ GlobalTheory.SmoothForms.SmF θ V :=
  (GlobalTheory.SmoothForms.isSmoothInf_iff φ).1 ((GlobalTheory.SmoothForms.smooth_iff R φ).1 hφ)

private theorem rder_eq_opInf_atPlace (R : GlobalTheory.SmoothForms.RealPoints θ V) (τ : D.what₂.Tau) (X : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ)
    (ψ : GlobalTheory.SmoothForms.SmF θ V) :
    Rder θ V τ X.1 ψ.1 = (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ X) ψ).1 := by
  rw [GlobalTheory.SmoothForms.opInf_coe]
  exact GlobalTheory.SmoothForms.Rder_eq R τ X ψ.1

theorem Rder_bracket (hθ : IsInfFam θ) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) {τ : D.what₂.Tau}
    {X Y : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) (hY : Y ∈ lieAt V τ) :
    Rder θ V τ X (Rder θ V τ Y φ) = Rder θ V τ Y (Rder θ V τ X φ) + Rder θ V τ (X * Y - Y * X) φ := by

  have R : GlobalTheory.SmoothForms.RealPoints θ V := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  have hXY := bracket_mem_lieAt hX hY
  set ψ : GlobalTheory.SmoothForms.SmF θ V := ⟨φ, mem_smF_of_mem_smFun R hφ⟩ with hψ
  set Xl : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ := ⟨X, (GlobalTheory.SmoothForms.mem_lieAt_iff τ X).1 hX⟩ with hXl
  set Yl : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ := ⟨Y, (GlobalTheory.SmoothForms.mem_lieAt_iff τ Y).1 hY⟩ with hYl
  set Zl : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ := ⟨X * Y - Y * X, (GlobalTheory.SmoothForms.mem_lieAt_iff τ _).1 hXY⟩ with hZl
  have e := GlobalTheory.SmoothForms.opAt_bracket R τ Xl Yl Zl rfl
  have a1 : Rder θ V τ Y φ = (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Yl) ψ).1 := rder_eq_opInf_atPlace R τ Yl ψ
  have a2 : Rder θ V τ X φ = (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Xl) ψ).1 := rder_eq_opInf_atPlace R τ Xl ψ
  have a3 : Rder θ V τ X (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Yl) ψ).1 =
      (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Xl)
        (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Yl) ψ)).1 := rder_eq_opInf_atPlace R τ Xl _
  have a4 : Rder θ V τ Y (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Xl) ψ).1 =
      (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Yl)
        (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Xl) ψ)).1 := rder_eq_opInf_atPlace R τ Yl _
  have a5 : Rder θ V τ (X * Y - Y * X) φ = (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Zl) ψ).1 :=
    rder_eq_opInf_atPlace R τ Zl ψ
  rw [a1, a3, a2, a4, a5, e, LinearMap.sub_apply, Submodule.coe_sub]
  change _ = _ + ((GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Xl)
        (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Yl) ψ)).1 -
      (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Yl)
        (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Xl) ψ)).1)
  abel

theorem Rder_comm (hθ : IsInfFam θ) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) {τ τ' : D.what₂.Tau} (hτ : τ ≠ τ')
    {X Y : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) (hY : Y ∈ lieAt V τ') :
    Rder θ V τ X (Rder θ V τ' Y φ) = Rder θ V τ' Y (Rder θ V τ X φ) := by

  have R : GlobalTheory.SmoothForms.RealPoints θ V := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  set ψ : GlobalTheory.SmoothForms.SmF θ V := ⟨φ, mem_smF_of_mem_smFun R hφ⟩ with hψ
  set Xl : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ := ⟨X, (GlobalTheory.SmoothForms.mem_lieAt_iff τ X).1 hX⟩ with hXl
  set Yl : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ' := ⟨Y, (GlobalTheory.SmoothForms.mem_lieAt_iff τ' Y).1 hY⟩ with hYl
  have hc := (GlobalTheory.SmoothForms.opAt_comm R hτ Xl Yl).eq
  have a1 : Rder θ V τ' Y φ = (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ' Yl) ψ).1 := rder_eq_opInf_atPlace R τ' Yl ψ
  have a2 : Rder θ V τ X φ = (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Xl) ψ).1 := rder_eq_opInf_atPlace R τ Xl ψ
  rw [a1, a2, rder_eq_opInf_atPlace R τ Xl, rder_eq_opInf_atPlace R τ' Yl]
  exact congrArg Subtype.val (LinearMap.congr_fun hc ψ)

private theorem commutator_add_I_smul' {n : ℕ} (A B X : Matrix (Fin n) (Fin n) ℂ) :
    (A + Complex.I • B) * X - X * (A + Complex.I • B) = (A * X - X * A) + Complex.I • (B * X - X * B) := by
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_sub]
  abel

theorem RderC_Rder : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (τ τ' : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ), ∀ X ∈ lieAt V τ, ∀ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V, (RderC θ V τ Z (Rder θ V τ X φ) = Rder θ V τ X (RderC θ V τ Z φ) + RderC θ V τ (Z * X - X * Z) φ) ∧ (τ' ≠ τ → RderC θ V τ' Z (Rder θ V τ X φ) = Rder θ V τ X (RderC θ V τ' Z φ)) := by
  intro D θ hθ V τ τ' Z X hX φ hφ
  constructor
  ·
    obtain ⟨hA, hB⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
    have hZ := GlobalTheory.SmoothAutCheck.parts_sum V τ Z
    set A := (1 / 2 : ℂ) • (Z + conjAt V τ Z) with hAdef
    set B := (1 / (2 * Complex.I)) • (Z - conjAt V τ Z) with hBdef
    have hc := commutator_add_I_smul' A B X
    rw [hZ] at hc
    have hAX := bracket_mem_lieAt hA hX
    have hBX := bracket_mem_lieAt hB hX
    have e1 : RderC θ V τ (Z * X - X * Z) φ =
        Rder θ V τ (A * X - X * A) φ + Complex.I • Rder θ V τ (B * X - X * B) φ := by
      rw [hc, GlobalTheory.Mem.RealTranslate.RderC_add hθ hφ, GlobalTheory.Mem.RealTranslate.RderC_smul hθ hφ,
        GlobalTheory.SmoothAutCheck.RderC_eq θ V τ hAX, GlobalTheory.SmoothAutCheck.RderC_eq θ V τ hBX]
    rw [e1]
    show Rder θ V τ A (Rder θ V τ X φ) + Complex.I • Rder θ V τ B (Rder θ V τ X φ) =
      Rder θ V τ X (Rder θ V τ A φ + Complex.I • Rder θ V τ B φ) + _
    rw [Rder_bracket hθ hφ hA hX, Rder_bracket hθ hφ hB hX,
      Rder_add (Rder_mem hφ hA) ((SmFun θ V).smul_mem _ (Rder_mem hφ hB)) hX, Rder_smul]
    rw [smul_add]
    abel
  ·
    intro hne
    obtain ⟨hA, hB⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ' Z
    show Rder θ V τ' ((1 / 2 : ℂ) • (Z + conjAt V τ' Z)) (Rder θ V τ X φ) +
        Complex.I • Rder θ V τ' ((1 / (2 * Complex.I)) • (Z - conjAt V τ' Z)) (Rder θ V τ X φ) =
      Rder θ V τ X (Rder θ V τ' ((1 / 2 : ℂ) • (Z + conjAt V τ' Z)) φ +
        Complex.I • Rder θ V τ' ((1 / (2 * Complex.I)) • (Z - conjAt V τ' Z)) φ)
    rw [Rder_add (Rder_mem hφ hA) ((SmFun θ V).smul_mem _ (Rder_mem hφ hB)) hX, Rder_smul,
      Rder_comm hθ hφ hne hA hX, Rder_comm hθ hφ hne hB hX]

end GlobalTheory.DerBracket

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead


theorem _root_.GlobalTheory.T.residue_levelCharacterArgument_at_typePlace : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ β : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → (∀ PP ∈ R.Pg, RedIs β PP (flagAt X h PP)) → ∀ PP ∈ R.Pg, ∀ κ : GA D (Yc D 0), finE (Yc D 0) κ ∈ St β → GlobalTheory.SeeConjChar.resT PP (GlobalTheory.SeeConjChar.argT X h (finE (Yc D 0) κ)) = ∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then ((GlobalTheory.SeeConjChar.wA D.R.rS D.R.k (GlobalTheory.SeeConjChar.sideAt X h PP) i j : ℤ) : kP PP) * ((upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) : GL (Fin D.R.r) (kP PP)).val i j) else 0 := by
  first | exact @GlobalTheory.SeeResAt.resT_argT | exact GlobalTheory.SeeResAt.resT_argT | (intros; apply GlobalTheory.SeeResAt.resT_argT <;> assumption)
end
