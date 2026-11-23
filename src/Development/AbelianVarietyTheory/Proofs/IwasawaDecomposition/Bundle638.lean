module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsGenericComponentPointsOffMeagre
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle070
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle108
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsClosedEmbeddingOfAffine
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle100
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle625
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle626
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle428
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle035
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle013
public import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle011
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

namespace GlobalTheory.FrameLiftAt


open Topology Filter Metric in
theorem exists_selection {X Y : Type} [MetricSpace X] [PseudoMetricSpace Y] (R : X → Y → Prop) (B : Set X)
    (b₀ : X) (x₀ : Y) (hB : B ∈ 𝓝 b₀) (h0 : R b₀ x₀) (hne : ∀ b ∈ B, ∃ x, R b x)
    (hl : ∀ V ∈ 𝓝 x₀, ∀ᶠ b in 𝓝 b₀, ∃ x ∈ V, R b x) :
    ∃ f : X → Y, (∀ b ∈ B, R b (f b)) ∧ ContinuousAt f b₀ := by
  have key : ∀ b, ∃ x, (b ∈ B → R b x ∧ dist x₀ x ≤ infDist x₀ {x | R b x} + dist b b₀) ∧ (b = b₀ → x = x₀) := by
    intro b
    by_cases hb : b = b₀
    · subst hb
      exact ⟨x₀, fun _ => ⟨h0, by rw [dist_self, dist_self, add_zero]; exact infDist_nonneg⟩, fun _ => rfl⟩
    by_cases hbB : b ∈ B
    · have hp : 0 < dist b b₀ := dist_pos.2 hb
      obtain ⟨x, hx, hd⟩ := (infDist_lt_iff (x := x₀) (s := {x | R b x})
        (r := infDist x₀ {x | R b x} + dist b b₀) (hne b hbB)).1 (by linarith)
      exact ⟨x, fun _ => ⟨hx, hd.le⟩, fun h => absurd h hb⟩
    · exact ⟨x₀, fun h => absurd h hbB, fun _ => rfl⟩
  choose f hf hf0 using key
  refine ⟨f, fun b hb => (hf b hb).1, ?_⟩
  rw [ContinuousAt, hf0 b₀ rfl, Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hB, hl _ (ball_mem_nhds x₀ (half_pos hε)), ball_mem_nhds b₀ (half_pos hε)] with b hb hx hbb
  obtain ⟨x, hx, hR⟩ := hx
  have h1 := (hf b hb).2
  have h2 : infDist x₀ {x | R b x} ≤ dist x₀ x := infDist_le_dist_of_mem hR
  rw [mem_ball] at hx hbb
  rw [dist_comm] at hx ⊢
  linarith


open Topology Filter GlobalTheory.GenericFrames in
theorem exists_frame_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : _root_.GlobalTheory.FrameUnif.ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), Formalism.L2.PjFree.GoodEmb c σ → ModelBase M → NegXi M → ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → ((F.Di k).La →+ (Fin g → ℂ))), IsOpen B → IsHolPeriods (F.Di k) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) B P → ∀ b₀ ∈ B, ∃ x : (Fin m → ℂ) → (Fin T.m → ℂ), (∀ b ∈ B, x b ∈ T.co ⁻¹' (M.X k).dom ∧ T.Pf (T.co (x b)) = P b) ∧ ContinuousAt x b₀ := by
  intro E _ _ _ H Dw l Xo c σ g e F r M k T hσ hM hN m B P hB hP b₀ hb₀
  obtain ⟨idx, hper, -, honto⟩ := dictionary c σ e (F.Di k) (M.X k) (M.φ k) hσ (F.sig _).1 (F.sig _).2 hM.rank
    (hM.type k).1 (hM.type k).2 (hM.ef k) (fun _ => hN k)
  choose! x₁ hx₁ hr₁ using fun b (hb : b ∈ B) => honto (P b) (hP.1 b hb)
  have hBn : ∀ᶠ b in 𝓝 b₀, b ∈ B := hB.mem_nhds hb₀
  have hPf : ∀ (x : Frame (M.X k).Ψ r) b,
      (∀ a j, pc (M.X k) x (M.φ k a : Fin r → E) (idx j).1 (idx j).2 = P b a j) → T.Pf x = P b := by
    intro x b h
    ext a j
    rw [T.per, hper, h]
  have key := GlobalTheory.PeriodLift.period_lift E r (M.X k) _ (𝓝 b₀) (x₁ b₀) x₁ (hx₁ b₀ hb₀) (hBn.mono hx₁)
    (fun v hv τ i => by
      obtain ⟨a, rfl⟩ : ∃ a, (M.φ k a : Fin r → E) = v := ⟨(M.φ k).symm ⟨v, hv⟩, by simp⟩
      obtain ⟨j, hj⟩ := idx.surjective (τ, i)
      obtain ⟨rfl, rfl⟩ : τ = (idx j).1 ∧ i = (idx j).2 := by rw [hj]; exact ⟨rfl, rfl⟩
      change Tendsto (fun b => pc (M.X k) (x₁ b) (M.φ k a) _ _) _ (𝓝 (pc (M.X k) (x₁ b₀) (M.φ k a) _ _))
      rw [hr₁ b₀ hb₀]
      have hc : ContinuousAt (fun b => P b a j) b₀ :=
        (continuous_apply j).continuousAt.comp ((hP.2 a).continuousOn.continuousAt hBn)
      exact hc.tendsto.congr' (hBn.mono fun b hb => (hr₁ b hb a j).symm))
  refine exists_selection (fun b x => x ∈ T.co ⁻¹' (M.X k).dom ∧ T.Pf (T.co x) = P b) B b₀ (T.co.symm (x₁ b₀)) hBn
    ⟨by simpa using hx₁ b₀ hb₀, by rw [T.co.apply_symm_apply]; exact hPf _ _ (hr₁ b₀ hb₀)⟩
    (fun b hb => ⟨T.co.symm (x₁ b), by simpa using hx₁ b hb,
      by rw [T.co.apply_symm_apply]; exact hPf _ _ (hr₁ b hb)⟩) fun V hV => ?_
  have hV' : T.co.symm ⁻¹' V ∩ (M.X k).dom ∈ 𝓝 (x₁ b₀) :=
    inter_mem (T.co.symm.continuous.continuousAt hV) ((FourierCoefficientDomain.isOpen_dom (M.X k)).mem_nhds (hx₁ b₀ hb₀))
  filter_upwards [hBn, key _ hV'] with b hb hx
  obtain ⟨x, ⟨hxV, hxd⟩, hxx⟩ := hx
  refine ⟨T.co.symm x, hxV, by simpa using hxd, ?_⟩
  rw [T.co.apply_symm_apply]
  exact hPf _ _ fun a j => (hxx _ _ _).trans (hr₁ b hb a j)

end GlobalTheory.FrameLiftAt
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam GlobalTheory.ShFam.BdArc
  Filter Topology
open scoped CategoryTheory.MonObj CategoryTheory.Obj
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.PeriodSpan GlobalTheory.Points GlobalTheory.IntegralPower

namespace GlobalTheory.TorusCocompact

theorem exists_isCompact_surjOn {V H : Type} [NormedAddCommGroup V] [ProperSpace V] [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [CompactSpace H] [T2Space H] (φ : V → H) (hφ : ∀ z w, φ (z + w) = φ z * φ w)
    (hs : Function.Surjective φ) (hc : Continuous φ) : ∃ C : Set V, IsCompact C ∧ ∀ z, ∃ c ∈ C, φ (z - c) = 1 := by
  let ψ : V →+ Additive H := AddMonoidHom.mk' (fun z => Additive.ofMul (φ z)) hφ
  have : BaireSpace (Additive H) := inferInstanceAs (BaireSpace H)
  have : T2Space (Additive H) := inferInstanceAs (T2Space H)
  have ho : IsOpenMap φ := AddMonoidHom.isOpenMap_of_sigmaCompact ψ hs hc
  obtain ⟨n, hn⟩ := isCompact_univ.elim_directed_cover (fun n : ℕ => φ '' Metric.ball 0 n)
    (fun n => ho _ Metric.isOpen_ball) (fun h _ => by
      obtain ⟨z, rfl⟩ := hs h
      obtain ⟨n, hn⟩ := exists_nat_gt ‖z‖
      exact Set.mem_iUnion.2 ⟨n, z, by simpa using hn, rfl⟩)
    (Monotone.directed_le fun m n h => Set.image_mono (Metric.ball_subset_ball (Nat.cast_le.2 h)))
  refine ⟨Metric.closedBall 0 n, isCompact_closedBall _ _, fun z => ?_⟩
  obtain ⟨c, hc, hcz⟩ := hn (Set.mem_univ (φ z))
  refine ⟨c, Metric.ball_subset_closedBall hc, ?_⟩
  have h := hφ (z - c) c
  rw [sub_add_cancel, hcz] at h
  exact (mul_eq_right.1 h.symm)

theorem exists_lift_point {A B : Over (Sp ℂ)} (q : A ⟶ B) [Surjective q.left] [LocallyOfFiniteType q.left]
    (w : Over.mk (𝟙 (Sp ℂ)) ⟶ B) : ∃ u : Over.mk (𝟙 (Sp ℂ)) ⟶ A, u ≫ q = w := by
  let w' : Sp ℂ ⟶ B.left := w.left
  obtain ⟨z, -⟩ := (pullback.snd q.left w').surjective (IsLocalRing.closedPoint ℂ)
  obtain ⟨x, hx, -⟩ := GlobalTheory.ComplexPoints.exists_point_mem (pullback.snd q.left w') isClosed_univ.isLocallyClosed
    ⟨z, trivial⟩
  have h : (x ≫ pullback.fst q.left w') ≫ q.left = w' := by
    rw [Category.assoc, pullback.condition, reassoc_of% hx]
  refine ⟨Over.homMk (x ≫ pullback.fst q.left w') ?_, Over.OverMorphism.ext h⟩
  rw [← Over.w q, ← Category.assoc]
  exact (congrArg (· ≫ B.hom) h).trans (Over.w w)

section Fibre

variable {X : Scheme.{0}} {G : Over X} {y : Sp ℂ ⟶ X}

def fibrePt (x : Over.mk y ⟶ G) : Over.mk (𝟙 (Sp ℂ)) ⟶ (Over.pullback y).obj G :=
  Over.homMk (pullback.lift x.left (𝟙 (Sp ℂ)) ((Over.w x).trans (Category.id_comp y).symm))
    (pullback.lift_snd _ _ _)

theorem fibrePt_fst (x : Over.mk y ⟶ G) : (fibrePt x).left ≫ pullback.fst G.hom y = x.left :=
  pullback.lift_fst _ _ _

theorem fibre_ext {u v : Over.mk (𝟙 (Sp ℂ)) ⟶ (Over.pullback y).obj G}
    (h : u.left ≫ pullback.fst G.hom y = v.left ≫ pullback.fst G.hom y) : u = v :=
  Over.OverMorphism.ext (pullback.hom_ext h ((Over.w u).trans (Over.w v).symm))

theorem fibrePt_surjective : Function.Surjective (fibrePt (G := G) (y := y)) := fun u =>
  ⟨Over.homMk (u.left ≫ pullback.fst G.hom y) (by
    have h : u.left ≫ pullback.snd G.hom y = 𝟙 _ := Over.w u
    rw [Category.assoc, pullback.condition, reassoc_of% h]
    rfl), fibre_ext (fibrePt_fst _)⟩

theorem fibrePt_mul [GrpObj G] (a b : Over.mk y ⟶ G) : fibrePt (a * b) = fibrePt a * fibrePt b := by
  let U : Over.mk ((Over.mk (𝟙 (Sp ℂ))).hom ≫ y) ⟶ Over.mk y := Over.homMk (𝟙 (Sp ℂ)) rfl
  have hU : ∀ x : Over.mk y ⟶ G, (U ≫ x).left = x.left := fun x => Category.id_comp _
  refine fibre_ext ?_
  rw [fibrePt_fst, ← (isGrpPullback_pullback G y).2 _ (fibrePt a) (fibrePt b) (U ≫ a) (U ≫ b)
    ((hU a).trans (fibrePt_fst a).symm) ((hU b).trans (fibrePt_fst b).symm), ← comp_mul, hU]

theorem continuous_fibrePt {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (e : V → (Over.mk y ⟶ G))
    (he : IsHolTo Set.univ (fun z => (e z).left)) :
    Continuous fun z => leftPt (𝟙 (Sp ℂ)) (fibrePt (e z)) := by
  have h1 : Continuous fun z => leftPt y (e z) := by
    refine GlobalTheory.Points.continuous_iff.2 fun U => ⟨?_, fun f => ?_⟩
    · simpa using (he U 0).1
    · exact (he U f).2.continuousOn.mono fun _ hb => ⟨trivial, hb⟩
  refine (isEmbedding_of_isPullback (C := ℂ) (IsPullback.of_hasPullback G.hom y)).continuous_iff.2 ?_
  refine (h1.prodMk (continuous_const (y := 𝟙 (Sp ℂ)))).congr fun z => ?_
  exact Prod.ext (fibrePt_fst (e z)).symm (Over.w (fibrePt (e z))).symm

end Fibre


attribute [local instance] ptTopology in
theorem exists_isCompact_mod_torusPts : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (y : Sp ℂ ⟶ X) (g : ℕ)
    (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) (E : TorusExtension ((Over.pullback y).obj G)), IsSemiAbelian G →
    (∀ z w, e (z + w) = e z * e w) → Function.Surjective e → IsHolTo Set.univ (fun z => (e z).left) →
    (∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
      ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left) →
    ∃ C : Set (Fin g → ℂ), IsCompact C ∧ ∀ z, ∃ c ∈ C, e (z - c) ∈ torusPts G y E := by
  intro X G _ y g e E hG hadd hsurj hhol _
  let := E.addCommGroup
  let := E.grpB
  have := E.q_hom
  have := E.q_surjective
  have := E.isAbelian.proper
  have := hG.smooth
  have : LocallyOfFiniteType (E.q.left ≫ E.B.hom) := by
    rw [Over.w E.q]
    exact inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom y))
  have : LocallyOfFiniteType E.q.left := locallyOfFiniteType_of_comp _ E.B.hom
  have : CompactSpace (PtsOver E.B.hom (𝟙 (Sp ℂ))) := GlobalTheory.ProperPoints.compactSpace_pts E.B.hom
  have := compactSpace_of_ptsOver (𝟙 (Sp ℂ)) E.B
  have : IsTopologicalGroup (Over.mk (𝟙 (Sp ℂ)) ⟶ E.B) := by
    exact { continuous_mul := (continuous_comp_over _ (μ[E.B])).comp (continuous_lift _ E.B E.B)
            continuous_inv := continuous_comp_over _ (GrpObj.inv (X := E.B)) }
  have : T2Space (Over.mk (𝟙 (Sp ℂ)) ⟶ E.B) :=
    have := PtsOver.t2Space E.B.hom (𝟙 (Sp ℂ))
    T2Space.of_injective_continuous (f := fun x => (⟨x.left, Over.w x⟩ : PtsOver E.B.hom (𝟙 (Sp ℂ))))
      (fun _ _ h => Over.OverMorphism.ext (congrArg Subtype.val h))
      ((isEmbedding_leftPt (𝟙 (Sp ℂ)) E.B).continuous.subtype_mk _)
  obtain ⟨C, hC, H⟩ := exists_isCompact_surjOn (fun z => fibrePt (e z) ≫ E.q)
    (fun z w => by rw [hadd, fibrePt_mul, mul_comp])
    (fun w => by
      obtain ⟨u, rfl⟩ := exists_lift_point E.q w
      obtain ⟨x, rfl⟩ := fibrePt_surjective u
      obtain ⟨z, rfl⟩ := hsurj x
      exact ⟨z, rfl⟩)
    ((continuous_comp_over _ E.q).comp ((isEmbedding_leftPt _ _).continuous_iff.2 (continuous_fibrePt e hhol)))
  refine ⟨C, hC, fun z => ?_⟩
  obtain ⟨c, hc, hz⟩ := H z
  refine ⟨c, hc, E.isKernel.lift (fibrePt (e (z - c))) (toUnit _) hz, ?_⟩
  rw [IsPullback.lift_fst]
  exact fibrePt_fst _

end GlobalTheory.TorusCocompact
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Hor.LogCh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh

open ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows (isDerivAt0_comp_hom isDerivAt0_unique)
open GlobalTheory.TrueCx.TorFrHolo (isDerivAt0_of_cart isHolTo_lift)

section Push

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) {g : ℕ}
  {ty : Fin g → (E →+* ℂ)} {σ₀ : KA l →+* ℂ} (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n)
  (P : (Fu.Di i).La →+ (Fin g → ℂ))

theorem isHolTo_ex_fixed (hP : IsPeriod (Fu.Di i) ty P) : IsHolTo Set.univ fun z => (Fu.ex i P z).left := by
  have h1 := (Fu.hol i 0 Set.univ (fun _ => P) isOpen_univ
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
  exact GlobalTheory.LocLift.isHolTo_comp h1 isOpen_univ (β := fun z => ((0 : Fin 0 → ℂ), z)) (by fun_prop)
    fun _ _ => ⟨trivial, trivial⟩

theorem isHolTo_liftEx (hP : IsPeriod (Fu.Di i) ty P)
    (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) :
    IsHolTo Set.univ fun z => liftEx Z Fu y i P hu z ≫ Z.m.φ := by
  have h1 := (Fu.hol i 0 Set.univ (fun _ => P) isOpen_univ
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
  have h2 := isHolTo_lift Z.m0.toSABMap.cart.1 isOpen_univ (fun _ z => (Fu.ex i P z).left) (fun _ => y) h1
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.ThetaHol.isHolTo_const y) (fun _ z => by rw [Over.w (Fu.ex i P z), ← hu]; rfl)
  have h3 := ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp h2 Z.m.φ
  exact GlobalTheory.LocLift.isHolTo_comp h3 isOpen_univ (β := fun z => ((0 : Fin 0 → ℂ), z)) (by fun_prop)
    fun _ _ => ⟨trivial, trivial⟩

theorem isDerivAt0_liftEx (hP : IsPeriod (Fu.Di i) ty P)
    (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
    {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left}
    (hv : v ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y)
    (hd : IsDerivAt0 (fun z => (Fu.ex i P z).left) w (v ≫ Z.m0.toSABMap.φ)) :
    IsDerivAt0 (liftEx Z Fu y i P hu) w v :=
  isDerivAt0_of_cart Z.m0.toSABMap.cart.1 y (fun z => liftEx_snd Z Fu y i P hu z)
    (by simpa only [liftEx_fst] using isHolTo_ex_fixed Fu i P hP) hv
    (by simpa only [liftEx_fst] using hd)

theorem isDerivAt0_ex_of_push (hP : IsPeriod (Fu.Di i) ty P)
    (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
    {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left}
    (hv : v ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y)
    (hd : IsDerivAt0 (fun z => liftEx Z Fu y i P hu z ≫ Z.m.φ) w (v ≫ Z.m.φ)) :
    IsDerivAt0 (fun z => (Fu.ex i P z).left) w (v ≫ Z.m0.toSABMap.φ) := by
  have h := isDerivAt0_comp_hom (isDerivAt0_of_cart Z.m.cart.1 y (fun z => liftEx_snd Z Fu y i P hu z)
    (isHolTo_liftEx Z Fu y i P hP hu) hv hd) Z.m0.toSABMap.φ
  simpa only [liftEx_fst] using h

end Push

theorem isExpAt_pushEx : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (σ₀ : KA l →+* ℂ) (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X) (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p), IsPeriod (Fu.Di i) ty P → IsExpAt Z.t p (pushEx Z Fu y i P p hu hp) := by
  intro E _ _ _ H Dw l Xo c O _ β Z g ty σ₀ Fu y i P p hu hp hP
  subst hp
  obtain ⟨t1, t2, t3⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo σ₀ g ty Fu i P hP
  refine ⟨fun a b => ?_, fun w => ?_, fun v hv => ?_⟩
  · let L : (Fin g → ℂ) → (Over.mk y ⟶ Z.oF.t.G) := fun z =>
      Over.homMk (liftEx Z Fu y i P hu z) (liftEx_snd Z Fu y i P hu z)
    have hL : (L (a + b)).left = (L a * L b).left := by
      refine Z.m0.toSABMap.cart.1.hom_ext ?_ ?_
      · have e1 := Z.m0.toSABMap.cart.2 (Over.mk y) (L a) (L b) (pushPt Z.m0.toSABMap.cart.1.w (L a))
          (pushPt Z.m0.toSABMap.cart.1.w (L b)) rfl rfl
        refine Eq.trans ?_ e1
        refine (liftEx_fst Z Fu y i P hu (a + b)).trans ?_
        rw [Fu.ex_add i P hP]
        exact mul_left_congr hu _ _ _ _ (liftEx_fst Z Fu y i P hu a).symm (liftEx_fst Z Fu y i P hu b).symm
      · rw [Over.w, Over.w]
    refine Over.OverMorphism.ext ?_
    have e2 := Z.m.cart.2 (Over.mk y) (L a) (L b) (pushEx Z Fu y i P _ hu rfl a) (pushEx Z Fu y i P _ hu rfl b) rfl rfl
    refine Eq.trans ?_ e2.symm
    exact congrArg (· ≫ Z.m.φ) hL
  · obtain ⟨v, hv, -⟩ := t2 w
    have ht := t1 w v hv
    obtain ⟨v', k1, rfl⟩ := GlobalTheory.ShFam.OpenReg.exists_lift Z.m0.toSABMap (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) v
      (by rw [ht.1, hu, Category.assoc])
    refine ⟨v' ≫ Z.m.φ, ⟨(GlobalTheory.ShFam.OpenReg.tan_iff Z.m rfl k1).2
      ((GlobalTheory.ShFam.OpenReg.tan_iff Z.m0.toSABMap hu.symm k1).1 ht),
      isDerivAt0_comp_hom (isDerivAt0_liftEx Z Fu y i P hP hu k1 hv) Z.m.φ⟩, fun v₂ hv₂ => ?_⟩
    exact isDerivAt0_unique hv₂.2 (isDerivAt0_comp_hom (isDerivAt0_liftEx Z Fu y i P hP hu k1 hv) Z.m.φ)
  · obtain ⟨v', k1, rfl⟩ := GlobalTheory.ShFam.OpenReg.exists_lift Z.m (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) v
      (by rw [hv.1, Category.assoc])
    have h1 := (GlobalTheory.ShFam.OpenReg.tan_iff Z.m rfl k1).1 hv
    have h2 := (GlobalTheory.ShFam.OpenReg.tan_iff Z.m0.toSABMap hu.symm k1).2 h1
    obtain ⟨w, hw, hw'⟩ := t3 _ h2
    exact ⟨w, isDerivAt0_comp_hom (isDerivAt0_liftEx Z Fu y i P hP hu k1 hw) Z.m.φ,
      fun w' h' => hw' w' (isDerivAt0_ex_of_push Z Fu y i P hP hu k1 h')⟩

end GlobalTheory.ShFam.Hor.LogCh
end
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LineNorm.Chart

open ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet

section Alg

theorem exists_minor_ne_zero {K : Type} [Field K] {m g k : ℕ} (a : Fin m → Fin g → K) (ha : LinearIndependent K a)
    (hk : k ≤ m) : ∃ s, minor a hk s ≠ 0 := by
  classical
  let M : Matrix (Fin k) (Fin g) K := Matrix.of fun l i => a (Fin.castLE hk l) i
  have hM : LinearIndependent K M.row := ha.comp _ (Fin.castLE_injective hk)
  obtain ⟨κ, b, hb, hsp, hli⟩ := exists_linearIndependent' K M.col
  have : Finite κ := Finite.of_injective b hb
  let : Fintype κ := Fintype.ofFinite κ
  have hκ : Fintype.card κ = k := by
    rw [← finrank_span_eq_card hli, hsp]
    exact (Matrix.finrank_span_range_col M).trans (hM.rank_matrix.trans (Fintype.card_fin k))
  let e : Fin k ≃ κ := (Fintype.equivFinOfCardEq hκ).symm
  have h1 : LinearIndependent K (M.submatrix id (b ∘ e)).col := hli.comp e e.injective
  exact ⟨b ∘ e, ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_cols_iff_isUnit.1 h1)).ne_zero⟩

theorem map_minor {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {m g k : ℕ} (a : Fin m → Fin g → R)
    (hk : k ≤ m) (s : Fin k → Fin g) : φ (minor a hk s) = minor (fun l i => φ (a l i)) hk s := by
  rw [minor, RingHom.map_det]; rfl

end Alg

section Tan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X}

theorem dual_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (φ : R →+* S) (ψ : S →+* T) {Z : Scheme.{0}}
    (v : Sp (DualNumber R) ⟶ Z) :
    spMap (dualMap ψ) ≫ spMap (dualMap φ) ≫ v = spMap (dualMap (ψ.comp φ)) ≫ v := by
  rw [← Category.assoc, spMap_comp']
  congr 2
  refine RingHom.ext fun z => ?_
  ext <;> simp [dualMap]

variable {R : Type} [CommRing R] {x : Sp R ⟶ X} {m g : ℕ}

theorem comb_iff {u : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} (hu : ∀ l, IsTanAtG t x (u l)) (a : Fin m → R)
    (w : Sp (DualNumber R) ⟶ t.G.left) :
    IsCombAtG t x u a w ↔ w = (tv (∑ l, a l • tanOf (hu l))).left := by
  have h0 : IsCombAtG t x u a (tv (∑ l, a l • tanOf (hu l))).left := (isComb_iff (fun l => tanOf (hu l)) a _).2 rfl
  refine ⟨fun h => ?_, fun h => h ▸ h0⟩
  exact ((isCombAtG_iff t x (fun j => ovT (hu j)) a _).1 h).symm.trans
    ((isCombAtG_iff t x (fun j => ovT (hu j)) a _).1 h0)

theorem comb_tan {u : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} (hu : ∀ l, IsTanAtG t x (u l)) {a : Fin m → R}
    {w : Sp (DualNumber R) ⟶ t.G.left} (h : IsCombAtG t x u a w) : IsTanAtG t x w :=
  (comb_iff hu a w).1 h ▸ isTan_tv _

theorem sum_comb {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (he : ∀ i, IsTanAtG t x (e i))
    {u : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} (hu : ∀ l, IsTanAtG t x (u l)) {a : Fin m → Fin g → R}
    (ha : ∀ l, IsCombAtG t x e (a l) (u l)) (c : Fin m → R) :
    ∑ l, c l • tanOf (hu l) = ∑ i, (∑ l, c l • a l) i • tanOf (he i) := by
  have h : ∀ l, tanOf (hu l) = ∑ i, a l i • tanOf (he i) := fun l => tan_ext ((comb_iff he _ _).1 (ha l))
  simp only [h, Finset.smul_sum, Finset.sum_apply, Finset.sum_smul, Pi.smul_apply, smul_smul, smul_eq_mul]
  exact Finset.sum_comm

theorem comb_comb {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (he : ∀ i, IsTanAtG t x (e i))
    {u : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} {a : Fin m → Fin g → R}
    (ha : ∀ l, IsCombAtG t x e (a l) (u l)) {c : Fin m → R} {w : Sp (DualNumber R) ⟶ t.G.left}
    (hw : IsCombAtG t x u c w) : IsCombAtG t x e (∑ l, c l • a l) w := by
  have hu := fun l => comb_tan he (ha l)
  rw [comb_iff he, ← sum_comb he hu ha]
  exact (comb_iff hu _ _).1 hw

end Tan

section Geo

theorem ringHom_ext {S : Scheme.{0}} {V : S.Opens} (hV : IsAffineOpen V) {R : Type} [CommRing R]
    {φ φ' : Γ(S, V) →+* R} (h : spMap φ ≫ hV.fromSpec = spMap φ' ≫ hV.fromSpec) : φ = φ' :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 h))

variable {F : Type} [Field F] [NumberField F] {Y : Var F}


end Geo

section Coord

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {A : Type} [CommRing A] {x₀ : Sp A ⟶ X} {g m : ℕ} {e : Fin g → (Sp (DualNumber A) ⟶ t.G.left)}

theorem coord_map {R S : Type} [CommRing R] [CommRing S] (α : A →+* R) (ψ : R →+* S) {a : Fin g → R}
    {w : Sp (DualNumber R) ⟶ t.G.left}
    (h : IsCombAtG t (spMap α ≫ x₀) (fun i => spMap (dualMap α) ≫ e i) a w) :
    IsCombAtG t (spMap (ψ.comp α) ≫ x₀) (fun i => spMap (dualMap (ψ.comp α)) ≫ e i) (fun i => ψ (a i))
      (spMap (dualMap ψ) ≫ w) := by
  have := GlobalTheory.LatDRFree.comb_map t ψ h
  simp only [dual_comp] at this
  rwa [← Category.assoc, spMap_comp'] at this

end Coord

end GlobalTheory.LineNorm.Chart

end
