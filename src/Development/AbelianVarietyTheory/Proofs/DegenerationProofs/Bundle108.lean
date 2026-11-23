module

public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsClosedEmbeddingOfAffine
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLevelPoint
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsGTransport
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle089
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle010
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle038
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle054
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle103
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Topology Filter GlobalTheory.Points

namespace GlobalTheory.IntegralPower

theorem eventually_extends {V C : Type} [CommRing V] [IsLocalRing V] [CommRing C] [TopologicalSpace C]
    (σ : V →+* C) (hσ : Function.Injective σ) (ho : IsOpen (Set.range σ)) {X : Scheme.{0}} (q : X ⟶ Sp V)
    [LocallyOfFiniteType q] (y : Sp V ⟶ X) :
    ∀ᶠ x : Sp C ⟶ X in 𝓝 (spMap σ ≫ y), x ≫ q = spMap σ →
      ∃ z : Sp V ⟶ X, z ≫ q = 𝟙 _ ∧ spMap σ ≫ z = x := by
  obtain ⟨U, hU, hy, -⟩ := exists_isAffineOpen_le y (le_preimage_top _)
  have hy' : ⊤ ≤ (spMap σ ≫ y) ⁻¹ᵁ U := le_preimage_comp _ y hy (le_preimage_top _)
  let c : V →+* Γ(X, U) := (q.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom
  have hc : ∀ a, c a = constFn q U a := fun _ => rfl
  have hft : c.FiniteType := (q.finiteType_appLE (isAffineOpen_top _) hU le_top).comp
    (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of V)).inv).2)
  letI := c.toAlgebra
  obtain ⟨s, hs⟩ := (show Algebra.FiniteType V Γ(X, U) from hft).out
  have h1 : ∀ᶠ x : Sp C ⟶ X in 𝓝 (spMap σ ≫ y), ∀ f ∈ s, valR x U f ∈ Set.range σ := by
    refine (eventually_all_finset s).2 fun f _ => (continuousAt_valR f hy').eventually (ho.mem_nhds ?_)
    exact ⟨_, (valR_spMap_comp σ y U hy f).symm⟩
  filter_upwards [h1, (isOpen_setOf_le_preimage U).mem_nhds hy'] with x hx hxU hxq
  have h2 : ∀ f, (valMap x U hxU).hom f ∈ σ.range := by
    intro f
    have hf : f ∈ Algebra.adjoin V (s : Set Γ(X, U)) := hs ▸ Algebra.mem_top
    induction hf using Algebra.adjoin_induction with
    | mem f hf =>
      rw [← valR_eq]
      exact hx f hf
    | algebraMap a =>
      rw [← valR_eq]
      exact ⟨a, (valR_constFn_of_over q σ x hxq U hxU a).symm⟩
    | add f g _ _ hf hg =>
      rw [map_add (f := _)]
      exact add_mem hf hg
    | mul f g _ _ hf hg =>
      rw [map_mul]
      exact mul_mem hf hg
  let e : V ≃+* σ.range := RingEquiv.ofBijective σ.rangeRestrict
    ⟨fun a b h => hσ (congrArg Subtype.val h), σ.rangeRestrict_surjective⟩
  let ψ : Γ(X, U) →+* V := e.symm.toRingHom.comp ((valMap x U hxU).hom.codRestrict σ.range h2)
  have hψ : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom σ = valMap x U hxU := by
    ext f
    exact congrArg Subtype.val (e.apply_symm_apply ⟨_, h2 f⟩)
  have hz : spMap σ ≫ Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec = x := by
    rw [← Category.assoc, ← Spec.map_comp, hψ, specMap_valMap_fromSpec]
  refine ⟨_, ?_, hz⟩
  rw [← hz, Category.assoc] at hxq
  obtain ⟨φ, hφ⟩ := Spec.map_surjective ((Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec) ≫ q)
  rw [← hφ, ← Spec.map_comp] at hxq
  rw [← hφ, ← Spec.map_id]
  congr 1
  ext a
  exact hσ (congrArg (fun u => u.hom a) (Spec.map_injective hxq))

section Group

variable {C : Type} [CommRing C] [TopologicalSpace C] {S : Scheme.{0}} (t : Sp C ⟶ S)


omit [TopologicalSpace C] in
abbrev leftPt {A : Over S} (x : Over.mk t ⟶ A) : Sp C ⟶ A.left := x.left

abbrev ptTopology (A : Over S) : TopologicalSpace (Over.mk t ⟶ A) :=
  TopologicalSpace.induced (leftPt t) (topology C A.left)

attribute [local instance] ptTopology

theorem isEmbedding_leftPt (A : Over S) : IsEmbedding (leftPt t (A := A)) :=
  ⟨⟨rfl⟩, fun _ _ h => Over.OverMorphism.ext h⟩

theorem compactSpace_of_ptsOver (A : Over S) [CompactSpace (PtsOver A.hom t)] :
    CompactSpace (Over.mk t ⟶ A) :=
  Function.Surjective.compactSpace (f := fun x : PtsOver A.hom t => (Over.homMk x.1 x.2 : Over.mk t ⟶ A))
    ((isEmbedding_leftPt t A).continuous_iff.2 continuous_subtype_val) fun x => ⟨⟨x.left, Over.w x⟩, rfl⟩

theorem continuous_comp_over {A B : Over S} (g : A ⟶ B) : Continuous fun x : Over.mk t ⟶ A => x ≫ g :=
  (isEmbedding_leftPt t B).continuous_iff.2 ((continuous_comp g.left).comp (isEmbedding_leftPt t A).continuous)

variable [IsTopologicalRing C] [IsLocalRing C] [IsOpenUnits C]

theorem continuous_lift (A B : Over S) :
    Continuous fun q : (Over.mk t ⟶ A) × (Over.mk t ⟶ B) => lift q.1 q.2 := by
  refine (isEmbedding_leftPt t _).continuous_iff.2 ?_
  refine (isEmbedding_of_isPullback (C := C) (IsPullback.of_hasPullback A.hom B.hom)).continuous_iff.2 ?_
  refine ((isEmbedding_leftPt t A).continuous.prodMap (isEmbedding_leftPt t B).continuous).congr fun q => ?_
  exact Prod.ext (congrArg (·.left) (lift_fst q.1 q.2)).symm (congrArg (·.left) (lift_snd q.1 q.2)).symm

theorem isTopologicalGroup (G : Over S) [GrpObj G] : IsTopologicalGroup (Over.mk t ⟶ G) := {
  continuous_mul := (continuous_comp_over t (μ[G])).comp (continuous_lift t G G)
  toContinuousInv :=
    ⟨by simpa only [Hom.inv_def] using continuous_comp_over t (GrpObj.inv (X := G))⟩ }

end Group


attribute [local instance] ptTopology in
theorem exists_pow_extends {V F : Type} [CommRing V] [IsLocalRing V] [NormedField F] [ProperSpace F]
    (σ : V →+* F) (hσ : Function.Injective σ) (ho : IsOpen (Set.range σ)) (G : Over (Sp V)) [GrpObj G]
    [LocallyOfFiniteType G.hom] (h : IsProjOver (pullback.snd G.hom (spMap σ))) (a : Over.mk (spMap σ) ⟶ G) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ g : 𝟙_ (Over (Sp V)) ⟶ G, toUnit _ ≫ g = a ^ k := by
  have h1 : CompactSpace (Pts (pullback.snd G.hom (spMap σ))) := PtsOver.compactSpace h _
  have h2 := (PtsOver.baseChangeHomeomorph (IsPullback.of_hasPullback G.hom (spMap σ))).compactSpace
  have h3 := compactSpace_of_ptsOver (spMap σ) G
  have h4 := isTopologicalGroup (spMap σ) G
  let r : (𝟙_ (Over (Sp V)) ⟶ G) →* (Over.mk (spMap σ) ⟶ G) :=
    MonoidHom.mk' (fun g => toUnit _ ≫ g) fun g g' => comp_mul _ g g'
  have hr : ∀ g, leftPt _ (r g) = spMap σ ≫ g.left := fun g => by
    have : (toUnit (Over.mk (spMap σ))).left = spMap σ := (Category.comp_id _).symm.trans (Over.w (toUnit (Over.mk (spMap σ))))
    exact congrArg (· ≫ g.left) this
  have hopen : IsOpen (r.range : Set (Over.mk (spMap σ) ⟶ G)) := by
    refine r.range.isOpen_of_mem_nhds (g := r 1) ?_
    have h5 := eventually_extends σ hσ ho G.hom (1 : 𝟙_ (Over (Sp V)) ⟶ G).left
    rw [← hr] at h5
    filter_upwards [(isEmbedding_leftPt _ G).continuous.continuousAt.eventually h5] with x hx
    obtain ⟨z, hz, hzx⟩ := hx (Over.w x)
    exact ⟨Over.homMk z hz, (isEmbedding_leftPt _ G).injective ((hr _).trans hzx)⟩
  have h6 : Finite (_ ⧸ r.range) := r.range.quotient_finite_of_isOpen hopen
  obtain ⟨k, hk, -, g, hg⟩ := r.range.exists_pow_mem_of_index_ne_zero Subgroup.index_ne_zero_of_finite a
  exact ⟨k, hk, g, hg⟩

theorem exists_pow_integral : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] (G : Over (Sp (integralClosure ℤ_[p] K))) [GrpObj G] [LocallyOfFiniteType G.hom] [IsSeparated G.hom], IsProjOver (pullback.snd G.hom (spMap (algebraMap (integralClosure ℤ_[p] K) K))) → ∀ a : Over.mk (spMap (algebraMap (integralClosure ℤ_[p] K) K)) ⟶ G, ∃ k : ℕ, 1 ≤ k ∧ ∃ g : 𝟙_ (Over (Sp (integralClosure ℤ_[p] K))) ⟶ G, toUnit _ ≫ g = a ^ k := by
  intro p _ K _ G _ _ _ h a
  letI : NormedField K := inferInstanceAs (NormedField K.toSubfield)
  letI : NormedSpace ℚ_[p] K := ⟨fun c x => norm_smul_le c (x : PadicAlgCl p)⟩
  haveI : ProperSpace K := FiniteDimensional.proper ℚ_[p] K
  haveI : IsUltrametricDist K := ⟨fun x y z => IsUltrametricDist.dist_triangle_max (x : PadicAlgCl p) y z⟩
  refine exists_pow_extends _ Subtype.val_injective ?_ G h a
  convert IsUltrametricDist.isOpen_closedBall (0 : K) one_ne_zero using 1
  ext x
  rw [mem_closedBall_zero_iff]
  exact (Set.ext_iff.1 Subtype.range_val x).trans (mem_integralClosure_padicInt_iff K x)

end GlobalTheory.IntegralPower
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.IntegralSum
open GlobalTheory.FormalValue Filter Topology ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT

theorem gtφ_eq {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
    (b : TF (R := R) F ⟶ D.P.A) (χ : D.X) (k : Fin 4) : DegPre.gtφ D F b χ k = b.left ≫ D.Oφ (𝟙 D.P.A) χ k := by
  rw [comp_Oφ_id]
  have h : padd D.P.A (DegPre.cF D F χ) b = padd D.P.A b (DegPre.cF D F χ) := _root_.mul_comm (DegPre.cF D F χ) b
  have h' : DegPre.gtφ D F b χ = D.Oφ b χ := by
    unfold DegPre.gtφ DegPre.Oφ
    rw [h]
  rw [h']

theorem Oφ_over {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (χ : D.X) (k : Fin 4) :
    D.Oφ (𝟙 D.P.A) χ k ≫ D.P.A.hom = D.P.A.hom := by
  fin_cases k <;> exact Over.w _

theorem gs_scal {F : Type} [CommRing F] {Y : Scheme.{0}} (q : Y ⟶ Sp F) (r : Sp F ⟶ Y) (h : r ≫ q = 𝟙 _) (z : Sp F)
    (a : F) : gs r z ⊤ (scal q a) = toStkA z a :=
  (gs_pull r q z ⊤ trivial _).trans ((congrArg (fun t => gs t z ⊤ _) h).trans (gs_eq (𝟙 _) z ⊤ trivial _))

theorem toStkA_surj {F : Type} [Field F] (z : Sp F) : Function.Surjective (toStkA z) := by
  intro a
  obtain ⟨U, hU, s, rfl⟩ := (Sp F).presheaf.exists_germ_eq a
  obtain rfl : U = ⊤ := eq_top_iff.2 fun y _ => Subsingleton.elim (α := PrimeSpectrum F) z y ▸ hU
  obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 s
  exact ⟨x, congrArg ((Sp F).presheaf.germ ⊤ z trivial).hom hx⟩

theorem exists_toStkA_unit {F : Type} [Field F] (z : Sp F) (v : ((Sp F).presheaf.stalk z)ˣ) :
    ∃ t : F, t ≠ 0 ∧ toStkA z t = v.val := by
  obtain ⟨t, e⟩ := toStkA_surj z v.val
  exact ⟨t, fun e0 => v.ne_zero (by rw [← e, e0, map_zero]), e⟩

theorem top_le_of_mem {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (z : Sp F) (h : x z ∈ U) :
    ⊤ ≤ x ⁻¹ᵁ U := fun y _ => Subsingleton.elim (α := PrimeSpectrum F) z y ▸ h

theorem exists_valF_secLin {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (h : Y ⟶ X)
    (q : Y ⟶ Sp F) (r : Sp F ⟶ Y) (hq : r ≫ q = 𝟙 _) (x : Sp F ⟶ X) (hr : r ≫ h = x) (k : ℕ) {l l' : L.ι}
    (hl : ⊤ ≤ x ⁻¹ᵁ L.U l) (hl' : ⊤ ≤ x ⁻¹ᵁ L.U l') : ∃ τ : F, τ ≠ 0 ∧
      ∀ (σ' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => h) (fun _ => (k : ℤ)))) (n : ℕ) (cc : Fin n → F)
        (σ : Fin n → H0 L k), GeneratorPullback.SecLin L (fun _ : Fin 1 => h) (fun _ => (k : ℤ)) σ'
          (fun _ : Fin 1 => 𝟙 X) (fun _ => (k : ℤ)) σ h (fun i => scal q (cc i)) →
        valF r _ (σ'.f (fun _ => l)) = τ * ∑ i, cc i *
          valR x (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => l')) ((σ i).f (fun _ => l')) := by
  subst hr
  let z : Sp F := cpt F
  obtain ⟨J, hJ, eJ⟩ := exists_good L hL z (fun _ : PUnit.{1} => r ≫ h) (fun _ => l')
    (fun _ _ _ => rfl) (fun _ => hl' trivial)
  replace eJ : J (r ≫ h) = l' := eJ PUnit.unit
  have hl₁ : ⊤ ≤ r ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => h) (fun _ => l) :=
    fun y hy => Set.mem_iInter.2 fun _ => hl hy
  have hl₂ : r z ∈ LB.wchart L (fun _ : Fin 1 => h) (fun _ => l') := Set.mem_iInter.2 fun _ => hl' trivial
  obtain ⟨τ, τ0, hτ⟩ := exists_toStkA_unit z (trF (L := L) (fun _ : Fin 1 => h)
    (fun _ => (k : ℤ)) r z (fun _ => l) (fun _ => l'))
  refine ⟨τ, τ0, fun σ' n cc σ hσ => (toStkA z).injective ?_⟩
  refine (toStkA_valR_eq_gs r _ z hl₁ _).trans ((sec_trans σ' r z (hl₁ trivial) hl₂).trans ?_)

  rw [map_mul, hτ, map_sum, ← sval_of σ' r z J (fun _ => l') (fun _ => eJ), ExpGTrans.secLin_val hσ r z hJ]
  refine congrArg (_ * ·) (Finset.sum_congr rfl fun i _ => ?_)
  rw [map_mul, sval_of (σ i) _ z J (fun _ => l') (fun _ => by rw [Category.comp_id, eJ])]
  exact congrArg₂ (· * ·) (gs_scal _ r hq z _)
    (toStkA_valR_eq_gs (r ≫ h) (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => l')) z
      (fun y hy => Set.mem_iInter.2 fun _ => hl' hy) _).symm

theorem exists_coef_secLin {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) (g : GtPtF D F) (w : Frm D F k g.b) (hw : w.IsGen) (z : Sp F)
    (J : (Sp F ⟶ D.P.A.left) → D.P.L.ι) (hJ : Good D.P.L z J) : ∃ κ : F, κ ≠ 0 ∧
      ∀ (s : Fam D F k) (χ : D.X) (n : ℕ) (cc : Fin n → F) (f : Fin n → D.SecB k χ),
        GeneratorPullback.SecLin D.P.L (DegPre.famφ D F χ) (DegPre.famε k) (s.s χ) (D.famφB χ) (DegPre.famε k) f
          (DegPre.prB D F).left (fun i => scal (fst (TF (R := R) F) D.P.A).left (cc i)) →
        ∀ (b : Sp F ⟶ D.P.A.left) (jf jt : Fin 4 → D.P.L.ι), b = g.b.left → (∀ i, J (b ≫ D.famφB χ i) = jf i) →
          (∀ i, J (b ≫ D.Oφ (𝟙 _) χ i) = jt i) →
          coef s g w χ = κ * ∑ i, cc i * (valR b _ ((f i).f jf) * valF (𝟙 (Sp F)) _ ((g.s χ).s jt).val) := by
  obtain ⟨Rg, R0, hR⟩ := exists_toStkA_unit z (rigV D (TF (R := R) F).hom z J)
  obtain ⟨W, W0, hW⟩ := exists_toStkA_unit z (val w (𝟙 _) z J)
  refine ⟨W * (Rg ^ k)⁻¹, by simp [R0, W0], fun s χ n cc f hs b jf jt hb hjf hjt => ?_⟩
  let rb : Sp F ⟶ (DegPre.BF D F).left := (lift (𝟙 (TF (R := R) F)) g.b).left
  have hrb : rb ≫ (DegPre.prB D F).left = b :=
    (congrArg (fun t => t.left) (lift_snd (𝟙 (TF (R := R) F)) g.b)).trans hb.symm
  have hrb' : rb ≫ (fst (TF (R := R) F) D.P.A).left = 𝟙 _ :=
    congrArg (fun t => t.left) (lift_fst (𝟙 (TF (R := R) F)) g.b)
  have hcf : IsCoef k g w χ (s.s χ) (coef s g w χ) := Classical.epsilon_spec
    (((CoefBasic.coef_basic R D F k g).2.2 w hw).1 χ (s.s χ)).exists
  have e := hcf z J hJ
  have a₁ : sval (s.s χ) rb z J = toStkA z (∑ i, cc i * valR b _ ((f i).f jf)) := by

    rw [ExpGTrans.secLin_val hs rb z hJ, hrb, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, sval_of (f i) _ z J jf hjf]
    refine congrArg₂ (· * ·) (gs_scal _ rb hrb' z _) (toStkA_valR_eq_gs b _ z (top_le_of_mem _ _ z ?_) _).symm
    have := hJ.mem (D.famφB χ) b
    rwa [funext hjf] at this
  have a₂ : (val (g.s χ) (𝟙 _) z J).val = toStkA z (valF (𝟙 (Sp F)) _ ((g.s χ).s jt).val) := by
    have c : ∀ i, J (𝟙 (Sp F) ≫ DegPre.gtφ D F g.b χ i) = jt i := fun i =>
      (congrArg J ((Category.id_comp _).trans ((gtφ_eq D F g.b χ i).trans
        (congrArg (· ≫ D.Oφ (𝟙 _) χ i) hb.symm)))).trans (hjt i)
    refine (congrArg Units.val (val_of (g.s χ) (𝟙 _) z J jt c)).trans ?_
    have toStkA_valR {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (z : Sp F)
        (ht : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)ˣ) :
        toStkA z (valF x U a.val) = (gm x z U a).val := by
      have hz : x z ∈ U := ht trivial
      rw [valF, dif_pos ht, gm, dif_pos hz]
      show ((Sp F).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
          ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom _)) = _
      rw [Iso.hom_inv_id_apply]
      exact TopCat.Presheaf.germ_res_apply (Sp F).presheaf (homOfLE ht) z trivial _
    refine (toStkA_valR (𝟙 (Sp F)) _ z (top_le_of_mem _ _ z ?_) _).symm
    have := hJ.mem (DegPre.gtφ D F g.b χ) (𝟙 (Sp F))
    rwa [funext c] at this
  have e' : toStkA z (coef s g w χ) * toStkA z Rg ^ k = toStkA z (∑ i, cc i * valR b _ ((f i).f jf)) *
      toStkA z (valF (𝟙 (Sp F)) _ ((g.s χ).s jt).val) * toStkA z W := by
    have a₃ : toStkA z (coef s g w χ) = GlobalTheory.UT.cst (R := R) F z (coef s g w χ) := (CoefBasic.cst_eq (R := R) z _).symm
    rw [hR, hW, ← a₁, ← a₂, a₃]
    exact e
  rw [← map_pow, ← map_mul, ← map_mul, ← map_mul] at e'
  rw [(eq_mul_inv_iff_mul_eq₀ (pow_ne_zero k R0)).2 ((toStkA z).injective e'), Finset.sum_mul]
  simp only [_root_.mul_assoc]
  ring

end GlobalTheory.ZH.IntegralSum
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section
namespace GlobalTheory.ZJ.TwoSections

theorem exists_torsion_pair (M : Type) [CommGroup M] (P : M → Prop) (n : ℕ) (x : M)
    (h : ∀ c : M, 6 * Nat.card {h : M // h ^ n = 1 ∧ ¬ P (c * h)} < Nat.card {h : M // h ^ n = 1}) :
    ∃ b c : M, b ^ n = 1 ∧ c ^ n = 1 ∧ P b ∧ P c ∧ P (b * c) ∧ P (x * b) ∧ P (x * c) ∧ P (x * b * c) := by
  let H : Subgroup M := (powMonoidHom n : M →* M).ker
  have hH : Nat.card H = Nat.card {h : M // h ^ n = 1} := rfl
  have hfin : Finite H := Nat.finite_of_card_ne_zero (by have := h 1; omega)
  have hB : ∀ c : M, 6 * Nat.card {h : H | ¬ P (c * h)} < Nat.card H := fun c => by
    have e : {h : H | ¬ P (c * h)} ≃ {h : M // h ^ n = 1 ∧ ¬ P (c * h)} :=
      Equiv.subtypeSubtypeEquivSubtypeInter (fun h : M => h ^ n = 1) (fun h => ¬ P (c * h))
    rw [Nat.card_congr e, hH]
    exact h c
  obtain ⟨b, c, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.exists_pair_avoiding_small_sets H _ _ (hB 1) (hB x)
  simp only [Set.mem_ofPred_eq, not_not, _root_.one_mul, Subgroup.coe_mul] at h1 h2 h3 h4 h5 h6
  exact ⟨b, c, b.2, c.2, h1, h2, h3, h4, h5, by rwa [_root_.mul_assoc]⟩

theorem exists_pushHom {S S' X : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (q : X ⟶ S') (s : X ⟶ S) (e : q ≫ f = s) :
    ∃ ρ : (Over.mk q ⟶ G') →* (Over.mk s ⟶ G), ∀ c, (ρ c).left = c.left ≫ φ := by
  subst e
  exact ⟨pushHom h (Over.mk q), fun _ => rfl⟩

theorem exists_residue_point (X : Scheme.{0}) (π : X ⟶ Sp ℤ) [LocallyOfFiniteType π] (w : X)
    (hw : IsClosed ({w} : Set X)) : ∃ (p : ℕ) (_ : Fact p.Prime) (x : Sp (kb p) ⟶ X), ∀ s, x s = w := by
  have := (GlobalTheory.jacobson_closedPoints_tools_int X π).2.1 w hw
  obtain ⟨p, hp⟩ := CharP.exists (X.residueField w)
  have hpp : Fact p.Prime := ⟨CharP.char_is_prime (X.residueField w) p⟩
  have : CharP (kb p) p := charP_kb
  have : IsAlgClosed (kb p) := isAlgClosed_kb
  letI : Algebra (ZMod p) (X.residueField w) := ZMod.algebra _ p
  letI : Algebra (ZMod p) (kb p) := ZMod.algebra _ p
  have : Module.Finite (ZMod p) (X.residueField w) := Module.Finite.of_finite
  let r : X.residueField w →+* kb p := (IsAlgClosed.lift (R := ZMod p) (S := X.residueField w) (M := kb p)).toRingHom
  refine ⟨p, hpp, Spec.map (CommRingCat.ofHom r) ≫ X.fromSpecResidueField w, fun s => ?_⟩
  have : (Spec.map (CommRingCat.ofHom r) ≫ X.fromSpecResidueField w) s ∈ Set.range (X.fromSpecResidueField w) :=
    ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
  rwa [Scheme.range_fromSpecResidueField] at this

end GlobalTheory.ZJ.TwoSections

namespace GlobalTheory.ZJ
open TwoSections

theorem Core.Law.six_of_few : Semi.extend_existsSt.{0} → ∀ (C : Core) (L : C.Law) (T : C.Theta) (n : ℕ), C.HasTests → T.BTest L → C.TorsSec n → T.Few n → L.CompanionTheory (T.Om L) := by
  intro hext C L T n hT hB hS hF w hw
  letI := L.grp
  letI := L.comm
  have := C.lft
  have := C.flat
  have hlft : LocallyOfFiniteType C.GG.hom := (GlobalTheory.ZJ.core_basic C).2.1
  have hlft' : LocallyOfFiniteType (C.GG.hom ≫ C.π) := inferInstance
  obtain ⟨p, hp, x, hx⟩ := @exists_residue_point C.G.toScheme (C.GG.hom ≫ C.π) hlft' w hw
  obtain ⟨hlift, hcl⟩ := GlobalTheory.exists_integral_point_lifting_residue_point C.Z C.π C.U C.ne p
  obtain ⟨y, hy, hyU⟩ := hlift (x ≫ C.GG.hom)
  obtain ⟨τ⟩ := hT p y hyU
  obtain ⟨E⟩ := GlobalTheory.T.nonempty_thetaExtension_test hext C T p y τ fun p _ y τ => (L.test p y τ).1
  let s₀ : Sp (kb p) := IsLocalRing.closedPoint (kb p)
  have hs : ∀ s : Sp (kb p), s = s₀ := fun s => Subsingleton.elim (α := PrimeSpectrum (kb p)) _ _
  have hr : rPt p s₀ = cPt p := IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p))
  have hz : y (cPt p) = (x ≫ C.GG.hom) s₀ := by rw [← hy, Scheme.Hom.comp_apply, hr]
  obtain ⟨N, hN, hsec⟩ := hS _ (hcl (x ≫ C.GG.hom) s₀)
  have hrange : Set.range (x ≫ C.GG.hom) ⊆ Set.range N.ι := by
    rintro _ ⟨s, rfl⟩
    rw [hs s, Scheme.Opens.range_ι]
    exact hN
  let t : Sp (kb p) ⟶ N.toScheme := IsOpenImmersion.lift N.ι (x ≫ C.GG.hom) hrange
  have ht : t ≫ N.ι = x ≫ C.GG.hom := IsOpenImmersion.lift_fac _ _ _
  have e : (rPt p ≫ spMap τ.j) ≫ τ.y₀ = t ≫ N.ι := by rw [Category.assoc, τ.fac, hy, ht]
  have hpb := (L.test p y τ).1
  let c₀ : Over.mk (rPt p ≫ spMap τ.j) ⟶ τ.H :=
    Over.homMk (hpb.lift x (rPt p ≫ spMap τ.j) (ht.symm.trans e.symm)) (hpb.lift_snd _ _ _)
  have hc₀ : c₀.left ≫ τ.f = x := hpb.lift_fst _ _ _
  obtain ⟨ρ, hρ⟩ := exists_pushHom (L.test p y τ) _ _ e
  obtain ⟨b, c, hb, hc, h1, h2, h3, h4, h5, h6⟩ := exists_torsion_pair (Over.mk (rPt p ≫ spMap τ.j) ⟶ τ.H)
    (fun c => ⊤ ≤ c.left ⁻¹ᵁ Out.nonzeroLocus E.θ) n c₀ (hF p y τ E)
  obtain ⟨b₁, hb₁, hb₂⟩ := hsec p y τ t b hz (ht.trans hy.symm) hb
  obtain ⟨c₁, hc₁, hc₂⟩ := hsec p y τ t c hz (ht.trans hy.symm) hc
  have key : ∀ d : Over.mk (rPt p ≫ spMap τ.j) ⟶ τ.H, ⊤ ≤ d.left ⁻¹ᵁ Out.nonzeroLocus E.θ →
      Set.range (ρ d).left ⊆ T.Om L := by
    rintro d hd _ ⟨s, rfl⟩
    have := τ.j_loc
    have h0 : τ.H.hom (d.left s) = IsLocalRing.closedPoint τ.V := by
      rw [← Scheme.Hom.comp_apply, Over.w d, hs s]
      exact (Scheme.Hom.comp_apply _ _ _).trans
        ((congrArg (spMap τ.j) hr).trans (IsLocalRing.comap_closedPoint τ.j))
    rw [hρ]
    exact (Scheme.Hom.comp_apply _ _ _).symm ▸ (hB p y τ E _ h0).2 (hd trivial)
  refine ⟨N, Over.homMk b₁ hb₁, Over.homMk c₁ hc₁, kb p, inferInstance, t, ρ c₀, ρ b, ρ c, ?_,
    (hρ b).trans hb₂.symm, (hρ c).trans hc₂.symm, ?_⟩
  · rw [hρ, hc₀]
    ext v
    exact ⟨fun ⟨s, h⟩ => h ▸ hx s, fun h => ⟨s₀, (hx _).trans h.symm⟩⟩
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false, ← map_mul] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [key _ h1, key _ h2, key _ h3, key _ h4, key _ h5, key _ h6]

end GlobalTheory.ZJ
end
end
