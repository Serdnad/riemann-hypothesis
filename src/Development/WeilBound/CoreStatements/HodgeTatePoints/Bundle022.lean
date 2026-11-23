module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle020
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteOpenHopfOrder
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle017
import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfSec
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle025
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsSplitIdempotentConjugation
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerCharacterOrderGenerates
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle001
import Development.WeilBound.CoreStatements.HodgeTatePoints.RiRank
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.DualLattices.Bundle007
public import ReciprocityTheory.DualLattices.Bundle021
public import Mathlib.RingTheory.Finiteness.Nakayama
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section

namespace PositivityTheory.HtPt.Mh

theorem quot : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (H : Type) [CommGroup H] [Finite H] (Γ₁ : QFGroup R H) (a : Γ₁.G ⟶ Γ.G) [IsMonHom a] (α : H →* T), (∀ h, Γ₁.pt h ≫ a = Γ.pt (α h)) → IsFinite Γ₁.G.hom → IsFinite Γ.G.hom → Flat a.left → Surjective a.left → quotOrder α (Γ₁.btOrder ⊤) = Γ.btOrder ⊤ := by
  intro R _ _ _ T _ _ Γ H _ _ Γ₁ a _ α hpt hfin₁ hfin hfl hsurj
  haveI : IsAffine Γ.G.left := isAffine_of_isAffineHom Γ.G.hom
  haveI : IsAffine Γ₁.G.left := isAffine_of_isAffineHom Γ₁.G.hom
  have hα : Function.Surjective α := by
    intro t
    let z : Spec (CommRingCat.of (FractionRing R)) := IsLocalRing.closedPoint (FractionRing R)
    obtain ⟨y, hy⟩ := a.left.surjective ((Γ.pt t).left z)
    have hgen : (Γ₁.G.hom y).asIdeal = ⊥ := by
      have e1 : Γ₁.G.hom y = Γ.G.hom ((Γ.pt t).left z) := by
        rw [← hy, ← Scheme.Hom.comp_apply, Over.w a]
      rw [e1, ← Scheme.Hom.comp_apply, Over.w (Γ.pt t)]
      show (PrimeSpectrum.comap (algebraMap R (FractionRing R)) z).asIdeal = ⊥
      rw [PrimeSpectrum.comap_asIdeal]
      have hz : z.asIdeal = ⊥ := (Ideal.eq_bot_or_top _).resolve_right z.isPrime.ne_top
      rw [hz]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R))
    obtain ⟨h, x, hx⟩ := Γ₁.pt_onto y hgen
    refine ⟨h, Γ.pt_inj (α h) t x z ?_⟩
    have e2 : a.left ((Γ₁.pt h).left x) = (Γ.pt (α h)).left x := by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hpt h]
    rw [← e2, hx, hy]
  have valAt_top : ∀ {B : Type} [CommRing B] {X : Scheme.{0}}
      (x : Spec (CommRingCat.of B) ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ ⊤) (s : Γ(X, ⊤)),
      valAt x ⊤ h s = val x s := by
    intro B _ X x h s
    simp only [valAt, val, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have sec_ext : ∀ {T : Type} [CommGroup T] [Finite T] (Γ : QFGroup R T) {s s' : Γ(Γ.G.left, ⊤)}, (∀ t, val (Γ.pt t).left s = val (Γ.pt t).left s') → s = s' := by
    intro T _ _ Γ s s' h
    rw [← sub_eq_zero]
    refine Twhopf.sec_inj R T Γ ⊤ _ fun t ht => ?_
    rw [valAt_top, map_sub, h, sub_self]
  have mem_top_iff : ∀ {T : Type} [CommGroup T] [Finite T] (Γ : QFGroup R T) (f : T → R), f ∈ Γ.btOrder ⊤ ↔
      ∀ t, ∃ s : Γ(Γ.G.left, ⊤), ∀ h, val (Γ.pt h).left s = algebraMap R (FractionRing R) (f (t * h)) := by
    intro T _ _ Γ f
    have hsub : ∀ {B : Type} [CommRing B] {X : Scheme} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
        (hx : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)), valAt x U hx (a - b) = valAt x U hx a - valAt x U hx b := by
      intro B _ X x U hx a b
      simp only [valAt, map_sub]
    constructor
    · intro hf t
      rw [Twhopf.mem_order] at hf
      have hreg : ∀ g : Γ.G.left, ∃ U : Γ.G.left.Opens, g ∈ U ∧ ∃ s : Γ(Γ.G.left, U),
          ∀ (h : T) (hh : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ U),
            valAt (Γ.pt h).left U hh s = algebraMap R (FractionRing R) (f (t * h)) :=
        fun g => hf t g (by simp)
      choose U hgU s hs using hreg
      obtain ⟨g0, hglue, -⟩ := TopCat.Sheaf.existsUnique_gluing' Γ.G.left.sheaf U ⊤
        (fun g => homOfLE le_top) (fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hgU x⟩) s (by
          intro g g'
          rw [← sub_eq_zero]
          apply Twhopf.sec_inj R T Γ _ _
          intro h hh
          have h1 : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ U g :=
            (SubOrder.top_le_iff_mem _ _).2 fun z => ((SubOrder.top_le_iff_mem _ _).1 hh z).1
          have h2 : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ U g' :=
            (SubOrder.top_le_iff_mem _ _).2 fun z => ((SubOrder.top_le_iff_mem _ _).1 hh z).2
          refine (hsub _ _ hh _ _).trans ?_
          erw [Twhopf.valAt_restrict _ _ hh h1, Twhopf.valAt_restrict _ _ hh h2]
          rw [hs, hs, sub_self])
      refine ⟨g0, fun h => ?_⟩
      have htop : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ ⊤ := (SubOrder.top_le_iff_mem _ _).2 fun _ => trivial
      let z : Spec (CommRingCat.of (FractionRing R)) := IsLocalRing.closedPoint (FractionRing R)
      have hh : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ U ((Γ.pt h).left z) :=
        Twhopf.top_le_of_mem _ z (hgU _)
      refine (valAt_top _ htop g0).symm.trans ?_
      refine (Twhopf.valAt_restrict _ (homOfLE le_top) hh htop g0).symm.trans ?_
      erw [hglue ((Γ.pt h).left z)]
      exact hs _ h hh
    · intro hf
      rw [Twhopf.mem_order]
      intro t g _
      obtain ⟨s, hs⟩ := hf t
      unfold QFGroup.RegularAt
      exact ⟨⊤, by simp, s, fun h hh => by rw [valAt_top, hs]⟩
  ext f
  rw [quotOrder, Subalgebra.mem_comap, mem_top_iff, mem_top_iff]
  constructor
  · intro hf t
    obtain ⟨d, hd0, hd⟩ := GlobalTheory.CompanionTheory.Ar.BT.btOrder_full_rank R T Γ
    obtain ⟨s0, hs0⟩ := (mem_top_iff Γ _).1 (hd (fun x => f (t * x))) 1
    obtain ⟨h0, rfl⟩ := hα t
    obtain ⟨s₁, hs₁⟩ := hf h0
    have key : a.left.appTop s0 = a.left.appTop (pb Γ.G.hom d) * s₁ := by
      apply sec_ext Γ₁
      intro h
      rw [map_mul, ← val_comp, ← val_comp, ← Over.comp_left, hpt h, hs0, val_pb (Over.w (Γ.pt (α h))), hs₁, ← map_mul]
      congr 1
      show d * f (α h0 * (1 * α h)) = d * f (α (h0 * h))
      rw [_root_.one_mul, MonoidHom.map_mul]
    have e : Spec.map a.left.appTop = Γ₁.G.left.isoSpec.inv ≫ a.left ≫ Γ.G.left.isoSpec.hom := by
      rw [← Scheme.isoSpec_hom_naturality, Iso.inv_hom_id_assoc]
    have hff : a.left.appTop.hom.FaithfullyFlat :=
      (flat_and_surjective_SpecMap_iff _).1 ⟨by rw [e]; infer_instance, by rw [e]; infer_instance⟩
    letI : Algebra Γ(Γ.G.left, ⊤) Γ(Γ₁.G.left, ⊤) := a.left.appTop.hom.toAlgebra
    have hmem : s0 ∈ Ideal.span {pb Γ.G.hom d} := by
      rw [← @Ideal.comap_map_eq_self_of_faithfullyFlat _ _ _ _ _ hff (Ideal.span {pb Γ.G.hom d}),
        Ideal.mem_comap, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
      exact ⟨s₁, key⟩
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 hmem
    refine ⟨s, fun h => ?_⟩
    have e3 := hs0 h
    rw [← hs, map_mul, val_pb (Over.w (Γ.pt h))] at e3
    have hd' : algebraMap R (FractionRing R) d ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hd0
    apply mul_right_cancel₀ hd'
    rw [e3, ← map_mul]
    congr 1
    show d * f (α h0 * (1 * h)) = f (α h0 * h) * d
    rw [_root_.one_mul, mul_comm]
  · intro hf h0
    obtain ⟨s, hs⟩ := hf (α h0)
    refine ⟨a.left.appTop s, fun h => ?_⟩
    rw [← val_comp, ← Over.comp_left, hpt h, hs]
    exact congrArg _ (congrArg f (map_mul α h0 h).symm)

end PositivityTheory.HtPt.Mh
end
end

section

noncomputable section

namespace PositivityTheory.HtPt.Rc

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

open ReciprocityTheory.PGsh.L2.SecondCohomologyLattice

lemma unimod {S V ι : Type} [CommRing S] [CommRing V] [Algebra S V] [Fintype ι] (f : ι → V)
    (b : ι → S) (h1 : 1 = ∑ j, b j • f j)
    (hmul : ∀ i j, f j * f i ∈ Submodule.span S (Set.range f)) :
    ∃ e : ι → S, algebraMap S V (∑ j, e j * b j) = 1 := by
  let A : Submodule S V := Submodule.span S (Set.range f)
  let J : Ideal S := Ideal.span (Set.range b)
  have hJ : A ≤ J • A := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have : f i = ∑ j, b j • (f j * f i) := by
      conv_lhs => rw [← one_mul (f i), h1, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => smul_mul_assoc _ _ _
    rw [SetLike.mem_coe, this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul
      (Ideal.subset_span ⟨j, rfl⟩) (hmul i j)
  obtain ⟨r, hr1, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul J A
    (Submodule.fg_span (Set.finite_range f)) hJ
  have h1A : (1 : V) ∈ A := by
    rw [h1]
    exact Submodule.sum_mem _ fun j _ => A.smul_mem _ (Submodule.subset_span ⟨j, rfl⟩)
  have hr := hr0 1 h1A
  rw [Algebra.smul_def, mul_one] at hr
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun S).1 (J.neg_mem hr1)
  refine ⟨e, ?_⟩
  simp only [smul_eq_mul] at he
  rw [he, neg_sub, map_sub, hr, map_one, sub_zero]

theorem invres : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, ∀ K K' : AddSubgroup N, K ≤ K' → ∀ g ∈ AA.carrier, (∀ x ∈ K', ∀ k ∈ K, g (x + k) = g x) → ∃ g' ∈ invFun AA.carrier K, ∀ x ∈ K', g' x = g x := by
  intro p _ C _ _ _ v R _ _ hv _ N _ _ _ AA K K' _ g hg hinv
  classical
  have : Fintype (N ⧸ K) := Fintype.ofFinite _
  obtain ⟨⟨f, hf, hfree⟩, -⟩ := ReciprocityTheory.PGsh.L2.h3 C R inferInstance inferInstance v hv N K AA
  have hB : ∀ b ∈ (AA.carrier.comap (pullQ (R := R) K)).map (pullQ K), b ∈ invFun AA.carrier K := by
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨hq, fun x k hk => ?_⟩
    show q ((x + k : N) : N ⧸ K) = q (x : N ⧸ K)
    rw [QuotientAddGroup.mk_add_of_mem x hk]
  have hdec : ∀ a ∈ AA.carrier, ∃ b : K → N → C, (∀ j, b j ∈ invFun AA.carrier K) ∧
      a = ∑ j, b j * f j := by
    intro a ha
    obtain ⟨b, ⟨hb, hab⟩, -⟩ := hfree a ha
    exact ⟨b, fun j => hB _ (hb j), hab⟩
  let S : Subalgebra R (N → C) := (invFun AA.carrier K).toSubalgebra ⟨AA.one_mem, fun _ _ _ => rfl⟩
    (fun x y hx hy => ⟨AA.mul_mem _ _ hx.1 hy.1, fun z k hk => by
      simp only [Pi.mul_apply, hx.2 z k hk, hy.2 z k hk]⟩)
  let A : Submodule S (N → C) := Submodule.span S (Set.range f)
  have hA : ∀ a ∈ AA.carrier, a ∈ A := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := hdec a ha
    exact Submodule.sum_mem _ fun j _ =>
      A.smul_mem (⟨b j, hb j⟩ : S) (Submodule.subset_span ⟨j, rfl⟩)
  obtain ⟨b, hb, h1⟩ := hdec 1 AA.one_mem
  obtain ⟨e, he⟩ := unimod f (fun j => (⟨b j, hb j⟩ : S)) h1
    (fun i j => hA _ (AA.mul_mem _ _ (hf j) (hf i)))
  have he' : ∀ x, ∑ j, (e j : N → C) x * b j x = 1 := by
    intro x
    have : ((∑ j, e j * (⟨b j, hb j⟩ : S) : S) : N → C) x = 1 := congrFun he x
    simpa using this
  obtain ⟨c, hc, hgc⟩ := hdec g hg
  refine ⟨((∑ j, e j * (⟨c j, hc j⟩ : S) : S) : N → C), (∑ j, e j * (⟨c j, hc j⟩ : S) : S).2,
    fun x hx => ?_⟩
  let ρ : (N → C) →ₗ[C] (K → C) := LinearMap.funLeft C C fun k : K => x + (k : N)
  have hρ : ∀ b : K → N → C, (∀ j, b j ∈ invFun AA.carrier K) →
      ρ (∑ j, b j * f j) = ∑ j, b j x • ρ (f j) := by
    intro b hb
    funext k
    simp only [ρ, LinearMap.funLeft_apply, Finset.sum_apply, Pi.mul_apply, Pi.smul_apply,
      smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [(hb j).2 x k k.2]
  have hli : LinearIndependent C fun j => ρ (f j) := by
    apply linearIndependent_of_top_le_span_of_card_eq_finrank
    · have hsurj : Function.Surjective ρ :=
        LinearMap.funLeft_surjective_of_injective _ _ _
          (fun k k' h => Subtype.ext (add_left_cancel h))
      rw [← LinearMap.range_eq_top.2 hsurj, ← Submodule.map_top, ← span_top_of_isLat (C := C) AA.lat,
        Submodule.map_span_le]
      intro a ha
      obtain ⟨b', hb', rfl⟩ := hdec a ha
      rw [hρ b' hb']
      exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · simp
  have hkey : ∀ j, c j x = g x * b j x := by
    have h2 : ∑ j, (c j x - g x * b j x) • ρ (f j) = 0 := by
      simp only [sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum]
      rw [← hρ c hc, ← hρ b hb, ← hgc, ← h1]
      funext k
      simp [ρ, LinearMap.funLeft_apply, hinv x hx k k.2]
    intro j
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ h2 j)
  have : ((∑ j, e j * (⟨c j, hc j⟩ : S) : S) : N → C) x = ∑ j, (e j : N → C) x * c j x := by
    simp
  rw [this]
  simp only [hkey]
  calc ∑ j, (e j : N → C) x * (g x * b j x) = g x * ∑ j, (e j : N → C) x * b j x := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    _ = g x := by rw [he', mul_one]

end PositivityTheory.HtPt.Rc
end
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Pmono

section
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
  {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
lemma mem_xIdeal (M : Submodule R (F → C)) (χ : MulChar F R) (r : R) :
    r ∈ xIdeal M χ ↔ (fun a => algebraMap R C (r * χ a)) ∈ M := by
  have : (fun a => algebraMap R C (r * χ a)) = r • fun a => algebraMap R C (χ a) := by
    funext a
    simp [Algebra.smul_def]
  rw [this]
  rfl

lemma pow_mem (AA : HopfOrder (C := C) R F) {g : F → C} (hg : g ∈ AA.carrier) (k : ℕ) :
    g ^ k ∈ AA.carrier := by
  induction k with
  | zero => rw [pow_zero]; exact AA.one_mem
  | succ k ih => rw [pow_succ]; exact AA.mul_mem _ _ ih hg

lemma mono_mem (AA : HopfOrder (C := C) R F) (σ : MulChar F R) {p f : ℕ} (hp : p ≠ 0)
    (c : ℕ → R) (hc : ∀ n, c n ∈ xIdeal AA.carrier (σ ^ p ^ n)) (e : Fin f → ℕ)
    (he : ∑ n : Fin f, e n * p ^ (n : ℕ) ≠ 0) :
    ∏ n : Fin f, c n ^ e n ∈ xIdeal AA.carrier (σ ^ (∑ n : Fin f, e n * p ^ (n : ℕ))) := by
  rw [mem_xIdeal]
  have hmem : (∏ n : Fin f, (fun a => algebraMap R C (c n * (σ ^ p ^ (n : ℕ)) a)) ^ e n) ∈
      AA.carrier :=
    Finset.prod_induction _ (fun g => g ∈ AA.carrier) (fun a b ha hb => AA.mul_mem a b ha hb)
      AA.one_mem fun n _ => pow_mem AA ((mem_xIdeal _ _ _).1 (hc n)) _
  have hfun : (fun a => algebraMap R C ((∏ n : Fin f, c n ^ e n) *
      (σ ^ (∑ n : Fin f, e n * p ^ (n : ℕ))) a)) =
      ∏ n : Fin f, (fun a => algebraMap R C (c n * (σ ^ p ^ (n : ℕ)) a)) ^ e n := by
    funext a
    rw [Finset.prod_apply, MulChar.pow_apply' _ he, ← Finset.prod_pow_eq_pow_sum,
      ← Finset.prod_mul_distrib, map_prod]
    refine Finset.prod_congr rfl fun n _ => ?_
    rw [Pi.pow_apply, MulChar.pow_apply' _ (pow_ne_zero _ hp), ← map_pow (algebraMap R C), mul_pow,
      ← pow_mul,
      mul_comm (e n)]
  rw [hfun]
  exact hmem

end

lemma prod_digits {p f : ℕ} (hp : p ≠ 0) (w : ℕ → NNReal) :
    (∏ d : Fin f → Fin p, if ∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ) = 0 then 1
      else w (∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ))) = ∏ m ∈ Finset.Icc 1 (p ^ f - 1), w m := by
  have h1 : (∏ d : Fin f → Fin p, if ∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ) = 0 then 1
      else w (∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ))) =
      ∏ i : Fin (p ^ f), if (i : ℕ) = 0 then 1 else w i :=
    Fintype.prod_equiv finFunctionFinEquiv _ _ fun d => by rw [finFunctionFinEquiv_apply]
  have hq : 0 < p ^ f := pow_pos (Nat.pos_of_ne_zero hp) _
  have h2 : Finset.range (p ^ f) = insert 0 (Finset.Icc 1 (p ^ f - 1)) := by
    ext m
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [h1, Fin.prod_univ_eq_prod_range (fun i => if i = 0 then 1 else w i), h2,
    Finset.prod_insert (by simp), if_pos rfl, one_mul]
  refine Finset.prod_congr rfl fun m hm => if_neg ?_
  have := (Finset.mem_Icc.1 hm).1
  omega

theorem r_mono : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable (F := F) AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ c : ℕ → R, (∀ n, xIdeal AA.carrier (σ ^ p ^ n) = Ideal.span {c n}) → (∀ n, v (p : C) ≤ v (algebraMap R C (c n)) ^ (p - 1)) ∧ ∀ d : Fin f → Fin p, (∃ n, (d n : ℕ) ≠ 0) → xIdeal AA.carrier (σ ^ (∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ))) = Ideal.span {∏ n : Fin f, c n ^ (d n : ℕ)} := by
  intro p hpp C _ _ _ v R _ _ hv hvp F _ _ _ _ f hf AA hst σ hσ c hc
  have hp0 : p ≠ 0 := hpp.out.ne_zero
  obtain ⟨AD, hstD, hcol, hfund⟩ := rank_one_sum p C v R hv hvp F f hf AA hst
  obtain ⟨-, -, hpow, -, -⟩ := GlobalTheory.CompanionTheory.Ar.GR.FundGen.main p C v R hv hvp F f hf σ hσ
  choose g hg0 hg using fun m : ℕ => (eig_rank_one p C v R hv hvp F f hf AA hst (σ ^ m)).1
  choose gD hgD0 hgD using fun m : ℕ => (eig_rank_one p C v R hv hvp F f hf AD hstD (σ ^ m)).1
  have hx : ∀ n : ℕ, (v (algebraMap R C (c n)) * v (algebraMap R C (gD (p ^ n)))) ^ (p - 1) =
      v (p : C) := fun n => hfund (σ ^ p ^ n) (hpow n) _ _ (hc n) (hgD _)
  have hle : ∀ (BB : HopfOrder (C := C) R F) (γ b : ℕ → R),
      (∀ m, xIdeal BB.carrier (σ ^ m) = Ideal.span {γ m}) →
      (∀ n, xIdeal BB.carrier (σ ^ p ^ n) = Ideal.span {b n}) →
      ∀ d : Fin f → Fin p, ∏ n : Fin f, v (algebraMap R C (b n)) ^ (d n : ℕ) ≤
        if ∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ) = 0 then 1
        else v (algebraMap R C (γ (∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ)))) := by
    intro BB γ b hγ hb d
    split_ifs with h
    · exact Finset.prod_le_one' fun n _ => pow_le_one' (hv.map_le_one _) _
    · have hm := mono_mem BB σ hp0 b
        (fun n => by rw [hb n]; exact Ideal.mem_span_singleton_self _) (fun n => (d n : ℕ)) h
      rw [hγ, Ideal.mem_span_singleton, hv.dvd_iff_le] at hm
      simpa only [map_prod, map_pow] using hm
  refine ⟨fun n => ?_, fun d hd => ?_⟩
  · rw [← hx n]
    exact pow_le_pow_left' (mul_le_of_le_one_right' (hv.map_le_one _)) _
  · have hN := (PositivityTheory.HtPt.Ri.r_decomp p C v R hv hvp F f hf AA hst σ hσ g hg).2.2
    have hD := (PositivityTheory.HtPt.Ri.r_decomp p C v R hv hvp F f hf AD hstD σ hσ gD hgD).2.2
    have hP : v (p : C) ≠ 0 := by
      rw [Ne, map_eq_zero]
      exact_mod_cast hp0
    have key := (count p f hpp.out.two_le (v (p : C)) hP (fun n => v (algebraMap R C (c n)))
      (fun n => v (algebraMap R C (gD (p ^ (n : ℕ))))) _ _ (fun n => hx n) (hle AA g c hg hc)
      (hle AD gD (fun n => gD (p ^ n)) hgD fun n => hgD _)
      (by
        rw [Finset.prod_mul_distrib, prod_digits hp0 fun m => v (algebraMap R C (g m)),
          prod_digits hp0 fun m => v (algebraMap R C (gD m))]
        exact hcol _ _ hN hD) d).1
    have hne : ∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ) ≠ 0 := by
      obtain ⟨n, hn⟩ := hd
      intro h
      exact mul_ne_zero hn (pow_ne_zero _ hp0)
        (Finset.sum_eq_zero_iff.1 h n (Finset.mem_univ n))
    rw [if_neg hne] at key
    rw [hg]
    have hval : v (algebraMap R C (∏ n : Fin f, c n ^ (d n : ℕ))) =
        v (algebraMap R C (g (∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ)))) := by
      rw [key]
      simp only [map_prod, map_pow]
    exact le_antisymm (Ideal.span_singleton_le_span_singleton.2 (hv.dvd_of_le hval.ge))
      (Ideal.span_singleton_le_span_singleton.2 (hv.dvd_of_le hval.le))

end PositivityTheory.HtPt.Pmono
end
