module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle081
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualInterSelfDualHermitianLatticeSubspace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle053
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle037
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle082
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryNormalisesStabil
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockUnitriangularRationalFromCommonStabiliser
public import Mathlib.Algebra.Module.Lattice.Full
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameMatrixCloseGivesLatticeCloseIntegral
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle035
public import Formalism.HermitianLattices.StatementLat
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle084
public import Formalism.LocalRingCardinality.Bundle001
public import Formalism.LocalRingCardinality.DataCoeff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle085
public import Formalism.LocalToGlobal.HermitianForms.Bundle001
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle086
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures

@[expose] public section

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Gluing

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem resQ_ne_zero [IsNonarchimedeanLocalField F] (ϖ : 𝒪[F]) (h : Irreducible ϖ) :
    resQ ϖ ≠ 0 := by
  unfold resQ
  rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 h]
  have : Finite (𝒪[F] ⧸ IsLocalRing.maximalIdeal 𝒪[F]) := inferInstanceAs (Finite 𝓀[F])
  exact Nat.card_pos.ne'

theorem encard_le [IsNonarchimedeanLocalField F] [CharZero F] {L : LocE F E} {n : ℕ}
    {Hm : Matrix (Fin n) (Fin n) E} (h : IsHermND L Hm) {m : ℕ} {y : Fin m → Fin n → E}
    (hy : LinearIndependent E y) {Y : Submodule E (Fin n → E)}
    (hY : Submodule.span E (Set.range y) = Y) (hc : Y ⊔ perp L Hm Y = ⊤)
    (Mh Λ₀ Md : Submodule L.O (Fin n → E))
    (hMd : ∀ x, x ∈ Md ↔ x ∈ Y ∧ ∀ z ∈ Mh, hf L Hm x z ∈ L.O)
    {ι : Type} [Fintype ι] (b : ι → Fin n → E) (hb : Md = Submodule.span L.O (Set.range b))
    (hN : Mh.toAddSubgroup.relIndex Md.toAddSubgroup ≠ 0) :
    {Λ : Submodule L.O (Fin n → E) | IsSD L Hm Λ ∧ Λ ⊓ Y.restrictScalars L.O = Mh ∧
      Λ ⊓ (perp L Hm Y).restrictScalars L.O = Λ₀}.encard ≤
      ((Mh.toAddSubgroup.relIndex Md.toAddSubgroup ^ Fintype.card ι : ℕ) : ℕ∞) := by
  set T := {Λ : Submodule L.O (Fin n → E) | IsSD L Hm Λ ∧ Λ ⊓ Y.restrictScalars L.O = Mh ∧
      Λ ⊓ (perp L Hm Y).restrictScalars L.O = Λ₀} with hT
  rcases T.eq_empty_or_nonempty with h0 | ⟨Λ₁, hΛ₁⟩
  · simp [h0]
  have hsym : ∀ x v, hf L Hm x v ∈ L.O → hf L Hm v x ∈ L.O := fun x v hx => by
    rw [← DualInter.cj_hf h]
    exact GlobalTheory.UnramOrder.cj_mem L hx
  have hM : ∀ Λ ∈ T, ∀ x, x ∈ Mh ↔ x ∈ Λ ∧ x ∈ Y := fun Λ hΛ x => by
    rw [← hΛ.2.1]; rfl
  have h0 : ∀ Λ ∈ T, ∀ x, x ∈ Λ₀ ↔ x ∈ Λ ∧ x ∈ perp L Hm Y := fun Λ hΛ x => by
    rw [← hΛ.2.2]; rfl
  have hproj : ∀ Λ ∈ T, ∀ l ∈ Λ, ∀ w ∈ perp L Hm Y, l - w ∈ Y → l - w ∈ Md := by
    intro Λ hΛ l hl w hw hlw
    refine (hMd _).2 ⟨hlw, fun z hz => ?_⟩
    have hz' := (hM Λ hΛ z).1 hz
    rw [DualInter.sub_l, hw z hz'.2, sub_zero]
    exact (hΛ.1.2 z).2 hz'.1 l hl
  have hbM : ∀ i, b i ∈ Md := fun i => hb ▸ Submodule.subset_span ⟨i, rfl⟩
  have hlift : ∀ Λ : T, ∀ i, ∃ a ∈ Λ.1, a - b i ∈ perp L Hm Y ∧
      ∃ c ∈ Λ₁, c - (a - b i) ∈ Y := by
    intro Λ i
    obtain ⟨-, -, h3, -⟩ := DualInter.dual_inter L Hm h Λ.1 Λ.2.1 m y hy
    obtain ⟨-, h2, -, -⟩ := DualInter.dual_inter L Hm h Λ₁ hΛ₁.1 m y hy
    rw [hY] at h2 h3
    obtain ⟨a, ha, hab⟩ := (h3 (b i)).1 fun x hx hxY =>
      hsym _ _ (((hMd _).1 (hbM i)).2 x ((hM _ Λ.2 x).2 ⟨hx, hxY⟩))
    obtain ⟨c, hc, hca⟩ := (h2 (a - b i)).1 fun x hx hxY => by
      rw [DualInter.sub_r, hxY _ ((hMd _).1 (hbM i)).1, sub_zero]
      exact (Λ.2.1.2 a).2 ha x ((h0 _ Λ.2 x).1 ((h0 _ hΛ₁ x).2 ⟨hx, hxY⟩)).1
    exact ⟨a, ha, by simpa using (perp L Hm Y).neg_mem hab, c, hc, by simpa using Y.neg_mem hca⟩
  choose a ha hab c hc1 hca using hlift
  have hle : ∀ Λ Λ' : T, (∀ i, a Λ i ∈ Λ'.1) → Λ.1 ≤ Λ'.1 := by
    intro Λ Λ' hi l hl
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.1 (hc ▸ Submodule.mem_top : l ∈ Y ⊔ perp L Hm Y)
    have hu' : l - w = u := by rw [← huw]; simp
    have h1 := hproj _ Λ.2 l hl w hw (hu' ▸ hu)
    rw [hb] at h1
    obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun L.O).1 h1
    have h2 : l - ∑ i, s i • a Λ i ∈ Λ₀ := by
      refine (h0 _ Λ.2 _).2 ⟨Λ.1.sub_mem hl (Λ.1.sum_mem fun i _ => Λ.1.smul_mem _ (ha Λ i)), ?_⟩
      have : l - ∑ i, s i • a Λ i = w - ∑ i, s i • (a Λ i - b i) := by
        simp only [smul_sub, Finset.sum_sub_distrib, hs]; abel
      rw [this]
      exact Submodule.sub_mem _ hw (Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ (s i : E) (hab Λ i))
    have h3 := Λ'.1.add_mem ((h0 _ Λ'.2 _).1 h2).1
      (Λ'.1.sum_mem (t := Finset.univ) fun i _ => Λ'.1.smul_mem (s i) (hi i))
    rwa [sub_add_cancel] at h3
  let Q := Md.toAddSubgroup ⧸ Mh.toAddSubgroup.addSubgroupOf Md.toAddSubgroup
  have hQ : Nat.card Q = Mh.toAddSubgroup.relIndex Md.toAddSubgroup := rfl
  have : Finite Q := Nat.finite_of_card_ne_zero (hQ ▸ hN)
  let Φ : T → ι → Q := fun Λ i =>
    QuotientAddGroup.mk ⟨c Λ i - (a Λ i - b i), hproj _ hΛ₁ _ (hc1 Λ i) _ (hab Λ i) (hca Λ i)⟩
  have key : ∀ Λ Λ' : T, Φ Λ = Φ Λ' → ∀ i, a Λ i ∈ Λ'.1 := by
    intro Λ Λ' he i
    have h1 : -(c Λ i - (a Λ i - b i)) + (c Λ' i - (a Λ' i - b i)) ∈ Mh :=
      QuotientAddGroup.eq.1 (congrFun he i)
    have h2 : a Λ i - a Λ' i ∈ Λ₀ := by
      refine (h0 _ hΛ₁ _).2 ⟨?_, ?_⟩
      · have := Λ₁.add_mem ((hM _ hΛ₁ _).1 h1).1 (Λ₁.sub_mem (hc1 Λ i) (hc1 Λ' i))
        convert this using 1; abel
      · have := (perp L Hm Y).sub_mem (hab Λ i) (hab Λ' i)
        convert this using 1; abel
    have h3 := Λ'.1.add_mem ((h0 _ Λ'.2 _).1 h2).1 (ha Λ' i)
    rwa [sub_add_cancel] at h3
  have hinj : Function.Injective Φ := fun Λ Λ' he =>
    Subtype.ext (le_antisymm (hle _ _ (key _ _ he)) (hle _ _ (key _ _ he.symm)))
  have : Finite T := Finite.of_injective Φ hinj
  have h4 := Nat.card_le_card_of_injective Φ hinj
  rw [Nat.card_fun, hQ, Nat.card_eq_fintype_card (α := ι)] at h4
  rw [← (Set.toFinite T).cast_ncard_eq, ← Nat.card_coe_set_eq]
  exact_mod_cast h4

theorem gluing_count : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ C, S.IsCls C → ∀ p ∈ C, ∀ Mh Λ₀ : Submodule L.O S.V, S.Mof p.1 p.2 ≤ Mh → (({Λ : Submodule L.O S.V | IsSD L S.Hm Λ ∧ S.sat Λ = Mh ∧ Λ ⊓ S.W0.restrictScalars L.O = Λ₀}.encard : ℕ∞) : ℝ≥0∞) ≤ (S.q : ℝ≥0∞) ^ (2 * S.a.toNat * (2 * r + 2)) := by
  intro F _ _ _ _ _ E _ _ _ L r k S C hC p hp Mh Λ₀ hM
  rcases {Λ : Submodule L.O S.V | IsSD L S.Hm Λ ∧ S.sat Λ = Mh ∧
    Λ ⊓ S.W0.restrictScalars L.O = Λ₀}.eq_empty_or_nonempty with h0 | ⟨Λ₁, hΛ₁⟩
  · simp [h0]
  obtain ⟨n, hn, n', hn', rfl⟩ := hC
  rw [((GlobalTheory.HL.FrameClass.frame_classes L r k S _ _).2.1 p hp).2] at hM
  obtain ⟨⟨c, hc0, hca, hdet⟩, -, hsp⟩ := GlobalTheory.T.frameLattice_gramDet_and_minors_orbit_invariant L r k S n hn n' hn'
  obtain ⟨hli, hcompl, -⟩ := GlobalTheory.FrameBasic.main L r k S
  have hMh : ∀ x, x ∈ Mh ↔ x ∈ Λ₁ ∧ x ∈ S.ME := fun x => by rw [← hΛ₁.2.1]; rfl
  let Md : Submodule L.O S.V :=
    { carrier := {x | x ∈ S.ME ∧ ∀ z ∈ Mh, hf L S.Hm x z ∈ L.O}
      zero_mem' := ⟨S.ME.zero_mem, fun z _ => by simp [hf]⟩
      add_mem' := by
        rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
        refine ⟨S.ME.add_mem hu hv, fun z hz => ?_⟩
        have : hf L S.Hm (u + v) z = hf L S.Hm u z + hf L S.Hm v z :=
          (DualInter.hfL L S.Hm z).map_add u v
        rw [this]
        exact L.O.add_mem (hu' z hz) (hv' z hz)
      smul_mem' := by
        rintro s u ⟨hu, hu'⟩
        refine ⟨S.ME.smul_mem (s : E) hu, fun z hz => ?_⟩
        have : hf L S.Hm (s • u) z = s * hf L S.Hm u z := DualInter.smul_l L S.Hm s u z
        rw [this]
        exact L.O.mul_mem s.2 (hu' z hz) }
  obtain ⟨-, hidx, -, b, hb⟩ := GlobalTheory.T.card_discriminantModule_integralOverlattice_span L S.Hm S.herm S.ϖ S.ϖ_irr _ c hc0 hdet Mh Md
    (by rw [Set.Sum.elim_range]; exact hM)
    (fun x hx => by rw [hsp]; exact ((hMh x).1 hx).2)
    (fun x hx z hz => (hΛ₁.1.2 z).2 ((hMh z).1 hz).1 x ((hMh x).1 hx).1)
    (fun x => by rw [hsp]; rfl)
  rw [hca] at hidx
  have hq : resQ S.ϖ ^ (2 * S.a.toNat) ≠ 0 := pow_ne_zero _ (resQ_ne_zero _ S.ϖ_irr)
  have hN : Mh.toAddSubgroup.relIndex Md.toAddSubgroup ≠ 0 := fun h => hq (by rw [← hidx, h, zero_mul])
  have hNle : Mh.toAddSubgroup.relIndex Md.toAddSubgroup ≤ S.q ^ (2 * S.a.toNat) :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hq) (Dvd.intro _ hidx)
  have hY : Submodule.span E (Set.range (Sum.elim S.f S.f' ∘ finSumFinEquiv.symm)) = S.ME := by
    rw [finSumFinEquiv.symm.surjective.range_comp, Set.Sum.elim_range, Submodule.span_union]
    have : {i : Fin (r + 1) | (i : ℕ) < r + 1} = Set.univ := Set.eq_univ_of_forall fun i => i.2
    simp only [Frames.ME, Frames.spanTo, this, Set.image_univ]
  have h1 := encard_le S.herm (hli.comp _ finSumFinEquiv.symm.injective) hY hcompl.sup_eq_top
    Mh Λ₀ Md (fun _ => Iff.rfl) b hb hN
  have h2 : Mh.toAddSubgroup.relIndex Md.toAddSubgroup ^ Fintype.card (Fin (r + 1) ⊕ Fin (r + 1))
      ≤ S.q ^ (2 * S.a.toNat * (2 * r + 2)) := by
    rw [pow_mul, show Fintype.card (Fin (r + 1) ⊕ Fin (r + 1)) = 2 * r + 2 by simp; ring]
    exact Nat.pow_le_pow_left hNle _
  have h3 := h1.trans (Nat.cast_le.2 h2)
  have h4 := ENat.toENNReal_le.2 h3
  rw [ENat.toENNReal_coe, Nat.cast_pow] at h4
  exact h4

end GlobalTheory.HL.Gluing
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

theorem GlobalTheory.HL.Frames.amp_mass_eq_one_of_one_orbit : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (P : Submodule L.O S.V → Prop), (∃ Λ, S.IsTerm d Λ) → (∀ Λ Λ', S.IsTerm d Λ → S.IsTerm d Λ' → ∃ h ∈ S.St, Λ' = h • Λ) → (∀ Λ, S.IsTerm d Λ → P Λ ∧ S.mu Λ = 1 ∧ S.om d Λ = 1) → S.amp d P = 1 ∧ S.mass d P = 1 := by
  intro F _ _ _ _ _ E _ _ _ L r k S d P hex huniq hall
  obtain ⟨Λ, hΛ⟩ := hex
  let o₀ : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V) := Quotient.mk'' Λ
  have hout : S.IsTerm d o₀.out := by
    have hm : o₀.out ∈ MulAction.orbit S.St Λ :=
      MulAction.orbitRel_apply.1 (Quotient.mk_out (s := MulAction.orbitRel S.St _) Λ)
    obtain ⟨g, hg⟩ := hm
    rw [← hg]
    exact (GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms L r k S d Λ hΛ g.1 g.2).1
  have hother : ∀ o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V), o ≠ o₀ →
      ¬ S.IsTerm d o.out := by
    intro o ho ht
    obtain ⟨h, hh, e⟩ := huniq Λ o.out hΛ ht
    apply ho
    rw [← Quotient.out_eq' o]
    apply Quotient.sound'
    exact MulAction.orbitRel_apply.2 ⟨⟨h, hh⟩, e.symm⟩
  obtain ⟨hP, hmu, hom⟩ := hall _ hout
  constructor
  · unfold GlobalTheory.HL.Frames.amp
    rw [tsum_eq_single o₀]
    · rw [if_pos ⟨hout, hP⟩, hmu, hom]; simp
    · intro o ho
      exact if_neg fun hc => hother o ho hc.1
  · unfold GlobalTheory.HL.Frames.mass
    rw [tsum_eq_single o₀]
    · rw [if_pos ⟨hout, hP⟩, hmu]; simp
    · intro o ho
      exact if_neg fun hc => hother o ho hc.1
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.stabilizer_commensurable_invVolume_smul_complement : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∀ Λ : Submodule L.O S.V, IsLat L Λ → S.complementReferenceCompactSubgroup.relIndex (S.H0 ⊓ MulAction.stabilizer S.GLV Λ) ≠ 0 ∧ (S.H0 ⊓ MulAction.stabilizer S.GLV Λ).relIndex S.complementReferenceCompactSubgroup ≠ 0 ∧ ∀ h ∈ S.H0, invVol S.complementReferenceCompactSubgroup (S.H0 ⊓ MulAction.stabilizer S.GLV (h • Λ)) = invVol S.complementReferenceCompactSubgroup (S.H0 ⊓ MulAction.stabilizer S.GLV Λ)) ∧ ∀ d Λ, S.IsTerm d Λ → S.complementReferenceCompactSubgroup.relIndex (S.H0 ⊓ MulAction.stabilizer S.GLV d) ≠ 0 ∧ (S.H0 ⊓ MulAction.stabilizer S.GLV d).relIndex S.complementReferenceCompactSubgroup ≠ 0 := by
  first | exact @GlobalTheory.HL.Frames.stab_commensurable_invVol_smul | exact GlobalTheory.HL.Frames.stab_commensurable_invVol_smul | (intros; apply GlobalTheory.HL.Frames.stab_commensurable_invVol_smul <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitianFrames_complementUnitary_normalises_stabiliser : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ h ∈ S.H0, (∀ s ∈ S.St, h * s * h⁻¹ ∈ S.St) ∧ ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.IsTerm (h • d) (h • Λ) ∧ S.om (h • d) (h • Λ) = S.om d Λ ∧ S.mu (h • Λ) = S.mu Λ := by
  first | exact @GlobalTheory.HL.FixFrames.unitary_complement_acts | exact GlobalTheory.HL.FixFrames.unitary_complement_acts | (intros; apply GlobalTheory.HL.FixFrames.unitary_complement_acts <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.blockUnitriangular_rational_from_commonStabiliser : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ t : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ i j, ¬ (i < j ∧ ∀ l : Fin (r + 2), ((i : Fin (r + 1)) : ℕ) < l → (l : ℕ) ≤ ((j : Fin (r + 1)) : ℕ) → G.D l = 0) → t i j = if i = j then 1 else 0) → ∃ g ∈ G.St, ∀ j, g (G.f j) = ∑ i, t i j • G.f i := by
  first | exact @GlobalTheory.HL.RatPat.main | exact GlobalTheory.HL.RatPat.main | (intros; apply GlobalTheory.HL.RatPat.main <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.frameMatrix_close_gives_lattice_close_integral : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ Λ : G.Lt, Submodule.IsFullLattice E Λ → ∃ d : ∀ p, (A.loc p).Fp, (∀ p, d p ≠ 0) ∧ {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = d p}.Finite ∧ ∀ p (c0 : (A.loc p).Fp) (h : (G.S p).GLV) (M : Matrix (Fin (r + 1)) (Fin (r + 1)) (A.loc p).Ep), c0 ≠ 0 → c0 ∈ 𝒪[(A.loc p).Fp] → h ∈ (G.S p).St → (∀ j, h (A.bc p (G.f j)) = ∑ i, M i j • A.bc p (G.f i)) → (∀ i j, ∃ o ∈ (A.L p).O, (M - 1) i j = algebraMap (A.loc p).Fp (A.loc p).Ep (c0 * d p) * o) → h ∈ (G.S p).K0 ∧ ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, h x - x = algebraMap (A.loc p).Fp (A.loc p).Ep c0 • y := by
  first | exact @GlobalTheory.HL.FrameClose.close_lattice | exact GlobalTheory.HL.FrameClose.close_lattice | (intros; apply GlobalTheory.HL.FrameClose.close_lattice <;> first | assumption | exact (show Submodule.IsFullLattice _ _ from by assumption).toIsLattice)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.stabilizer_framesCoordinateLattice_goodPlace : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), Good S → S.a = 0 → ∀ d₀, S.IsTermW d₀ (coordLat S) 1 1 → S.St ⊓ MulAction.stabilizer S.GLV (coordLat S) = S.K0 := by
  first | exact @GlobalTheory.HL.StdStab.stab_coordLat | exact GlobalTheory.HL.StdStab.stab_coordLat | (intros; apply GlobalTheory.HL.StdStab.stab_coordLat <;> assumption)
end

section

open NumberField

theorem _root_.GlobalTheory.T.finite_isometryClasses_definiteHermitian_boundedScale : ∀ {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm → (∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) → ∀ (d c : ℕ), 0 < d → 0 < c → ∃ s : Finset (Submodule (𝓞 K) V), (∀ M₀ ∈ s, Submodule.IsLattice K M₀) ∧ ∀ M : Submodule (𝓞 K) V, Submodule.IsLattice K M → (∀ x ∈ M, ∀ y ∈ M, (d : K) * h x y ∈ Set.range (algebraMap (𝓞 K) K)) → (∀ y : V, (∀ x ∈ M, h x y ∈ Set.range (algebraMap (𝓞 K) K)) → (c : K) • y ∈ M) → ∃ M₀ ∈ s, ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g M₀ = M := by
  first | exact @GlobalTheory.hermLat_boundedScaleDual_finite | exact GlobalTheory.hermLat_boundedScaleDual_finite | (intros; apply GlobalTheory.hermLat_boundedScaleDual_finite <;> assumption)
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_ideal_coprime_conj_mul_eq_spanSingleton' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], Formalism.BasicNotions.CMData F E → ∀ (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), c ≠ 0 → ∀ N : 𝓞 E, N ≠ 0 → ∃ P : Ideal (𝓞 E), P ≠ ⊥ ∧ P ⊔ P.comap (RingOfIntegers.mapRingHom (starRingEnd E)) = ⊤ ∧ (∃ t : 𝓞 E, ∃ p ∈ P, t * N + p = 1) ∧ ∃ α : E, (P : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) α := by
  first | exact @GlobalTheory.exists_ideal_coprime_conj_mul_eq_spanSingleton | exact GlobalTheory.exists_ideal_coprime_conj_mul_eq_spanSingleton | (intros; apply GlobalTheory.exists_ideal_coprime_conj_mul_eq_spanSingleton <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

theorem _root_.GlobalTheory.T.conj_coefficients_weylModule_rowAct_normFock : ∀ (n : ℕ) (lam : DomWeight n), (∀ p ∈ delSq ℂ n lam, MvPolynomial.map (starRingEnd ℂ) p ∈ delSq ℂ n lam) ∧ (∀ (g : Matrix (Fin n) (Fin n) ℂ) (p : MvPolynomial (Fin n × Fin n) ℂ), MvPolynomial.map (starRingEnd ℂ) (Formalism.GradedWeylDivisibility.rowAct ℂ g p) = Formalism.GradedWeylDivisibility.rowAct ℂ (g.map (starRingEnd ℂ)) (MvPolynomial.map (starRingEnd ℂ) p)) ∧ ∀ p q : MvPolynomial (Fin n × Fin n) ℂ, normFock lam (MvPolynomial.map (starRingEnd ℂ) p) (MvPolynomial.map (starRingEnd ℂ) q) = normFock lam q p := by
  first | exact @GlobalTheory.ConjCoeff.conj_coefficients | exact GlobalTheory.ConjCoeff.conj_coefficients | (intros; apply GlobalTheory.ConjCoeff.conj_coefficients <;> assumption)
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.Torus

theorem exists_mulShift {k : Type} [Field k] [Finite k] (ψ ψ' : AddChar k ℂ) (h : ψ ≠ 1) (h' : ψ' ≠ 1) :
    ∃ a : k, a ≠ 0 ∧ ψ' = ψ.mulShift a := by
  classical
  haveI : Fintype k := Fintype.ofFinite k
  have hinj : Function.Injective ψ.mulShift :=
    AddChar.to_mulShift_inj_of_isPrimitive (AddChar.IsPrimitive.of_ne_one h)
  have hbij : Function.Bijective ψ.mulShift :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, by simp⟩
  obtain ⟨a, ha⟩ := hbij.2 ψ'
  refine ⟨a, ?_, ha.symm⟩
  rintro rfl
  exact h' (by rw [← ha, AddChar.mulShift_zero])

theorem conj_apply {k : Type} [Field k] {n : ℕ} (d : Fin n → kˣ) (M : Matrix (Fin n) (Fin n) k) (x y : Fin n) :
    (diagonal (fun i => ((d i)⁻¹ : kˣ).1) * M * diagonal (fun i => (d i).1) : Matrix (Fin n) (Fin n) k) x y
      = (((d x)⁻¹ * d y : kˣ) : k) * M x y := by
  rw [mul_diagonal, diagonal_mul, Units.val_mul]
  ring

private lemma inJ_diagonal_conj_iff {k : Type} [Field k] {n t : ℕ} (d : Fin n → kˣ) (M : Matrix (Fin n) (Fin n) k) :
    InJ n t n false M ↔ InJ n t n false (diagonal (fun i => ((d i)⁻¹ : kˣ).1) * M * diagonal (fun i => (d i).1)) := by
  have hc : ∀ x y : Fin n, (((d x)⁻¹ * d y : kˣ) : k) ≠ 0 := fun x y => Units.ne_zero _
  have h1 : ∀ x : Fin n, (((d x)⁻¹ * d x : kˣ) : k) = 1 := fun x => by
    rw [inv_mul_cancel, Units.val_one]
  simp only [InJ, conj_apply, mul_eq_zero, hc, false_or, Bool.false_eq_true, false_implies, and_true]
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · refine forall_congr' fun x => imp_congr_right fun _ => ?_
    rw [h1, one_mul]
  · refine forall_congr' fun x => forall_congr' fun y => imp_congr_right fun _ => ?_
    split_ifs with hxy
    · subst hxy
      rw [h1, one_mul]
    · simp [hc]

private lemma inv_pow_mul_pow_succ_eq {k : Type} [Field k] (u : kˣ) (x y : ℕ) (h : x + 1 = y) :
    (((u ^ x)⁻¹ * u ^ y : kˣ) : k) = u := by
  subst h
  rw [pow_succ, ← mul_assoc, inv_mul_cancel, one_mul]

theorem torus_transitive : ∀ (k : Type) [Field k] [Finite k] (n t : ℕ) (ψ ψ' : AddChar k ℂ) (χ χ' : ℕ → MulChar k ℂ), ψ ≠ 1 → ψ' ≠ 1 → ∃ d : Fin n → kˣ, ∀ M : Matrix (Fin n) (Fin n) k, (InJ n t n false M ↔ InJ n t n false (diagonal (fun i => ((d i)⁻¹ : kˣ).1) * M * diagonal (fun i => (d i).1))) ∧ lamJ ψ' χ' n t 0 n M = (lamJ ψ χ n t 0 n (diagonal (fun i => ((d i)⁻¹ : kˣ).1) * M * diagonal (fun i => (d i).1)))⁻¹ := by
  intro k _ _ n t ψ ψ' χ χ' hψ hψ'
  obtain ⟨a, ha, rfl⟩ := exists_mulShift ψ ψ' hψ hψ'
  set u : kˣ := Units.mk0 (-a) (neg_ne_zero.mpr ha) with hu
  refine ⟨fun i => u ^ (i : ℕ), fun M => ⟨inJ_diagonal_conj_iff _ M, ?_⟩⟩
  simp only [lamJ, conj_apply, Finset.prod_range_zero, mul_one, AddChar.mulShift_apply]
  rw [← AddChar.map_neg_eq_inv]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs with hxy
  · rw [inv_pow_mul_pow_succ_eq u _ _ hxy.1, hu, Units.val_mk0]
    ring
  · simp

end GlobalTheory.St.G.Torus
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.localUnitaryGroup_tuple_haar_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (a : ℕ) (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)), μ.IsAddHaarMeasure → ∀ g : HA (Fv F v) σ J, μ.map (fun X => g • X) = μ := by
  first | exact @GlobalTheory.LocalUnitaryHaar.haar_tuple_invariant | exact GlobalTheory.LocalUnitaryHaar.haar_tuple_invariant | (intros; apply GlobalTheory.LocalUnitaryHaar.haar_tuple_invariant <;> assumption)
end
