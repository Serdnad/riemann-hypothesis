module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle065
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle046
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle076
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle042
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermOverFrameCoordinates
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle025
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle082
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle083
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle084
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLocalUnitaryOfSelfDualAtPlace
public import Formalism.LocalToGlobal.HermitianForms.Bundle001
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle006
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeStabilizerInfLeConjNormalisingSubgroup
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

@[expose] public section

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.HL.CoordTermWt
open GlobalTheory.HL.CoordTerm

lemma unitri_mem {E W : Type} [CommRing E] [AddCommGroup W] [Module E W] {m : ℕ} (g g' : Fin m → W)
    (s : Matrix (Fin m) (Fin m) E) (h0 : ∀ i j, j < i → s i j = 0) (h1 : ∀ i, s i i = 1)
    (hs : ∀ j, g' j = ∑ i, s i j • g i) (A : Submodule E W) :
    (∀ b, g' b ∈ A) ↔ ∀ b, g b ∈ A := by
  constructor
  · intro h j
    induction j using WellFoundedLT.induction with
    | ind j ih =>
      have h2 : g j = g' j - ∑ i ∈ Finset.univ.erase j, s i j • g i := by
        rw [hs, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), h1, one_smul, add_sub_cancel_right]
      rw [h2]
      refine sub_mem (h j) (Submodule.sum_mem _ fun i hi => ?_)
      rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hi) with h3 | h3
      · exact A.smul_mem _ (ih i h3)
      · rw [h0 i j h3, zero_smul]; exact zero_mem _
  · intro h j
    rw [hs]
    exact Submodule.sum_mem _ fun i _ => A.smul_mem _ (h i)

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)

lemma fam_mem {R : Type} [Ring R] [Module R V] (t : Term V M r) (A : Submodule R V) :
    (∀ i, H.MMfam t i ∈ A) ↔ (∀ b, t.f b ∈ A) ∧
      ∀ b, algebraMap F E (LocNG.theta M)⁻¹ • (t.f' b - t.f b) ∈ A := by
  unfold HermSp.MMfam LocNG.theta
  cases M.split with
  | none =>
    simp only [Sum.forall, Sum.elim_inl, Sum.elim_inr, inv_one, map_one, one_smul]
    refine and_congr_right fun h => forall_congr' fun b => ?_
    exact (A.sub_mem_iff_left (h b)).symm
  | some g => simp only [Sum.forall, Sum.elim_inl, Sum.elim_inr]

lemma th_ne (S : Frames M.L r k) : S.th ≠ 0 := by
  unfold Frames.th
  split_ifs
  · intro h
    exact S.ϖ_irr.ne_zero (Subtype.ext h)
  · exact one_ne_zero

lemma lat_span (t : Term V M r) :
    c.lat (Submodule.span M.L.O (Set.range (H.MMfam t))) =
      S.Mof (fun b => c.e (t.f b)) (fun b => c.e (t.f' b)) := by
  refine eq_of_forall_ge_iff fun A => ?_
  unfold Coord.lat Frames.Mof
  rw [Submodule.map_le_iff_le_comap, Submodule.span_le, Submodule.span_le, Set.range_subset_iff,
    Set.union_subset_iff, Set.range_subset_iff, Set.range_subset_iff]
  refine (fam_mem t _).trans ?_
  rw [CoordUnip.theta_eq c]
  simp [Submodule.mem_comap]

lemma map_span (t : Term V M r) (A : Submodule E S.V) :
    (Submodule.span E (Set.range (H.MMfam t))).map (c.e : V →ₗ[E] S.V) ≤ A ↔
      (∀ b, c.e (t.f b) ∈ A) ∧ ∀ b, c.e (t.f' b) ∈ A := by
  rw [Submodule.map_le_iff_le_comap, Submodule.span_le, Set.range_subset_iff]
  refine (fam_mem t _).trans ?_
  rw [CoordUnip.theta_eq c]
  refine and_congr_right fun h => forall_congr' fun b => ?_
  have hu : IsUnit (algebraMap F E S.th⁻¹) := (IsUnit.mk0 _ (inv_ne_zero (th_ne S))).map _
  rw [Submodule.smul_mem_iff_of_isUnit _ hu, Submodule.sub_mem_iff_left _ (h b)]
  rfl

lemma ME_le (S : Frames M.L r k) (A : Submodule E S.V) :
    S.ME ≤ A ↔ (∀ b, S.f b ∈ A) ∧ ∀ b, S.f' b ∈ A := by
  unfold Frames.ME Frames.spanTo
  have h : {i : Fin (r + 1) | (i : ℕ) < r + 1} = Set.univ := by
    exact Set.eq_univ_of_forall fun i => i.2
  rw [sup_le_iff, Submodule.span_le, Submodule.span_le, h, Set.image_univ, Set.image_univ,
    Set.range_subset_iff, Set.range_subset_iff]
  rfl

theorem terms_correspond : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), (∀ (d : LocNG.Datum P) (t : Term V M r), LocNG.IsTermOver P d t → S.IsTerm (c.dat d) (c.lat t.abelian₂) ∧ LocNG.om P t = S.om (c.dat d) (c.lat t.abelian₂) ∧ (LocNG.BBne (H := H) t ↔ ¬ S.BBzero (c.dat d) (c.lat t.abelian₂))) ∧ (∀ (d : LocNG.Datum P) Λ, S.IsTerm (c.dat d) Λ → ∃ t, LocNG.IsTermOver P d t ∧ c.lat t.abelian₂ = Λ) ∧ ∀ δ Λ, S.IsTerm δ Λ → ∃ d : LocNG.Datum P, δ = c.dat d := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c
  letI := hM.loc
  haveI := hM.char0
  obtain ⟨hth, hN, hN', -, hpsi, -⟩ := GlobalTheory.HL.CoordUnip.transport M hM H r k P S c
  obtain ⟨-, iA, oA, sA⟩ := GlobalTheory.T.hermitianFrameCoordinates_transport_innerLattices M hM H r k P S c
  obtain ⟨-, iB, oB, sB⟩ := GlobalTheory.T.framePairCoordinates_transport_innerLattices M hM H r k P S c
  have T1 := isTermW_iff M hM H r k P S c
  have hsurj : ∀ Λ : Submodule M.L.O S.V, ∃ Λ₀, c.lat Λ₀ = Λ := by
    intro B
    refine ⟨B.comap ((c.e : V →ₗ[E] S.V).restrictScalars M.L.O), ?_⟩
    ext v
    obtain ⟨v, rfl⟩ := c.e.surjective v
    rw [mem_lat]; rfl
  refine ⟨?_, ?_, ?_⟩
  · rintro d ⟨Λ, f, f', T, T'⟩ ht
    obtain ⟨hT, hT', ⟨n, hn, hf, h1⟩, ⟨n', hn', hf', h2⟩, -⟩ := id ht
    dsimp only at hT hT' hf hf' h1 h2
    subst hT hT' hf hf'
    have hW := (T1 d n n' Λ).1 ⟨ht, hn, hn', h1, h2⟩
    have hI : S.IsTerm (c.dat d) (c.lat Λ) := ⟨(c.grp n, c.grp n'), hW⟩
    obtain ⟨w1, w2, -⟩ := GlobalTheory.HL.WitIndep.witness_independence M.L r k S _ _ _ _ hW
    obtain ⟨-, -, hle, -⟩ := GlobalTheory.HL.TermBasic.term_basic M.L r k S _ _ hI
    refine ⟨hI, ?_, ?_⟩
    · dsimp only
      rw [w1, ← (hpsi n).1, ← (hpsi n').2]
      rfl
    · dsimp only
      set t : Term V M r := ⟨Λ, fun b => n (P.A.f b), fun b => n' (P.B.f b), P.A.T, P.B.T⟩ with htd
      have e1 : ∀ b, c.e (t.f b) = c.grp n (S.f b) := fun b => by rw [c.f_eq, grp_e]
      have e2 : ∀ b, c.e (t.f' b) = c.grp n' (S.f' b) := fun b => by rw [c.f'_eq, grp_e]
      have hO : c.lat (Submodule.span M.L.O (Set.range (H.MMfam t))) = S.M (c.dat d) (c.lat Λ) := by
        rw [lat_span, w2]
        simp only [e1, e2]
      obtain ⟨o1, o2, -⟩ := GlobalTheory.HL.FrameOnto.unipotent_onto M.L r k S
      obtain ⟨s, ⟨s0, s1⟩, hs⟩ := o1 _ hW.2.2.1
      obtain ⟨s', ⟨s0', s1'⟩, hs'⟩ := o2 _ hW.2.2.2.1
      have hE : (Submodule.span E (Set.range (H.MMfam t))).map (c.e : V →ₗ[E] S.V) = S.ME := by
        refine eq_of_forall_ge_iff fun A => ?_
        rw [map_span, ME_le]
        simp only [e1, e2]
        exact and_congr (unitri_mem _ _ s s0 s1 hs A) (unitri_mem _ _ s' s0' s1' hs' A)
      have hE' : ∀ v, c.e v ∈ S.ME ↔ v ∈ Submodule.span E (Set.range (H.MMfam t)) := by
        intro v
        rw [← hE]
        constructor
        · rintro ⟨y, hy, h⟩
          have : y = v := c.e.injective h
          exact this ▸ hy
        · intro h; exact ⟨v, h, rfl⟩
      have hsat : ∀ v, c.e v ∈ S.sat (c.lat Λ) ↔
          v ∈ Λ ∧ v ∈ Submodule.span E (Set.range (H.MMfam t)) := by
        intro v
        rw [← hE', ← mem_lat c]
        rfl
      unfold Frames.BBzero
      constructor
      · rintro ⟨v, hv, hv1, hv2⟩ h
        apply hv2
        rw [← mem_lat c, hO, h, hsat]
        exact ⟨hv, hv1⟩
      · intro h
        by_contra hc
        apply h
        refine le_antisymm hle fun y hy => ?_
        obtain ⟨v, rfl⟩ := c.e.surjective y
        rw [hsat] at hy
        rw [← hO, mem_lat]
        by_contra hv
        exact hc ⟨v, hy.1, hy.2, hv⟩
  · rintro d Λ ⟨⟨n, n'⟩, hW⟩
    obtain ⟨Λ, rfl⟩ := hsurj Λ
    obtain ⟨n, rfl⟩ := c.grp.surjective n
    obtain ⟨n', rfl⟩ := c.grp.surjective n'
    exact ⟨_, ((T1 d n n' Λ).2 hW).1, rfl⟩
  · rintro δ Λ hI
    obtain ⟨⟨n, n'⟩, hA, hB, hn, hn', h1, h2, hc, -⟩ := id hI
    dsimp only at hn hn' h1 h2 hc
    obtain ⟨Λ, rfl⟩ := hsurj Λ
    obtain ⟨n, rfl⟩ := c.grp.surjective n
    obtain ⟨n', rfl⟩ := c.grp.surjective n'
    obtain ⟨L, hL⟩ := oA _ hA
    obtain ⟨L', hL'⟩ := oB _ hB
    rw [hL, ← iA] at hA
    rw [hL', ← iB] at hB
    rw [hL, ← sA, ← lat_img, lat_inj] at h1
    rw [hL', ← sB, ← lat_img, lat_inj] at h2
    rw [← hN] at hn
    rw [← hN'] at hn'
    let d : LocNG.Datum P :=
      { L := L, L' := L', hL := hA, hL' := hB
        io := {q | ∃ g, M.split = some g ∧ q ∈ H.iotaGraph g ⟨Λ, P.A.f, P.B.f, P.A.T, P.B.T⟩}
        io_L := fun h => by simp [h] }
    have hW := (T1 d n n' Λ).1 ⟨⟨rfl, rfl, ⟨n, hn, rfl, h1⟩, ⟨n', hn', rfl, h2⟩, fun g hg => ⟨?_, ?_⟩⟩,
      hn, hn', h1, h2⟩
    · obtain ⟨-, -, -, -, -, -, -, hu⟩ := GlobalTheory.HL.TermBasic.term_basic M.L r k S _ _ hI
      exact ⟨d, (hu _ ⟨(c.grp n, c.grp n'), hW⟩).symm⟩
    · intro b
      have hq : S.th = (g.q : F) := by rw [← hth, LocNG.theta, hg]
      have h := hc b
      rwa [c.f_eq, c.f'_eq, grp_e, grp_e, ← map_sub, inTh_iff, hq] at h
    · ext q
      simp [d, hg]

end GlobalTheory.HL.CoordTermWt
end
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CoordDatum

theorem exists_invVol_eq_mul {G : Type} [Group G] (K' K0 : Subgroup G) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ K : Subgroup G, K0.relIndex K ≠ 0 → K.relIndex K0 ≠ 0 →
      invVol K' K = κ * invVol K0 K := by
  by_cases hc : K'.relIndex K0 ≠ 0 ∧ K0.relIndex K' ≠ 0
  · refine ⟨invVol K' K0, ?_, fun K hK hK' => ?_⟩
    · unfold invVol
      positivity
    · exact (invVol_mul_pos_le_conj K' K0 K hc.1 hc.2
        (Subgroup.relIndex_ne_zero_trans hc.1 hK)
        (Subgroup.relIndex_ne_zero_trans hK' hc.2)).1
  · refine ⟨0, le_rfl, fun K hK hK' => ?_⟩
    rw [zero_mul]
    unfold invVol
    by_cases h1 : K.relIndex K' = 0
    · simp [h1]
    · have h2 : K'.relIndex K = 0 := by
        by_contra h2
        exact hc ⟨Subgroup.relIndex_ne_zero_trans h2 hK', Subgroup.relIndex_ne_zero_trans hK h1⟩
      simp [h2]

theorem exists_wt_eq_mul_nu : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), ∀ d0 : LocNG.Datum P, ∃ κ : ℝ, 0 ≤ κ ∧ ∀ (d : LocNG.Datum P) Λ, S.IsTerm (c.dat d) Λ → LocNG.Datum.wt d0 d = κ * S.nu (c.dat d) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c d0
  have := hM.loc
  have := hM.char0
  obtain ⟨κ, hκ, hK⟩ :=
    exists_invVol_eq_mul (S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d0)) S.complementReferenceCompactSubgroup
  refine ⟨κ, hκ, fun d Λ hT => ?_⟩
  obtain ⟨h1, h2⟩ := (Frames.stab_commensurable_invVol_smul M.L r k S).2 (c.dat d) Λ hT
  rw [(transport M hM H r k P S c).2.2.2.2 d0 d]
  exact hK _ h1 h2

end GlobalTheory.HL.CoordDatum
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.term_over_frame_coordinates : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), ∀ (d : LocNG.Datum P) (n n' : V ≃ₗ[E] V) (Λ : Submodule M.L.O V), LocNG.IsTermOver P d ⟨Λ, fun b => n (P.A.f b), fun b => n' (P.B.f b), P.A.T, P.B.T⟩ ∧ n ∈ P.A.N ∧ n' ∈ P.B.N ∧ Λ = LocNG.img n (P.A.LamStd d.L) ∧ Λ = LocNG.img n' (P.B.LamStd d.L') ↔ S.IsTermW (c.dat d) (c.lat Λ) (c.grp n) (c.grp n') := by
  first | exact @GlobalTheory.HL.CoordTerm.isTermW_iff | exact GlobalTheory.HL.CoordTerm.isTermW_iff | (intros; apply GlobalTheory.HL.CoordTerm.isTermW_iff <;> assumption)
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_adelic_unitary_of_finite_support : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (h : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (E ⊗[F] v.adicCompletion F)), (∀ v, h v ∈ UPts σ J (v.adicCompletion F)) → {v | h v ≠ 1}.Finite → ∃ x ∈ UPts σ J (Ad F), ∀ v, bc (prV (E := E) v) x = h v := by
  first | exact @GlobalTheory.St.G.exists_adelic_of_finite_support | exact GlobalTheory.St.G.exists_adelic_of_finite_support | (intros; apply GlobalTheory.St.G.exists_adelic_of_finite_support <;> assumption)
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isLocallySelfDual_of_hermitianLatticeOfLevel : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), TLat cm.sig J T f L → ∀ (v : HeightOneSpectrum (𝓞 F)), (T : 𝓞 F) ∉ v.asIdeal → SelfDualAt cm.sig J v L := by
  first | exact @GlobalTheory.St.G.selfDualAt_of_tLat | exact GlobalTheory.St.G.selfDualAt_of_tLat | (intros; apply GlobalTheory.St.G.selfDualAt_of_tLat <;> assumption)
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.transport_frame_along_unitary_adelic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (Λ Λ' : Submodule (OAd F E) (Fin n → E ⊗[F] Ad F)) (g k : ℕ) (h : UPts σ J (Ad F)), (∀ x, (h⁻¹).1.1 *ᵥ x ∈ Λ' ↔ x ∈ Λ) → ∀ Fr : AdFrame σ J Λ g k, ∃ Fr' : AdFrame σ J Λ' g k, ∀ y : UPts σ J (Ad F), (Fr.InK y.1 ↔ Fr'.InK (h⁻¹ * y * h : UPts σ J (Ad F)).1) ∧ Fr.chi y.1 = Fr'.chi (h⁻¹ * y * h : UPts σ J (Ad F)).1 := by
  first | exact @GlobalTheory.St.G.FrMap.transport | exact GlobalTheory.St.G.FrMap.transport | (intros; apply GlobalTheory.St.G.FrMap.transport <;> assumption)
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.first_components_basis_local_lattice_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → (∀ x, x ∈ intV E v ↔ (sp x).1 ∈ v.adicCompletionIntegers F ∧ (sp x).2 ∈ v.adicCompletionIntegers F) → ∀ (g : ℕ), IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {((g : ℕ) : v.adicCompletionIntegers F)} → ∀ (L : Submodule (𝓞 E) (Fin n → E)), IsLat L → ∀ (c : Fin n → Fin n → E ⊗[F] v.adicCompletion F) (S : Set (Fin n → E ⊗[F] v.adicCompletion F)), (∀ j, c j ∈ loc v L) → (∀ x ∈ S, ∀ a, (sp (x a)).1 = 0) → (∀ y ∈ loc v L, InModL (loc v L) g (Set.range c ∪ S) y) → ∃ fr : GL (Fin n) (v.adicCompletion F), (fr : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = Matrix.of (fun a j => (sp (c j a)).1) ∧ ∀ x : Fin n → v.adicCompletion F, (∃ y ∈ loc v L, ∀ a, (sp (y a)).1 = x a) ↔ ∀ a, ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x a ∈ v.adicCompletionIntegers F := by
  first | exact @GlobalTheory.St.G.first_components_basis | exact GlobalTheory.St.G.first_components_basis | (intros; apply GlobalTheory.St.G.first_components_basis <;> assumption)
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.local_frame_idempotent_factor_cases : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR σ (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → ∀ (g : ℕ), (g : 𝓞 F) ∈ v.asIdeal → ∀ (L : Submodule (𝓞 E) (Fin n → E)), IsLat L → 0 < n → ∀ e : E ⊗[F] v.adicCompletion F, e * e = e → e * sigR σ (v.adicCompletion F) e = 0 → (∀ y ∈ loc v L, ∃ z ∈ loc v L, (1 - e - sigR σ (v.adicCompletion F) e) • y = (g : E ⊗[F] v.adicCompletion F) • z) → sp e = (1, 0) ∨ sp e = (0, 1) := by
  first | exact @GlobalTheory.St.G.local_idempotent_cases | exact GlobalTheory.St.G.local_idempotent_cases | (intros; apply GlobalTheory.St.G.local_idempotent_cases <;> assumption)
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.mem_level_of_preserves_first_components_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → ∀ (L : Submodule (𝓞 E) (Fin n → E)), SelfDualAt cm.sig J v L → ∀ κ ∈ UPts cm.sig J (v.adicCompletion F), (∀ x : Fin n → v.adicCompletion F, (∃ y ∈ loc v L, ∀ b, (sp (y b)).1 = x b) ↔ ∃ y ∈ loc v L, ∀ b, (sp (y b)).1 = ((bc ((RingHom.fst _ _).comp sp.toRingHom) κ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x b) → κ ∈ levelVL cm.sig J v L := by
  first | exact @GlobalTheory.St.G.mem_levelVL_of_first_components | exact GlobalTheory.St.G.mem_levelVL_of_first_components | (intros; apply GlobalTheory.St.G.mem_levelVL_of_first_components <;> assumption)
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_localUnitary_of_selfDual_at_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (L M : Submodule (𝓞 E) (Fin n → E)), IsLat L → IsLat M → ∀ (v : HeightOneSpectrum (𝓞 F)), SelfDualAt cm.sig J v L → SelfDualAt cm.sig J v M → ∃ h ∈ UPts cm.sig J (v.adicCompletion F), ∀ x, x ∈ loc v L ↔ h.1 *ᵥ x ∈ loc v M := by
  first | exact @GlobalTheory.St.G.Unimod.exists_unitary_of_selfDualAt | exact GlobalTheory.St.G.Unimod.exists_unitary_of_selfDualAt | (intros; apply GlobalTheory.St.G.Unimod.exists_unitary_of_selfDualAt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem intV_iff_sp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (gp : Fin 2 → ℕ) (G : GLoc F E cm.sig gp), (∀ i, (gp i).Prime) → (∀ i, SplitsIn E (gp i)) → ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (hv : (gp i : 𝓞 F) ∈ v.asIdeal) (x : E ⊗[F] v.adicCompletion F), x ∈ intV E v ↔ (G.sp i v hv x).1 ∈ v.adicCompletionIntegers F ∧ (G.sp i v hv x).2 ∈ v.adicCompletionIntegers F := by
  intro F E _ _ _ _ _ _ cm gp G _ _ i v hv x
  exact split_integral_local F E v (G.sp i v hv) (G.sp_alg i v hv) x

end GlobalTheory.St.G
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.latticeStabilizer_inf_le_conj_normalisingSubgroup : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ n ∈ S.N, ∃ h ∈ S.St, S.St ⊓ stabL L (Submodule.span L.O (Set.range fun b => n (S.f b))) ≤ MulAut.conj h • S.K0 ∧ ∃ u : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUni u ∧ (∀ i j : Fin (r + 1), sameBlock S.w.blocks i j = true → u i j ∈ L.O) ∧ ∀ j, h⁻¹ (n (S.f j)) = ∑ i, u i j • S.f i := by
  first | exact @GlobalTheory.HL.StabConj.main | exact GlobalTheory.HL.StabConj.main | (intros; apply GlobalTheory.HL.StabConj.main <;> assumption)
end
