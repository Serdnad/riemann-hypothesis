module

public import Development.EtaleCohomology.EtaleSheaves.Bundle016
public import Development.EtaleCohomology.EtaleSheaves.Bundle017
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGeoVCut

namespace LateralTheory.E.LeafGeoVV2Cut

def CurveThroughGenericPointSpreadsToSmoothProperFamily : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k)
  [IsProper p] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω], (∀ R : Subalgebra k Ω, R.FG → ringKrullDim R <
    topologicalKrullDim X) → ∀ {C0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (e : C0 ⟶ X), IsCurve c0 →
    e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) → genericPoint X ∈ Set.range e →
    ∀ (C1 C2 : Scheme.{0}) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1), IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
      Surjective γ1 → Surjective γ2 → FamilyVe (k := k) X c0 e γ1 γ2

def LeafDescendQF : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k)
  [IsProper p] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω], (∀ R : Subalgebra k Ω, R.FG → ringKrullDim R <
    topologicalKrullDim X) → ∀ {C0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (e : C0 ⟶ X), IsCurve c0 →
    e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) → genericPoint X ∈ Set.range e →
    ∀ (C1 C2 : Scheme.{0}) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1), IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
      Surjective γ1 → Surjective γ2 →
    ∃ (R : Subalgebra k Ω), R.FG ∧ ∃ (D0 D1 D2 : Scheme.{0}) (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1)
      (f : D0 ⟶ X) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2)
      (hf : f ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))),
      IsSeparated q ∧ QuasiCompact q ∧ SmoothOfRelativeDimension 1 q ∧
      IsSeparated (d1 ≫ q) ∧ QuasiCompact (d1 ≫ q) ∧ SmoothOfRelativeDimension 1 (d1 ≫ q) ∧
      IsSeparated (d2 ≫ d1 ≫ q) ∧ QuasiCompact (d2 ≫ d1 ≫ q) ∧ SmoothOfRelativeDimension 1 (d2 ≫ d1 ≫ q) ∧
      IsIntegral D0 ∧ IsIntegral D1 ∧ IsIntegral D2 ∧
      LocallyQuasiFinite (pullback.lift q f hf.symm) ∧ LocallyQuasiFinite d1 ∧ LocallyQuasiFinite d2 ∧
      topologicalKrullDim D0 ≤ ringKrullDim R + 1 ∧
      IsPullback v0 c0 q (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ∧
      IsPullback v1 (γ1 ≫ c0) (d1 ≫ q) (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ∧
      IsPullback v2 (γ2 ≫ γ1 ≫ c0) (d2 ≫ d1 ≫ q) (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ∧
      γ1 ≫ v0 = v1 ≫ d1 ∧ γ2 ≫ v1 = v2 ≫ d2 ∧ v0 ≫ f = e

def LeafExtendZMT : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p]
  (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) (B : Scheme.{0}) (b : B ⟶ Sp k) [IsProper b]
  (ι : Sp R ⟶ B) [IsOpenImmersion ι], ι ≫ b = Spec.map (CommRingCat.ofHom (algebraMap k R)) →
  ∀ {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1) (e : C0 ⟶ X),
    IsCurve c0 → IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
    e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) →
  ∀ {D0 D1 D2 : Scheme.{0}} (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1) (f : D0 ⟶ X) (v0 : C0 ⟶ D0)
    (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2) (hf : f ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))),
    IsSeparated q → QuasiCompact q → SmoothOfRelativeDimension 1 q →
    IsSeparated (d1 ≫ q) → QuasiCompact (d1 ≫ q) → SmoothOfRelativeDimension 1 (d1 ≫ q) →
    IsSeparated (d2 ≫ d1 ≫ q) → QuasiCompact (d2 ≫ d1 ≫ q) → SmoothOfRelativeDimension 1 (d2 ≫ d1 ≫ q) →
    IsIntegral D0 → IsIntegral D1 → IsIntegral D2 →
    LocallyQuasiFinite (pullback.lift q f hf.symm) → LocallyQuasiFinite d1 → LocallyQuasiFinite d2 →
    IsPullback v0 c0 q (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) →
    IsPullback v1 (γ1 ≫ c0) (d1 ≫ q) (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) →
    IsPullback v2 (γ2 ≫ γ1 ≫ c0) (d2 ≫ d1 ≫ q) (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) →
    γ1 ≫ v0 = v1 ≫ d1 → γ2 ≫ v1 = v2 ≫ d2 → v0 ≫ f = e →
    ∃ (Y0 Y1 Y2 : Scheme.{0}) (π : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1) (h : Y0 ⟶ X) (V : B.Opens)
      (u0 : C0 ⟶ Y0) (u1 : C1 ⟶ Y1) (u2 : C2 ⟶ Y2),
      Set.range (Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ ι) ⊆ V ∧
      SmP π V ∧ SmP (g1 ≫ π) V ∧ SmP (g2 ≫ g1 ≫ π) V ∧ IsProper (g2 ≫ g1 ≫ h) ∧
      IrreducibleSpace Y0 ∧ topologicalKrullDim Y0 ≤ topologicalKrullDim D0 ∧
      IsPullback u0 c0 π (Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ ι) ∧
      IsPullback u1 (γ1 ≫ c0) (g1 ≫ π) (Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ ι) ∧
      IsPullback u2 (γ2 ≫ γ1 ≫ c0) (g2 ≫ g1 ≫ π) (Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ ι) ∧
      γ1 ≫ u0 = u1 ≫ g1 ∧ γ2 ≫ u1 = u2 ≫ g2 ∧ u0 ≫ h = e

theorem spread_of (hD : LeafDescendQF) (hB : LateralTheory.E.LeafSpreadVCut.LeafCloseB) (hE : LeafExtendZMT) :
    CurveThroughGenericPointSpreadsToSmoothProperFamily := by
  intro k _ _ X _ p _ Ω _ _ _ hdim C0 c0 e hc0 he hη C1 C2 γ1 γ2 h1 h2 s1 s2
  obtain ⟨R, hR, D0, D1, D2, q, d1, d2, f, v0, v1, v2, hf, sp0, qc0, sm0, sp1, qc1, sm1, sp2, qc2, sm2, i0, i1, i2,
    qf0, qf1, qf2, dD, P0, P1, P2, c1, c2, ve⟩ := hD k p Ω hdim c0 e hc0 he hη C1 C2 γ1 γ2 h1 h2 s1 s2
  have : Algebra.FiniteType k R := Subalgebra.fg_iff_finiteType R |>.mp hR
  obtain ⟨B, b, ι, iB, pb, oι, hι, dB⟩ := hB k R
  obtain ⟨Y0, Y1, Y2, π, g1, g2, h, V, u0, u1, u2, hs, m0, m1, m2, f1, irrY, dY, Q0, Q1, Q2, e1, e2, ue⟩ :=
    hE k p Ω R B b ι hι c0 γ1 γ2 e hc0 h1 h2 he q d1 d2 f v0 v1 v2 hf sp0 qc0 sm0 sp1 qc1 sm1 sp2 qc2 sm2 i0 i1 i2
      qf0 qf1 qf2 P0 P1 P2 c1 c2 ve
  have hR' : ringKrullDim R < topologicalKrullDim X := hdim R hR
  obtain ⟨hle, hlt⟩ := LateralTheory.E.LeafSpreadVCut.succ_le_of_lt hR'
  have := hc0.1
  obtain ⟨x⟩ : Nonempty C0 := inferInstance
  refine ⟨B, Y0, Y1, Y2, b, V, π, g1, g2, h, Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ ι,
    u0, u1, u2, iB, pb, hs, m0, m1, m2, f1, lt_of_le_of_lt dB hR', irrY, dY.trans (dD.trans hle),
    lt_of_le_of_lt (dY.trans dD) hlt, ⟨u0 x, ?_⟩, Q0, Q1, Q2, e1, e2, ue⟩
  show π (u0 x) ∈ (V : Set B)
  rw [← Scheme.Hom.comp_apply, Q0.w]
  exact hs ⟨c0 x, rfl⟩

theorem geoV_of (hC : LeafCurveV) (hS : CurveThroughGenericPointSpreadsToSmoothProperFamily) : LateralTheory.E.LeafGeoCut.LeafGeoV := by
  intro k _ _ X _ p _ hd
  obtain ⟨Ω, iF, iA, iK, C0, c0, e, hc0, he, hη, hdim⟩ := hC k p hd
  refine ⟨Ω, iF, iA, iK, C0, c0, hc0, fun C1 C2 γ1 γ2 h1 h2 s1 s2 => ?_⟩
  obtain ⟨B, Y0, Y1, Y2, b, V, π, g1, g2, h, s, u0, u1, u2, iB, pb, hs, m0, m1, m2, f1, dB, irr, dY, fin, ne,
    P0, P1, P2, w1, w2, ue⟩ := hS k p Ω hdim c0 e hc0 he hη C1 C2 γ1 γ2 h1 h2 s1 s2
  refine ⟨B, Y0, Y1, Y2, b, V, π, g1, g2, h, s, u0, u1, u2, iB, pb, hs, m0, m1, m2, f1, ?_, dB, irr, dY, fin, ne,
    P0, P1, P2, w1, w2⟩
  obtain ⟨x0, hx0⟩ := hη
  obtain ⟨x1, rfl⟩ := s1.surj x0
  obtain ⟨x2, rfl⟩ := s2.surj x1
  have key : u2 ≫ g2 ≫ g1 ≫ h = γ2 ≫ γ1 ≫ e := by
    rw [← ue, ← Category.assoc u2 g2, ← w2, Category.assoc, ← Category.assoc u1 g1, ← w1]
    simp only [Category.assoc]
  have := f1
  refine surj_of_generic (g2 ≫ g1 ≫ h) ⟨u2 x2, ?_⟩
  rw [← Scheme.Hom.comp_apply, key, ← hx0]
  simp only [Scheme.Hom.comp_apply]

end LateralTheory.E.LeafGeoVV2Cut

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Set Order TopologicalSpace Topology

namespace LateralTheory.E.LeafBdryPf

def univIC (Y : Type*) [TopologicalSpace Y] [IrreducibleSpace Y] : IrreducibleCloseds Y where
  carrier := univ
  isIrreducible' := IrreducibleSpace.isIrreducible_univ Y
  isClosed' := isClosed_univ

lemma withBot_lt_of_add_one_le {a b : WithBot ℕ∞} (h : a + 1 ≤ b) (hb : b < ⊤) (ha : a ≠ ⊥) : a < b := by
  induction a using WithBot.recBotCoe with
  | bot => exact absurd rfl ha
  | coe a =>
    induction b using WithBot.recBotCoe with
    | bot => exact absurd h (by simp)
    | coe b =>
      have hb' : b < ⊤ := by
        rw [← WithBot.coe_top] at hb
        exact WithBot.coe_lt_coe.mp hb
      have h' : a + 1 ≤ b := by exact_mod_cast h
      have ha' : a ≠ ⊤ := (lt_of_le_of_lt (le_self_add.trans h') hb').ne
      exact WithBot.coe_lt_coe.mpr ((ENat.add_one_le_iff ha').mp h')

theorem dim_lt_of_closedEmbedding {Z Y : Type*} [TopologicalSpace Z] [TopologicalSpace Y] [IrreducibleSpace Y]
    (f : Z → Y) (hf : IsClosedEmbedding f) (hfin : topologicalKrullDim Y < ⊤) (hne : (range f)ᶜ.Nonempty) :
    topologicalKrullDim Z < topologicalKrullDim Y := by
  have hY : Nonempty (IrreducibleCloseds Y) := ⟨univIC Y⟩
  by_cases hZ : Nonempty (IrreducibleCloseds Z)
  · have hlt : ∀ c : IrreducibleCloseds Z, IrreducibleCloseds.map f hf.continuous c < univIC Y := by
      intro c
      refine lt_of_le_of_ne (fun x _ => trivial) ?_
      intro heq
      obtain ⟨y, hy⟩ := hne
      have h1 : (IrreducibleCloseds.map f hf.continuous c : Set Y) ⊆ range f := by
        rw [IrreducibleCloseds.coe_map]
        exact closure_minimal (image_subset_range _ _) hf.isClosed_range
      apply hy
      apply h1
      rw [heq]
      trivial
    let g : WithTop (IrreducibleCloseds Z) → IrreducibleCloseds Y :=
      fun o => WithTop.recTopCoe (univIC Y) (IrreducibleCloseds.map f hf.continuous) o
    have hg : StrictMono g := by
      intro a b hab
      induction a using WithTop.recTopCoe with
      | top => exact absurd hab (by simp)
      | coe a =>
        induction b using WithTop.recTopCoe with
        | top => exact hlt a
        | coe b =>
          exact IrreducibleCloseds.map_strictMono_of_isInducing hf.isInducing (WithTop.coe_lt_coe.mp hab)
    have h := krullDim_le_of_strictMono g hg
    rw [krullDim_WithTop] at h
    exact withBot_lt_of_add_one_le h hfin (bot_lt_krullDim).ne'
  · rw [not_nonempty_iff] at hZ
    have : topologicalKrullDim Z = ⊥ := krullDim_eq_bot
    rw [this]
    exact bot_lt_krullDim

theorem LeafBdry_of : LateralTheory.E.LeafGeoCut.LeafBdry := by
  intro Y B W p ι hι hirr hfin hne
  have : IsClosedImmersion (pullback.fst p ι) := inferInstance
  refine dim_lt_of_closedEmbedding _ (pullback.fst p ι).isClosedEmbedding hfin ?_
  rw [Scheme.Pullback.range_fst, ← preimage_compl]
  exact hne

end LateralTheory.E.LeafBdryPf

end
end

section

noncomputable section
open LateralTheory.E.t_E1Cut LateralTheory.E.LCSplitPf LateralTheory.E.TorEtPf

namespace LateralTheory.E.ProjFPf

section Tw
variable {q : ℕ} [NeZero q] {A : Type} [CommRing A] {ε : ZMod q → A}

theorem twist_apply (hε : CompleteOrthogonalIdempotents ε) (z : ZMod q → A) (k : ZMod q) :
    twist hε z k = ∑ c, ε c * z (k + c) := rfl

def tinv (ε : ZMod q → A) (z : ZMod q → A) : ZMod q → A := fun k => ∑ d, ε (-d) * z (k + d)

theorem twist_tinv (hε : CompleteOrthogonalIdempotents ε) (z : ZMod q → A) : twist hε (tinv ε z) = z := by
  funext k
  rw [twist_apply]
  unfold tinv
  have : ∀ c, ε c * ∑ d, ε (-d) * z (k + c + d) = ε c * z k := by
    intro c
    rw [Finset.mul_sum, Finset.sum_eq_single (-c)]
    · rw [neg_neg, ← mul_assoc, (hε.idem c).eq, add_neg_cancel_right]
    · intro d _ hd
      have : c ≠ -d := fun h => hd (by rw [h, neg_neg])
      rw [← mul_assoc, hε.ortho this, zero_mul]
    · simp
  simp_rw [this, ← Finset.sum_mul, hε.complete, one_mul]

theorem tinv_twist (hε : CompleteOrthogonalIdempotents ε) (z : ZMod q → A) : tinv ε (twist hε z) = z := by
  funext k
  unfold tinv
  simp_rw [twist_apply]
  have : ∀ d, ε (-d) * ∑ c, ε c * z (k + d + c) = ε (-d) * z k := by
    intro d
    rw [Finset.mul_sum, Finset.sum_eq_single (-d)]
    · rw [← mul_assoc, (hε.idem (-d)).eq, add_neg_cancel_right]
    · intro c _ hc
      rw [← mul_assoc, hε.ortho (Ne.symm hc), zero_mul]
    · simp
  simp_rw [this, ← Finset.sum_mul]
  rw [show (∑ d : ZMod q, ε (-d)) = ∑ d, ε d from
    Fintype.sum_equiv (Equiv.neg _) _ _ (fun _ => rfl), hε.complete, one_mul]

theorem twist_const_mul (hε : CompleteOrthogonalIdempotents ε) (a : A) (z : ZMod q → A) :
    twist hε (fun k => a * z k) = fun k => a * twist hε z k := by
  funext k
  simp only [twist_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

theorem eq_zero_of_twist (hε : CompleteOrthogonalIdempotents ε) (z : ZMod q → A) (h : twist hε z = 0) : z = 0 := by
  rw [← tinv_twist hε z, h]; funext k; simp [tinv]
end Tw

section Main
variable {q : ℕ} [NeZero q] {S : Type} [CommRing S] (f g : S)

theorem mem_tor {ε : ZMod q → Localization.Away (f * g)} (hε : CompleteOrthogonalIdempotents ε) (p : Amb f g q) :
    p ∈ Tor f g hε ↔ ∀ k, rL f g (p.1 k) = twist hε (fun j => rR f g (p.2 j)) k :=
  funext_iff

theorem rR_alg (a : S) : rR f g (algebraMap S (Localization.Away g) a) = algebraMap S (Localization.Away (f * g)) a := by
  unfold rR; exact IsLocalization.Away.awayToAwayLeft_eq g f a

theorem rL_alg (a : S) : rL f g (algebraMap S (Localization.Away f) a) = algebraMap S (Localization.Away (f * g)) a := by
  unfold rL; exact IsLocalization.Away.awayToAwayRight_eq f g a

theorem unit_g : IsUnit (algebraMap S (Localization.Away (f * g)) g) := by
  refine isUnit_of_mul_isUnit_right (x := algebraMap S (Localization.Away (f * g)) f) ?_
  rw [← map_mul]; exact IsLocalization.Away.algebraMap_isUnit (f * g)

theorem kill (z : Localization.Away g) (hz : rR f g z = 0) :
    ∃ m : ℕ, algebraMap S (Localization.Away g) f ^ m * z = 0 := by
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers g) z
  dsimp only at hz ⊢
  have hb : algebraMap S (Localization.Away (f * g)) b = 0 := by
    rw [← rR_alg, ← IsLocalization.mk'_spec (Localization.Away g) b s, map_mul, hz, zero_mul]
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (f * g)) _ b).mp hb
  refine ⟨n, ?_⟩
  have hu : IsUnit (algebraMap S (Localization.Away g) (s : S) * algebraMap S (Localization.Away g) (g ^ n)) :=
    (IsLocalization.map_units (Localization.Away g) s).mul
      (by rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit g).pow n)
  refine (hu.mul_left_eq_zero).mp ?_
  calc algebraMap S (Localization.Away g) f ^ n * IsLocalization.mk' (Localization.Away g) b s *
        (algebraMap S (Localization.Away g) (s : S) * algebraMap S (Localization.Away g) (g ^ n))
      = algebraMap S (Localization.Away g) f ^ n *
        (IsLocalization.mk' (Localization.Away g) b s * algebraMap S (Localization.Away g) (s : S)) *
        algebraMap S (Localization.Away g) (g ^ n) := by ring
    _ = algebraMap S (Localization.Away g) ((f * g) ^ n * b) := by
        rw [IsLocalization.mk'_spec, mul_pow]; simp only [map_mul, map_pow]; ring
    _ = 0 := by simp only at hn; rw [hn, map_zero]
end Main

theorem projF : ProjF := by
  intro q _ S _ f g _ ε hε
  let _ := (torMap f g hε).toAlgebra
  let _ := (pr1 f g hε).toAlgebra
  have hA : ∀ t : Tor f g hε, algebraMap (Tor f g hε) (ZMod q → Localization.Away f) t = (t : Amb f g q).1 :=
    fun _ => rfl
  have hf : algebraMap S (Tor f g hε) f = torMap f g hε f := rfl
  have hT1 : ((torMap f g hε f : Tor f g hε) : Amb f g q).1 = fun _ => algebraMap S (Localization.Away f) f := rfl
  have hT2 : ((torMap f g hε f : Tor f g hε) : Amb f g q).2 = fun _ => algebraMap S (Localization.Away g) f := rfl
  refine IsLocalization.Away.mk _ ?_ ?_ ?_
  · rw [hA, hf, hT1, Pi.isUnit_iff]; intro _; exact IsLocalization.Away.algebraMap_isUnit f
  · intro s
    set w : ZMod q → Localization.Away (f * g) := tinv ε (fun k => rL f g (s k)) with hw
    obtain ⟨⟨_, n, rfl⟩, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (Submonoid.powers (f * g)) w
    have hb' : ∀ i, ∃ a, algebraMap S (Localization.Away (f * g)) a = (f * g) ^ n • w i :=
      fun i => RingHom.mem_rangeS.mp (hb i)
    choose a ha using hb'
    let y : ZMod q → Localization.Away g := fun k =>
      IsLocalization.mk' (Localization.Away g) (a k) (⟨g ^ n, n, rfl⟩ : Submonoid.powers g)
    have hy : ∀ k, rR f g (y k) = algebraMap S _ (f ^ n) * w k := by
      intro k
      have hu : IsUnit (algebraMap S (Localization.Away (f * g)) (g ^ n)) := by
        rw [map_pow]; exact (unit_g f g).pow n
      apply hu.mul_left_injective
      have e1 := IsLocalization.mk'_spec (Localization.Away g) (a k) (⟨g ^ n, n, rfl⟩ : Submonoid.powers g)
      simp only at e1 ⊢
      rw [← rR_alg f g (g ^ n), ← map_mul, e1]
      simp only [rR_alg, ha k, Algebra.smul_def, mul_pow, map_mul, map_pow]
      ring
    let x : ZMod q → Localization.Away f := fun k => s k * algebraMap S _ f ^ n
    have hmem : ((x, y) : Amb f g q) ∈ Tor f g hε := by
      rw [mem_tor]; intro k
      have h2 : (fun j => rR f g (((x, y) : Amb f g q).2 j)) = fun j => algebraMap S _ (f ^ n) * w j := funext hy
      rw [h2, twist_const_mul, hw, twist_tinv]
      show rL f g (s k * algebraMap S _ f ^ n) = _
      rw [map_mul, map_pow, rL_alg, map_pow]; ring
    refine ⟨n, ⟨(x, y), hmem⟩, ?_⟩
    show s * (((torMap f g hε f : Tor f g hε) : Amb f g q).1) ^ n = x
    rw [hT1]
    funext k
    simp only [Pi.mul_apply, Pi.pow_apply]
    rfl
  · intro a b hab
    have hc1 : ((a - b : Tor f g hε) : Amb f g q).1 = 0 := by
      rw [← hA (a - b), map_sub, hab, sub_self]
    have hm := (mem_tor f g hε _).mp (a - b).2
    have htw : twist hε (fun j => rR f g (((a - b : Tor f g hε) : Amb f g q).2 j)) = 0 := by
      funext k; rw [← hm k, hc1]; simp
    have hc2 := eq_zero_of_twist hε _ htw
    have hk : ∀ k, ∃ m : ℕ, algebraMap S (Localization.Away g) f ^ m * ((a - b : Tor f g hε) : Amb f g q).2 k = 0 :=
      fun k => kill f g _ (congrFun hc2 k)
    choose m hm' using hk
    refine ⟨Finset.univ.sup m, ?_⟩
    rw [← sub_eq_zero, ← mul_sub]
    apply Subtype.ext
    apply Prod.ext
    · have e : ((algebraMap S (Tor f g hε) f ^ Finset.univ.sup m : Tor f g hε) : Amb f g q).1 *
          ((a - b : Tor f g hε) : Amb f g q).1 = 0 := by rw [hc1, mul_zero]
      exact e
    · funext k
      show (algebraMap S (Localization.Away g) f) ^ (Finset.univ.sup m) * ((a - b : Tor f g hε) : Amb f g q).2 k = 0
      rw [← Nat.sub_add_cancel (Finset.le_sup (Finset.mem_univ k) : m k ≤ Finset.univ.sup m), pow_add, mul_assoc, hm' k,
        mul_zero]

end LateralTheory.E.ProjFPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafCurveVCut

def LeafFibreField : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k) [IsProper p],
  0 < topologicalKrullDim X → ∃ (F : Type) (_ : Field F) (_ : Algebra k F) (K : Type) (_ : Field K) (_ : Algebra F K)
    (n : ℕ) (s : Finset F) (t : K) (η : Sp K ⟶ X), (n : WithBot ℕ∞) < topologicalKrullDim X ∧ s.card ≤ n ∧
    Algebra.IsAlgebraic (IntermediateField.adjoin k (s : Set F)) F ∧ Transcendental F t ∧
    FiniteDimensional (IntermediateField.adjoin F {t}) K ∧
    η ≫ p = Spec.map (CommRingCat.ofHom ((algebraMap F K).comp (algebraMap k F))) ∧ genericPoint X ∈ Set.range η

def LeafTrdegDim : Prop := ∀ (k F Ω : Type) [Field k] [Field F] [Field Ω] [Algebra k F] [Algebra F Ω] [Algebra k Ω]
  [IsScalarTower k F Ω] [Algebra.IsAlgebraic F Ω] (n : ℕ) (s : Finset F), s.card ≤ n →
    Algebra.IsAlgebraic (IntermediateField.adjoin k (s : Set F)) F →
    ∀ R : Subalgebra k Ω, R.FG → ringKrullDim R ≤ n

def LeafBaseChangeField : Prop := ∀ (F Ω K : Type) [Field F] [Field Ω] [Field K] [Algebra F Ω] [Algebra F K] (t : K),
  Transcendental F t → FiniteDimensional (IntermediateField.adjoin F {t}) K →
    ∃ (L : Type) (_ : Field L) (_ : Algebra Ω L) (u : L) (φ : K →+* L), Transcendental Ω u ∧
      FiniteDimensional (IntermediateField.adjoin Ω {u}) L ∧ φ.comp (algebraMap F K) = (algebraMap Ω L).comp (algebraMap F Ω)

def LeafModelCurve : Prop := ∀ (Ω L : Type) [Field Ω] [IsAlgClosed Ω] [Field L] [Algebra Ω L] (u : L),
  Transcendental Ω u → FiniteDimensional (IntermediateField.adjoin Ω {u}) L →
    ∃ (C0 : Scheme.{0}) (c0 : C0 ⟶ Sp Ω) (x : C0) (ψ : Spec (C0.presheaf.stalk x) ⟶ Sp L), IsCurve c0 ∧
      IsGenericPoint x (⊤ : Set C0) ∧ ψ ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω L)) = C0.fromSpecStalk x ≫ c0

def LeafExtend : Prop := ∀ (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] {X C0 : Scheme.{0}} (p : X ⟶ Sp k)
  [IsProper p] (c0 : C0 ⟶ Sp Ω) (x : C0), IsCurve c0 → IsGenericPoint x (⊤ : Set C0) →
    ∀ ψ : Spec (C0.presheaf.stalk x) ⟶ X,
      ψ ≫ p = C0.fromSpecStalk x ≫ c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) →
      ∃ e : C0 ⟶ X, C0.fromSpecStalk x ≫ e = ψ ∧ e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω))

theorem goal_of (hA : LeafFibreField) (hT : LeafTrdegDim) (hB1 : LeafBaseChangeField) (hB2 : LeafModelCurve)
    (hC : LeafExtend) : LateralTheory.E.LeafGeoVCut.LeafCurveV := by
  intro k _ _ X _ p _ hd
  obtain ⟨F, _, _, K, _, _, n, s, t, η, hn, hs, halg, ht, hfin, hη, hgen⟩ := hA k p hd
  obtain ⟨L, _, _, u, φ, hu, hufin, hφ⟩ := hB1 F (AlgebraicClosure F) K t ht hfin
  obtain ⟨C0, c0, x, ψ, hc0, hx, hψ⟩ := hB2 (AlgebraicClosure F) L u hu hufin
  have hring : CommRingCat.ofHom ((algebraMap F K).comp (algebraMap k F)) ≫ CommRingCat.ofHom φ =
      CommRingCat.ofHom (algebraMap k (AlgebraicClosure F)) ≫ CommRingCat.ofHom (algebraMap (AlgebraicClosure F) L) := by
    ext a
    have := congrArg (fun f => f (algebraMap k F a)) hφ
    simp only [RingHom.coe_comp, Function.comp_apply] at this
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply, this,
      IsScalarTower.algebraMap_apply k F (AlgebraicClosure F)]
  have hcompat : (ψ ≫ Spec.map (CommRingCat.ofHom φ) ≫ η) ≫ p =
      C0.fromSpecStalk x ≫ c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure F))) := by
    rw [Category.assoc, Category.assoc, hη, ← Spec.map_comp, hring, Spec.map_comp, ← Category.assoc, hψ,
      Category.assoc]
  obtain ⟨e, he1, he2⟩ := hC k (AlgebraicClosure F) p c0 x hc0 hx _ hcompat
  refine ⟨AlgebraicClosure F, inferInstance, inferInstance, inferInstance, C0, c0, e, hc0, he2, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := hgen
    let w : Spec (C0.presheaf.stalk x) := IsLocalRing.closedPoint (C0.presheaf.stalk x)
    refine ⟨C0.fromSpecStalk x w, ?_⟩
    rw [← Scheme.Hom.comp_apply, he1, ← hz]
    simp only [Scheme.Hom.comp_apply]
    congr 1
    exact Subsingleton.elim _ _
  · intro R hR
    exact lt_of_le_of_lt (hT k F (AlgebraicClosure F) n s hs halg R hR) hn

end LateralTheory.E.LeafCurveVCut

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.LeafTwistPf

def LeafLoc : Prop := Hyps → ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (F G : Shv R)
  (e : ∀ U : Scheme.{0}, (U ⟶ X) → (Sec F U ≃ₗ[ULift.{1} R] Sec G U)),
  (∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : U ⟶ X) (s : Sec F U), e V (g ≫ x) (Sec.res g s) = Sec.res g (e U x s)) →
  ∀ n : ℤ, Nonempty (H R (sch.obj X) F n ≃+ H R (sch.obj X) G n)

def LeafTwSec : Prop := ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], Prim q B → ∀ i j : ℤ,
  ∃ e : ∀ U : Scheme.{0}, (U ⟶ Spec (CommRingCat.of B)) → (Sec (tw q i) U ≃ₗ[ULift.{1} (ZMod q)] Sec (tw q j) U),
    ∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : U ⟶ Spec (CommRingCat.of B)) (s : Sec (tw q i) U),
      e V (g ≫ x) (Sec.res g s) = Sec.res g (e U x s)

theorem LeafTwist_of (hL : LeafLoc) (hT : LeafTwSec) : LateralTheory.E.LeafKumCut.LeafTwist := by
  intro hy q _ B _ hP n i j
  obtain ⟨ζ⟩ := hP
  obtain ⟨e, he⟩ := hT q B ζ i j
  exact hL hy (ZMod q) (Spec (CommRingCat.of B)) (tw q i) (tw q j) e he n

end LateralTheory.E.LeafTwistPf
end
end
