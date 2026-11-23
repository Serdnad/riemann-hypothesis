module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalHeckeMatrixIntermediateLattice
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentPartCompletedLatticeLocalChart
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle140
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle224
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle225
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle223
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.GridJoin

theorem natCast_mem_under_iff (Aa : Type) [CommRing Aa] [IsDomain Aa] {B : Type} [CommRing B] [IsDomain B]
    [Algebra Aa B] [Algebra.IsIntegral Aa B] (w : HeightOneSpectrum B) (n : ℕ) :
    (n : Aa) ∈ (w.under Aa).asIdeal ↔ (n : B) ∈ w.asIdeal := by
  rw [HeightOneSpectrum.under_asIdeal, Ideal.mem_under, map_natCast]

theorem placeDat_of_grid : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc}, (∀ PP ∈ R.Pg, ∀ PP' ∈ R.Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') → PP = PP') → Formalism.L2.Host.SplitsCompletely {G'.pl.w G'.pl.v0} → (∀ k, GlobalTheory.ChiGrid.q0 D ≠ D.host.g k) → (GlobalTheory.ChiGrid.q0 D ≠ D.sp.T ∧ ∀ u : D.what₂.Word, GlobalTheory.ChiGrid.q0 D ≠ (D.mem u).A.T) → ∀ e : AE D, IsIdemSum e G'.pl.W0 → ∃ Z : GlobalTheory.Grid.PlaceDat D, Z.Is R.Pg R.Q e ∧ Z.q0 = GlobalTheory.ChiGrid.q0 D ∧ Z.w0 = G'.pl.w G'.pl.v0 ∧ Z.e0 = G'.pl.depth sc G'.pl.v0 ∧ Z.W R.Pg = G'.pl.W0 ∧ Z.ideal R.Pg = G'.modul ∧ Z.S0 R.Pg = G'.pl.S0 ∧ ∀ w, w ∈ R.Pg ∨ w ∈ Z.Wd → w.under (𝓞 D.host.F) ∈ GlobalTheory.ChiGrid.S1 D := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc F hR G' hPg hsplit hg hT e he
  classical

  have hPgOver : ∀ PP ∈ R.Pg, ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    intro PP hPP
    obtain ⟨k, hk⟩ := (hR.lev.Pg PP).1 hPP
    refine ⟨k, (natCast_mem_under_iff (𝓞 D.host.K) PP _).1 ?_⟩
    rw [show PP.under (𝓞 D.host.K) = R.C.P.pb k from hk]
    exact R.C.P.pb_over k
  have gS1 : ∀ (v : Pl D.host.F) (k : Fin 2), ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal → v ∈ S1 D := by
    intro v k hk
    rw [S1_mem_OmF]
    fin_cases k
    · exact Or.inl hk
    · exact Or.inr (Or.inl hk)
  have hPgS1 : ∀ PP ∈ R.Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ S1 D := by
    intro PP hPP
    obtain ⟨k, hk⟩ := hPgOver PP hPP
    exact gS1 _ k ((natCast_mem_under_iff (𝓞 D.host.F) PP _).2 hk)
  set P := G'.pl with hPdef
  have hS0 : ∀ v ∈ S1 D, v ∈ insert P.v0 (S1 D) := fun v hv => Finset.mem_insert_of_mem hv
  have hv0 : P.v0 ∈ insert P.v0 (S1 D) := Finset.mem_insert_self _ _

  have hPgw : ∀ PP ∈ R.Pg, P.w ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) = PP := by
    intro PP hPP
    obtain ⟨k, hk⟩ := hPgOver PP hPP
    have hkF := (natCast_mem_under_iff (𝓞 D.host.F) PP _).2 hk
    exact hPg _ (P.w_g _ k hkF) _ hPP (P.w_over _ (hS0 _ (gS1 _ k hkF)))
  let pd : Pl D.host.F → Prop := fun v =>
    ((D.host.pde : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal ∨ ((D.host.pde' : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal
  let Wd : Finset (Pl D.host.E) := ((S1 D).filter pd).image P.w
  let Z : GlobalTheory.Grid.PlaceDat D := ⟨q0 D, P.w P.v0, P.depth sc P.v0, Wd⟩
  have hmemWd : ∀ w, w ∈ Wd ↔ ∃ v ∈ S1 D, pd v ∧ P.w v = w := by
    intro w
    simp only [Wd, Finset.mem_image, Finset.mem_filter, and_assoc]

  have hW : Z.W R.Pg = P.W0 := by
    ext x
    simp only [GlobalTheory.Grid.PlaceDat.W, Places.W0, Places.S0, Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
      Finset.mem_insert, Z]
    constructor
    · rintro ((hx | hx) | rfl)
      · exact ⟨_, Or.inr (hPgS1 x hx), hPgw x hx⟩
      · obtain ⟨v, hv, -, rfl⟩ := (hmemWd x).1 hx
        exact ⟨v, Or.inr hv, rfl⟩
      · exact ⟨P.v0, Or.inl rfl, rfl⟩
    · rintro ⟨v, hv | hv, rfl⟩
      · exact Or.inr (by rw [hv])
      · rcases (S1_mem_OmF D).1 hv with h | h | h | h
        · exact Or.inl (Or.inl (P.w_g v 0 h))
        · exact Or.inl (Or.inl (P.w_g v 1 h))
        · exact Or.inl (Or.inr ((hmemWd _).2 ⟨v, hv, Or.inl h, rfl⟩))
        · exact Or.inl (Or.inr ((hmemWd _).2 ⟨v, hv, Or.inr h, rfl⟩))
  have hinj : ∀ v ∈ P.S0, ∀ v' ∈ P.S0, P.w v = P.w v' → v = v' := fun v hv v' hv' h =>
    (P.under_w hv).symm.trans ((congrArg _ h).trans (P.under_w hv'))
  have hIdeal : Z.ideal R.Pg = G'.modul := by
    rw [GlobalTheory.Grid.PlaceDat.ideal, hW, Places.W0, Finset.prod_image hinj]
    refine Finset.prod_congr rfl fun v hv => ?_
    congr 1
    have hv0' : P.v0 ∈ P.S0 := P.mem_S0_of_sum_eq.2 (Or.inl rfl)
    simp only [GlobalTheory.Grid.PlaceDat.depth, Z]
    by_cases h : v = P.v0
    · rw [h, if_pos rfl]
    · rw [if_neg (fun h' => h (hinj v hv _ hv0' h'))]
      unfold Places.depth
      rw [if_neg h]
  have hS0eq : Z.S0 R.Pg = P.S0 := by
    ext v
    simp only [GlobalTheory.Grid.PlaceDat.S0, hW, Places.W0, Finset.mem_image]
    constructor
    · rintro ⟨_, ⟨v', hv', rfl⟩, rfl⟩
      rwa [P.under_w hv']
    · intro hv
      exact ⟨_, ⟨v, hv, rfl⟩, P.under_w hv⟩

  have hWdS1 : ∀ w ∈ Wd, w.under (𝓞 D.host.F) ∈ S1 D := by
    intro w hw
    obtain ⟨v, hv, -, rfl⟩ := (hmemWd w).1 hw
    rw [P.w_over v (hS0 v hv)]; exact hv
  have hq := leastSplitAuxiliaryPrimeThetaChain_spec D
  refine ⟨Z, ?_, rfl, rfl, rfl, hW, hIdeal, hS0eq, ?_⟩
  · refine
      { prime := hq.1
        five_le := ?_
        referencePlaceOverPrime := ?_
        split := hsplit
        ne_g := hg
        ne_pde := leastSplitAuxiliaryPrime_ne_typePrimes D
        referencePrimeNeTwist := hT
        coprime := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hq.1).2 hq.2.2)
        offQ := ?_
        depth_pos := P.depth_pos sc P.v0
        Wd_over := ?_
        Wd_all := ?_
        idem := by rw [hW]; exact he }
    · have h1 : 0 < LevelStarExponents.condE D := by
        have := D.host.qd_big
        unfold LevelStarExponents.condE
        exact mul_pos (mul_pos D.host.QS_pos (by omega)) (by omega)
      have h4 : 4 ≤ LevelStarExponents.condE D := Nat.le_of_dvd h1 (by unfold LevelStarExponents.condE; exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left ((Dvd.intro_left (2 ^ D.R.e) (by rw [pow_add]; norm_num)).trans D.host.tower_dvd) _) _)
      have h2 := (rPr_spec D).1.two_le
      have h3 : 5 < Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D := by nlinarith
      show 5 ≤ q0 D
      by_contra hlt
      have hm := hq.2.1
      rw [Nat.mod_eq_of_lt (by show q0 D < _; omega)] at hm
      exact hq.1.one_lt.ne' hm
    · show (((q0 D : ℕ) : 𝓞 D.host.E) ∈ (P.w P.v0).asIdeal)
      refine (natCast_mem_under_iff (𝓞 D.host.F) _ _).1 ?_
      rw [P.w_over _ hv0]; exact P.basePlace_over_qZero
    · intro t w hw
      show w.under (𝓞 D.host.F) ≠ (P.w P.v0).under (𝓞 D.host.F)
      rw [P.w_over _ hv0]
      exact P.levelPlace_ne_basePlace t w hw
    · intro w hw
      obtain ⟨v, hv, hpd, rfl⟩ := (hmemWd w).1 hw
      have hu := P.w_over v (hS0 v hv)
      rcases hpd with h | h
      · left; show ((D.host.pde : ℕ) : 𝓞 D.host.E) ∈ (P.w v).asIdeal
        exact (natCast_mem_under_iff (𝓞 D.host.F) _ _).1 (by rw [hu]; exact h)
      · right; show ((D.host.pde' : ℕ) : 𝓞 D.host.E) ∈ (P.w v).asIdeal
        exact (natCast_mem_under_iff (𝓞 D.host.F) _ _).1 (by rw [hu]; exact h)
    · intro p hp
      have hpd : ∀ v : Pl D.host.F, ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal → pd v := by
        intro v h
        rcases hp with rfl | rfl
        · exact Or.inl h
        · exact Or.inr h
      have hS1 : ∀ v : Pl D.host.F, ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal → v ∈ S1 D := by
        intro v h
        rcases hp with rfl | rfl
        · exact (S1_mem_OmF D).2 (Or.inr (Or.inr (Or.inl h)))
        · exact (S1_mem_OmF D).2 (Or.inr (Or.inr (Or.inr h)))
      refine ⟨?_, ?_, ?_⟩
      · intro w hw
        have h := (natCast_mem_under_iff (𝓞 D.host.F) w p).2 hw
        exact ⟨P.w (w.under (𝓞 D.host.F)), (hmemWd _).2 ⟨_, hS1 _ h, hpd _ h, rfl⟩,
          P.w_over _ (hS0 _ (hS1 _ h))⟩
      · obtain ⟨𝔭, h𝔭⟩ := P.w_de p hp
        refine ⟨𝔭, fun w hw hpw => ?_⟩
        obtain ⟨v, hv, -, rfl⟩ := (hmemWd w).1 hw
        have h := (natCast_mem_under_iff (𝓞 D.host.F) (P.w v) p).2 hpw
        rw [P.w_over v (hS0 v hv)] at h
        exact h𝔭 v h
      · intro t w hw hpw
        have h := (natCast_mem_under_iff (𝓞 D.host.F) w p).2 hpw
        rw [P.w_Q t w hw (hS1 _ h)]
        exact (hmemWd _).2 ⟨_, hS1 _ h, hpd _ h, rfl⟩
  · rintro w (hw | hw)
    · exact hPgS1 w hw
    · exact hWdS1 w hw

end GlobalTheory.GridJoin
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField
open IsDedekindDomain Formalism.L2.NTheta
open scoped Matrix


theorem _root_.GlobalTheory.T.exists_local_matrix_chart_split_idempotent_completion : ∀ (D : D7) (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F))
    (π : GlobalTheory.SplitPlace.RF D →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) (s : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v → AE D) (n : ℕ)
    (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), e * e = e →
    (∀ a, π (finPart D (s a)) = a) → (∀ x, finPart D (s (π x)) = finPart D e * x) →
    (∀ x, finPart D e * x ∈ intAE D ↔ π x ∈ Formalism.UG.Ov D.host.F v) →
    L.FG → Submodule.span D.host.E (L : Set (Fin n → D.host.E)) = ⊤ →
    ∃ C : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v), ∀ y : Fin n → GlobalTheory.SplitPlace.RF D,
      finPart D e • y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)) ↔
        ∀ i, ((C⁻¹ : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)).1 *ᵥ fun j => π (y j)) i ∈ Formalism.UG.Ov D.host.F v := by
  first | exact @GlobalTheory.HatLocalChart.exists_chart | exact GlobalTheory.HatLocalChart.exists_chart | (intros; apply GlobalTheory.HatLocalChart.exists_chart <;> assumption)
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField
open IsDedekindDomain Formalism.L2.NTheta
open scoped Matrix


theorem _root_.GlobalTheory.T.exists_localHeckeMatrix_intermediateLattice : ∀ (D : D7) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E) (k n : ℕ)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (π : GlobalTheory.SplitPlace.RF D →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)
    (s : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v → AE D)
    (Λ M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (t : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)
    (T C : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)),
    IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    (∀ x, s (π (finPart D x)) = e * x) → (∀ a, π (finPart D (s a)) = a) →
    (∀ x, finPart D (s (π x)) = finPart D e * x) →
    (∀ x, finPart D e * x ∈ intAE D ↔ π x ∈ Formalism.UG.Ov D.host.F v) →
    (∀ x : D.host.F, π (finPart D (incA D (algebraMap D.host.F D.host.E x))) =
      algebraMap D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) x) →
    Λ.FG → Submodule.span D.host.E (Λ : Set (Fin n → D.host.E)) = ⊤ →
    P.asIdeal • Λ ≤ M → M ≤ Λ → M.toAddSubgroup.relIndex Λ.toAddSubgroup = Ideal.absNorm P.asIdeal ^ k →
    t ≠ 0 →
    (∀ y : Fin n → GlobalTheory.SplitPlace.RF D, finPart D e • y ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)) ↔
      ∀ i, ((t • T.1) *ᵥ fun j => π (y j)) i ∈ Formalism.UG.Ov D.host.F v) →
    (∀ y : Fin n → GlobalTheory.SplitPlace.RF D, finPart D e • y ∈ GlobalTheory.AdLat.hat D.host.F (M : Set (Fin n → D.host.E)) ↔
      ∀ i, ((C⁻¹ : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)).1 *ᵥ fun j => π (y j)) i ∈ Formalism.UG.Ov D.host.F v) →
    ∃ Z : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v), (∀ i j, Z.1 i j ∈ Formalism.UG.Ov D.host.F v) ∧
      (∀ i j, π (finPart D (incA D (ϖ : D.host.E))) * (Z⁻¹).1 i j ∈ Formalism.UG.Ov D.host.F v) ∧
      Valued.v Z.1.det = Valued.v (π (finPart D (incA D (ϖ : D.host.E)))) ^ k ∧
      ∀ y : Fin n → GlobalTheory.SplitPlace.RF D, (finPart D e • y ∈ GlobalTheory.AdLat.hat D.host.F (M : Set (Fin n → D.host.E)) ↔
        ∀ i, (((Z⁻¹).1 * (t • T.1)) *ᵥ fun j => π (y j)) i ∈ Formalism.UG.Ov D.host.F v) := by
  first | exact @GlobalTheory.HeckeLocMatrix.exists_local_matrix | exact GlobalTheory.HeckeLocMatrix.exists_local_matrix | (intros; apply GlobalTheory.HeckeLocMatrix.exists_local_matrix <;> assumption)
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField
open IsDedekindDomain Formalism.L2.NTheta
open scoped Matrix


theorem _root_.GlobalTheory.T.idempotent_part_completed_lattice_local_chart : ∀ (D : D7) (V : HSp D) (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F))
    (π : GlobalTheory.SplitPlace.RF D →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) (s : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v → AE D)
    (B : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)), e * e = e →
    (∀ a, π (finPart D (s a)) = a) → (∀ x, finPart D (s (π x)) = finPart D e * x) →
    (∀ x, finPart D e * x ∈ intAE D ↔ π x ∈ Formalism.UG.Ov D.host.F v) →
    (∀ y : Fin V.rank → GlobalTheory.SplitPlace.RF D, (fun i => finPart D e * y i) ∈ LamHat V ↔
      ∀ i, ((B⁻¹ : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)).1 *ᵥ fun j => π (y j)) i ∈ Formalism.UG.Ov D.host.F v) →
    ∃ t : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v, t ≠ 0 ∧ ∀ (x : GA D V) (y : Fin V.rank → GlobalTheory.SplitPlace.RF D),
      finPart D e • y ∈ latGHat V x ↔
        ∀ i, ((t • ((GlobalTheory.SplitPlace.comp V π B x⁻¹).1 * (B⁻¹ : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)).1)) *ᵥ
          fun j => π (y j)) i ∈ Formalism.UG.Ov D.host.F v := by
  first | exact @GlobalTheory.EPartChart.latGHat_chart | exact GlobalTheory.EPartChart.latGHat_chart | (intros; apply GlobalTheory.EPartChart.latGHat_chart <;> assumption)
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mixedModelHeisenbergPhase_eq_cexp_realPoints : ∀ (D : D7) (V W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E), adj D C * V.gram * C' = 1 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (y : Matrix (Fin W.rank) (Fin r) D.host.E) (κ : Mx D W.rank r), κ.map (finPart D) = 0 → phase ψ V W C C' y κ = Complex.exp (2 * Real.pi * Complex.I * ((∑ τ, 2 * (Matrix.trace ((pairQ W y).map (tauE D τ) * compAt θ τ κ)).re : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.PhaseReal.phase_eq | exact GlobalTheory.PhaseReal.phase_eq | (intros; apply GlobalTheory.PhaseReal.phase_eq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

noncomputable section

namespace GlobalTheory.ArchRec.Direct

def barRev {n : ℕ} (g : Mn n) : Mn n := (g.map (starRingEnd ℂ)).submatrix Fin.rev Fin.rev

theorem barRev_barRev {n : ℕ} (g : Mn n) : barRev (barRev g) = g := by
  ext i j
  simp [barRev]

theorem barRev_mul {n : ℕ} (g h : Mn n) : barRev (g * h) = barRev g * barRev h := by
  ext i j

  simp only [barRev, Matrix.submatrix_apply, Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]
  exact (Fintype.sum_equiv Fin.revPerm _ _ (fun x => by simp [Fin.revPerm_apply])).symm

theorem barRev_one {n : ℕ} : barRev (1 : Mn n) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [barRev]
  · have h' : i.rev ≠ j.rev := fun h'' => h (Fin.rev_injective h'')
    simp [barRev, Matrix.one_apply, h, h']

theorem barRev_conjTranspose {n : ℕ} (g : Mn n) : barRev gᴴ = (barRev g)ᴴ := by
  ext i j
  simp [barRev, Matrix.conjTranspose_apply]

theorem barRev_Jm {n : ℕ} (ε : Fin n → Bool) : barRev (Formalism.REAL.Jm ε) = Formalism.REAL.Jm (fun a => ε a.rev) := by
  ext i j
  by_cases h : i = j
  · subst h
    by_cases hε : ε i.rev <;> simp [barRev, Formalism.REAL.Jm, hε]
  · have h' : i.rev ≠ j.rev := fun h'' => h (Fin.rev_injective h'')
    simp [barRev, Formalism.REAL.Jm, Matrix.diagonal_apply, h, h']

theorem barRev_mem_K {n : ℕ} {ε : Fin n → Bool} {g : Mn n} (hg : g ∈ Formalism.REAL.Kset ε) :
    barRev g ∈ Formalism.REAL.Kset (fun a => ε a.rev) := by
  simp only [Formalism.REAL.Kset, Set.mem_setOf_eq] at hg ⊢
  obtain ⟨hu, hc⟩ := hg
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff] at hu ⊢
    rw [Matrix.star_eq_conjTranspose, ← barRev_conjTranspose, ← barRev_mul, ← Matrix.star_eq_conjTranspose, hu,
      barRev_one]
  · rw [← barRev_Jm, ← barRev_mul, hc, barRev_mul]

theorem isKFin_barRev {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (σ : Mn n → (H →L[ℂ] H)) (x : H) :
    IsKFin (fun a => ε a.rev) (fun g => σ (barRev g)) x ↔ IsKFin ε σ x := by
  have hK : ∀ g ∈ Formalism.REAL.Kset (fun a => ε a.rev), barRev g ∈ Formalism.REAL.Kset ε := by
    intro g hg
    simpa only [Fin.rev_rev] using barRev_mem_K hg
  simp only [IsKFin, IsKStableOn]
  constructor
  · rintro ⟨S, hS, hx, hst⟩
    refine ⟨S, hS, hx, fun g hg v hv => ?_⟩
    simpa only [barRev_barRev] using hst (barRev g) (barRev_mem_K hg) v hv
  · rintro ⟨S, hS, hx, hst⟩
    exact ⟨S, hS, hx, fun g hg v hv => hst (barRev g) (hK g hg) v hv⟩

theorem isEnum_rev {n : ℕ} {S : SPar} {lam : Fin n → ℝ} {ε : Fin n → Bool} (h : IsEnum S lam ε) :
    IsEnum (dualPar S) (fun a => -lam a.rev) (fun a => ε a.rev) := by
  obtain ⟨hanti, r, hr, hS⟩ := h
  refine ⟨fun a b hab => ?_, fun a => -r a.rev, fun a => by simp [hr], ?_⟩
  · have hba : b.rev < a.rev := Fin.rev_lt_rev.mpr hab
    simpa using hanti hba
  · rw [show dualPar S = S.image fun x => (-x.1, x.2) from rfl, hS, Finset.image_image]
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a.rev, by simp⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a.rev, rfl⟩

theorem Jm_rev {n : ℕ} (ε : Fin n → Bool) :
    Formalism.REAL.Jm (fun a => ε a.rev) = (Formalism.REAL.Jm ε).submatrix Fin.revPerm Fin.revPerm := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Formalism.REAL.Jm]
  · have h' : i.rev ≠ j.rev := fun h'' => h (Fin.rev_injective h'')
    simp [Formalism.REAL.Jm, Matrix.diagonal_apply, h, h']

def barModel {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (hds : ∀ τ, letI := M.nacg τ; letI := M.ips τ
      IsDS (fun a => M.ε τ a.rev) (fun a => -M.lam τ a.rev) (fun g => M.σ τ (barRev g))) :
    DSModel V (fun τ => dualPar (S τ)) where
  H := M.H
  nacg := M.nacg
  ips := M.ips
  σ τ g := M.σ τ (barRev g)
  lam τ a := -M.lam τ a.rev
  ε τ a := M.ε τ a.rev
  fr τ := (M.fr τ).submatrix Fin.revPerm (Equiv.refl _)
  enum τ := isEnum_rev (M.enum τ)
  ds := hds
  fr_unit τ := (Matrix.isUnit_submatrix_equiv _ _).2 (M.fr_unit τ)
  fr_gram τ := by
    rw [Jm_rev, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, M.fr_gram]
    rfl

theorem barRev_barMat {p q n : ℕ} (e : Ix p q ≃ Fin n) (g : Mat p q) :
    barRev (barMat (e.trans Fin.revPerm) g) = plainMat e g := by
  ext i j
  simp [barRev, barMat, plainMat, Matrix.reindex_apply]

theorem barRev_plainMat {p q n : ℕ} (e : Ix p q ≃ Fin n) (g : Mat p q) :
    barRev (plainMat (e.trans Fin.revPerm) g) = barMat e g := by
  ext i j
  simp [barRev, barMat, plainMat, Matrix.reindex_apply]

theorem directBridge : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D → DirectBridge D := by
  intro D hB X V S M τ p q l₁ l₂ c hpq h₁ h₂ hpar hhas hS
  obtain ⟨hsrc, htgt⟩ := hB
  have hds : ∀ τ, letI := M.nacg τ; letI := M.ips τ
      IsDS (fun a => M.ε τ a.rev) (fun a => -M.lam τ a.rev) (fun g => M.σ τ (barRev g)) :=
    fun τ => GlobalTheory.T.isDiscreteSeries_conjugate_reverse_contragredient _ _ _ _ _ (M.ds τ)
  have hset : GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.HidaSetting X p q l₁ l₂ c (fun τ => dualPar (S τ)) τ := by
    refine ⟨hpq, h₁, h₂, hpar, hhas, ?_⟩
    show dualPar (S τ) = _
    rw [hS]
  obtain ⟨-, m, hm, hU⟩ := hsrc X V _ (barModel M hds) τ p q l₁ l₂ c hset
  obtain ⟨-, m', hm', hU'⟩ := htgt X V _ (barModel M hds) τ p q l₁ l₂ c hset
  obtain rfl : m' = m := by exact_mod_cast hm'.trans hm.symm
  refine ⟨m', hm', fun e he b => ?_⟩
  have he' : SignCompat ((barModel M hds).ε τ) (e.trans Fin.revPerm) := by
    intro a
    change M.ε τ ((e.trans Fin.revPerm) a).rev = a.isLeft
    simp [he a]
  cases b
  · obtain ⟨U, hUm⟩ := hU _ he'
    refine ⟨U, ⟨fun x y => map_add U x y, fun z x => ?_, U.bijective, fun x => U.norm_map x, fun g x => ?_,
      fun x => ?_⟩⟩
    · exact U.map_smul z x
    · have hg := hUm.grp g x
      change _ = _ • U (M.σ τ (barRev (barMat (e.trans Fin.revPerm) _)) x) at hg
      rw [barRev_barMat] at hg
      simpa [phi] using hg
    · exact (isKFin_barRev (M.ε τ) (M.σ τ) x).symm.trans (hUm.kfin x)
  · obtain ⟨U, hUm⟩ := hU' _ he'
    refine ⟨U, ⟨fun x y => map_add U x y, fun z x => ?_, U.bijective, fun x => U.norm_map x, fun g x => ?_,
      fun x => ?_⟩⟩
    · exact U.map_smulₛₗ z x
    · have hg := hUm.grp g x
      change _ = _ • U (M.σ τ (barRev (plainMat (e.trans Fin.revPerm) _)) x) at hg
      rw [barRev_plainMat] at hg
      simpa [phi] using hg
    · exact (isKFin_barRev (M.ε τ) (M.σ τ) x).symm.trans (hUm.kfin x)

end GlobalTheory.ArchRec.Direct

end
end
