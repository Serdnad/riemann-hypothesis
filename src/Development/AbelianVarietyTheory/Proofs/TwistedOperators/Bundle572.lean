module

public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.NormalFrameClauses
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesExistG2OfStandardLattices
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.FramesExistOfDiagonalTypePlaces
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle558
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mi Formalism.IndefR.Seed.Frm IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormalFramesStd

open GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices GlobalTheory.StdFrames GlobalTheory.NormalFramesLevels

variable {D : D7}

def eCo (E : ∀ j, ℕ → (D.sp.Y j).V) (j i : ℕ) : Fin (D.sp.Y j).rank → D.host.E := ⇑((D.sp.Y j).frame.repr (E j i))

def zCo (z : ∀ j, (D.sp.Y j).V) (j : ℕ) : Fin (D.sp.Y j).rank → D.host.E := ⇑((D.sp.Y j).frame.repr (z j))

theorem normalFr_repr' (E Ev : ∀ j, ℕ → (D.sp.Y j).V) (z : ∀ j, (D.sp.Y j).V) {j : ℕ} (hj : j < D.R.m) {i : ℕ}
    (hi : i < D.R.m - 1 - j) (r : Fin (D.sp.Y j).rank) :
    (D.sp.Y j).frame.repr (normalFr D j (E j) (Ev j) (z j) i) r =
      nfScal (kap D) (fun _ => 1) j i * adaptedVector (eCo E) (eCo Ev) (zCo z) j i r := by
  have hpar := even_iff_odd_c hj
  have hb : 0 < bI D j := by unfold bI; omega
  rw [nfScal_kap j hb i]
  unfold normalFr adaptedVector nAux
  by_cases h1 : i < (D.R.m - 1 - j) / 2
  · have hb' : ¬ bI D j ≤ i := by unfold bI; omega
    simp only [if_pos h1, if_neg hb', one_mul]
    rfl
  · by_cases h2 : Even j ∧ i = (D.R.m - 1 - j) / 2
    · have hc : (D.R.m - 1 - j) % 2 = 1 ∧ i = (D.R.m - 1 - j) / 2 := ⟨hpar.1 h2.1, h2.2⟩
      have hb' : ¬ bI D j ≤ i := by unfold bI; omega
      simp only [if_neg h1, if_pos h2, if_pos hc, if_neg hb', one_mul]
      rfl
    · have h3 : ¬ ((D.R.m - 1 - j) % 2 = 1 ∧ i = (D.R.m - 1 - j) / 2) := fun h => h2 ⟨hpar.2 h.1, h.2⟩
      have hb' : bI D j ≤ i := by
        unfold bI
        by_cases hc : (D.R.m - 1 - j) % 2 = 1
        · have : i ≠ (D.R.m - 1 - j) / 2 := fun h => h3 ⟨hc, h⟩
          omega
        · omega
      simp only [if_neg h1, if_neg h2, if_neg h3, if_pos hb', map_smul, Finsupp.smul_apply, smul_eq_mul]
      rfl

theorem normalFr_zero_repr' (E Ev : ∀ j, ℕ → (D.sp.Y j).V) (z : ∀ j, (D.sp.Y j).V)
    (hE0 : ∀ i (hi : i < D.R.rS), E 0 i = D.sp.hypE ⟨i, hi⟩ ∧ Ev 0 i = D.sp.hypF ⟨i, hi⟩) (hz0 : z 0 = D.sp.zm)
    {i : ℕ} (hi : i < D.R.m - 1) :
    ⇑((D.sp.Y 0).frame.repr (normalFr D 0 (E 0) (Ev 0) (z 0) i)) = frame0 (D := D) i := by
  obtain ⟨a, ha⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  have hρ : nAux D 0 / 2 = D.R.rS := by unfold nAux Ranks.rS; omega
  unfold normalFr frame0
  rw [hρ]
  by_cases h1 : i < D.R.rS
  · rw [if_pos h1, dite_eq_left h1, (hE0 i h1).1]
  · rw [if_neg h1, dite_eq_right h1]
    by_cases h3 : i = D.R.rS
    · rw [if_pos ⟨(Nat.even_iff.2 rfl : Even 0), h3⟩, if_pos h3, hz0]
    · rw [if_neg (fun h => h3 h.2), if_neg h3, if_pos (Nat.even_iff.2 rfl : Even 0)]
      have h5 : 2 * D.R.rS - i < D.R.rS := by unfold Ranks.rS at *; omega
      have h6 : nAux D 0 - 1 - i = 2 * D.R.rS - i := by unfold nAux Ranks.rS at *; omega
      rw [dite_eq_left h5, h6, (hE0 _ h5).2]

theorem isAdaptedVectorSystem_eCo_zCo (E Ev : ∀ j, ℕ → (D.sp.Y j).V) (z : ∀ j, (D.sp.Y j).V)
    (hAux : ∀ j, j < D.R.m → IsAuxiliaryHeckeCharacter D j (E j) (Ev j) (z j)) : IsAdaptedVectorSystem (eCo E) (eCo Ev) (zCo z) := by
  intro j hj
  obtain ⟨hA, hB, hC⟩ := hAux j hj
  have hpar := even_iff_odd_c hj
  simp only [nAux] at hA hB hC
  simp only [eCo, zCo, Formalism.IndefR.Seed.Frm.vecY_repr]
  refine ⟨fun i hi l hl => ⟨?_, ?_, ?_⟩, fun hc => ?_, fun x i' hi' => ?_⟩
  · refine hT_swap _ _ (hA i hi l hl).2.2 ?_
    split_ifs <;> simp
  · exact (hA l hl i hi).1
  · exact (hA l hl i hi).2.1
  · obtain ⟨h1, -, h3⟩ := hC (hpar.2 hc)
    exact ⟨h1, fun i hi => ⟨(h3 i hi).1, (h3 i hi).2⟩⟩
  · unfold adaptedVector
    split_ifs with h1 h2
    · simp only [eCo, Formalism.IndefR.Seed.Frm.vecY_repr]
      exact (hB _ h1 x).1
    · simp only [zCo, Formalism.IndefR.Seed.Frm.vecY_repr]
      exact (hC (hpar.2 h2.1)).2.1 x
    · simp only [eCo, Formalism.IndefR.Seed.Frm.vecY_repr]
      refine (hB _ ?_ x).2
      by_cases hc : (D.R.m - 1 - j) % 2 = 1
      · have : i' ≠ (D.R.m - 1 - j) / 2 := fun h => h2 ⟨hc, h⟩
        omega
      · omega

end GlobalTheory.NormalFramesStd

namespace GlobalTheory.NormalFramesStd

open GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices GlobalTheory.StdFrames GlobalTheory.NormalFramesLevels

variable {D : D7}

theorem colsAt' (γ : ∀ j, GL (Fin (D.sp.X j).rank) (Ef D)) (E Ev : ∀ j, ℕ → (D.sp.Y j).V) (z : ∀ j, (D.sp.Y j).V)
    {j : ℕ} (hj : j < D.R.m) (β : GL (Fin (D.sp.Y j).rank) (EAf D)) (P : Formalism.L2.Host.PiBar D.host)
    {l : Fin 2} {PP : Pl D.host.E} (hl : P.Div l PP)
    (hA : AgreeAt PP β.val (chainMat D j (γ j) (E j) (Ev j) (z j) (D.host.g l)))
    {ei : AE D} (hei : Formalism.L2.NTheta.IsIdemAt ei PP) :
    (∀ i < D.R.m - 1 - j, ∀ col : Fin (D.sp.Y j).rank, col.val = D.R.k + i → ∀ r,
      toEAf D ei * β.val r col = toEAf D ei * eToEAf D (((Ideal.absNorm PP.asIdeal : ℕ) : D.host.E) ^ (i + 1) *
        (nfScal (kap D) (fun _ => 1) j i * adaptedVector (eCo E) (eCo Ev) (zCo z) j i r))) ∧
    ∀ (col : Fin (D.sp.Y j).rank) (l' : Fin (D.sp.X j).rank), IsXCol (D := D) j col l' → ∀ r,
      toEAf D ei * β.val r col = toEAf D ei * (xMat (D := D) j).mulVec (fun i => (γ j).val i l') r := by
  refine ⟨fun i hi col hcol r => ?_, fun col l' hcl r => ?_⟩
  · rw [agree_all hA hei r col]
    simp only [chainMat]
    rw [if_neg (by omega), if_pos (by unfold nAux; omega), absNorm_of_div P hl,
      show (col : ℕ) - D.R.k = i by omega, normalFr_repr' E Ev z hj hi r]
  · rw [agree_all hA hei r col]
    simp only [chainMat]
    rcases hcl with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hl' : l' = ⟨col, (idx_lt hj col).1 h1⟩ := Fin.ext h2
      subst hl'
      rw [if_pos h1, colX_eq j _ col ((idx_lt hj col).1 h1)]
    · have h3 : ¬ (col : ℕ) < D.R.k := by omega
      have h4 : ¬ (col : ℕ) < D.R.k + nAux D j := by unfold nAux; omega
      have hl' : l' = ⟨(col : ℕ) - nAux D j, (idx_lt hj col).2 h4⟩ := Fin.ext (by simp only [nAux]; omega)
      subst hl'
      rw [if_neg h3, if_neg h4, colX_eq j _ _ ((idx_lt hj col).2 h4)]

theorem normalFrames_of_stdShape : ∀ {D : D7} {T : Type} (L : LevCh D T), (∀ PP, PP ∈ L.Pg ↔ ∃ l, L.C.P.Div l PP) → ∀ (γ : ∀ j, GL (Fin (D.sp.X j).rank) (Formalism.IndefR.Lev.EAf D)) (E Ev : ∀ j, ℕ → (D.sp.Y j).V) (z : ∀ j, (D.sp.Y j).V), (∀ j, j < D.R.m → IsFrame (γ j) (Formalism.L2.Herm.crdLat (D.sp.X j) (D.sp.X j).L0)) → (∀ j, j < D.R.m → GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.IsAuxiliaryHeckeCharacter D j (E j) (Ev j) (z j)) → (∀ i (hi : i < D.R.rS), E 0 i = D.sp.hypE ⟨i, hi⟩ ∧ Ev 0 i = D.sp.hypF ⟨i, hi⟩) → z 0 = D.sp.zm → GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.StdShape L γ E Ev z → (∃ (e ev : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E) (z' : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E) (κ : ℕ → ℕ → D.host.E) (s : ℕ → D.host.E), NormalFrames (betaYOf L.βY) e ev z' κ s L.Pg L.Pg ∧ NormalFrame0 (betaYOf L.βY 0) L.Pg L.Pg) ∧ XBasesG L.Pg L.βY := by
  intro D T L hPg γ E Ev z hγ hAux hE0 hz0 hSh
  have hshape : ∀ j < D.R.m, ShapeY L j (γ j) (E j) (Ev j) (z j) (betaYOf L.βY j) := fun j hj =>
    shape_betaYOf L γ E Ev z L.βY j hj.le (hSh.1 j hj (hAux _ (lt_of_le_of_lt (min_le_left _ _) hj)))
  have hcols : ∀ j (hj : j < D.R.m), ∀ PP ∈ L.Pg, ∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP →
      (∀ i < D.R.m - 1 - j, ∀ col : Fin (D.sp.Y j).rank, col.val = D.R.k + i → ∀ r,
        toEAf D ei * (betaYOf L.βY j).val r col =
          toEAf D ei * eToEAf D (((Ideal.absNorm PP.asIdeal : ℕ) : D.host.E) ^ (i + 1) *
            (nfScal (kap D) (fun _ => 1) j i * adaptedVector (eCo E) (eCo Ev) (zCo z) j i r))) ∧
      ∀ (col : Fin (D.sp.Y j).rank) (l' : Fin (D.sp.X j).rank), IsXCol (D := D) j col l' → ∀ r,
        toEAf D ei * (betaYOf L.βY j).val r col =
          toEAf D ei * (xMat (D := D) j).mulVec (fun i => (γ j).val i l') r := by
    intro j hj PP hPP ei hei
    obtain ⟨l, hl⟩ := (hPg PP).1 hPP
    exact colsAt' γ E Ev z hj _ L.C.P hl ((hshape j hj).1 l PP hl) hei
  have hxspan : ∀ j (hj : j < D.R.m), ∀ PP ∈ L.Pg, ∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP →
      ∀ col : Fin (D.sp.Y j).rank, (col.val < D.R.k ∨ D.R.k + (D.R.m - 1 - j) ≤ col.val) →
        XSpanAt j (betaYOf L.βY j).val ei col := by
    intro j hj PP hPP ei hei col hcol
    have hc := (hcols j hj PP hPP ei hei).2
    rcases hcol with h | h
    · exact ⟨_, hc col ⟨col, (idx_lt hj col).1 h⟩ (Or.inl ⟨h, rfl⟩)⟩
    · exact ⟨_, hc col ⟨(col : ℕ) - (D.R.m - 1 - j), (idx_lt hj col).2 (by unfold nAux; omega)⟩ (Or.inr ⟨h, rfl⟩)⟩
  have h0m : 0 < D.R.m := lt_of_lt_of_le two_pos D.R.two_le_m
  refine ⟨⟨eCo E, eCo Ev, zCo z, kap D, fun _ => 1,
    ⟨isAdaptedVectorSystem_eCo_zCo E Ev z hAux, kap_ne, fun _ => one_ne_zero, ?_, ?_⟩, ?_⟩, ?_⟩
  · intro PP hPP j _ i hi
    obtain ⟨l, hl⟩ := (hPg PP).1 hPP
    have hb : 0 < bI D j := by unfold bI; omega
    rw [nfScal_kap j hb i]
    split_ifs
    · unfold sgT
      split_ifs
      · rw [Valuation.map_neg, valuation_splitTraceElement_eq_one L.C.P hl]
      · exact valuation_splitTraceElement_eq_one L.C.P hl
    · exact map_one _
  · intro PP hPP ei hei j hj
    refine ⟨fun i hi col hcol r => ?_, hxspan j hj PP hPP ei hei⟩
    rw [if_pos hPP]
    exact (hcols j hj PP hPP ei hei).1 i hi col hcol r
  · intro PP hPP ei hei
    have hc := (hcols 0 h0m PP hPP ei hei).1
    refine ⟨fun i hi col hcol r => ?_, fun col hcol => hxspan 0 h0m PP hPP ei hei col
      (Or.inl (by rw [← Formalism.IndefR.Seed.FrmC.N_zero D]; exact hcol))⟩
    have hi' : i < D.R.m - 1 - 0 := by omega
    rw [if_pos hPP, hc i hi' col (by rw [hcol, Formalism.IndefR.Seed.FrmC.N_zero]) r, ← normalFr_repr' E Ev z h0m hi' r,
      normalFr_zero_repr' E Ev z hE0 hz0 hi]
  · intro j hj
    refine ⟨γ j, by rw [← crdLat_eq_l0X]; exact hγ j hj, fun PP hPP ei hei col l' hcl r => ?_⟩
    exact (hcols j hj PP hPP ei hei).2 col l' hcl r

end GlobalTheory.NormalFramesStd

end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceProduct

theorem mix_orth {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {e f : A} (h : e * f = 0)
    (a : Matrix n n A) :
    (e • a + (1 - e) • (1 : Matrix n n A)) * (f • a + (1 - f) • (1 : Matrix n n A)) =
      (e + f) • a + (1 - (e + f)) • (1 : Matrix n n A) := by
  have h1 : e * (1 - f) = e := by linear_combination -h
  have h2 : (1 - e) * f = f := by linear_combination -h
  have h3 : (1 - e) * (1 - f) = 1 - (e + f) := by linear_combination h
  simp only [add_mul, mul_add, smul_mul_smul_comm, mul_one, one_mul]
  rw [h, h1, h2, h3, zero_smul, zero_add, add_smul]
  abel

theorem sum_idem {A ι : Type} [CommRing A] (e : ι → A) (h1 : ∀ i, e i * e i = e i)
    (h2 : ∀ i j, i ≠ j → e i * e j = 0) (B : Finset ι) : (∑ i ∈ B, e i) * (∑ i ∈ B, e i) = ∑ i ∈ B, e i := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i (fun j _ hj => h2 i j (Ne.symm hj)) (fun hn => absurd hi hn), h1]

theorem exists_components (D : D7) (V : HSp D) (g : GA D V)
    (ε : HeightOneSpectrum (𝓞 D.host.F) → AF D.host.F) (hε : ∀ v, IsPlaceIdem D v (ε v)) :
    ∃ gs : Finset (HeightOneSpectrum (𝓞 D.host.F)) → GA D V,
      (∀ A, Formalism.L2.Theta.mt V (gs A) = algebraMap (AF D.host.F) (AE D) (∑ v ∈ A, ε v) • Formalism.L2.Theta.mt V g +
        (1 - algebraMap (AF D.host.F) (AE D) (∑ v ∈ A, ε v)) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) ∧
      gs ∅ = 1 ∧ ∀ v B (h : v ∉ B), gs (Finset.cons v B h) = gs {v} * gs B := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have hsum : ∀ A : Finset (HeightOneSpectrum (𝓞 D.host.F)),
      algebraMap (AF D.host.F) (AE D) (∑ v ∈ A, ε v) = ∑ v ∈ A, algebraMap (AF D.host.F) (AE D) (ε v) :=
    fun A => map_sum _ _ _
  have hid : ∀ A : Finset (HeightOneSpectrum (𝓞 D.host.F)),
      algebraMap (AF D.host.F) (AE D) (∑ v ∈ A, ε v) * algebraMap (AF D.host.F) (AE D) (∑ v ∈ A, ε v) =
        algebraMap (AF D.host.F) (AE D) (∑ v ∈ A, ε v) := by
    intro A
    rw [hsum]
    exact sum_idem (fun v => algebraMap (AF D.host.F) (AE D) (ε v))
      (fun v => GlobalTheory.IdemSupport.place_idem hΦ (hε v))
      (fun v w hvw => GlobalTheory.IdemSupport.place_orth hΦ (hε v) (hε w) hvw) A
  have hc := fun A : Finset (HeightOneSpectrum (𝓞 D.host.F)) =>
    GlobalTheory.IdemSupport.cA_algebraMap (D := D) (∑ v ∈ A, ε v)
  choose gs hgs using fun A => GlobalTheory.IdemSupport.exists_piece V (hid A) (hc A) g
  refine ⟨gs, hgs, ?_, ?_⟩
  · apply GlobalTheory.IdemSupport.mt_inj V
    rw [hgs, GlobalTheory.IdemSupport.mt_one, Finset.sum_empty, map_zero, zero_smul, sub_zero, one_smul, zero_add]
  · intro v B hvB
    apply GlobalTheory.IdemSupport.mt_inj V
    rw [GlobalTheory.IdemSupport.mt_mul, hgs, hgs, hgs, Finset.sum_cons, Finset.sum_singleton, map_add (f := _)]
    refine (mix_orth ?_ _).symm
    rw [hsum, Finset.mul_sum]
    exact Finset.sum_eq_zero fun w hw =>
      GlobalTheory.IdemSupport.place_orth hΦ (hε v) (hε w) (fun hvw => hvB (by rw [hvw]; exact hw))

theorem eigen_of_local_components : ∀ (D : D7) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (f : WO S T → ℂ), (∀ w, Continuous fun p : GA D S × GA D T => om p f w) → ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ (A : Finset (HeightOneSpectrum (𝓞 D.host.F))) (s : HeightOneSpectrum (𝓞 D.host.F) → ℂ), (∀ v, v ∉ A → s v = 1) → (∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε → ∀ (g' : GA D S) (h' : GA D T), Formalism.L2.Theta.mt S g' = algebraMap (AF D.host.F) (AE D) ε • Formalism.L2.Theta.mt S g + (1 - algebraMap (AF D.host.F) (AE D) ε) • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) → Formalism.L2.Theta.mt T h' = algebraMap (AF D.host.F) (AE D) ε • Formalism.L2.Theta.mt T h + (1 - algebraMap (AF D.host.F) (AE D) ε) • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) → om (g', h') f = s v • f) → om (g, h) f = (∏ v ∈ A, s v) • f := by
  intro D S T om f hcont g hg h hh A s hs hloc
  choose ε hε using fun v : HeightOneSpectrum (𝓞 D.host.F) => GlobalTheory.IdemSupport.exists_placeIdem (D := D) v
  obtain ⟨gs, hgs, hgs0, hgsm⟩ := exists_components D S g ε hε
  obtain ⟨hs', hhs, hhs0, hhsm⟩ := exists_components D T h ε hε
  have key : ∀ B : Finset (HeightOneSpectrum (𝓞 D.host.F)), om (gs B, hs' B) f = (∏ v ∈ B, s v) • f := by
    intro B
    induction B using Finset.cons_induction with
    | empty =>
      rw [hgs0, hhs0, Finset.prod_empty, one_smul]
      show om 1 f = f
      rw [map_one]
      rfl
    | cons v B hvB ih =>
      have hv := hloc v (ε v) (hε v) (gs {v}) (hs' {v}) (by rw [hgs, Finset.sum_singleton])
        (by rw [hhs, Finset.sum_singleton])
      rw [hgsm v B hvB, hhsm v B hvB, ← Prod.mk_mul_mk, map_mul, Module.End.mul_apply, ih, map_smul, hv,
        smul_smul, Finset.prod_cons, mul_comm]
  have hpair : Filter.Tendsto (fun B => (gs B, hs' B)) Filter.atTop (nhds (g, h)) :=
    (GlobalTheory.T.tendsto_placeComponents_finiteAdelicUnitary D S g hg ε hε gs hgs).prodMk_nhds (GlobalTheory.T.tendsto_placeComponents_finiteAdelicUnitary D T h hh ε hε hs' hhs)
  funext w
  rw [Pi.smul_apply, smul_eq_mul]
  have ht := ((hcont w).tendsto (g, h)).comp hpair
  refine tendsto_nhds_unique ht (tendsto_const_nhds.congr' ?_)
  filter_upwards [Filter.eventually_ge_atTop A] with B hB
  show _ = om (gs B, hs' B) f w
  rw [key, Pi.smul_apply, smul_eq_mul, Finset.prod_subset hB fun v _ hv => hs v hv]

end GlobalTheory.PlaceProduct
end
