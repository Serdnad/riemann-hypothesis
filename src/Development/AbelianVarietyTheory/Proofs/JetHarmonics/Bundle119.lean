module

public import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle005
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle005
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Formalism.LocalToGlobal.ProjectiveLattices.CrudeVal
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
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
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.RunDepth

theorem plOf_bijective_card (D : D7) :
    Function.Bijective (plOf D) ∧ Fintype.card D.what₂.Tau = D.R.f := by
  refine ⟨?_, D.what₂.card_Tau⟩
  have hb := D.R.toFrame.iota_bijective
  refine D.eTau.symm.bijective.comp (f := fun z : RPl D.R =>
    (if z.1 then ⟨D.R.tau2 z.2, rfl⟩ else ⟨D.R.tau1 z.2, rfl⟩ : D.R.Psi)) ⟨?_, ?_⟩
  · rintro ⟨a, s⟩ ⟨b, t⟩ h
    have h' := congrArg Subtype.val h
    cases a <;> cases b <;>
      simp only [Formalism.HC.Frame.tau1, Formalism.HC.Frame.tau2, Bool.false_eq_true, if_true, if_false, Prod.mk.injEq] at h'
    · exact Prod.ext rfl (hb.1 h'.2)
    · exact absurd h'.1.1 (by decide)
    · exact absurd h'.1.1 (by decide)
    · exact Prod.ext rfl (hb.1 h'.2)
  · rintro ⟨⟨⟨a, b⟩, h⟩, hg⟩
    obtain ⟨t, rfl⟩ := hb.2 h
    have hb1 : b = 1 := hg
    subst hb1
    rcases Int.units_eq_one_or a with rfl | rfl
    · exact ⟨(false, t), rfl⟩
    · exact ⟨(true, t), rfl⟩

end GlobalTheory.RunDepth
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.RunDepth

theorem sizes_le_two_mul : ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L), 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → L.Sc + L.etaSz ≤ 2 * L.sc.b ∧ ∀ j, InR D j → (∀ τ, 0 ≤ wj D j τ ∧ wj D j τ ≤ 2 * L.sc.b) ∧ (∀ t, wj D j (plOf D (false, t)) ≤ 2 * L.sc.b') ∧ ∀ z, (numOf D L).w j z = wj D j (plOf D z) := by
  intro D L P hx hkb
  have hk : (5 : ℝ) ≤ D.R.k := by
    have : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
    exact_mod_cast this
  have hn : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := Formalism.HC.Frame.ord_pos _
    exact_mod_cast this
  have hx0 : 0 < L.sc.x := by linarith
  have hb' : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X' Scale.b
    positivity
  have hbb : 5 * L.sc.b' ≤ L.sc.b := le_trans (by nlinarith) hkb
  have hbx : L.sc.b' / L.sc.x ≤ L.sc.b' / 3 := div_le_div_of_nonneg_left hb'.le (by norm_num) hx
  have hw0 : 0 < L.sc.w'' D.R.n := by unfold Scale.w''; positivity
  have hw : L.sc.w'' D.R.n ≤ L.sc.b' / 3 := by
    unfold Scale.w''
    exact div_le_div_of_nonneg_left hb'.le (by norm_num) (by nlinarith)
  have ht := L.t_win.1
  have he1 : 1 ≤ L.etaSz := le_trans ht P.t_le_eta
  have he : L.etaSz ≤ L.sc.b' / 9 := by
    have h1 := P.teta
    have h2 : L.sc.w'' D.R.n / L.sc.x ≤ L.sc.w'' D.R.n / 3 :=
      div_le_div_of_nonneg_left hw0.le (by norm_num) hx
    nlinarith
  have hS0 := L.Sc_pos
  have hS : L.Sc ≤ L.sc.b' / 3 := by
    have := P.kS_le
    nlinarith
  have hk0 : (0 : ℝ) < D.R.k := by linarith
  have hLa : 0 < L.LaG := by
    have h1 : 0 < L.LaG * L.sc.b' / D.R.k := by have := P.S_le; linarith
    have h2 : 0 < L.LaG * L.sc.b' := (div_pos_iff_of_pos_right hk0).1 h1
    exact (mul_pos_iff_of_pos_right hb').1 h2
  have hbT : ∀ t, (L.bT t : ℝ) ≤ L.sc.b' + L.sc.b' / 4 := by
    intro t
    have h1 := P.bT_le t
    have h2 := P.rho_le
    have h3 : L.sc.x ^ (-2 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    have h4 : 0 ≤ P.Crho * Real.log L.sc.x * L.LaG / D.R.k := by
      have := P.Crho_pos
      have := Real.log_nonneg (show 1 ≤ L.sc.x by linarith)
      positivity
    unfold LevelStarExponents.rhoP at h2
    set A := LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k with hA
    have h5 : 4 * LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k = 4 * A := by rw [hA]; ring
    have h6 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k = A * L.sc.b' := by rw [hA]; ring
    have h7 : A ≤ 1 / 4 := by linarith
    rw [h6] at h1
    nlinarith
  refine ⟨by linarith, fun j hj => ?_⟩
  have hoff : ∀ τ, (D.eTau τ : D.R.GG) ∉ D.host.thickPlaces →
      0 ≤ wj D j τ ∧ wj D j τ ≤ 2 * L.sc.b' := by
    intro τ hτ
    by_cases htop : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
    · classical
      unfold Host.topPlaces at htop
      obtain ⟨t, htT, hteq⟩ := Finset.mem_image.1 htop
      obtain ⟨h1, h2⟩ := L.win_top j hj.1 hj.2 τ ⟨t, htT⟩ hteq.symm
      have h3 := hbT ⟨t, htT⟩
      have h4 := L.bT_ge ⟨t, htT⟩
      have h5 : 0 ≤ L.sc.b' / L.sc.x := by positivity
      constructor <;> linarith
    · obtain ⟨h1, h2⟩ := L.win_thin j hj.1 hj.2 τ ⟨(D.eTau τ).2, htop, hτ⟩
      constructor <;> linarith
  refine ⟨fun τ => ?_, fun t => (hoff _ ?_).2, fun z => ?_⟩
  · by_cases hτ : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
    · obtain ⟨h1, h2⟩ := L.win_thick j hj.1 hj.2 τ hτ
      constructor <;> linarith
    · obtain ⟨h1, h2⟩ := hoff τ hτ
      constructor <;> linarith
  · classical
    intro h
    unfold Host.thickPlaces at h
    obtain ⟨s, -, hs⟩ := Finset.mem_image.1 h
    have h1 : (D.eTau (plOf D (false, t)) : D.R.GG) = D.R.tau1 t := by
      simp [plOf]
    rw [h1] at hs
    have h2 := congrArg (fun g : D.R.GG => g.1.1) hs
    simp only [Formalism.HC.Frame.tau1, Formalism.HC.Frame.tau2] at h2
    exact absurd h2 (by decide)
  · have h1 : 1 ≤ j ∧ j ≤ (numOf D L).R.m := hj
    have h2 : j - 1 < D.R.m := by have := hj.1; have := hj.2; omega
    rw [NumDatum.w, NumDatum.eQ, dite_eq_left h1, wj, dite_eq_left h2]
    rfl

end GlobalTheory.RunDepth
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodDepth.Gap

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

variable {D : D7}

theorem emb_inj {t t' : D.what₂.Tau} (h : DV.tauEmb D t = DV.tauEmb D t') : t = t' :=
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem emb_ne_conj (t t' : D.what₂.Tau) :
    DV.tauEmb D t ≠ ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (DV.tauEmb D t') := by
  intro h
  have h1 : ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (DV.tauEmb D t') =
      D.host.emb (((D.eTau t' : D.R.Psi) : D.R.GG) * D.R.cc) := by
    rw [Formalism.L2.Geo.emb_mul_cc_comp]
    refine RingHom.ext fun x => ?_
    exact (Formalism.MainNotions.WeightFamilies.emb_conj D (DV.tauEmb D t') x).symm
  have h2 := (Formalism.L2.Geo.exists_tauEmb_iff D _).1 ⟨t, (h.trans h1).symm⟩
  exact (Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).1 (D.eTau t').2 h2

theorem wtA_emb {j : ℕ} (w : WeightFamilies.Wt D j) (t : D.what₂.Tau) (i : ℕ) :
    wtA w (DV.tauEmb D t, i) = ext0 (w.aP t) i := by
  classical
  unfold wtA
  rw [Finset.sum_eq_single t]
  · simp [emb_ne_conj]
  · intro t' _ ht'
    have : DV.tauEmb D t ≠ DV.tauEmb D t' := fun h => ht' (emb_inj h).symm
    simp [emb_ne_conj, this]
  · simp

theorem real_bounds {T Dd G y w η t S S' η' w2 x : ℝ} (hT : 40 * (Dd + 2) ≤ T) (hD : 0 ≤ Dd) (hG : 0 ≤ G)
    (h1 : (T + Dd + 2) * G ≤ y) (h2 : y < (T + Dd + 2) * (G + 1)) (hy1 : w - η ≤ y) (hy2 : y ≤ S + w + η + 1)
    (hTt : T ≤ t) (htη : t ≤ η) (h3 : t * η ≤ w2 / x) (hx : 1 < x) (hw : w2 ≤ w)
    (hS : S ≤ 2 * S') (hS' : 0 ≤ S') (hη : η ≤ 2 * η') :
    (1 - (Dd + 4) / T) * w ≤ T * G ∧ T * G ≤ w + 100 * (S' + η') := by
  have hT0 : 0 < T := by linarith
  have htη0 : 0 < t * η := mul_pos (by linarith) (by linarith)
  have h4 : t * η * x ≤ w2 := (le_div_iff₀ (by linarith)).1 h3
  have h5 : t * η ≤ w := by nlinarith
  constructor
  · have e : (1 - (Dd + 4) / T) * w = (T - Dd - 4) * w / T := by field_simp; ring
    rw [e, div_le_iff₀ hT0]
    have a1 : (T - Dd - 2) * (w - η - (T + Dd + 2)) ≤ (T - Dd - 2) * ((T + Dd + 2) * G) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have a2 : 0 ≤ (Dd + 2) ^ 2 * G := by positivity
    have a3 : T * η ≤ t * η := mul_le_mul_of_nonneg_right hTt (by linarith)
    have a4 : T * T ≤ t * η := mul_le_mul hTt (by linarith) hT0.le (by linarith)
    have a5 : 0 ≤ (Dd + 2) * η := mul_nonneg (by linarith) (by linarith)
    have a6 : 0 ≤ (Dd + 2) ^ 2 := by positivity
    nlinarith
  · have a1 : 0 ≤ (Dd + 2) * G := by positivity
    nlinarith

theorem le_two_floor {a : ℝ} (h : 1 ≤ a) : a ≤ 2 * (⌊a⌋₊ : ℝ) := by
  have h1 : (1 : ℝ) ≤ (⌊a⌋₊ : ℝ) := by exact_mod_cast (Nat.one_le_floor_iff a).2 h
  have h2 := Nat.lt_floor_add_one a
  linarith

variable {L : SizeData₂ D} {Pm : ParameterChoice' D L}

theorem gap_kappa (Tp : ParamsT D L Pm) (hK : DV.KapDef D) {j : ℕ} (hj : InR D j) (τ : D.what₂.Tau)
    (h1 : D.R.k - 2 < (D.R.sigW j).1) (h2 : D.R.k - 2 + 1 < (D.R.sigW j).1) (hv : D.R.k - 2 < D.R.k - 1) (hm : 0 < D.R.m) :
    0 ≤ WeightAlgebra.gapZ ((kaR Tp hK j).aP τ) ⟨D.R.k - 2, h1⟩ ∧
    ((WeightAlgebra.gapZ ((kaR Tp hK j).aP τ) ⟨D.R.k - 2, h1⟩ : ℤ) : ℚ) = (D.hc τ).v ⟨D.R.k - 2, hv⟩ + (D.hc τ).b ⟨0, hm⟩ - 1 := by
  unfold WeightAlgebra.gapZ
  rw [dite_eq_left h2]
  constructor
  · have := (kaR Tp hK j).aPlus_antitone τ (show (⟨D.R.k - 2, h1⟩ : Fin _) ≤ ⟨D.R.k - 2 + 1, h2⟩ from Nat.le_succ _)
    have h3 : (((kaR Tp hK j).aP τ ⟨D.R.k - 2 + 1, h2⟩ : ℕ) : ℤ) ≤ (kaR Tp hK j).aP τ ⟨D.R.k - 2, h1⟩ := by
      exact_mod_cast this
    exact sub_nonneg.2 h3
  · unfold kaR
    rw [kaWt_big D hK _ j hj.1 hj.2, kaWt_big D hK _ j hj.1 hj.2, Int.cast_sub, (hK j hj.1 hj.2 τ).1,
      (hK j hj.1 hj.2 τ).1, DV.aPlusQ_eq, DV.aPlusQ_eq]
    have e0 : D.R.k - 2 + 1 - (D.R.k - 1) = 0 := by omega
    have s1 : DV.sigPar D τ (D.R.k - 2) = (D.hc τ).v ⟨D.R.k - 2, hv⟩ := by
      unfold DV.sigPar; rw [dite_eq_left hv]
    have s2 : DV.sigPar D τ (D.R.k - 2 + 1) = -(D.hc τ).b ⟨0, hm⟩ := by
      unfold DV.sigPar
      rw [dite_eq_right (by omega), dite_eq_left (by omega)]
      congr 2
      exact Fin.ext e0
    simp only [s1, s2]
    push_cast
    ring

theorem gapW_eq (Tp : ParamsT D L Pm) (hK : DV.KapDef D) {j : ℕ} (z : RPl D.R)
    (h1 : D.R.k - 2 < (D.R.sigW j).1) (h2 : D.R.k - 2 + 1 < (D.R.sigW j).1) (hk : 2 ≤ D.R.k) :
    gapW (numOf D L) (fun z => DV.tauEmb D (plOf D z)) (wtA (lR Tp hK j)) z =
      (Int.fdiv (WeightAlgebra.gapZ ((kaR Tp hK j).aP (plOf D z)) ⟨D.R.k - 2, h1⟩ + 2) (WeightAlgebra.Tp D j Tp.TO)).toNat := by
  have e : D.R.k - 1 = D.R.k - 2 + 1 := by omega
  show wtA (lR Tp hK j) (DV.tauEmb D (plOf D z), D.R.k - 2) - wtA (lR Tp hK j) (DV.tauEmb D (plOf D z), D.R.k - 1) = _
  rw [wtA_emb, wtA_emb, e]
  unfold ext0
  rw [dite_eq_left h1, dite_eq_left h2]
  show ofGaps (lGapP D (kaR Tp hK j) Tp.TO Tp.nWn (plOf D z)) ⟨D.R.k - 2, h1⟩ -
    ofGaps (lGapP D (kaR Tp hK j) Tp.TO Tp.nWn (plOf D z)) ⟨D.R.k - 2 + 1, h2⟩ = _
  rw [ofGaps_succ _ ⟨D.R.k - 2, h1⟩ h2, Nat.add_sub_cancel]
  unfold lGapP
  rw [if_pos h2]

theorem TO_le_t (Tp : ParamsT D L Pm) : Tp.TO ≤ D.R.t := by
  have a1 := Tp.split
  have a2 := Tp.nP_eq
  have a4 := Tp.nW_40
  have hf : 1 ≤ D.R.f := by
    have h0 : 0 < D.R.toFrame.ord := D.R.toFrame.ord_pos
    have h1 : D.R.f = 2 * D.R.toFrame.ord := rfl
    omega
  have a5 : Tp.TO * 1 ≤ Tp.TO * Tp.nWn := Nat.mul_le_mul_left _ (by omega)
  have a6 : 1 * D.R.r ≤ 8 * D.R.f * D.R.r := Nat.mul_le_mul_right _ (by omega)
  omega

theorem gap_bounds : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (j : ℕ), InR D j → ∀ z : RPl D.R, L.sc.w'' D.R.n ≤ (numOf D L).w j z →
  (1 - ((Tp.Dp : ℝ) + 4) / Tp.TO) * (numOf D L).w j z ≤ (Tp.TO : ℝ) * gapW (numOf D L) (fun z => DV.tauEmb D (plOf D z)) (wtA (lR Tp hK j)) z ∧
  (Tp.TO : ℝ) * gapW (numOf D L) (fun z => DV.tauEmb D (plOf D z)) (wtA (lR Tp hK j)) z ≤ (numOf D L).w j z + 100 * ((numOf D L).Sc + (numOf D L).eta) := by
  intro D L Pm Tp hK j hj z hw
  have hj1 := hj.1
  have hj2 := hj.2
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hs : (D.R.sigW j).1 = D.R.k + j - 1 := rfl
  have h1 : D.R.k - 2 < (D.R.sigW j).1 := by omega
  have h2 : D.R.k - 2 + 1 < (D.R.sigW j).1 := by omega
  have hv : D.R.k - 2 < D.R.k - 1 := by omega
  have hm : 0 < D.R.m := by omega
  have hjm : j - 1 < D.R.m := by omega
  rw [gapW_eq Tp hK z h1 h2 (by omega)]
  obtain ⟨g0, g1⟩ := gap_kappa Tp hK hj (plOf D z) h1 h2 hv hm
  generalize WeightAlgebra.gapZ ((kaR Tp hK j).aP (plOf D z)) ⟨D.R.k - 2, h1⟩ = c at g0 g1 ⊢
  have hT' : WeightAlgebra.Tp D j Tp.TO = Tp.TO + Tp.Dp + 2 := by
    unfold WeightAlgebra.Tp; rw [GlobalTheory.DepthBoundProbe.dimY_eq Tp hj]
  rw [hT', Int.fdiv_eq_ediv_of_nonneg _ (Nat.cast_nonneg _)]
  have hpos : (0 : ℤ) < ((Tp.TO + Tp.Dp + 2 : ℕ) : ℤ) := by positivity
  have q0 : 0 ≤ (c + 2) / ((Tp.TO + Tp.Dp + 2 : ℕ) : ℤ) := Int.ediv_nonneg (by omega) hpos.le
  have q1 := Int.mul_ediv_self_le (x := c + 2) hpos.ne'
  have q2 := Int.lt_mul_ediv_self_add (x := c + 2) hpos
  have q3 := Int.toNat_of_nonneg q0
  generalize ((c + 2) / ((Tp.TO + Tp.Dp + 2 : ℕ) : ℤ)).toNat = G at q3 ⊢
  rw [← q3] at q1 q2
  have r1 : ((Tp.TO : ℝ) + Tp.Dp + 2) * (G : ℝ) ≤ (c : ℝ) + 2 := by exact_mod_cast q1
  have r2 : (c : ℝ) + 2 < ((Tp.TO : ℝ) + Tp.Dp + 2) * (G : ℝ) + ((Tp.TO : ℝ) + Tp.Dp + 2) := by exact_mod_cast q2
  have g2 : (c : ℝ) = (((D.hc (plOf D z)).v ⟨D.R.k - 2, hv⟩ : ℚ) : ℝ) + (((D.hc (plOf D z)).b ⟨0, hm⟩ : ℚ) : ℝ) - 1 := by
    exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) g1
  have hwe : (numOf D L).w j z = (((D.hc (plOf D z)).e ⟨j - 1, hjm⟩ : ℚ) : ℝ) := by
    unfold NumDatum.w NumDatum.eQ
    congr 1
    split_ifs with h
    · rfl
    · exact absurd (by first | exact hjm | exact ⟨hj1, hj2⟩) h
  have c1 := L.cloud_v (plOf D z) ⟨D.R.k - 2, hv⟩
  have c2 := abs_le.1 (L.be_close (plOf D z) ⟨0, hm⟩ ⟨j - 1, hjm⟩)
  rw [Rat.cast_sub] at c2
  have hT40 : 40 * ((Tp.Dp : ℝ) + 2) ≤ Tp.TO := by exact_mod_cast Tp.TO_40
  have hD : (0 : ℝ) ≤ Tp.Dp := Nat.cast_nonneg _
  have hT2 : (1 : ℝ) ≤ (Tp.TO : ℝ) ^ 2 := one_le_pow₀ (by linarith)
  have hDel := le_two_floor (hT2.trans Tp.Del_TO)
  have hh0 : (1 : ℝ) ≤ LevelStarExponents.h0 L := by
    have := Tp.heightBound_ge_order_sq
    have : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
    linarith
  have hh := le_two_floor hh0
  have hmR : (0 : ℝ) < D.R.m := by exact_mod_cast hm
  refine real_bounds (y := (c : ℝ) + 2) (η := L.etaSz) (t := D.R.t) (S := L.Sc) hT40 hD (Nat.cast_nonneg _) r1
    (by linarith) (by rw [hwe]; linarith [c1.1, c2.1]) (by rw [hwe]; linarith [c1.2, c2.2])
    (by exact_mod_cast TO_le_t Tp) Pm.t_le_eta Pm.teta L.sc.one_lt_alt hw ?_ ?_ ?_
  · rw [L.Sc_eq]
    show _ ≤ 2 * ((D.R.k : ℝ) * (4 * ((⌊(D.s.Del : ℝ)⌋₊ : ℕ) : ℝ)))
    have : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
    nlinarith
  · unfold NumDatum.Sc; positivity
  · show _ ≤ 2 * ((D.R.m : ℝ) * ((⌊LevelStarExponents.h0 L⌋₊ : ℕ) : ℝ))
    have e : L.etaSz = D.R.m * LevelStarExponents.h0 L := by unfold LevelStarExponents.h0; field_simp
    rw [e]
    nlinarith

end GlobalTheory.GoodDepth.Gap
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrobPlace

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

theorem comap_liesOver {E K : Type} [Field E] [Field K] [NumberField K] (f : 𝓞 E →+* 𝓞 K)
    (la : HeightOneSpectrum (𝓞 K)) :
    (la.asIdeal.comap f).LiesOver (Ideal.span {((resCharOf la : ℕ) : ℤ)}) := by
  have hl := Crude.resCharOf_prime la
  have hP := la.isPrime
  have hmax : (Ideal.span {((resCharOf la : ℕ) : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible
  have hle : Ideal.span {((resCharOf la : ℕ) : ℤ)} ≤ (la.asIdeal.comap f).under ℤ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show f (algebraMap ℤ (𝓞 E) ((resCharOf la : ℕ) : ℤ)) ∈ la.asIdeal
    rw [map_natCast, map_natCast]
    exact Crude.crv_char_mem la
  have hne : (la.asIdeal.comap f).under ℤ ≠ ⊤ := by
    intro h
    apply la.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : ℤ) ∈ (la.asIdeal.comap f).under ℤ := by rw [h]; trivial
    change f (algebraMap ℤ (𝓞 E) 1) ∈ la.asIdeal at h1
    rwa [map_one, map_one] at h1
  exact ⟨hmax.eq_of_le hne hle⟩

theorem card_under {S : Type} [CommRing S] (p : ℕ) (Q : Ideal S) [h : Q.LiesOver (Ideal.span {(p : ℤ)})] :
    Nat.card (ℤ ⧸ Q.under ℤ) = p := by
  rw [← h.over, Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]

theorem eTau_plOf (D : D7) (z : RPl D.R) :
    ((D.eTau (plOf D z) : D.R.Psi) : D.R.GG) =
      ((if z.1 then -1 else 1, 1), D.R.iota z.2) := by
  unfold plOf
  rw [Equiv.apply_symm_apply]
  cases z.1 <;> rfl

theorem inert_ne {N : NumDatum} {l : ℕ} (h : Inert N l) : l ∉ N.H.small ∧ l ≠ N.q ∧ l ≠ N.d := by
  unfold Inert NumDatum.cls primeClass at h
  refine ⟨fun h2 => ?_, fun hq => ?_, fun hd => ?_⟩
  · rw [if_pos h2] at h
    rcases h with h | h <;> cases h
  · rw [if_pos hq] at h
    split_ifs at h <;> rcases h with h | h <;> cases h
  · rw [if_pos hd] at h
    split_ifs at h <;> rcases h with h | h <;> cases h

theorem gal_step (D : D7) (L : SizeData₂ D) (p : ℕ) [Fact p.Prime] (hI : Inert (numOf D L) p)
    (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (σ : D.host.E ≃ₐ[ℚ] D.host.E) (hσ : IsArithFrobAt ℤ σ P) (z : RPl D.R) :
    ((D.eTau (plOf D ((numOf D L).pos p z 1)) : D.R.Psi) : D.R.GG) * D.R.cc =
      ((D.eTau (plOf D z) : D.R.Psi) : D.R.GG) *
        D.host.galE σ := by
  obtain ⟨h2, hq, hd⟩ := inert_ne hI
  have hN : ¬ p ∣ D.host.condN := fun h => by
    rcases (D.host.toHostRaw.dvd_condN_iff_small Fact.out).1 h with h | h | h
    exacts [h2 h, hq h, hd h]
  have hc : p.Coprime D.host.condN := (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hN
  have hC := factClassFrob D.R D.host p hN P σ hσ
  have hH : (D.host.galE σ).2 = D.R.iota ((numOf D L).hP p) := by
    have e1 := (D.host.toHostAx.frob_iff p hc P σ).1 hσ
    have e2 : (numOf D L).hP p = D.R.iotaInv (D.host.art (ZMod.unitOfCoprime p hc)).2 := dif_pos hc
    rw [e2, Formalism.HC.Frame.iota_iotaInv]
    exact congrArg Prod.snd e1
  have hcls : (numOf D L).cls p = D.host.cls p := rfl
  have hpos := eTau_plOf D
    (xor z.1 (decide (D.host.cls p = PrimeClass.signal ∧ Odd 1)), z.2 + 1 • (numOf D L).hP p)
  refine (congrArg (· * D.R.cc) hpos).trans ?_
  rw [eTau_plOf]
  refine Prod.ext ?_ ?_
  · rcases hI with h | h
    · rw [hcls] at h
      have h1 := hC.2.2.1 h
      simp only [Prod.fst_mul, h1, h, Formalism.HC.Frame.cc, Formalism.FrobeniusOrbits.c0]
      cases z.1 <;> simp
    · rw [hcls] at h
      have h1 := hC.2.1.1 h
      simp only [Prod.fst_mul, h1, h, Formalism.HC.Frame.cc, Formalism.FrobeniusOrbits.c0]
      cases z.1 <;> simp
  · simp only [Prod.snd_mul, Formalism.HC.Frame.cc, mul_one, hH]
    rw [Formalism.HC.Frame.iota_add]
    exact congrArg (fun t => D.R.iota z.2 * D.R.iota t) (one_nsmul _)

theorem conj_emb {R : Ranks} (H : Formalism.BasicNotions.Host R) (g g' : R.GG) (σ : H.E ≃ₐ[ℚ] H.E)
    (h : g' * R.cc = g * H.galE σ) (x : H.E) :
    ComplexEmbedding.conjugate (H.emb g') x = H.emb g (σ x) := by
  have hg : ∀ g : R.GG, H.galE (H.sigmaOf g) = g := fun g => MulEquiv.apply_symm_apply _ _
  have he : H.sigmaOf g' * H.conj = H.sigmaOf g * σ := by
    apply H.galE_injective
    rw [H.galE_mul, H.galE_mul, hg, hg, H.galE_conjE, h]
  rw [ComplexEmbedding.conjugate_coe_eq, ← H.conjE_apply (H.emb g') x]
  change H.φ₀ ((H.sigmaOf g' * H.conj) x) = H.φ₀ ((H.sigmaOf g * σ) x)
  rw [he]

theorem frob_place : ∀ (D : D7) (L : SizeData₂ D) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (lv : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff lv) (la : HeightOneSpectrum (𝓞 c.F)), Inert (numOf D L) (resCharOf la) → ∀ (z : RPl D.R) (x : 𝓞 D.host.E),
  ∃ y ∈ la.asIdeal, ((y : 𝓞 c.F) : c.F) = embK c (ComplexEmbedding.conjugate (DV.tauEmb D (plOf D ((numOf D L).pos (resCharOf la) z 1)))) x - embK c (DV.tauEmb D (plOf D z)) x ^ resCharOf la := by
  intro D L H lv c la hI z x
  haveI : Fact (resCharOf la).Prime := ⟨Crude.resCharOf_prime la⟩
  obtain ⟨h2, hq, hd⟩ := inert_ne hI
  let f : 𝓞 D.host.E →+* 𝓞 c.F := RingOfIntegers.mapRingHom (embF c (DV.tauEmb D (plOf D z)))
  haveI := la.isPrime
  haveI := comap_liesOver f la
  have hN : ¬ resCharOf la ∣ D.host.condN := fun h => by
    rcases (D.host.toHostRaw.dvd_condN_iff_small Fact.out).1 h with h | h | h
    exacts [h2 h, hq h, hd h]
  obtain ⟨σ, hσ⟩ := (D.host.der.frob (resCharOf la) hN (la.asIdeal.comap f)).1
  have hg := gal_step D L (resCharOf la) hI (la.asIdeal.comap f) σ hσ z
  have h1 := hσ x
  rw [card_under (resCharOf la)] at h1
  refine ⟨_, h1, ?_⟩
  rw [map_sub, map_pow]
  push_cast
  congr 1
  apply Subtype.ext
  rw [embK_coe]
  exact (conj_emb D.host _ _ σ hg (x : D.host.E)).symm

end GlobalTheory.FrobPlace
end
end
