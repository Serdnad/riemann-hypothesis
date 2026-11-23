module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RecHeightSWith
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Formalism.LocalRingCardinality.DataDIVDefs
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle113
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle065

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.RdVal
variable {D : D7}

theorem toEAf_sig (a : AE D) :
    toEAf D (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig a) =
      Formalism.UG.sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (toEAf D a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    simp [toEAf, finPart, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.UG.sigR, sigD]
  | add a b ha hb =>
    rw [RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb, RingHom.map_add (f := _), RingHom.map_add (f := _)]

theorem toEAf_incl (e : D.host.E) :
    toEAf D (incA D e) = Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) e := by
  simp [toEAf, finPart, incA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Formalism.UG.inclE]

theorem isUnit_det_mt (V : HSp D) (g : GA D V) : IsUnit (mt V g).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit (matHom V g))

theorem mt_unitary (V : HSp D) (g : GA D V) :
    Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) (mt V g) * V.gram.map (incA D) * mt V g =
      V.gram.map (incA D) := by
  exact (show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF D.host.F) D.sp.cm.sig V.gram from g).2

theorem finM_mem (V : HSp D) {n : ℕ} (hn : V.rank = n) (J : Matrix (Fin n) (Fin n) D.host.E)
    (hJ : J = V.gram.reindex (finCongr hn) (finCongr hn)) (g : GA D V) :
    ∃ x : UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F), x.1.1 = finM V hn g := by
  have hdet : IsUnit (finM V hn g).det := by
    simp only [finM, Matrix.det_reindex_self]
    have hm := RingHom.map_det (toEAf D) (mt V g)
    rw [RingHom.mapMatrix_apply] at hm
    rw [← hm]
    exact (isUnit_det_mt V g).map _
  refine ⟨⟨((Matrix.isUnit_iff_isUnit_det _).mpr hdet).unit, ?_⟩, rfl⟩
  show Formalism.UG.cT _ (finM V hn g) * J.map _ * finM V hn g = J.map _
  have key : Formalism.UG.cT (Formalism.UG.sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (finM V hn g) =
      ((Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) (mt V g)).map (toEAf D)).reindex
        (finCongr hn) (finCongr hn) := by
    ext i j; simp [finM, Formalism.UG.cT, Matrix.reindex_apply, toEAf_sig]
  have hJ' : J.map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) =
      ((V.gram.map (incA D)).map (toEAf D)).reindex (finCongr hn) (finCongr hn) := by
    subst hJ; ext i j; simp [Matrix.reindex_apply, toEAf_incl]
  rw [key, hJ', finM]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, ← Matrix.map_mul, mt_unitary]

theorem infM_unit (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V) (τ : D.what₂.Tau) :
    IsUnit (infM θ V hn g τ).det := by
  simp only [infM, Matrix.det_reindex_self]
  have hm := RingHom.map_det ((θ τ).comp (infPart D)) (mt V g)
  rw [RingHom.mapMatrix_apply] at hm
  have e : compAt θ τ (mt V g) = (mt V g).map ((θ τ).comp (infPart D)) := rfl
  rw [e, ← hm]
  exact (isUnit_det_mt V g).map _

theorem atInf_mul_inv {n : ℕ} (γ : GL (Fin n) D.host.E) (τ : D.what₂.Tau) :
    atInf (embT D) (γ : Matrix (Fin n) (Fin n) D.host.E) τ * atInf (embT D) ((γ⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) τ = 1 := by
  simp only [atInf, ← Matrix.map_mul, Units.mul_inv]
  exact Matrix.map_one _ (map_zero _) (map_one _)

end GlobalTheory.AdForm.RdVal


open GlobalTheory.AdForm.RdVal in
theorem GlobalTheory.AdForm.rdS_val : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (hn : V.rank = n) (J : Matrix (Fin n) (Fin n) D.host.E), J = V.gram.reindex (finCongr hn) (finCongr hn) → ∀ (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 D.host.F))) (S : StepLevel D.host.F D.host.E (sigD D) J T f bad) (cl : Type) (yc : cl → UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F)), Function.Bijective (fun c => (Quotient.mk'' (yc c) : Cls S)) → ∀ Ψ ∈ AdFun S (embT D), ∀ (y : Frames (gramC J (embT D))) (g : GA D V), (∃ x : UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F), x.1.1 = finM V hn g) ∧ (∀ τ, IsUnit (infM θ V hn g τ).det) ∧ ∀ (x : UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (y' : Frames (gramC J (embT D))), x.1.1 = finM V hn g → IsTr (infM θ V hn g) y y' → rdS θ V hn S yc (fun c => Ψ (yc c)) y g = Ψ x y' := by
  intro D θ _ V n hn J hJ T f bad S cl yc hbij Ψ hΨ y g
  refine ⟨finM_mem V hn J hJ g, fun τ => infM_unit θ V hn g τ, ?_⟩
  intro x y' hx hy
  obtain ⟨c, hc⟩ := hbij.2 (Quotient.mk'' x : Cls S)
  have hex : ∃ p, IsDec S yc (finM V hn g) p := by
    obtain ⟨h, hh, k, hk, hxe⟩ := (@DoubleCoset.eq _ _ _ _ _ _).mp hc
    obtain ⟨γ, hγ, hγe⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hh)
    refine ⟨(c, γ, ⟨k.1, Subgroup.mem_subgroupOf.mp hk⟩), hγ, ?_⟩
    dsimp only
    rw [hγe, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← hxe, hx]
  have hp := hex.choose_spec
  have hfr : ∀ τ, IsUnit (atInf (embT D) ((hex.choose.2.1)⁻¹ : GL (Fin n) D.host.E).1 τ * infM θ V hn g τ * y.1 τ).det := by
    intro τ
    rw [Matrix.det_mul, Matrix.det_mul]
    exact ((Matrix.isUnit_det_of_left_inverse (atInf_mul_inv hex.choose.2.1 τ)).mul (infM_unit θ V hn g τ)).mul (y.2 τ)
  unfold rdS
  rw [dite_eq_left hex, atFr, dite_eq_left hfr]
  have law := hΨ hex.choose.2.1 hp.1 (yc hex.choose.1) x hex.choose.2.2 (Units.ext (hx.trans hp.2)) y' ⟨_, hfr⟩ (by
    intro τ
    show y'.1 τ = _
    rw [hy τ]
    simp only [← Matrix.mul_assoc, atInf_mul_inv, Matrix.one_mul])
  exact law.symm
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.CoreHt.RowsRangeS

variable {D : D7}

variable {D : D7}

theorem one_le_scL (L : SizeData₂ D) : 1 ≤ L.sc.L :=
  Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le

theorem one_le_b (L : SizeData₂ D) : 1 ≤ L.sc.b :=
  Real.one_le_exp (by linarith [one_le_scL L])

theorem b'_pos (L : SizeData₂ D) : 0 < L.sc.b' := by
  have := L.sc.one_lt_alt
  have := one_le_b L
  unfold Scale.b' Scale.a Scale.X'
  positivity

theorem one_le_n (D : D7) : (1 : ℝ) ≤ D.R.n := by
  have : 1 ≤ D.R.n := by
    have := D.R.two_le_m
    have := D.R.m_le_f
    unfold Ranks.n
    omega
  exact_mod_cast this

theorem exists_top {τ : D.what₂.Tau} (h : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces) :
    ∃ t : D.host.TT, (D.eTau τ : D.R.GG) = D.R.tau1 t := by
  unfold Host.topPlaces at h
  obtain ⟨t, ht, hte⟩ := Finset.mem_image.1 h
  exact ⟨⟨t, ht⟩, hte.symm⟩

theorem uW_numRec (large₂ : SizeData₂ D) (hD : ∃ n : ℕ, D.s.Del = n) (u : D.what₂.Word) (z : RPl D.R) (i : Fin D.R.k) :
    (numDatumOfParameters D large₂).uW (codeRec large₂ u) z i = (D.hcW u (tauPl D z)).u i := by
  obtain ⟨n, hn⟩ := hD
  obtain ⟨r, hr⟩ := i
  unfold NumDatum.uW
  split_ifs with h h1
  · obtain ⟨l, rfl⟩ : ∃ l, r = l + 1 := ⟨r - 1, by have := h.1; simp only at this; omega⟩
    have h' : l < D.R.k - 2 := by have := h.2; simp only at this; omega
    have a := D.s.u_letter u (tauPl D z) l h'
    have h2 : D.s.letter u ⟨l, h'⟩ = true := h1
    rw [if_pos h2, D.hcW_v] at a
    have h3 : (((numDatumOfParameters D large₂).Del : ℕ) : ℚ) = D.s.Del := by
      show ((⌊D.s.Del⌋₊ : ℕ) : ℚ) = D.s.Del
      rw [hn, Nat.floor_natCast]
    rw [a, h3]
    rfl
  · obtain ⟨l, rfl⟩ : ∃ l, r = l + 1 := ⟨r - 1, by have := h.1; simp only at this; omega⟩
    have h' : l < D.R.k - 2 := by have := h.2; simp only at this; omega
    have a := D.s.u_letter u (tauPl D z) l h'
    have h2 : ¬ D.s.letter u ⟨l, h'⟩ = true := h1
    rw [if_neg h2, D.hcW_v] at a
    rw [a]
    rfl
  · by_cases h0 : r = 0
    · subst h0
      exact (D.hcW_first u _ hr).symm
    · obtain rfl : r = D.R.k - 1 := by simp only at h; omega
      exact (D.hcW_last u _ (by omega)).symm

theorem nu_numRec (large₂ : SizeData₂ D) (hD : ∃ n : ℕ, D.s.Del = n) (u : D.what₂.Word) (j : ℕ) (z : RPl D.R) (i : ℕ) :
    (((numDatumOfParameters D large₂).nu (codeRec large₂ u) j z i : ℚ) : ℝ) = DV.nuRow D u j (tauPl D z) i := by
  have e1 : (numDatumOfParameters D large₂).srcPar (codeRec large₂ u) z i = DV.srcPar D u (tauPl D z) i := by
    unfold NumDatum.srcPar DV.srcPar
    by_cases h : i < D.R.k
    · rw [dite_eq_left h, dite_eq_left h]
      exact uW_numRec large₂ hD u z ⟨i, h⟩
    · rw [dite_eq_right h, dite_eq_right h, D.hcW_e]
  have e2 : (((numDatumOfParameters D large₂).eQ j z : ℚ) : ℝ) = DV.wSz D j (tauPl D z) := by
    unfold NumDatum.eQ DV.wSz
    by_cases h : 1 ≤ j ∧ j ≤ D.R.m
    · rw [dite_eq_left h, dite_eq_left h]
    · rw [dite_eq_right h, dite_eq_right h, Rat.cast_zero]
  unfold NumDatum.nu DV.nuRow
  rw [e1, ← e2]
  push_cast
  rfl

theorem nuRow_zero_le_three_mul (large₂ : SizeData₂ D) (P : ParameterChoice' D large₂) (hb : ∀ t, (large₂.bT t : ℝ) ≤ 2 * large₂.sc.b')
    (hT : ThickUp large₂) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) :
    DV.nuRow D u (i + 1) τ 0 ≤ 3 * large₂.sc.a := by
  have hm := D.R.two_le_m
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hk0 : 0 < D.R.k := by omega
  have hk' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  have hm' : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hkN : (D.R.k : ℝ) ≤ D.R.N i := by
    have : D.R.k ≤ D.R.N i := by unfold Ranks.N; omega
    exact_mod_cast this
  have hx := large₂.sc.one_lt_alt
  have hb1 := one_le_b large₂
  have hb' := b'_pos large₂
  have hba : large₂.sc.b ≤ large₂.sc.a := le_mul_of_one_le_left (by linarith) hx.le
  have hX : 2 ≤ large₂.sc.X' := by
    have h1 : 1 ≤ large₂.sc.x ^ (large₂.sc.eps / 3) := Real.one_le_rpow hx.le (by linarith [large₂.sc.eps_pos])
    have h2 := Real.add_one_le_exp (large₂.sc.x ^ (large₂.sc.eps / 3))
    unfold Scale.X'
    linarith
  have hb'a : large₂.sc.b' ≤ large₂.sc.a / 2 := div_le_div_of_nonneg_left (by linarith) (by norm_num) hX
  have hw : large₂.sc.w'' D.R.n ≤ large₂.sc.b' :=
    div_le_self hb'.le (one_le_mul_of_one_le_of_one_le hx.le (one_le_n D))
  have he := large₂.etaSz_pos
  have hS := large₂.Sc_pos
  have heta : 2 * large₂.etaSz ≤ large₂.sc.b' := by
    have h1 : (2 : ℝ) ≤ D.R.m * ((D.R.t : ℝ) + 1) := by nlinarith
    linarith [P.mteta, mul_le_mul_of_nonneg_right h1 he.le]
  have hSc : 5 * large₂.Sc ≤ large₂.sc.b' := by
    linarith [P.kS_le, mul_le_mul_of_nonneg_right hk' hS.le]
  have hwj : wj D (i + 1) τ = (((D.hc τ).e ⟨i, hi⟩ : ℚ) : ℝ) := by
    unfold wj
    rw [dite_eq_left (by simpa using hi)]
    rfl
  rw [RowWeightLemmas.nuRow_head D u i hi τ 0 hk0, D.hcW_first u τ hk0, D.hcW_e]
  push_cast
  rw [← hwj]
  by_cases ha : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
  · obtain ⟨t, htt⟩ := exists_top ha
    rw [(large₂.top_u τ t hk0 htt).1]
    have a1 := (large₂.win_top (i + 1) (by omega) hi τ t htt).2
    have a2 := (large₂.aT_win t).2
    have a3 : (5 : ℝ) ≤ (D.R.k : ℝ) * large₂.sc.x ^ (Scale.A / 2) :=
      hk'.trans (le_mul_of_one_le_right (by linarith) (Real.one_le_rpow hx.le (by unfold Scale.A; norm_num)))
    have a4 : large₂.sc.a / ((D.R.k : ℝ) * large₂.sc.x ^ (Scale.A / 2)) ≤ large₂.sc.a / 5 :=
      div_le_div_of_nonneg_left (by linarith) (by norm_num) a3
    have a5 : large₂.sc.b' / large₂.sc.x ≤ large₂.sc.b' := div_le_self hb'.le hx.le
    linarith [hb t]
  · have h1 := P.cloud_place_bound τ (by omega) ha
    have h2 := (large₂.cloud_v τ ⟨0, by omega⟩).2
    push_cast at h1
    by_cases hc : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
    · have a1 := hT (i + 1) (by omega) hi τ hc
      linarith
    · have a1 := (large₂.win_thin (i + 1) (by omega) hi τ ⟨(D.eTau τ).2, ha, hc⟩).2
      linarith

theorem nu_numRec_mem : ∀ (D : D7) (L : SizeData₂ D) (CY : ℝ), HtRowsS L CY → ∀ (u : D.what₂.Word), ∀ j ∈ (numDatumOfParameters D L).lifts, ∀ z,
    ∀ i < D.R.N (j - 1), 0 ≤ (numDatumOfParameters D L).nu (codeRec L u) j z i ∧
      (((numDatumOfParameters D L).nu (codeRec L u) j z i : ℚ) : ℝ) ≤ 3 * L.sc.a := by
  rintro D large₂ CY ⟨⟨P⟩, -, -, hN, hD, hT⟩ u j hj z r hr
  obtain ⟨j1, j2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hi : i < D.R.m := j2
  have hr' : r < D.R.N i := hr
  have e := nu_numRec large₂ hD u (i + 1) z r
  constructor
  · have h := (RowWeightLemmas.nuRow_pos D u i hi (tauPl D z) r hr').le
    rw [← e] at h
    exact_mod_cast h
  · rw [e]
    exact (RowWeightLemmas.nuRow_anti' D u i hi _ r 0 (Nat.zero_le _) hr').trans
      (nuRow_zero_le_three_mul large₂ P hN.2.2.2.2 hT u i hi _)

end GlobalTheory.CoreHt.RowsRangeS
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_diagonal_frame_change_unweighting_symEdges : ∀ {D : D7} {n : ℕ} (ρ k : ℕ) (Pg : Finset (Pl D.host.E)) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (β₀ : GL (Fin n) (Formalism.IndefR.Lev.EAf D)), Formalism.L2.DIV.IsFrame β₀ Λ → ∀ a : ∀ PP : Pl D.host.E, Fin n → Fin n → kP PP, (∀ PP ∈ Pg, ∀ i j, Formalism.L2.DIV.symEdge ρ k i j → a PP i j ≠ 0) → ∃ β₃ : GL (Fin n) (Formalism.IndefR.Lev.EAf D), Formalism.L2.DIV.IsFrame β₃ Λ ∧ Formalism.L2.DIV.St β₃ = Formalism.L2.DIV.St β₀ ∧ ∀ PP ∈ Pg, ∀ y ∈ Formalism.L2.DIV.St β₀, (Formalism.L2.DIV.redFn β₃ PP y ∈ Formalism.L2.DIV.unipSym (kP PP) n ρ k ↔ Formalism.L2.DIV.redFn β₀ PP y ∈ Formalism.L2.DIV.unipSym (kP PP) n ρ k) ∧ (∑ i, ∑ j, if Formalism.L2.DIV.symEdge ρ k i j then a PP i j * ((Formalism.L2.DIV.redFn β₀ PP y : GL (Fin n) (kP PP)) : Matrix (Fin n) (Fin n) (kP PP)) i j else 0) = Formalism.L2.DIV.edgeSum (Formalism.L2.DIV.symEdge ρ k) (Formalism.L2.DIV.redFn β₃ PP y) := by
  first | exact @GlobalTheory.DiagFrameWeights.exists_diag_frame | exact GlobalTheory.DiagFrameWeights.exists_diag_frame | (intros; apply GlobalTheory.DiagFrameWeights.exists_diag_frame <;> assumption)
end
