module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle003
public import Formalism.HermitianCurvature.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle053
public import Formalism.PeriodIntegrals.Bundle024
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Formalism.LocalToGlobal.CharacterGerms.ExistsStrictMonoMinor
public import Formalism.LocalToGlobal.CharacterGerms.Bundle023
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001
public import Development.AutomorphicArithmetic.CMTraceForms.Places
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle185
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle082
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsIntegralGaugedFormalGroupLawSelfConjugateSquar
public import Formalism.LocalToGlobal.CharacterGerms.Bundle015
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle086
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle061
public import Formalism.LocalToGlobal.CharacterGerms.CharacteristicFromRanks
import Formalism.LocalToGlobal.CharacterGerms.Bundle016
import Formalism.LocalToGlobal.CharacterGerms.Bundle007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle039
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle088
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle186
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle069
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaRuleIntegralPointValueBaseChange
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle117
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle015
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall

@[expose] public section

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

theorem _root_.GlobalTheory.T.levelZeroPairing_eq_integral_inner_topVectors : P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (A : ℝ) (N : ℕ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A → KB.CutWord P p.l0 w → w.length ≤ N → ∀ ε₁ ε₂ : ℝ, 0 < ε₁ → 0 < ε₂ → B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) G) ((D.cutF p.T.base χ f ε₁)) w) (D.cutF p.T.base χ f ε₂) = ∫ c, inner ℂ (tv p (D.cutF p.T.base χ f ε₂) w c) (tv p (D.cutF p.T.base χ f ε₁) w c) := by
  first | exact @GlobalTheory.beta_word_cutF_eq_integral_inner_tv | exact GlobalTheory.beta_word_cutF_eq_integral_inner_tv | (intros; apply GlobalTheory.beta_word_cutF_eq_integral_inner_tv <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.CharSquare

open GlobalTheory.RowLawSquare

theorem tsum_alt (l : ℝ) (hl : 1 < l) (a b : ℝ) (m : ℕ → ℝ) (h0 : ∀ k, m (2 * k) = a) (h1 : ∀ k, m (2 * k + 1) = b) :
    ∑' i : ℕ, l ^ (-((i : ℝ) + 1)) * m i = (a * l + b) / (l ^ 2 - 1) := by
  have hp : 0 < l := by linarith
  have hq : (l ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
  have hg := hasSum_geometric_of_lt_one (r := (l ^ 2)⁻¹) (by positivity) hq
  have e : ∀ i : ℕ, l ^ (-((i : ℝ) + 1)) = (l ^ (i + 1))⁻¹ := fun i => by
    rw [Real.rpow_neg hp.le, ← Real.rpow_natCast]; push_cast; rfl
  have hne : l ^ 2 - 1 ≠ 0 := by nlinarith
  have he : HasSum (fun k : ℕ => l ^ (-(((2 * k : ℕ) : ℝ) + 1)) * m (2 * k)) (l⁻¹ * a * (1 - (l ^ 2)⁻¹)⁻¹) := by
    refine Eq.mp (congrArg (HasSum · _) (funext fun k => Eq.symm ?_)) (hg.mul_left (l⁻¹ * a))
    rw [e, h0, pow_succ, pow_mul, inv_pow]; field_simp
  have ho : HasSum (fun k : ℕ => l ^ (-(((2 * k + 1 : ℕ) : ℝ) + 1)) * m (2 * k + 1))
      ((l ^ 2)⁻¹ * b * (1 - (l ^ 2)⁻¹)⁻¹) := by
    refine Eq.mp (congrArg (HasSum · _) (funext fun k => Eq.symm ?_)) (hg.mul_left ((l ^ 2)⁻¹ * b))
    rw [e, h1, add_assoc, pow_add, pow_mul, inv_pow]; field_simp
  rw [(HasSum.even_add_odd (f := fun i : ℕ => l ^ (-((i : ℝ) + 1)) * m i) he ho).tsum_eq]
  field_simp

theorem alt_le (l : ℝ) (hl : 1 < l) (n j j' : ℝ) (hj : 0 ≤ j) (hj' : 0 ≤ j') :
    ((n + j) * l + j') / (l ^ 2 - 1) ≤ n * (l / (l ^ 2 - 1)) + (j + j') / (l - 1) := by
  have h1 : 0 < l - 1 := by linarith
  have h2 : 0 < l ^ 2 - 1 := by nlinarith
  have e : (j + j') / (l - 1) = (j + j') * (l + 1) / (l ^ 2 - 1) := by
    field_simp; ring
  rw [e, ← mul_div_assoc, ← add_div]
  refine div_le_div_of_nonneg_right ?_ h2.le
  nlinarith

section Chart

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  (Y : FBChart C V O dd) {d : ℕ} {I0 : Type} [Fintype I0] (p : SelfData Y d I0)

theorem exists_unit (a : ZMod d) (g : Fin 2) : ∃ col, V.v (p.gm a col g) = 0 := by
  by_contra hc
  push Not at hc
  have hpos : ∀ r, 0 < V.v (p.gm (a + p.hd) r (1 - g) * p.gm a r g) := fun r => by
    have h1 : (0 : WithTop ℝ) ≤ V.v (p.gm (a + p.hd) r (1 - g)) := gm_int Y p _ _ _
    have h2 : (0 : WithTop ℝ) ≤ V.v (p.gm a r g) := gm_int Y p _ _ _
    rw [V.v.map_mul]
    exact lt_of_lt_of_le (lt_of_le_of_ne h2 (hc r).symm) (le_add_of_nonneg_left h1)
  have hg : 1 - g ≠ g := by fin_cases g <;> decide
  have e := p.gm_hyp a (1 - g) g
  rw [if_neg hg, Fin.sum_univ_two] at e
  have := V.v.map_lt_add (hpos 0) (hpos 1)
  rw [e, V.v.map_one] at this
  exact lt_irrefl _ this

omit [CharZero C] in
theorem inCol_eq (col : Fin 2) (f : PS C 1 dd) : inCol col (un1 f) =
    MvPowerSeries.subst (fun q : Fin 1 × Fin dd =>
      (MvPowerSeries.X (col, q.2) : MvPowerSeries (Fin 2 × Fin dd) C)) f :=
  _root_.GlobalTheory.RowLawSquare.subst_singlePointUncurry (fun _ => MvPowerSeries.constantCoeff_X _) f

omit [CharZero C] in
theorem intS_inCol (col : Fin 2) {f : PS C 1 dd} (hf : IntS V f) : IntS V (inCol col (un1 f)) := by
  rw [inCol_eq]
  exact intS_subst V (fun _ => MvPowerSeries.constantCoeff_X _) (fun _ => intS_X V _) hf


omit [CharZero C] in
theorem coeff_inCol (col : Fin 2) (f : PS C 1 dd) (μ : Fin 2 × Fin dd →₀ ℕ) (hμ : μ.degree ≤ 1) :
    MvPowerSeries.coeff μ (inCol col (un1 f)) = MvPowerSeries.coeff μ
      (MvPowerSeries.C (MvPowerSeries.constantCoeff f) +
        ∑ i, Pdiv.ChartF.dl f i • (MvPowerSeries.X (col, i) : MvPowerSeries (Fin 2 × Fin dd) C)) := by
  have hS : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd =>
      (MvPowerSeries.X (col, q.2) : MvPowerSeries (Fin 2 × Fin dd) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _
  rw [inCol_eq, coeff_rename_low (fun q : Fin 1 × Fin dd => (col, q.2)) (N := 1)
    (g := MvPowerSeries.C (MvPowerSeries.constantCoeff f) +
        ∑ i, Pdiv.ChartF.dl f i • (MvPowerSeries.X ((0 : Fin 1), i) : PS C 1 dd)) ?_ μ hμ]

  · rw [← MvPowerSeries.coe_substAlgHom (R := C) hS, map_add (f := _), map_sum]
    simp only [map_smul, MvPowerSeries.substAlgHom_X]
    congr 2
    exact (MvPowerSeries.substAlgHom (R := C) hS).commutes _
  · intro e he
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 he with h | h
    · rw [Finsupp.degree_eq_zero_iff] at h
      subst h
      simp
    · obtain ⟨⟨s, i⟩, rfl⟩ : ∃ q, e = Finsupp.single q 1 := finsupp_deg_one e h
      obtain rfl : s = 0 := Subsingleton.elim _ _
      simp [MvPowerSeries.coeff_C, MvPowerSeries.coeff_X, Finsupp.single_eq_single_iff, Pdiv.ChartF.dl]

omit [CharZero C] in
theorem cc_inCol (col : Fin 2) (f : PS C 1 dd) :
    MvPowerSeries.constantCoeff (inCol col (un1 f)) = MvPowerSeries.constantCoeff f := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_inCol col f 0 (by simp)]
  simp

omit [CharZero C] in
theorem lin_inCol (col : Fin 2) (f : PS C 1 dd) (x : Fin 2 × Fin dd) :
    MvPowerSeries.coeff (Finsupp.single x 1) (inCol col (un1 f)) = if x.1 = col then Pdiv.ChartF.dl f x.2 else 0 := by
  rw [coeff_inCol col f _ (by simp)]
  obtain ⟨r, i⟩ := x
  by_cases h : r = col <;>
    simp [MvPowerSeries.coeff_C, MvPowerSeries.coeff_X, Finsupp.single_eq_single_iff, h]

theorem lin_u (col g : Fin 2) (f : PS C 1 dd) (x : I0) :
    ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) (inCol col (un1 f)) * (Y.rawSelf p).u g x i =
      p.gm (p.ty0 x) col g * ∑ i, Pdiv.ChartF.dl f i * p.e x i := by
  simp only [lin_inCol, Fintype.sum_prod_type, ite_mul, zero_mul, FBChart.rawSelf]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem char_inCol (col : Fin 2) {f : PS C 1 dd} (hf : Pdiv.ChartF.IsCh Y.B.G.F f) :
    MvPowerSeries.subst (addP (Y.rawSelf p) (gp C _ (0 : Fin 2)) (gp C _ 1)) (inCol col (un1 f)) =
      MvPowerSeries.subst (gp C _ (0 : Fin 2)) (inCol col (un1 f)) *
        MvPowerSeries.subst (gp C _ (1 : Fin 2)) (inCol col (un1 f)) := by
  have z := fun (j : Fin 2) => zc_col (zc_gp (C := C) (κ := Fin 2 × Fin dd) j) col
  have h2 := zc2 (z 0) (z 1)
  have e := congrArg (sb ![RowLawSquare.colOf (gp C _ (0 : Fin 2)) col, RowLawSquare.colOf (gp C _ 1) col]) hf.2
  have hm : ∀ f g : PS C 2 dd, sb ![RowLawSquare.colOf (gp C _ (0 : Fin 2)) col, RowLawSquare.colOf (gp C _ 1) col] (f * g) =
      sb ![RowLawSquare.colOf (gp C _ (0 : Fin 2)) col, RowLawSquare.colOf (gp C _ 1) col] f *
        sb ![RowLawSquare.colOf (gp C _ (0 : Fin 2)) col, RowLawSquare.colOf (gp C _ 1) col] g :=
    fun f g => MvPowerSeries.subst_mul (hasSubst_sb h2) f g
  rw [substPointsPowerSeries_eval_one h2 (zc_addOf Y 0 1), sb_addOf Y h2, hm, substPointsPowerSeries_eval_one h2 (zc_pt 0), substPointsPowerSeries_eval_one h2 (zc_pt 1), sb_pt' h2,
    sb_pt' h2] at e
  rw [_root_.GlobalTheory.RowLawSquare.subst_inCol (zc_addP Y p (zc_gp _) (zc_gp _)), _root_.GlobalTheory.RowLawSquare.subst_inCol (zc_gp _), _root_.GlobalTheory.RowLawSquare.subst_inCol (zc_gp _)]
  have e2 := col_addP Y p (zc_gp (C := C) (0 : Fin 2)) (zc_gp 1) col
  unfold RowLawSquare.colOf at e2
  rw [e2]
  exact e

end Chart

theorem isSat_fst {C : Type} [Field C] {V : VF C} {m : ZMod 2 → ℕ} {n : ℕ} {w : Fin n → (Σ s : ZMod 2, Fin (m s)) → C}
    (hw : IsSat V w) (h1 : ∀ q i, w q ⟨1, i⟩ = 0) : IsSat V fun q i => w q ⟨0, i⟩ := by
  obtain ⟨hi, u, hu, e⟩ := hw
  refine ⟨fun _ _ => hi _ _, fun i q => u ⟨0, i⟩ q, fun _ _ => hu _ _, fun q q' => ?_⟩
  rw [← e q q', Fintype.sum_sigma, show (Finset.univ : Finset (ZMod 2)) = {0, 1} by decide,
    Finset.sum_pair (by decide)]
  simp [h1]

theorem chSt_rawSelf : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → y.IsAlg → ∀ (Orb : Type) [Fintype Orb] (lab : LabS E Orb), ArithS V io ι lab → lab.RankOK Dw → ∀ p : ∀ o, SelfData Y 2 (lab.II Dw o), IsSelfOf C3 ι Y lab p → ∀ (o : Orb) (Hc : ∀ g, (Y.rawSelf (p o)).CartHyp V g), RawChart.CHSt Hc := by
  intro hup E _ _ _ H Dw lv Xo c _ hst T io y C3 C _ _ V ι hι k Y hY hy Orb _ lab hA hR p hp o Hc g a hbig w hw hw0
  have ha : a = ((g.val : ℕ) : ZMod 2) := (hp.big o g a).1 hbig
  have h1 : ∀ q i, w q ⟨1, i⟩ = 0 := fun q i => hw0 q _ (by
    simp only [FBChart.rawSelf, hp.ty0, hp.hd, ha]
    fin_cases g <;> decide)
  obtain ⟨χ, hχ, hdet⟩ := GlobalTheory.T.exists_characters_bounded_minor_eigenspace hup E H Dw lv Xo c hst T io y C3 C V ι hι k Y hY hy hA.unr 2 (lab.tau o)
    (fun s s' h => (Prod.ext_iff.1 (hA.inj (a₁ := (o, s)) (a₂ := (o, s')) h)).2) (hA.frob o) 0 _ _ (isSat_fst hw h1)
  obtain ⟨col, hcol⟩ := exists_unit Y (p o) 0 g
  refine ⟨fun ρ x => ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) (inCol col (un1 (χ ρ))) *
    (Y.rawSelf (p o)).u g x i, fun ρ x => ?_, fun S t ht ρ => ?_, fun _ => ?_, fun hall => ?_⟩
  · exact VF.Ge.sum fun i _ => (intS_inCol col (hχ ρ).1 _).mul_int
      ((rlaw_rawSelf C V _ _ Y 2 _ (p o)).uint g x i)
  · exact GlobalTheory.RowLaw.upG_mvExp_char_mem_intGerm C V 2 _ _ _ (rlaw_rawSelf C V _ _ Y 2 _ (p o)) Hc _
      (intS_inCol col (hχ ρ).1) (by rw [cc_inCol, (hχ ρ).2.1]) (char_inCol Y (p o) col (hχ ρ).2) g S t ht
  · have hl : (1 : ℝ) < V.l := by exact_mod_cast V.l_prime.one_lt
    have hm : ∀ i : ℕ, ComplexEmbedding.conjugate (lab.tau o (0 + ((i + 1 : ℕ) : ZMod 2))) = lab.tau o i := fun i => by
      rw [← hA.conj]
      congr 1
      push_cast
      generalize (i : ZMod 2) = z
      revert z
      decide
    simp only [hm] at hdet
    rw [tsum_alt V.l hl ((lab.n : ℝ) + lab.j) lab.j' (fun i : ℕ => (Dw.mult (lab.tau o i) : ℝ))
      (fun k => by
        have : ((2 * k : ℕ) : ZMod 2) = 0 := by push_cast; exact mul_eq_zero_of_left rfl _
        simp only [this, (hR o).1, Nat.cast_add])
      (fun k => by
        have : ((2 * k + 1 : ℕ) : ZMod 2) = 1 := by
          push_cast; rw [mul_eq_zero_of_left (show (2 : ZMod 2) = 0 from rfl), zero_add]
        simp only [this, (hR o).2])] at hdet
    have hM : (Matrix.of fun ρ q : Fin (Y.rawSelf (p o)).n => ∑ x, (∑ i, MvPowerSeries.coeff (Finsupp.single i 1)
        (inCol col (un1 (χ ρ))) * (Y.rawSelf (p o)).u g x i) * w q x) =
        (p o).gm 0 col g • Matrix.of fun ρ q : Fin (Y.rawSelf (p o)).n => ∑ x, (∑ i, Pdiv.ChartF.dl (χ ρ) i *
          ι (chartUnitVectors C3 ⟨lab.tau o 0, x⟩ i)) * w q ⟨0, x⟩ := by
      ext ρ q
      simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, lin_u, hp.ty0, hp.e]
      rw [Fintype.sum_sigma, show (Finset.univ : Finset (ZMod 2)) = {0, 1} by decide, Finset.sum_pair (by decide)]
      simp only [h1, mul_zero, Finset.sum_const_zero, add_zero]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _
    rw [hM, Matrix.det_smul, V.v.map_mul, V.v.map_pow, hcol, smul_zero, zero_add]
    refine hdet.trans (WithTop.coe_le_coe.2 ?_)
    simp only [FBChart.rawSelf, hp.n, hp.j, hp.j', Formalism.IncomingBounds.gam]
    exact alt_le _ hl _ _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact absurd (((hp.big o g 0).1 (hall 0)).trans ((hp.big o g 1).1 (hall 1)).symm) (by decide)

end GlobalTheory.CharSquare
end
end

section

open BranchingSupport BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.discreteSeries_coefficient_expansion_bound_ball' : ∀ (C : ℝ), 0 ≤ C → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (a₁ : ℕ) (ν₀ : Fin (2 * P.r + P.k + 1) → ℤ) (R0 : Rep P.k P.r) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), Num P.k P.r lam P.u b bv ga h q0 → Num P.k P.r lam P.u' b bv ga h q0 → P.T ≤ b ^ (C * ((2 * P.r + 2 : ℕ) : ℝ)) → P.T' ≤ b ^ (C * ((2 * P.r + 2 : ℕ) : ℝ)) → n1 ν₀ + (P.r + 1) * a₁ + (P.r + 1) * (P.r + 2) ≤ q0 → R0.IsDS (PI.BesselPeriodGGP.eps48 P.k P.r) (fun a => lam a + (ν₀ a : ℝ)) → PI.CapelliEig.IsKFinCoefT (k := P.k) (r := P.r) R0.σ f → Formalism.FourierDecayAlt.P.CutBP.BigCellDerivativeExpansion p f b (C / 2 + 6) a₁ := by
  first | exact @GlobalTheory.discreteSeries_coefficient_expansion_bound_ball | exact GlobalTheory.discreteSeries_coefficient_expansion_bound_ball | (intros; apply GlobalTheory.discreteSeries_coefficient_expansion_bound_ball <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.CharPair

theorem sum_sigma_type {M : Type} [AddCommMonoid M] {d : ℕ} [NeZero d] (m : ZMod d → ℕ) (a : ZMod d)
    (f : (Σ b : ZMod d, Fin (m b)) → M) (hf : ∀ x, x.1 ≠ a → f x = 0) : ∑ x, f x = ∑ i : Fin (m a), f ⟨a, i⟩ := by
  rw [Fintype.sum_sigma, Finset.sum_eq_single a]
  · intro b _ hb
    exact Finset.sum_eq_zero fun i _ => hf _ hb
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem isSat_type {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] (m : ZMod d → ℕ) (a : ZMod d) {n : ℕ}
    {w : Fin n → (Σ b : ZMod d, Fin (m b)) → C} (hw : IsSat V w) (h0 : ∀ q x, x.1 ≠ a → w q x = 0) :
    IsSat V fun q (i : Fin (m a)) => w q ⟨a, i⟩ := by
  obtain ⟨h1, w', h2, h3⟩ := hw
  refine ⟨fun q i => h1 q _, fun i q => w' ⟨a, i⟩ q, fun i q => h2 _ q, fun q q' => ?_⟩
  rw [← h3 q q', sum_sigma_type m a (fun x => w q x * w' x q') fun x hx => by rw [h0 q x hx, zero_mul]]

theorem coeff_single_one_uncurry_eq_partialDerivative {C : Type} [Field C] {dd : ℕ} (f : PS C 1 dd) (i : Fin dd) :
    MvPowerSeries.coeff (Finsupp.single i 1) (un1 f) = ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.dl f i := by
  show MvPowerSeries.coeff ((Finsupp.single i 1).mapDomain fun x : Fin dd => ((0 : Fin 1), x)) f = _
  rw [Finsupp.mapDomain_single]
  rfl

theorem integralSeries_uncurry_one {C : Type} [Field C] {V : VF C} {dd : ℕ} {f : PS C 1 dd} (hf : IntS V f) : IntS V (un1 f) :=
  fun _ => hf _

theorem isCharacter_uncurry_logarithm_law {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
    (Y : FBChart C V O dd) {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] (p : PairData Y d I) {f : PS C 1 dd}
    (hf : ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.IsCh Y.B.G.F f) :
    MvPowerSeries.subst (addP (Y.raw p) (gp C (Fin dd) (0 : Fin 2)) (gp C (Fin dd) 1)) (un1 f) =
      MvPowerSeries.subst (gp C (Fin dd) (0 : Fin 2)) (un1 f) * MvPowerSeries.subst (gp C (Fin dd) (1 : Fin 2)) (un1 f) := by
  rw [RowLawPair.formalAdd_eq_law Y p (RowLawPair.zc_gp 0) (RowLawPair.zc_gp 1),
    RowLawPair.subst_oneVarGerm_eq_substPointsPowerSeries (RowLawSquare.zc_law Y (RowLawPair.zc_gp 0) (RowLawPair.zc_gp 1)),
    RowLawPair.subst_oneVarGerm_eq_substPointsPowerSeries (RowLawPair.zc_gp 0), RowLawPair.subst_oneVarGerm_eq_substPointsPowerSeries (RowLawPair.zc_gp 1)]
  exact hf.2

theorem orbitSum_eq {d l : ℕ} (hl : 0 < l) (p : ZMod d → ℕ) (s : ZMod d) :
    (∑' i : ℕ, ((l : ℝ) ^ (-((i : ℝ) + 1))) * (p (s + ((i + 1 : ℕ) : ZMod d)) : ℝ)) = S4.frobSum l p s := by
  unfold S4.frobSum
  exact tsum_congr fun i => by rw [ValuationFitting.rpow_neg_succ hl]

theorem chSt_pair : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → y.IsAlg → ¬ (V.l : ℤ) ∣ NumberField.discr E → ∀ (Orb : Type) (d : ℕ) [NeZero d] (lab : Lab E Orb d) (ha : LabArith V io ι lab) (hg : LabGeo C3 ι Y lab), lab.RankOK Dw → ∀ (o : Orb) (Hc : ∀ g, (Y.raw (pairOfLab ha hg o)).CartHyp V g), RawChart.CHSt Hc := by
  intro hUp E _ _ _ H Dw lv Xo c _ hstar T io y C3 C _ _ V ι hι k Y hY hy hl Orb d _ lab ha hg hr o Hc g a hb w hw h0
  have hinj : Function.Injective (lab.tau o g) := fun s s' h =>
    (Prod.mk.inj (Prod.mk.inj (ha.inj (a₁ := (o, g, s)) (a₂ := (o, g, s')) h)).2).2
  obtain ⟨χ, hχ, hdet⟩ := GlobalTheory.T.exists_characters_bounded_minor_eigenspace hUp E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY hy hl d (lab.tau o g) hinj
    (ha.frob o g) a lab.n (fun q i => w q ⟨a, i⟩) (isSat_type (fun b => Dw.mult (lab.tau o g b)) a hw h0)
  have hconj : ∀ s, ComplexEmbedding.conjugate (lab.tau o g s) = lab.tau o (1 - g) s := by
    intro s
    fin_cases g
    · exact (ha.conj o s).symm
    · show ComplexEmbedding.conjugate (lab.tau o 1 s) = lab.tau o 0 s
      rw [ha.conj]
      exact star_star _
  simp only [hconj] at hdet
  have hl1 : 1 < V.l := V.l_prime.one_lt
  rw [orbitSum_eq V.l_prime.pos (fun s => Dw.mult (lab.tau o (1 - g) s)) a] at hdet
  have hL : (1 : ℝ) < V.l := by exact_mod_cast hl1
  have h1 := S4.one_div_eq_gam_add_rho hl1
  have hdiv : ∀ x : ℝ, x / ((V.l : ℝ) - 1) = x * (S4.gam V.l + S4.rho V.l) := fun x => by
    rw [← h1]; ring
  have hrho : 0 ≤ S4.rho V.l := div_nonneg zero_le_one (by nlinarith)
  have hgam : 0 ≤ S4.gam V.l := div_nonneg (by linarith) (by nlinarith)
  have hj : (0 : ℝ) ≤ lab.j := Nat.cast_nonneg _
  have hj' : (0 : ℝ) ≤ lab.j' := Nat.cast_nonneg _
  obtain ⟨hc, hbig, hsm⟩ := hr o
  have hpb : ∀ b, lab.big o g b → Dw.mult (lab.tau o (1 - g) b) = 0 + lab.j' := fun b h => by
    rw [hsm (1 - g) b fun hh => (hc g b).1 hh h, zero_add]
  have hps : ∀ b, ¬ lab.big o g b → Dw.mult (lab.tau o (1 - g) b) = lab.n + lab.j := fun b h =>
    hbig (1 - g) b ((hc g b).2 h)
  have hmat : (Matrix.of fun ρ q : Fin lab.n => ∑ x : lab.II Dw o g,
      (∑ i, MvPowerSeries.coeff (Finsupp.single i 1) (un1 (χ ρ)) * lieBasisVector C3 ι lab o g x i) * w q x) =
      Matrix.of fun ρ q : Fin lab.n => ∑ x, (∑ i, ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.dl (χ ρ) i *
        ι (chartUnitVectors C3 ⟨lab.tau o g a, x⟩ i)) * w q ⟨a, x⟩ := by
    ext ρ q
    simp only [Matrix.of_apply, coeff_single_one_uncurry_eq_partialDerivative]
    exact sum_sigma_type (fun b => Dw.mult (lab.tau o g b)) a _ fun x hx => by rw [h0 q x hx, mul_zero]
  rw [← hmat] at hdet
  refine ⟨fun ρ x => ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) (un1 (χ ρ)) * lieBasisVector C3 ι lab o g x i,
    fun ρ x => VF.Ge.sum fun i _ => (integralSeries_uncurry_one (hχ ρ).1 _).mul_int (hg.u_int o g x i), fun S t ht ρ => ?_,
    fun hA => hdet.trans (WithTop.coe_le_coe.mpr ?_), fun hB => hdet.trans (WithTop.coe_le_coe.mpr ?_)⟩
  · exact GlobalTheory.T.mvExp_linearPart_integralChar_mem_integralGerm C V d (lab.II Dw o) (Fin (chD C3.ch)) (Y.raw (pairOfLab ha hg o))
      (RowLawPair.rLaw_raw Y _) Hc (un1 (χ ρ)) (integralSeries_uncurry_one (hχ ρ).1) ((constantCoeff_uncurry _).trans (hχ ρ).2.1)
      (isCharacter_uncurry_logarithm_law Y _ (hχ ρ).2) g S t ht
  · rw [S4.frobSum_alt hl1 0 lab.j' (lab.n + lab.j) (lab.big o g) (CharacteristicFromRanks.alt_step (lab.big o) hc hA g) _ hpb hps a hb]
    show _ ≤ (lab.n : ℝ) * S4.gam V.l + ((lab.j : ℝ) + lab.j') / ((V.l : ℝ) - 1)
    rw [hdiv]
    push_cast
    nlinarith [mul_nonneg hj hrho, mul_nonneg hj' hgam]
  · rw [S4.frobSum_const hl1 (0 + lab.j') _ (fun b => hpb b (hB b)) a]
    show _ ≤ ((lab.j : ℝ) + lab.j') / ((V.l : ℝ) - 1)
    rw [hdiv, hdiv]
    push_cast
    nlinarith [mul_nonneg hj hrho, mul_nonneg hj hgam]

end GlobalTheory.CharPair
end
end

section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.integralChart_colength_bound_prime_two : ∀ (p : ℕ) [Fact p.Prime], AvFSt p → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p), y.IsAlg → ∀ (f : ℕ) (vd : ℝ), UpperTheory.Depth.SplitPlaces p H f vd → ∃ xs : (E →+* ℂ) → NNReal, (∀ τ, InPsi H τ → HasAF X.v (fun i => MvPowerSeries.map X.ι (Ch.FT i)) (fun (i : Fin (Dw.mult τ)) j => X.ι (Ch.uvecT ⟨τ, i⟩ j)) (xs τ)) ∧ (open Classical in (X.v ((p : ℕ) : X.C) : ℝ) ^ ((f : ℝ) * Dw.q * (1 + vd / 2)) ≤ ∏ τ ∈ Finset.univ.filter (fun τ => InPsi H τ), (xs τ : ℝ)) := by
  first | exact @GlobalTheory.CharDepth.colength_bound_at_two | exact GlobalTheory.CharDepth.colength_bound_at_two | (intros; apply GlobalTheory.CharDepth.colength_bound_at_two <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

namespace GlobalTheory.UnifPoint

theorem exists_uniformised_chart : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtA j la), letI := T.Q.H.starRing; ∃ (T' : CDVR) (io : T.Q.c.F →+* T'.Fr) (e : ℕ) (_ : OverLa la T'.V io e) (z : IntFr (T.Q.Xo j) T.Q.c T' io) (_ : z.IsAlg) (_ : T.G.lies j la T' io z (imgV y)) (C : IntegralChartA3 (T.Q.Xo j) T.Q.c T' io z) (P : PELUnif (maximalIdeal T'.V) C.I.G), FrTrunc C.I.G (𝟙 (Sp T'.V)) (chD C.ch) C.xT C.eT ∧ P.TorsionIso ∧ ∀ w : WeightFamilies.Wt D j, ∀ f ∈ T.th j w, vAtV y f = nval T'.V e (evI z f) := by
  intro D T h j hj la y
  letI := T.Q.H.starRing
  obtain ⟨q, S, io, e, ho, z, hz, eta, heta, rfl⟩ := y
  obtain ⟨S', io', z', r, hz', hr, hU, φ, hv, hm⟩ := GlobalTheory.T.exists_extension_all_models_uniformized _ _ _ _ (T.Q.Xo j) T.Q.c S io z hz
  letI := io.toAlgebra
  let ψ : S.Fr →+* S'.Fr := letI := io'.toAlgebra; φ.toRingHom
  have hio : io' = ψ.comp io := by
    letI := io'.toAlgebra
    exact RingHom.ext fun a => (φ.commutes a).symm
  have hv' : ∀ a : S.Fr, vV S'.V (ψ a) = (r : ℤ) * vV S.V a := fun a => by
    by_cases ha : a = 0
    · simp [ha, vV]
    · exact hv a ha
  have hfin : ψ.Finite := IntegralFrameAllCompare.finite_of_scale ψ hr hv' hz'
  have hnab : IsNab (T.Q.Xo j) T.Q.c (T.nab j) := by
    obtain ⟨inst, hn⟩ := h.nabPin j hj
    obtain rfl := GlobalTheory.PowGerm.starSt _ T.Q.H inst hn.1
    exact hn
  have hev : ∀ w : WeightFamilies.Wt D j, ∀ f ∈ T.th j w, ψ (evI z f) = evI z' f := fun w f hf =>
    GlobalTheory.T.thetaRule_integralPoint_value_baseChange _ _ _ _ (T.Q.Xo j) T.Q.c (T.nab j) hnab S S' io io' z z' φ hm _ _ f hf
  have hx : letI := io'.toAlgebra; z'.1.x = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap ψ ≫ z.1.x := hm.1
  have hu : letI := io'.toAlgebra
      ∀ τ i, z'.1.u τ i = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.1.u τ i := hm.2.1
  clear_value ψ
  clear hm hv φ
  subst hio
  obtain ⟨C, hCh⟩ := GlobalTheory.IntChartTrunc.intChart_frTrunc_exists _ T.Q.H _ _ (T.Q.Xo j) T.Q.c (fun _ => rfl) S' _ z'
  obtain ⟨P, hP⟩ := hU C.I
  refine ⟨S', ψ.comp io, r * e, ho.bc ψ hr hv', z', hz', fun hjm => ?_, C, P, hCh, hP, fun w f hf => ?_⟩
  · obtain ⟨u, hu', hl⟩ := heta hjm
    exact ⟨u, hu', GlobalTheory.LiesBaseChange.baseChange_of_finite_extension la _ S S' io ψ z z' hfin hr hv' hx hu u hl⟩
  · rw [← hev w f hf, nval_bc ψ hr hv']
    rfl

end GlobalTheory.UnifPoint
end
