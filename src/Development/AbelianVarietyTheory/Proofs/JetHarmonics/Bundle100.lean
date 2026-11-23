module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle003
public import Formalism.LocalToGlobal.CharacterGerms.BlockMembershipSelfConjugate
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle014
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffShiftS
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle084
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesMultiplicativeShiftCompAndSubst
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle025
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle051
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle058
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle098
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle082
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle097
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle085
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle087
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle091
import Formalism.LocalToGlobal.CharacterGerms.Bundle033
public import Formalism.LocalToGlobal.CharacterGerms.Bundle026
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle096
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Linter.Style
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002

@[expose] public section

section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowAt

theorem sum_sigma_extend {A C W : Type} [Fintype A] [Field C] [AddCommGroup W] [Module C W] (m : A → ℕ)
    (e : (Σ s : A, Fin (m s)) → W) (a : A) (b : Fin (m a) → C) :
    ∃ b' : (Σ s : A, Fin (m s)) → C, (∀ q, q.1 ≠ a → b' q = 0) ∧ ∑ x, b x • e ⟨a, x⟩ = ∑ q, b' q • e q := by
  refine ⟨fun q => if h : q.1 = a then b (h ▸ q.2) else 0, fun q hq => dif_neg hq, ?_⟩
  rw [Fintype.sum_sigma, Finset.sum_eq_single a]
  · simp
  · intro s _ hs
    simp [hs]
  · simp

theorem card_sigma_fst_add {d : ℕ} [NeZero d] (m : ZMod d → ℕ) (h a : ZMod d) :
    (Finset.univ.filter fun x : (Σ a : ZMod d, Fin (m a)) => x.1 + h = a).card = m (a - h) := by
  rw [← card_sigma_fst m (a - h)]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact eq_sub_iff_add_eq.symm

theorem exists_selfData : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → ∀ (Orb : Type) [Fintype Orb] (lab : LabS E Orb), ArithS V io ι lab → ∃ p : ∀ o, SelfData Y 2 (lab.II Dw o), IsSelfOf C3 ι Y lab p ∧ SelfSep Y p ∧ (lab.RankOK Dw → ∀ o, (Y.rawSelf (p o)).RankHyp ∧ (Y.rawSelf (p o)).AltC) := by
  intro E _ _ _ H Dw lv Xo c _ hstar T io y C3 C _ _ V ι hι k Y hY Orb _ lab ha
  obtain ⟨hint, hsep⟩ := GlobalTheory.T.cmEmbeddings_integral_and_distinct_mod_maximal E H lv c T io C V ι hι ha.unr
  have hsep' : ∀ x x' : Orb × ZMod 2, x ≠ x' →
      ∃ a : 𝓞 E, V.v (emA3 io ι (lab.tau x.1 x.2) a - emA3 io ι (lab.tau x'.1 x'.2) a) = 0 :=
    fun x x' h => hsep _ _ fun e => h (ha.inj e)
  have hsep1 : ∀ o (s s' : ZMod 2), s ≠ s' →
      ∃ a : 𝓞 E, V.v (emA3 io ι (lab.tau o s) a - emA3 io ι (lab.tau o s') a) = 0 :=
    fun o s s' h => hsep' (o, s) (o, s') fun e => h (Prod.mk.inj e).2
  have hconj : ∀ o (a : ZMod 2) (x : 𝓞 E), emA3 io ι (lab.tau o a) (star x) = emA3 io ι (lab.tau o (a + 1)) x := by
    intro o a x
    rw [ha.conj o a, embedding_conjugate hstar]
  have hgeo := fun o => GlobalTheory.T.separatedEmbeddings_directions_typedBasis E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY (ZMod 2) (lab.tau o) (hsep1 o)
  have := Y.algClosed
  have hgm := fun o => GlobalTheory.T.exists_matrix_standard_to_hyperbolic_inertPlace C V Y.l_odd Y.cpl (𝓞 E) (fun a => emA3 io ι (lab.tau o a))
    (fun a x => hint _ x) (ha.frob o) (hsep1 o 0 1 (by decide)) (hconj o)
  choose gm hlim hhyp using hgm
  let p : ∀ o, SelfData Y 2 (lab.II Dw o) := fun o =>
    { em := fun a => emA3 io ι (lab.tau o a)
      em_int := fun a x => hint _ x
      em_frob := ha.frob o
      em_sep := hsep1 o
      em_unr := GlobalTheory.T.exists_idempotent_frobeniusOrbit_unramified E H lv c T io C V ι hι ha.unr 2 (lab.tau o) (ha.frob o)
      hd := 1
      hd_ne := by decide
      hd_two := by decide
      em_conj := hconj o
      e := fun x i => ι (chartUnitVectors C3 ⟨lab.tau o x.1, x.2⟩ i)
      ty0 := fun x => x.1
      e_int := fun x i => (hgeo o).1 x.1 x.2 i
      e_eig := fun x a => (hgeo o).2.1 x.1 x.2 a
      e_sat := by
        obtain ⟨w, h1, h2⟩ := (hgeo o).2.2.1
        exact ⟨w, h1, fun q q' => by convert h2 q q'⟩
      e_full := fun a v hv => by
        obtain ⟨b, hb⟩ := (hgeo o).2.2.2 a v hv
        obtain ⟨b', h1, h2⟩ := sum_sigma_extend (fun s => Dw.mult (lab.tau o s))
          (fun (x : lab.II Dw o) i => ι (chartUnitVectors C3 ⟨lab.tau o x.1, x.2⟩ i)) a b
        exact ⟨b', h1, hb.trans h2⟩
      gm := gm o
      gm_lim := hlim o
      gm_hyp := hhyp o
      n := lab.n
      j := lab.j
      j' := lab.j'
      big := fun g s => s = ((g.val : ℕ) : ZMod 2) }
  refine ⟨p, ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ _ _ => Iff.rfl⟩, hsep', fun hr o => ⟨⟨?_, ?_, ?_⟩, by decide, ?_⟩⟩
  · show ∀ (g : Fin 2) (a : ZMod 2), a = (((1 - g).val : ℕ) : ZMod 2) ↔ ¬ a = ((g.val : ℕ) : ZMod 2)
    decide
  · intro g a hb
    change a = ((g.val : ℕ) : ZMod 2) at hb
    subst hb
    fin_cases g
    · exact (card_sigma_fst (fun a => Dw.mult (lab.tau o a)) _).trans (hr o).1
    · exact (card_sigma_fst_add (fun a => Dw.mult (lab.tau o a)) 1 _).trans (hr o).1
  · intro g a hb
    change ¬ a = ((g.val : ℕ) : ZMod 2) at hb
    fin_cases g
    · obtain rfl : a = 1 := by revert hb; revert a; decide
      exact (card_sigma_fst (fun a => Dw.mult (lab.tau o a)) _).trans (hr o).2
    · obtain rfl : a = 0 := by revert hb; revert a; decide
      exact (card_sigma_fst_add (fun a => Dw.mult (lab.tau o a)) 1 _).trans (hr o).2
  · show ∀ a : ZMod 2, a = (((0 : Fin 2).val : ℕ) : ZMod 2) ↔ Even a.val
    decide

end GlobalTheory.RowAt
end

section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.chartValues_bound_products_on_planes : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (Orb : Type) [Fintype Orb] (I0 : Orb → Type) [∀ o, Fintype (I0 o)] (p : ∀ o, SelfData Y d (I0 o)) (H : ∀ o, (Y.rawSelf (p o)).Hyps V) (Ls : LetSys C dd) (N n : ℕ) (pl : Fin N × Fin 2 ↪ Fin n) (ν : ℝ), SelfSep Y p → (ν : EReal) ≤ Y.nuPlE Ls n → RF.ValO (fun o => (Y.rawSelf (p o)).rowData (H o)) N (imgFamS Y p Ls pl) ν := by
  first | exact @GlobalTheory.RowAt.valO_self | exact GlobalTheory.RowAt.valO_self | (intros; apply GlobalTheory.RowAt.valO_self <;> assumption)
end

section

noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.ProdMeasure
variable {q : ℕ} [Fact q.Prime]

theorem hasSum_pi_prod : ∀ (g : ℕ) (u : Fin g → ℕ → ℂ_[q]) (s : Fin g → ℂ_[q]),
    (∀ i, HasSum (u i) (s i)) → HasSum (fun ν : Fin g → ℕ => ∏ i, u i (ν i)) (∏ i, s i) := by
  haveI : NonarchimedeanRing ℂ_[q] := ⟨NonarchimedeanAddGroup.is_nonarchimedean⟩
  intro g
  induction g with
  | zero =>
    intro u s _
    simpa using hasSum_fintype (fun ν : Fin 0 → ℕ => ∏ i, u i (ν i))
  | succ g ih =>
    intro u s h
    have h1 := (h 0).mul_of_nonarchimedean (ih (fun i => u i.succ) (fun i => s i.succ) fun i => h _)
    rw [← (Fin.consEquiv (fun _ : Fin (g + 1) => ℕ)).hasSum_iff, Fin.prod_univ_succ]
    convert h1 using 1
    funext p
    simp [Fin.consEquiv, Fin.prod_univ_succ]

theorem bd_one_pow {f : ℂ_[q]⟦X⟧} (h : Bd 1 f) (a : ℕ) : Bd 1 (f ^ a) := by
  induction a with
  | zero =>
    intro n
    rw [pow_zero, coeff_one]
    split_ifs <;> simp
  | succ a ih =>
    have := ((sup_norm_laws q).1 _ _ _ _ ih h).2
    rwa [mul_one, ← pow_succ] at this

theorem shiftS_pow {ζ : ℂ_[q]} (hζ : ‖ζ - 1‖ < 1) {f : ℂ_[q]⟦X⟧} (h : Bd 1 f) (a : ℕ) :
    shiftS ζ (f ^ a) = shiftS ζ f ^ a := by
  have H := Shift.shift_laws q ζ hζ
  induction a with
  | zero => simpa using H.2.2.1 1
  | succ a ih => rw [pow_succ, (H.2.1 _ _ ⟨1, bd_one_pow h a⟩ ⟨1, h⟩).2, ih, pow_succ]

theorem hat_pow (ι : ℂ ≃+* ℂ_[q]) (ℓ : ℂ_[q]⟦X⟧) (hl : constantCoeff ℓ = 0) (G : ℂ → ℂ)
    (hG : AnalyticAt ℂ G 0) (a : ℕ) : hat ι ℓ (fun z => G z ^ a) = hat ι ℓ G ^ a := by
  have H := TaylorRead.hat_laws q ι ℓ hl
  induction a with
  | zero => simpa using H.2.1 1
  | succ a ih =>
    simp only [pow_succ]
    rw [(H.1 (fun z => G z ^ a) G (hG.pow a) hG).2.1, ih]

theorem prod_fiber_pow {g k : ℕ} (σ : Fin k → Fin g) (x : Fin g → ℂ_[q]) :
    ∏ l, x (σ l) = ∏ i, x i ^ (Finset.univ.filter (fun l => σ l = i)).card := by
  rw [← Finset.prod_fiberwise Finset.univ σ (fun l => x (σ l))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_const]
  exact Finset.prod_congr rfl fun l hl => by rw [(Finset.mem_filter.mp hl).2]

theorem measure_of_products : ∀ (d q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (δ : ℂ) (Ω : ℂ_[q]) (θ : ℂ → ℂ), 0 < d → δ ≠ 0 → Ω ≠ 0 → Differentiable ℂ θ → ThetaLaws ι d (Ω / ι δ) θ → ∀ (g m : ℕ) (a : Fin g → ℕ) (c : Fin m → ℂ) (t : Fin m → Fin g → ℂ), (∀ j i, PrimeTo d q (t j i)) → ∃ μ : C(Fin g → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q], (∀ B : ℝ, 0 ≤ B → (‖μ‖ ≤ B ↔ ∀ ν : Fin g → ℕ, ‖∑ j, ι (c j) * ∏ i, coeff (ν i) (hat ι (C (Ω / ι δ) * logS) (U1 d (t j i) θ) ^ a i)‖ ≤ B)) ∧ ∀ (n s : ℕ) (y : Fin g → ℂ), Nat.Coprime s q → (∀ j i, InOK d ((s : ℂ) * t j i)) → (∀ i, Good ι d n s (y i)) → ∀ (k : ℕ) (ys : Fin k → Fin g → ℂ) (F : C(Fin g → ℤ_[q], ℂ_[q])), (∀ A, F A = (∏ i, ι (kap1 d 1 (y i)) ^ (PadicInt.toZModPow n (A i)).val) * ∏ l, (Ω⁻¹ * ∑ i, ι (ys l i) * zc (A i))) → ι (iteratedFDeriv ℂ k (fun z : Fin g → ℂ => ∑ j, c j * ∏ i, W1 d (y i) (U1 d (t j i) θ) (z i) ^ a i) 0 (fun l => δ⁻¹ • ys l)) = μ F := by
  intro d q _ ι δ Ω θ hd hδ hΩ hθ hL g m a c t ht
  set ω : ℂ_[q] := Ω / ι δ with hω
  have hS : ∀ j i, Bd 1 (hat ι (C ω * logS) (U1 d (t j i) θ) ^ a i) :=
    fun j i => bd_one_pow (hL.1 _ (ht j i)) _
  obtain ⟨μ, hμ1, hμ2⟩ := GlobalTheory.MultiMahler.exists_measure_of_bounded_moments q g
    (fun ν => ∑ j, ι (c j) * ∏ i, coeff (ν i) (hat ι (C ω * logS) (U1 d (t j i) θ) ^ a i))
    ⟨∑ j, ‖ι (c j)‖, fun ν => (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => by
      rw [norm_mul, norm_prod]
      exact mul_le_of_le_one_right (norm_nonneg _)
        (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => hS j i _))⟩
  refine ⟨μ, hμ1, ?_⟩
  intro n s y hs hst hy k ys F hF
  have hl : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := by
    simp [logS, ← coeff_zero_eq_constantCoeff_apply]
  have hdiff : ∀ j i, Differentiable ℂ (W1 d (y i) (U1 d (t j i) θ)) := fun j i =>
    ((heisenbergOne d hd).2.2.1 _ _ ((heisenbergOne d hd).2.2.1 _ _ hθ).1).2
  have hroot : ∀ i, ι (kap1 d 1 (y i)) ^ (q ^ n) = 1 := fun i =>
    (hL.2.1 0 (y i) n s hs ⟨0, 0, by simp⟩ (hy i)).1
  have hf : ∀ (i : Fin g) (e : ℕ), ∃ f : C(ℤ_[q], ℂ_[q]),
      (∀ A, f A = ι (kap1 d 1 (y i)) ^ (PadicInt.toZModPow n A).val * zc A ^ e) ∧
      ∀ j, HasSum (fun r : ℕ => coeff r (hat ι (C ω * logS) (U1 d (t j i) θ) ^ a i) *
        (fwdDiff (1 : ℤ_[q]))^[r] f 0)
        (ω ^ e * ι (iteratedDeriv e (fun z => W1 d (y i) (U1 d (t j i) θ) z ^ a i) 0)) := by
    intro i e
    obtain ⟨f, hf, -⟩ := GlobalTheory.T.twisted_measure_moments_eq_shifted_series_jets q 0 _ n e ⟨0, fun r => by simp⟩ (hroot i)
    refine ⟨f, hf, fun j => ?_⟩
    obtain ⟨f', hf', h⟩ := GlobalTheory.T.twisted_measure_moments_eq_shifted_series_jets q _ _ n e ⟨1, hS j i⟩ (hroot i)
    obtain rfl : f' = f := by ext A; rw [hf, hf']
    have han := (hdiff j i).analyticAt 0
    rw [shiftS_pow (ShiftComp.norm_sub_one_lt_of_root (hroot i)) (hL.1 _ (ht j i)),
      ← (hL.2.1 _ _ n s hs (hst j i) (hy i)).2, ← hat_pow ι _ hl _ han,
      (hat_multiplicative_chart q ι ω (fun z => W1 d (y i) (U1 d (t j i) θ) z ^ a i)
        (han.pow (a i))).2.1 e] at h
    exact h
  choose f hf1 hf2 using hf
  let P : (Fin k → Fin g) → C(Fin g → ℤ_[q], ℂ_[q]) := fun σ =>
    ⟨fun A => ∏ i, f i (Finset.univ.filter (fun l => σ l = i)).card (A i), by fun_prop⟩
  have hP : ∀ σ, μ (P σ) = ∑ j, ι (c j) * ∏ i, (ω ^ (Finset.univ.filter (fun l => σ l = i)).card *
      ι (iteratedDeriv (Finset.univ.filter (fun l => σ l = i)).card
        (fun z => W1 d (y i) (U1 d (t j i) θ) z ^ a i) 0)) := by
    intro σ
    refine (hμ2 (fun i => f i (Finset.univ.filter (fun l => σ l = i)).card) (P σ) fun _ => rfl).unique ?_
    have := hasSum_sum (s := Finset.univ) fun j _ =>
      (hasSum_pi_prod g _ _ fun i => hf2 i (Finset.univ.filter (fun l => σ l = i)).card j).mul_left (ι (c j))
    simp only [Finset.sum_mul, mul_assoc]
    simp only [Finset.prod_mul_distrib] at this ⊢
    exact this
  have hFP : F = ∑ σ : Fin k → Fin g, (∏ l, Ω⁻¹ * ι (ys l (σ l))) • P σ := by
    ext A
    rw [hF]
    simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul, Pi.smul_apply,
      smul_eq_mul, P, ContinuousMap.coe_mk, hf1, Finset.mul_sum]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.prod_mul_distrib (f := fun i => ι (kap1 d 1 (y i)) ^ (PadicInt.toZModPow n (A i)).val),
      ← prod_fiber_pow σ (fun i => zc (A i))]
    simp only [← mul_assoc]
    rw [Finset.prod_mul_distrib (g := fun l => zc (A (σ l)))]
    ring
  have hcd : ∀ j, ContDiff ℂ k (fun z : Fin g → ℂ => ∏ i, W1 d (y i) (U1 d (t j i) θ) (z i) ^ a i) :=
    fun j => contDiff_prod fun i _ => (((hdiff j i).contDiff).comp (contDiff_apply ℂ (fun _ => ℂ) i)).pow _
  have hit : iteratedFDeriv ℂ k (fun z : Fin g → ℂ => ∑ j, c j * ∏ i, W1 d (y i) (U1 d (t j i) θ) (z i) ^ a i) 0
      = ∑ j, c j • iteratedFDeriv ℂ k
        (fun z : Fin g → ℂ => ∏ i, W1 d (y i) (U1 d (t j i) θ) (z i) ^ a i) 0 := by
    rw [iteratedFDeriv_sum (fun j _ => contDiff_const.mul (hcd j)), Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact iteratedFDeriv_const_smul_apply' (a := c j) (x := 0) (hcd j).contDiffAt

  rw [hit, hFP, map_sum μ]

  simp only [map_smul, hP, smul_eq_mul, ContinuousMultilinearMap.sum_apply,
  ContinuousMultilinearMap.smul_apply, Finset.mul_sum, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [GlobalTheory.CoordProdDeriv.iteratedFDeriv_prod_coord g k
    (fun i z => W1 d (y i) (U1 d (t j i) θ) z ^ a i) _ (fun i => (hdiff j i).pow _)]

  simp only [Finset.mul_sum, map_sum, map_mul, map_prod, Pi.smul_apply, smul_eq_mul, map_inv₀]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib (f := fun i => ω ^ (Finset.univ.filter (fun l => σ l = i)).card),
    ← prod_fiber_pow σ (fun _ => ω)]
  have e : ∏ l, (ι δ)⁻¹ * ι (ys l (σ l)) = (∏ l, Ω⁻¹ * ι (ys l (σ l))) * ∏ _l : Fin k, ω := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [hω]; field_simp
  rw [e]
  ring

end GlobalTheory.MomOne.ProdMeasure
end
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem isMod_smooth_of_isDS : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), 1 ≤ k → R.IsDS ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → IsMod ε E mu := by
  intro hH k r ε mu R hk hDS Q E hQ hE
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hU : IsUnit Q := by
    have h1 : Q * star Q = 1 := (Matrix.mem_unitaryGroup_iff).1 hQ.2
    have h2 : star Q * Q = 1 := (Matrix.mem_unitaryGroup_iff').1 hQ.2
    exact ⟨⟨Q, star Q, h1, h2⟩, rfl⟩
  have hG : Formalism.REAL.GlRel E := (GlobalTheory.T.derivedAction_expand_matrixUnits hK k r ε mu R hDS Q E hU hE).1
  refine ⟨hG, GlobalTheory.T.cayley_endomorphisms_unitary hK k r ε mu R hDS Q E hQ hE, ?_⟩
  exact GlobalTheory.T.casimir_scalar_of_capelliDeterminant_eigenvalue R.smSub (2 * r + k + 1) E mu (by omega) hG
    (GlobalTheory.T.quantum_determinant_eigenvalue hH k r ε mu R hDS Q E hU hE)

end GlobalTheory
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselAdjoint

theorem integral_comp_involution {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure X} {T : X → X} (hT : MeasurePreserving T μ μ) (hTT : ∀ᵐ p ∂μ, T (T p) = p) (f : X → E) :
    ∫ p, f (T p) ∂μ = ∫ p, f p ∂μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · have h1 : AEStronglyMeasurable f (μ.map T) := by rw [hT.map_eq]; exact hf
    rw [← integral_map hT.measurable.aemeasurable h1, hT.map_eq]
  · have hg : ¬ AEStronglyMeasurable (fun p => f (T p)) μ := by
      intro hg
      apply hf
      refine (hg.comp_measurePreserving hT).congr ?_
      filter_upwards [hTT] with p hp
      simp [hp]
    rw [integral_non_aestronglyMeasurable hf, integral_non_aestronglyMeasurable hg]

def adjR (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] :
    (W →L[ℂ] W) →ₗᵢ[ℝ] (W →L[ℂ] W) where
  toFun A := ContinuousLinearMap.adjoint A
  map_add' A B := map_add _ A B
  map_smul' c A := by
    have e : ∀ B : W →L[ℂ] W, c • B = (c : ℂ) • B := fun B => by
      ext x; simp
    rw [RingHom.id_apply, e, e, map_smulₛₗ]; simp
  norm_map' A := ContinuousLinearMap.adjoint.norm_map A

theorem adjoint_integral {X W : Type*} [MeasurableSpace X] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [CompleteSpace W] (μ : Measure X) (f : X → (W →L[ℂ] W)) :
    ContinuousLinearMap.adjoint (∫ p, f p ∂μ) = ∫ p, ContinuousLinearMap.adjoint (f p) ∂μ :=
  ((adjR W).integral_comp_comm f).symm

theorem adjoint_be : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, ∀ w ∈ R.TK, ContinuousLinearMap.adjoint (be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v) = be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v w := by
  intro _ k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hDS _ hOK hS v _ w _
  obtain ⟨hz, hT, ⟨u₀, hπ⟩, -, hW, hN, -, -⟩ := hS
  obtain ⟨-, hinv, -, -, -, hae⟩ := GlobalTheory.T.besselSubgroup_parameter_measurePreserving k r z μW μN hOK.1 hz hT hW hN
  obtain ⟨-, -, hψi, hψc, hUW, hNG⟩ := GlobalTheory.BesselPsi.psi_character k r z Formalism.QuantumDeterminants.cStd hz
  unfold be
  rw [adjoint_integral, ← integral_comp_involution hinv ?_ (beInt z Formalism.QuantumDeterminants.cStd π R.σ v w)]
  · refine integral_congr_ae ?_
    filter_upwards [hae] with p hp
    obtain ⟨hp1, hp2⟩ := hp
    obtain ⟨hi, hhi, hih⟩ := P.MatrixMultiplicationContinuity.uw_inv hp1
    have hg1 : Matrix.of p.1 ∈ GG k r := hp1.1
    have hg2 : Matrix.of p.2 ∈ GG k r := hp2.1
    have hg : Matrix.of p.1 * Matrix.of p.2 ∈ GG k r := by
      have a1 : (Matrix.of p.1)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of p.1 = Formalism.QuantumDeterminants.Hpk k r := hg1
      have a2 : (Matrix.of p.2)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of p.2 = Formalism.QuantumDeterminants.Hpk k r := hg2
      show (Matrix.of p.1 * Matrix.of p.2)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (Matrix.of p.1 * Matrix.of p.2) = Formalism.QuantumDeterminants.Hpk k r
      calc _ = (Matrix.of p.2)ᴴ * ((Matrix.of p.1)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of p.1) * Matrix.of p.2 := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [a1, a2]
    have hii : ((Matrix.of p.1)⁻¹)⁻¹ = (Matrix.of p.1 : Mx k r) := Matrix.inv_eq_left_inv hhi
    have e1 : (Matrix.of p.1)⁻¹ * (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹) =
        ((Matrix.of p.1 * Matrix.of p.2)⁻¹ : Mx k r) := by
      rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hih, Matrix.one_mul]
    have e2 : Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹) =
        star (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of p.2)) := by
      rw [(hψc _ hp1 _ (hψi _ hp2).1).2.2.1, (hψi _ hp2).2]
    have e3 : ContinuousLinearMap.adjoint (π (Matrix.of p.1)⁻¹) = π (Matrix.of p.1) := by
      symm
      rw [ContinuousLinearMap.eq_adjoint_iff]
      intro x y
      rw [P.MatrixMultiplicationContinuity.piW_inner hT hπ hi, hii]
    show ContinuousLinearMap.adjoint ((⟪v, R.σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ *
        star (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹) =
      (⟪w, R.σ ((Matrix.of p.1)⁻¹ * (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹)) v⟫_ℂ *
        star (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹))) •
        π ((Matrix.of p.1)⁻¹)⁻¹
    rw [e1, e2, hii, map_smulₛₗ, e3, P.MatrixMultiplicationContinuity.sigma_inner hDS.2 hg v w, map_mul, inner_conj_symm]
    rfl
  · filter_upwards [hae] with p hp
    obtain ⟨hp1, hp2⟩ := hp
    obtain ⟨hi, hhi, hih⟩ := P.MatrixMultiplicationContinuity.uw_inv hp1
    obtain ⟨-, hni, hin⟩ := P.MatrixMultiplicationContinuity.uh_inv hp2.1
    have hii : ((Matrix.of p.1)⁻¹)⁻¹ = (Matrix.of p.1 : Mx k r) := Matrix.inv_eq_left_inv hhi
    have hnn : ((Matrix.of p.2)⁻¹)⁻¹ = (Matrix.of p.2 : Mx k r) := Matrix.inv_eq_left_inv hni
    have e : (Matrix.of p.1)⁻¹ * (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹)⁻¹ * ((Matrix.of p.1)⁻¹)⁻¹ =
        (Matrix.of p.2 : Mx k r) := by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hii, hnn, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hih,
        Matrix.one_mul, Matrix.mul_assoc, hih, Matrix.mul_one]
    exact Prod.ext hii e

end GlobalTheory.BesselAdjoint
end
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.tensor_weighted_bessel_sum : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (om om' : ι → ℂ) (l : R.H → Wp) (l' : R.H → Wq) (lI : ∀ I, (RI I).H → Wp) (lI' : ∀ I, (RI I).H → Wq) (F : Mx k r → (Wq →L[ℂ] Wp)) (s : ℂ), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → IsCoef R l l' F s → ∃ (Ft : κ → Mx k r → (Wq →L[ℂ] Wp)) (st : κ → ℂ), (∀ I, IsCoef (RI I) (lI I) (lI' I) (Ft I) (st I)) ∧ (∀ g ∈ GG k r, Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ om') om • F g = ∑ I, Ft I g) ∧ (∀ I, (¬ NzOn (RI I) (lI I) ∨ ¬ NzOn (RI I) (lI' I)) → st I = 0) ∧ ∀ I (κ₀ κ₁ : ℂ), (∀ v ∈ R.sm, lI I (∑ c, pr I c (tm R om v c)) = κ₀ • l v) → (∀ v ∈ R.sm, lI' I (∑ c, pr I c (tm R om' v c)) = κ₁ • l' v) → st I = (ep I : ℂ) * κ₁ * star κ₀ * s := by
  first | exact @GlobalTheory.coef_mul_split | exact GlobalTheory.coef_mul_split | (intros; apply GlobalTheory.coef_mul_split <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem exists_isQuotMeas_bessel_subgroup : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (μW μN μG : Measure (Formalism.QuantumDeterminants.Mt k r)), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z →
    PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW →
    PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN →
    PI.BesselPeriodGGP.IsHaarOn (GG k r) μG →
    ∃ νq, PI.BesselPeriodGGP.IsQuotMeas μG (muSof μW μN) νq := by
  intro k r z μW μN μG hz hT hW hN hG
  obtain ⟨hGgrp, hGinv⟩ := GlobalTheory.T.isMatGroup_GG_and_haar_right_invariant k r
  obtain ⟨hGhaar, _⟩ := hGinv μG hG
  obtain ⟨hSgrp, hSsub, hShaar, hSright⟩ := GlobalTheory.T.besselSubgroup_product_measure_isHaar k r z μW μN hz hT hW hN
  exact GlobalTheory.T.exists_quotientMeasure_weil (2 * r + k + 1) (GG k r) (Formalism.QuantumDeterminants.Sset k r z) μG (muSof μW μN)
    hGgrp hSgrp hSsub hGhaar hShaar hSright

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_characterGerm_valuation_eq_columnTyped : ∀ (C : Type) [Field C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (d : ℕ) (OE : Type) [CommRing OE] [StarRing OE] (B : FB O d OE) (h : PS C 2 d), B.IsCanonGauge C h → ∀ (w0 : OE) (k n : ℕ) (Ty : Type) [Fintype Ty] (r : Ty → ℕ) [Fintype (Letter Ty r n)] (σ : Ty → (OE →+* O)) (u : (Σ τ : Ty, Fin (r τ)) → Fin d → O), (∀ ℓ a, (linPart (B.A.act a)).mulVec (u ℓ) = σ ℓ.1 a • u ℓ) → (∀ τ, ∃ a0, IsUnit (σ τ a0 - σ τ (star a0))) → (∀ x : O, x ≠ 0 → ∃ N : ℕ, v (N : C) < v (algebraMap O C x) ∧ ∀ τ, ∃ a : OE, star a * a = (N : OE) ∧ v (algebraMap O C (σ τ a - 1)) < v (algebraMap O C x)) → ∀ (ty : Fin n → Ty) (P : MvPolynomial (Letter Ty r n) O), (∀ mo ∈ P.support, ∀ ℓ, mo ℓ ≠ 0 → ℓ.1 = ty ℓ.2.2) → ∀ χ : Fin n → PS O 1 d, (∀ b, IsCh B.G.F (χ b)) → MvPolynomial.eval (fun ℓ : Letter Ty r n => ∑ j, u ⟨ℓ.1, ℓ.2.1⟩ j * dl (χ ℓ.2.2) j) P ≠ 0 → ∃ f : PS O n d, v (nabValN B C h w0 k (MvPowerSeries.map (algebraMap O C) f) (fun ℓ : Letter Ty r n => ℓ.2.2) (fun (ℓ : Letter Ty r n) i => algebraMap O C (u ⟨ℓ.1, ℓ.2.1⟩ i)) (MvPolynomial.map (algebraMap O C) P)) = v (algebraMap O C (MvPolynomial.eval (fun ℓ : Letter Ty r n => ∑ j, u ⟨ℓ.1, ℓ.2.1⟩ j * dl (χ ℓ.2.2) j) P)) := by
  first | exact @GlobalTheory.CharValue.exists_germ_valuation_eq | exact GlobalTheory.CharValue.exists_germ_valuation_eq | (intros; apply GlobalTheory.CharValue.exists_germ_valuation_eq <;> assumption)
end
