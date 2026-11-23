module

import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle003
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeries₂.Bundle001
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle079
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle080
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle255
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle256
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle257
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle223
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.PowerSeries.Inverse
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle251

@[expose] public section

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.TensForm

theorem common_bound {ι α β : Type} [DecidableEq ι] (P : α → Prop) (S : Set β) (n : α → β → ℝ)
    (hn : ∀ a v, 0 ≤ n a v) (f : ι → β → ℝ)
    (h : ∀ c, ∃ (C : ℝ) (L : List α), (∀ a ∈ L, P a) ∧ ∀ v ∈ S, f c v ≤ C * (L.map fun a => n a v).sum)
    (s : Finset ι) :
    ∃ (C : ℝ) (L : List α), 0 ≤ C ∧ (∀ a ∈ L, P a) ∧
      ∀ c ∈ s, ∀ v ∈ S, f c v ≤ C * (L.map fun a => n a v).sum := by
  apply Gp91.GlobalTheory.TensForm.common_bound <;> assumption

variable {k r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem hh_act (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (R : Rep k r) (g : Mx k r)
    (hρ : (ρ g)ᴴ * Γ * ρ g = Γ) (hσ : ∀ v, ‖R.σ g v‖ = ‖v‖) (x y : ι → R.H) :
    hh Γ R (act ρ R g x) (act ρ R g y) = hh Γ R x y := by
  apply Gp91.GlobalTheory.TensForm.hh_act <;> assumption


omit [DecidableEq ι] in
theorem norm_hh_le (Γ : Matrix ι ι ℂ) (R : Rep k r) (x y : ι → R.H) (A B : ℝ)
    (hx : ∀ c, ‖x c‖ ≤ A) (hy : ∀ c, ‖y c‖ ≤ B) :
    ‖hh Γ R x y‖ ≤ (∑ i, ∑ j, ‖Γ i j‖) * (A * B) := by
  rw [hh, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ((norm_inner_le_norm _ _).trans ?_) (norm_nonneg _)
  rw [mul_comm A B]
  exact mul_le_mul (hy i) (hx j) (norm_nonneg _) ((norm_nonneg _).trans (hy i))

theorem family_bound (R R' : Rep k r) (T : ι → R.H → R'.H) (hT : ∀ c, SmMap R R' (T c)) :
    ∃ (C : ℝ) (Ws : List (List (Mx k r))), (∀ W ∈ Ws, ∀ X ∈ W, PI.UpqRep.InLieHpk k r X) ∧
      ∀ c, ∀ v ∈ R.sm, ‖T c v‖ ≤ C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W v‖).sum := by
  obtain ⟨C, L, -, hL, hb⟩ := common_bound (fun W : List (Mx k r) => ∀ X ∈ W, PI.UpqRep.InLieHpk k r X) R.sm
    (fun W v => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W v‖) (fun _ _ => norm_nonneg _)
    (fun c v => ‖T c v‖) (fun c => (hT c).cont [] (by simp)) Finset.univ
  exact ⟨C, L, hL, fun c => hb c (Finset.mem_univ c)⟩

theorem pulledBack_isInvForm : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → IsFRep ρ Γ d → TensRaw ρ R RI io pr → ∀ I J, IsInvForm (RI I) (RI J) (fun y y' => hh Γ R (fun c => io I c y) (fun c => io J c y')) := by
  intro _ k r ι κ _ _ _ _ ρ Γ d R RI io pr ε mu muI hR _ hF hT I J
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx x' hx' y _
    simp only [hh, fun c => (hT.io_sm I c).add x hx x' hx', inner_add_right, mul_add, Finset.sum_add_distrib]
  · intro a x hx y _
    simp only [hh, fun c => (hT.io_sm I c).smul a x hx, inner_smul_right, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  · intro x _ y hy y' hy'
    simp only [hh, fun c => (hT.io_sm J c).add y hy y' hy', inner_add_left, mul_add, Finset.sum_add_distrib]
  · intro a x _ y hy
    simp only [hh, fun c => (hT.io_sm J c).smul a y hy, inner_smul_left, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [RCLike.star_def]; ring
  · intro g hg x hx y hy
    show hh Γ R (fun c => io I c ((RI I).σ g x)) (fun c => io J c ((RI J).σ g y)) = _
    rw [hT.io_eq I g hg x hx, hT.io_eq J g hg y hy]
    exact hh_act ρ Γ R g (hF.2.2.2.2.1 g hg) ((Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.sigma_facts hR.2).2 g hg) _ _
  · obtain ⟨C, Ws, hW, hb⟩ := family_bound (RI I) R (io I) (hT.io_sm I)
    obtain ⟨C', Ws', hW', hb'⟩ := family_bound (RI J) R (io J) (hT.io_sm J)
    refine ⟨(∑ i, ∑ j, ‖Γ i j‖) * C * C', Ws, Ws', ?_, ?_⟩
    · intro W hWm
      rcases List.mem_append.1 hWm with h | h
      · exact hW W h
      · exact hW' W h
    · intro x hx y hy
      refine (norm_hh_le Γ R _ _ _ _ (fun c => hb c x hx) (fun c => hb' c y hy)).trans (le_of_eq ?_)
      ring

end GlobalTheory.TensForm
end

section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_formalBiextension_integral_chart_valuedExtension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (p : ℕ) [Fact p.Prime] (X : ValExt T p), ∃ B : FB X.O (chD Ch.ch) (𝓞 E), B.G.F = (fun i => MvPowerSeries.map X.ι (Ch.FT i)) ∧ (∀ a, B.A.act a = fun i => MvPowerSeries.map X.ι (Ch.actT a i)) ∧ B.IsCanonGauge X.C (letI := io.toAlgebra; MvPowerSeries.map X.ιF Ch.ch.h) := by
  first | exact @GlobalTheory.CharDepth.exists_formalBiext_valExt | exact GlobalTheory.CharDepth.exists_formalBiext_valExt | (intros; apply GlobalTheory.CharDepth.exists_formalBiext_valExt <;> assumption)
end

section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.realPlaceLabelling_inert_frobenius_not_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (c : Coeff lv) (N : NumDatum) (pl : RPl N.R → (E →+* ℂ)), PlaceTie N c pl → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → V.l = resCharOf la → (∀ x ∈ la.asIdeal, V.MM (ι (io ((x : 𝓞 c.F) : c.F)))) → Inert N V.l → ¬ ConjIn N V.l → ∀ j : ℕ, ∃ Z : Finset (RPl N.R), RF.IsReps (parOf N j V.l) Z ∧ Z.Nonempty ∧ Even (N.ordP V.l) ∧ Function.Bijective (fun x : Z × Fin 2 × ZMod (N.ordP V.l) => tauIn N pl V.l x.1.1 x.2.1 x.2.2) ∧ ∀ z g, FrobOrd V io ι (tauIn N pl V.l z g) ∧ ∀ s, tauIn N pl V.l z 1 s = ComplexEmbedding.conjugate (tauIn N pl V.l z 0 s) := by
  exact @GlobalTheory.InertLabelling.main
end

section

set_option autoImplicit false

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowAt

private theorem restDeg_add {d : ℕ} [NeZero d] (bgr : ZMod d → Fin 2) (n K : ℕ) (h1 : 1 ≤ n) (hK : n ≤ K)
    (ga : Fin 2 → ZMod d → ℕ → ℕ) :
    RF.restDeg bgr n ga K + ∑ s, n * ga (bgr s) s n =
      ∑ g : Fin 2, ∑ s : ZMod d, ∑ k ∈ Finset.Icc 1 K, k * ga g s k := by
  unfold RF.restDeg
  rw [Finset.sum_comm, Finset.sum_comm (f := fun g s => ∑ k ∈ Finset.Icc 1 K, k * ga g s k),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  have e : n * ga (bgr s) s n =
      ∑ g : Fin 2, ∑ k ∈ Finset.Icc 1 K, if g = bgr s ∧ k = n then k * ga g s k else 0 := by
    rw [Finset.sum_eq_single (bgr s), Finset.sum_eq_single n]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_Icc.2 ⟨h1, hK⟩) h
    · intro b _ hb; simp [hb]
    · simp
  rw [e, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

private theorem sum_reps (P : RF.Par) (Z : Finset P.Pl) (h : RF.IsReps P Z) (W : P.Pl → ℕ) :
    ∑ z ∈ Z, ∑ s : ZMod P.d, W (P.pos z s.val) = ∑ z, W z := by
  rw [← Finset.sum_product']
  refine Finset.sum_bij (fun p _ => P.pos p.1 p.2.val) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
  · intro p hp q hq hpq
    exact (h (P.pos q.1 q.2.val)).unique ⟨(Finset.mem_product.1 hp).1, hpq⟩ ⟨(Finset.mem_product.1 hq).1, rfl⟩
  · intro z _
    obtain ⟨p, hp, -⟩ := h z
    exact ⟨p, Finset.mem_product.2 ⟨hp.1, Finset.mem_univ _⟩, hp.2⟩

theorem wtHyp_gap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (N : NumDatum) (j : ℕ) (pl : RPl N.R → (E →+* ℂ)) (a : (E →+* ℂ) × ℕ → ℕ), 1 ≤ j → j ≤ N.R.m → (∀ z, InPsi H (pl z)) → Dw.p = (N.R.sigW j).1 → Dw.q = (N.R.sigW j).2 → DomW Dw a → ∀ (d : ℕ) [NeZero d] (pos : RPl N.R → ℕ → RPl N.R) (Z : Finset (RPl N.R)) (bgr : ZMod d → Fin 2) (tau : RPl N.R → Fin 2 → ZMod d → (E →+* ℂ)), RF.IsReps (parAt N j d pos) Z → Function.Bijective (fun x : Z × Fin 2 × ZMod d => tau x.1.1 x.2.1 x.2.2) → (∀ z s, tau z (bgr s) s = pl (pos z s.val)) → RF.WtHyp N.R.k N.R.r Z bgr (fun z g s => Dw.mult (tau z g s)) (fun z g s => gap (Dw.mult (tau z g s)) fun i => a (tau z g s, i)) (fun z => RF.alongOrb (parAt N j d pos) z (gapW N pl a)) (fun _ _ => 0) (restOf N Dw pl a) := by
  intro E _ _ _ H Dw N j pl a hj1 hjm hpsi hp hq hdom d _ pos Z bgr tau hZ hbij htau
  have hmk := N.R.m_add_three_le_k
  have hp' : Dw.p = N.R.k + j - 1 := hp
  have hq' : Dw.q = N.R.m - j := hq
  have hr : N.R.r = N.R.k + N.R.m - 1 := rfl
  have hmul : ∀ τ, Dw.mult τ ≤ N.R.r := fun τ => by
    unfold Datum.mult; split_ifs <;> omega
  have hgs := fun τ => gap_sums (Dw.mult τ) (fun i => a (τ, i)) (fun i i' hi hi' => hdom τ ⟨i, lt_of_le_of_lt hi hi'⟩ ⟨i', hi'⟩ hi)
  have hmain : ∀ z s, gap (Dw.mult (tau z (bgr s) s)) (fun i => a (tau z (bgr s) s, i)) (N.R.k - 1) =
      gapW N pl a (pos z s.val) := by
    intro z s
    rw [htau]
    have hm : Dw.mult (pl (pos z s.val)) = Dw.p := if_pos (hpsi _)
    rw [hm]
    unfold gap gapW
    rw [if_pos (by omega), if_pos (by omega)]
    rfl
  refine ⟨fun z _ g s k hk => (hgs _).1 k hk, fun z _ s => hmain z s, ?_⟩
  have hDF : DF Dw a = ∑ z ∈ Z, ∑ g : Fin 2, ∑ s : ZMod d, ∑ i : Fin (Dw.mult (tau z g s)), a (tau z g s, i) := by
    unfold DF
    rw [← hbij.sum_comp (fun τ => ∑ i : Fin (Dw.mult τ), a (τ, i)), Fintype.sum_prod_type,
      ← Finset.sum_coe_sort Z]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Fintype.sum_prod_type]
  have key : (∑ z ∈ Z, RF.restDeg bgr (N.R.k - 1)
      (fun g s => gap (Dw.mult (tau z g s)) fun i => a (tau z g s, i)) N.R.r) +
      (N.R.k - 1) * ∑ z, gapW N pl a z = DF Dw a := by
    have hs : ∑ z ∈ Z, ∑ s : ZMod d, gapW N pl a (pos z s.val) = ∑ z, gapW N pl a z :=
      sum_reps (parAt N j d pos) Z hZ (gapW N pl a)
    rw [hDF, ← hs, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    have := restDeg_add bgr (N.R.k - 1) N.R.r (by omega) (by omega)
      (fun g s => gap (Dw.mult (tau z g s)) fun i => a (tau z g s, i))
    simp only [hmain] at this
    rw [Finset.mul_sum, this]
    exact Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun s _ => ((hgs _).2 _ (hmul _)).2
  unfold restOf
  rw [← key]
  push_cast [Nat.cast_sub (show 1 ≤ N.R.k by omega)]
  simp

end GlobalTheory.RowAt
end

section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

theorem sup_norm_laws : ∀ (q : ℕ) [Fact q.Prime], (∀ (f g : ℂ_[q]⟦X⟧) (A B : ℝ), Bd A f → Bd B g → Bd (max A B) (f + g) ∧ Bd (A * B) (f * g)) ∧ (∀ (f h : ℂ_[q]⟦X⟧) (A : ℝ), Bd A f → Bd 1 h → constantCoeff h = 0 → Bd A (f.subst h)) ∧ (∀ (f g : ℂ_[q]⟦X⟧), Bd 1 f → ‖constantCoeff f‖ = 1 → f * g = 1 → Bd 1 g) ∧ (∀ (f g : ℂ_[q]⟦X⟧) (B : ℝ), Bdd f → Bdd g → Bd B (f * g) → ∀ i j, ‖coeff i f‖ * ‖coeff j g‖ ≤ B) ∧ (∀ (f g : ℂ_[q]⟦X⟧), Bdd f → Bdd g → f * g = 1 → constantCoeff f = 1 → Bd 1 f ∧ Bd 1 g) ∧ (∀ (f v : ℂ_[q]⟦X⟧) (k : ℕ) (B : ℝ), Bd 1 v → ‖constantCoeff v‖ = 1 → Bd B (X ^ k * v * f) → Bd B f) := by
  intro q _
  have R := GlobalTheory.EvenTheta.SerRing.series_ring_laws q
  have hmul : ∀ (f g : ℂ_[q]⟦X⟧) (A B : ℝ), Bd A f → Bd B g → Bd (A * B) (f * g) :=
    fun f g A B hf hg => R.2.2.2.2.2.2 f g A B hf hg
  have hinv : ∀ f : ℂ_[q]⟦X⟧, Bd 1 f → ‖constantCoeff f‖ = 1 → Bd 1 f⁻¹ :=
    fun f hf h0 => R.2.2.2.2.1 f hf h0
  have hinv' : ∀ (f g : ℂ_[q]⟦X⟧), Bd 1 f → ‖constantCoeff f‖ = 1 → f * g = 1 → Bd 1 g := by
    intro f g hf h0 hfg
    have hc : constantCoeff f ≠ 0 := by
      intro h
      rw [h, norm_zero] at h0
      exact zero_ne_one h0
    have hgf : g = f⁻¹ := by
      rw [PowerSeries.eq_inv_iff_mul_eq_one hc, mul_comm]
      exact hfg
    rw [hgf]
    exact hinv f hf h0
  have hgauss : ∀ (f g : ℂ_[q]⟦X⟧) (B : ℝ), Bdd f → Bdd g → Bd B (f * g) →
      ∀ i j, ‖coeff i f‖ * ‖coeff j g‖ ≤ B :=
    fun f g B hf hg hB => GlobalTheory.EvenTheta.sup_norm_mul_padicComplex q f g B hf hg hB
  refine ⟨fun f g A B hf hg => ⟨fun n => GlobalTheory.EvenTheta.SerRing.norm_coeff_add_le f g A B hf hg n,
    hmul f g A B hf hg⟩, fun f h A hf hh h0 => R.2.2.2.2.2.1 f h A hf hh h0, hinv', hgauss, ?_, ?_⟩
  · intro f g hf hg hfg h1
    have hg0 : constantCoeff g = 1 := by
      have hc := congrArg constantCoeff hfg
      rw [map_mul, h1, one_mul, map_one] at hc
      exact hc
    have hB : Bd 1 (f * g) := by
      rw [hfg]
      intro n
      rw [coeff_one]
      split_ifs <;> simp
    have H := hgauss f g 1 hf hg hB
    refine ⟨fun i => ?_, fun j => ?_⟩
    · have hi := H i 0
      rwa [coeff_zero_eq_constantCoeff_apply, hg0, norm_one, mul_one] at hi
    · have hj := H 0 j
      rwa [coeff_zero_eq_constantCoeff_apply, h1, norm_one, one_mul] at hj
  · intro f v k B hv h0 hB
    have hw : Bd B (v * f) := by
      intro m
      have hm := hB (m + k)
      rwa [mul_assoc, coeff_X_pow_mul] at hm
    have hc : constantCoeff v ≠ 0 := by
      intro h
      rw [h, norm_zero] at h0
      exact zero_ne_one h0
    have hvf := hmul v⁻¹ (v * f) 1 B (hinv v hv h0) hw
    rwa [← mul_assoc, PowerSeries.inv_mul_cancel _ hc, one_mul, one_mul] at hvf

end GlobalTheory.MomOne
end

section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

noncomputable section

namespace GlobalTheory.MomOne.ThetaZero

theorem indep {d : ℕ} (hd : 0 < d) : LinearIndependent ℝ ![(1 : ℂ), wK d] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp [wK] at him hre
  have ht : t = 0 := by
    rcases him with h1 | h1
    · exact h1
    · exact absurd h1 (by positivity)
  subst ht
  simp at hre
  exact ⟨hre, rfl⟩

def pair {d : ℕ} (hd : 0 < d) : PeriodPair := ⟨1, wK d, indep hd⟩

theorem isOK_pair {d : ℕ} (hd : 0 < d) : IsOK d (pair hd) := by
  intro z
  rw [PeriodPair.mem_lattice]
  simp only [pair, mul_one, InOK]
  exact ⟨fun ⟨m, n, h⟩ => ⟨m, n, h.symm⟩, fun ⟨m, n, h⟩ => ⟨m, n, h.symm⟩⟩

theorem G_eq {d : ℕ} {L : PeriodPair} (h : IsOK d L) {k : ℕ} (hk : k ≠ 0) :
    L.G (2 * k) = eis d k := by
  unfold PeriodPair.G eis
  have e1 := tsum_subtype (L.lattice : Set ℂ) (fun w : ℂ => (w ^ (2 * k))⁻¹)
  have e2 := tsum_subtype {w : ℂ | InOK d w ∧ w ≠ 0} (fun w : ℂ => 1 / w ^ (2 * k))
  refine e1.trans (Eq.trans ?_ e2.symm)
  refine tsum_congr fun w => ?_
  by_cases h0 : w = 0
  · subst h0
    simp [Set.indicator, hk]
  · have hw : w ∈ (L.lattice : Set ℂ) ↔ w ∈ {w : ℂ | InOK d w ∧ w ≠ 0} :=
      ⟨fun a => ⟨(h w).1 a, h0⟩, fun a => (h w).2 a.1⟩
    by_cases hm : w ∈ (L.lattice : Set ℂ)
    · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (hw.1 hm), one_div]
    · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (hw.not.1 hm)]

def lam (d : ℕ) : AddSubgroup ℂ := AddSubgroup.closure {1, wK d}

theorem mem_lam (d : ℕ) (z : ℂ) : z ∈ lam d ↔ InOK d z := by
  rw [lam, AddSubgroup.mem_closure_pair]
  simp only [zsmul_eq_mul, mul_one, InOK]
  exact ⟨fun ⟨m, n, h⟩ => ⟨m, n, h.symm⟩, fun ⟨m, n, h⟩ => ⟨m, n, h.symm⟩⟩

theorem area_lam {d : ℕ} (hd : 0 < d) : Formalism.MainNotions.TaylorLogMetric.area (lam d) = Real.sqrt d / 2 := by
  rw [lam, GlobalTheory.TransInv.area_closure_pair (indep hd)]
  simp [wK, abs_div]

theorem thetaTranslationOperator_apply {d : ℕ} (hd : 0 < d) (x : ℂ) (F : ℂ → ℂ) (z : ℂ) :
    Formalism.MainNotions.TaylorLogMetric.U1 (lam d) x F z = U1 d x F z := by
  simp only [Formalism.MainNotions.TaylorLogMetric.U1, U1, h1, area_lam hd]
  congr 2
  push_cast
  ring

theorem thetaTranslation_comp_eq_cocycle_mul (d : ℕ) (a b : ℂ) (F : ℂ → ℂ) (z : ℂ) :
    U1 d a (U1 d b F) z =
      Complex.exp ((Real.pi : ℂ) / 2 * (h1 d b a - h1 d a b)) * U1 d (a + b) F z := by
  simp only [U1]
  rw [mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add, add_assoc z a b]
  congr 2
  simp only [h1, map_add (f := _)]
  ring

theorem half_not_mem {d : ℕ} (hd : 0 < d) (u v : ℤ) (h : ¬ (Odd u ∧ Even v)) :
    ((u : ℂ) + (v : ℂ) * wK d) / 2 + 1 / 2 ∉ lam d := by
  rw [mem_lam]
  rintro ⟨m, n, e⟩
  have := (LinearIndependent.pair_iff.1 (indep hd)) ((u + 1 - 2 * m : ℤ) : ℝ) ((v - 2 * n : ℤ) : ℝ) (by
    simp only [Complex.real_smul]
    push_cast
    linear_combination 2 * e)
  have h1 : u + 1 - 2 * m = 0 := by exact_mod_cast this.1
  have h2 : v - 2 * n = 0 := by exact_mod_cast this.2
  exact h ⟨⟨m - 1, by omega⟩, ⟨n, by omega⟩⟩

theorem normSq_eq {d : ℕ} (c : ℤ) (hc : (d : ℤ) + 1 = 8 * c) (u v : ℤ) :
    Complex.normSq ((u : ℂ) + (v : ℂ) * wK d) = ((u ^ 2 + u * v + 2 * c * v ^ 2 : ℤ) : ℝ) := by
  have hs : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt (Nat.cast_nonneg d)
  have hc' : (d : ℝ) + 1 = 8 * c := by exact_mod_cast hc
  simp [Complex.normSq_apply, wK]
  linear_combination (v : ℝ) ^ 2 / 4 * hs + (v : ℝ) ^ 2 / 4 * hc'

theorem exp_even {n : ℤ} (h : Even n) : Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ)) = 1 := by
  obtain ⟨k, rfl⟩ := h
  rw [← Complex.exp_int_mul_two_pi_mul_I k]
  congr 1
  push_cast
  ring

theorem comm_eq {d : ℕ} (hd : 0 < d) (u v : ℤ) :
    h1 d (wK d) ((u : ℂ) + (v : ℂ) * wK d) - h1 d ((u : ℂ) + (v : ℂ) * wK d) (wK d) =
      2 * u * Complex.I := by
  have hs : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.mpr (by exact_mod_cast hd)).ne'
  simp only [h1, wK, map_add (f := _), map_mul, map_div₀, map_intCast, map_one, Complex.conj_I,
    Complex.conj_ofReal, map_ofNat]
  push_cast
  field_simp
  ring

theorem exists_isTh {d : ℕ} (hd8 : d % 8 = 7) : ∃ θ : ℂ → ℂ, IsTh d θ := by
  have hd : 0 < d := by omega
  obtain ⟨c, hc⟩ : ∃ c : ℤ, (d : ℤ) + 1 = 8 * c := ⟨((d : ℤ) + 1) / 8, by omega⟩
  have hlat : GlobalTheory.EvenTheta.IsLat (lam d) := ⟨1, wK d, indep hd, rfl⟩
  have ht : (1 / 2 : ℂ) ∉ lam d := by
    simpa using half_not_mem hd 0 0 (by simp)
  have ht2 : 2 * (1 / 2 : ℂ) ∈ lam d := (mem_lam d _).2 ⟨1, 0, by simp⟩
  obtain ⟨b1, b2, b3, -, b5, b6⟩ := GlobalTheory.EvenTheta.evenThetaTwoTorsion_basic_properties (lam d) hlat (1 / 2) ht ht2
  generalize Formalism.MainNotions.GL3Theta.th0 (lam d) (1 / 2) = θ at b1 b2 b3 b5 b6
  have fix : ∀ u v : ℤ, ¬ (Odd u ∧ Even v) → U1 d ((u : ℂ) + (v : ℂ) * wK d) θ = θ := by
    intro u v h
    funext z
    rw [← thetaTranslationOperator_apply hd]
    exact b6 _ ((mem_lam d _).2 ⟨u, v, rfl⟩) (half_not_mem hd u v h) z
  refine ⟨θ, b1, b2, b3, ?_, fun z hz => ?_⟩
  · rintro x ⟨u, v, rfl⟩
    funext z
    simp only [W1]
    rw [normSq_eq c hc, Complex.ofReal_intCast]
    by_cases h : Odd u ∧ Even v
    · have f1 := fix u (v - 1) (by
        rintro ⟨-, h2⟩
        rcases h2 with ⟨a, ha⟩
        rcases h.2 with ⟨b, hb⟩
        omega)
      have f2 : U1 d (wK d) θ = θ := by simpa using fix 0 1 (by simp)
      have k := thetaTranslation_comp_eq_cocycle_mul d ((u : ℂ) + ((v - 1 : ℤ) : ℂ) * wK d) (wK d) θ z
      rw [f2, f1, comm_eq hd,
        show (u : ℂ) + ((v - 1 : ℤ) : ℂ) * wK d + wK d = (u : ℂ) + (v : ℂ) * wK d by
          push_cast; ring] at k
      have hev : Even (u ^ 2 + u * v + 2 * c * v ^ 2 - u) := by
        obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := h
        exact ⟨(2 * a + 1) * a + (2 * a + 1) * b + c * (b + b) ^ 2, by ring⟩
      have e := exp_even hev
      rw [k]
      congr 1
      rw [← one_mul (Complex.exp ((Real.pi : ℂ) / 2 * _)), ← e, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    · have hev : Even (u ^ 2 + u * v + 2 * c * v ^ 2) := by
        rcases Int.even_or_odd u with ⟨a, rfl⟩ | ⟨a, rfl⟩
        · exact ⟨2 * a ^ 2 + a * v + c * v ^ 2, by ring⟩
        · rcases Int.even_or_odd v with hv | ⟨b, rfl⟩
          · exact absurd ⟨⟨a, rfl⟩, hv⟩ h
          · exact ⟨(2 * a + 1) * (a + b + 1) + c * (2 * b + 1) ^ 2, by ring⟩
      rw [exp_even hev, one_mul, fix u v h]
  · obtain ⟨m, n, e⟩ := (mem_lam d _).1 ((b5 z).1 hz)
    exact ⟨m - 1, n, by push_cast; linear_combination e⟩

end GlobalTheory.MomOne.ThetaZero

namespace GlobalTheory.MomOne

theorem exists_pair_and_isTh : ∀ d : ℕ, d.Prime → d % 16 = 7 → (∃ L : PeriodPair, IsOK d L ∧ L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = discr d) ∧ ∃ θ : ℂ → ℂ, IsTh d θ := by
  intro d hp h
  refine ⟨⟨ThetaZero.pair hp.pos, ThetaZero.isOK_pair hp.pos, ?_⟩, ThetaZero.exists_isTh (by omega)⟩
  have h2 := ThetaZero.G_eq (ThetaZero.isOK_pair hp.pos) (k := 2) (by norm_num)
  have h3 := ThetaZero.G_eq (ThetaZero.isOK_pair hp.pos) (k := 3) (by norm_num)
  unfold discr PeriodPair.g₂ PeriodPair.g₃
  rw [← h2, ← h3]

end GlobalTheory.MomOne
end
end
