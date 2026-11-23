module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle033
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.Bundle001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroPairingCutoffLocality
public import Formalism.HermitianCurvature.StatementD
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle154
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle160
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle091
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle153
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartFormalBiext
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle069
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle017
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK

@[expose] public section

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.pointwiseBounded_of_mem_boundedFactors_monoid : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ b ∈ bmon d, PtB P Bs b := by
  first | exact @GlobalTheory.HatNF.BoundedFactors.ptB_of_mem_bmon | exact GlobalTheory.HatNF.BoundedFactors.ptB_of_mem_bmon | (intros; apply GlobalTheory.HatNF.BoundedFactors.ptB_of_mem_bmon <;> assumption)
end

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowGerm

theorem isAdicComplete_ov_of_range {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) (O : Type) [CommRing O]
    [Algebra O F] (hinj : Function.Injective (algebraMap O F))
    (hr : ∀ z : F, 0 ≤ v z ↔ z ∈ (algebraMap O F).range) (g : ℕ)
    (hc : IsAdicComplete (Ideal.span {((g : ℕ) : O)}) O) :
    IsAdicComplete (Ideal.span {((g : ℕ) : TWO.Ov v)}) (TWO.Ov v) := by
  let φ : O →+* TWO.Ov v := (algebraMap O F).codRestrict (TWO.Ov v) fun a => (hr _).2 ⟨a, rfl⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun a b h => hinj (congrArg Subtype.val h), fun z => ?_⟩
    obtain ⟨a, ha⟩ := (hr z).1 z.2
    exact ⟨a, Subtype.ext ha⟩
  have h := (IsAdicComplete.congr_ringEquiv (Ideal.span {((g : ℕ) : O)}) (RingEquiv.ofBijective φ hφ)).2 hc
  rwa [Ideal.map_span, Set.image_singleton, map_natCast] at h

theorem isUnit_iff_not_isUnit_of_coprime {R : Type} [CommRing R] [IsLocalRing R] {x y u u' : R}
    (h : ¬ IsUnit (x * y)) (h1 : u * x + u' * y = 1) : IsUnit x ↔ ¬ IsUnit y := by
  refine ⟨fun hx hy => h (hx.mul hy), fun hy => ?_⟩
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one h1 with h2 | h2
  · exact isUnit_of_mul_isUnit_right h2
  · exact absurd (isUnit_of_mul_isUnit_right h2) hy

theorem card_filter_val_lt (n₁ n₂ : ℕ) :
    (Finset.univ.filter fun b : Fin (n₁ + n₂) => b.val < n₁).card = n₁ := by
  rw [Fin.card_filter_val_lt]; omega

theorem lemmaBT_of_characters : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → (∀ (p : ℕ) [Fact p.Prime], ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : FamGerm.Pt1 E H V F), letI := H.starRing; IsAdicComplete (Ideal.span {(p : TWO.Ov y.v)}) (TWO.Ov y.v) → ¬ IsUnit (p : TWO.Ov y.v) → ∀ a : 𝓞 E, a * star a = (p : 𝓞 E) → (∃ u u' : 𝓞 E, u * a + u' * star a = 1) → ∀ (T : Type) [Fintype T] [DecidableEq T] (rk : T → ℕ) (τ : T → 𝓞 E →+* TWO.Ov y.v) (e : (Σ t, Fin (rk t)) → Fin y.d → TWO.Ov y.v), (∀ (c : 𝓞 E) l, (dAct F y.B c).mulVec (fun i => (e l i : F)) = (τ l.1 c : F) • fun i => (e l i : F)) → (∀ t, τ t a ∈ Ideal.span {(p : TWO.Ov y.v)}) → (∀ t, ∃ lam : Fin (rk t) → Fin y.d → TWO.Ov y.v, ∀ i i', ∑ s, lam i s * e ⟨t, i'⟩ s = if i = i' then 1 else 0) → (∃ ε : T → 𝓞 E, ∀ t t', τ t' (ε t) - (if t = t' then 1 else 0) ∈ Ideal.span {(p : TWO.Ov y.v)}) → ∀ c : TWO.Ov y.v, (p - 1) • y.v (c : F) = y.v (p : F) → ∀ (n : ℕ) (col : ∀ t, Fin (rk t) → Fin n), (∀ t, Function.Injective (col t)) → ∃ yy : (Σ t, Fin (rk t)) × Fin n → TWO.Ov y.v, (∀ b, y.CharAt a p e (fun l => yy (l, b))) ∧ ∀ t (s : Fin (rk t)), y.v (((Matrix.of fun a i : Fin (s.val + 1) => yy (⟨t, Fin.castLE s.isLt a⟩, col t (Fin.castLE s.isLt i))).det : TWO.Ov y.v) : F) ≤ (s.val + 1) • y.v (c : F)) → LemmaBT := by
  intro L1 L2 L4 TB hch E _ _ _ H Dw l Xo c inst hst
  obtain rfl := starSt E H inst hst
  letI := H.starRing
  intro T io y hy C hfr P tors ϖ hϖ Q hQ g g' hg hg' hne og og' π π' hπ hπ' hcop hcop' hcard hnd hnu F _ _ _ _ _ _ v hv
    O _ _ _ _ hinj hO hOc I Φ M0 r b hΦ hb1 hb2 n₁ n₂ hn D' A' G' _ _ pD pA pG U' PU _ oD' hx1 hx2 m hm hd1 hd2 hd3 ρg hρg
  letI := io.toAlgebra
  classical
  haveI : Fact g.Prime := ⟨hg⟩
  obtain ⟨σ, e, hσ, he1, -, heig, hval, hconj, ⟨lam, hlam⟩, hε, hgu⟩ :=
    GlobalTheory.T.exists_integral_types_and_directions' E H Dw l Xo c T io y C ϖ hϖ g hg hnu hcard hnd F v hv
  obtain ⟨x, hx, j, hj, u, hu, B, hB, ρ, hρ, -, hact, htr⟩ :=
    GlobalTheory.T.integralChart_columns_to_tuple_harmonicValues L1 L2 L4 TB E H Dw l Xo c T io y C hfr P tors ϖ hϖ Q hQ F v hv
  obtain ⟨BT, -, hBT, -, -, -, -, hBF⟩ := integralChart_formalBiext E H Dw l Xo c T io y C
  have hdA : ∀ a, dAct F B a = dAct F C.ch.B a := by
    intro a
    have h1 : B.actK F a = C.ch.B.actK F a := by
      rw [← (hBF F).2.1 a]
      unfold FB.actK
      rw [hact, hBT]
    unfold dAct
    rw [h1]
  obtain ⟨rk, hrk, col, m', hcol, hty, hdeg, hmin⟩ :=
    minorSt E H Dw F (fun τ => 0 < v (algebraMap T.Fr F (io (embK c τ (star π))))) m n₁ n₂ (by convert hm)
  obtain ⟨h₀, hh₀⟩ := canonGauge_exists T.V (chD C.ch) (𝓞 E) F B
  have hππ : star π * star (star π) = (g : 𝓞 E) := by rw [star_star, mul_comm, hπ]
  obtain ⟨u₁, u₂, hu12⟩ := hcop
  have hg'0 : (0 : ℝ) < g' := by exact_mod_cast hg'.pos
  have hred : (FamGerm.Pt1.mk ϖ hϖ T.cpl C.I.G P tors Q hQ v hv (chD C.ch) x hx j hj u hu B hB ρ hρ :
      FamGerm.Pt1 E H T.V F).Red r b Φ (max M0 0) := by
    refine ⟨hΦ, le_max_right _ _, hb1, fun i z => ?_⟩
    have h1 := hb2 i z
    have h2 : (0 : ℝ) ≤ Q z := by
      by_cases hz : z = 0
      · rw [hz, Q_zero hϖ P.D hQ, Int.cast_zero]
      · have h3 := Q_pos hϖ P.D hQ hz
        exact_mod_cast (by omega : 0 ≤ Q z)
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) h2)
  obtain ⟨s, s', t, f, gm, hs, hgm, hle⟩ := GlobalTheory.T.depth_bound_from_characters_pointDatum L1 L2 L4 TB hch g E H T.V F
    (FamGerm.Pt1.mk ϖ hϖ T.cpl C.I.G P tors Q hQ v hv (chD C.ch) x hx j hj u hu B hB ρ hρ)
    (isAdicComplete_ov_of_range v O hinj hO g hOc) hgu Dw I r b Φ (max M0 0) hred (star π) g' hππ
    ⟨u₂, u₁, by rw [star_star, add_comm, hu12]⟩ ((Nat.coprime_primes hg hg').2 hne) (E →+* ℂ) rk σ
    (fun l => e ⟨l.1, Fin.castLE (hrk l.1) l.2⟩)
    (fun a l => by rw [show dAct F _ a = dAct F C.ch.B a from hdA a]; exact heig a _)
    (fun τ => 0 < v (algebraMap T.Fr F (io (embK c τ (star π)))))
    (fun τ h => (hval τ _).1 (by rw [hσ]; exact h)) (fun τ h => (hval τ _).2 (by rw [hσ]; exact h))
    ⟨fun l => lam ⟨l.1, Fin.castLE (hrk l.1) l.2⟩, fun l l' => by
      refine (hlam _ _).trans (if_congr ?_ rfl rfl)
      obtain ⟨τ, i⟩ := l
      obtain ⟨τ', i'⟩ := l'
      constructor
      · intro h
        obtain rfl : τ = τ' := congrArg Sigma.fst h
        have h2 := eq_of_heq (Sigma.mk.inj h).2
        obtain rfl : i = i' := Fin.castLE_injective _ h2
        rfl
      · intro h
        rw [h]⟩
    (by convert hε) (n₁ + n₂) (Finset.univ.filter fun b => b.val < n₁) col m' hcol
    (fun τ i => by rw [Finset.mem_filter, ← hty τ i]; simp) (degOf Dw m) hdeg.symm hd1 hd2
    (by
      rcases le_total M0 0 with h | h
      · rw [max_eq_right h, mul_zero]; exact hg'0
      · rw [max_eq_left h]; exact hd3)
    h₀ hh₀ ρg hρg
  simp only [star_star] at hs
  obtain ⟨S, S₂, p', w', ζ', x', T₀, T₁, σ', h, un, hbox, -, -, hvl⟩ :=
    htr g g' π hg.one_le hg'.one_le hπ (n₁ + n₂) D' A' G' pD pA pG U' PU oD' hx1 hx2 s s' t f hs
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := hbox
  refine ⟨S, S₂, p', w', ζ', x', T₀, T₁, σ', h, gm, b1, b2, b3, b4, b5, b6, b7, b8, b9, ?_, ?_⟩
  · rw [hmin, hvl h₀ hh₀ rk hrk (FamGerm.minorsP F col m') ?_, ← hgm]
    · simp only [he1]
    · intro τ
      refine minors_disjoint_columns_harmonic F _ rk _ col m' _ rfl τ _ fun i i' hii => ?_
      have k1 := hty τ i
      have k2 := hty _ i'
      rw [hii, k2, ← hσ, ← hσ, hconj, star_star] at k1
      have k3 : ∀ a, 0 < v (σ τ a : F) ↔ ¬ IsUnit (σ τ a) := fun a =>
        ⟨fun h hu => hgu (isUnit_of_dvd_unit (Ideal.mem_span_singleton.1 ((hval τ a).1 h)) hu),
          fun h => by_contra fun h' => h ((hval τ a).2 h')⟩
      rw [k3, k3] at k1
      have k4 : IsUnit (σ τ π) ↔ ¬ IsUnit (σ τ (star π)) :=
        isUnit_iff_not_isUnit_of_coprime (u := σ τ u₁) (u' := σ τ u₂) (by rw [← map_mul, hπ, map_natCast]; exact hgu)
          (by rw [← map_mul, ← map_mul, ← map_add (f := _), hu12, map_one])
      tauto
  · rw [card_filter_val_lt] at hle
    have h1 : (0 : ℝ) ≤ (degOf Dw m : ℝ) ^ 2 * Φ / g' := by positivity
    have h2 : 2 * (degOf Dw m : ℝ) ^ 2 * Φ / g' = 2 * ((degOf Dw m : ℝ) ^ 2 * Φ / g') := by ring
    rw [h2, mul_comm (ρg : ℝ)]
    linarith

end GlobalTheory.PowGerm
end

section

open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.QuantumDeterminants GlobalTheory.ThA

theorem _root_.GlobalTheory.T.exists_place_of_localBesselDatum_interlacing : ∀ (k r : ℕ) (L : LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (lam0 : Fin (2 * r + k + 1) → ℝ) (hk : k ≤ 2 * r + k + 1), 2 ≤ k → IsSection k r L.z L.z' μsec → InterlaceS hk L.u lam0 → InterlaceS hk L.u' lam0 → ∃ (U U' : ℕ → ℝ) (p : KB.Pl ⟨k, r, Tz k r L.z, Tz k r L.z', U, U'⟩ L.Wp L.Wq), (∀ i : Fin k, U (i.val + 1) = L.u i ∧ U' (i.val + 1) = L.u' i) ∧ IsStdOf L μsec p.T.base := by
  first | exact @GlobalTheory.exists_place_of_locBessel | exact GlobalTheory.exists_place_of_locBessel | (intros; apply GlobalTheory.exists_place_of_locBessel <;> assumption)
end

section


theorem _root_.GlobalTheory.T.wignerMapsThreePlaces_exists : GlobalTheory.WigSh.AmapsShExists := by
  first | exact @GlobalTheory.WigSh.amapsShExists | exact GlobalTheory.WigSh.amapsShExists | (intros; apply GlobalTheory.WigSh.amapsShExists <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

theorem _root_.GlobalTheory.T.levelZeroPairing_cutoff_locality : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (s : ℂ) (w : List (Bool × ℝ)) (χ : ℝ → ℝ) (δ ε ε₁ : ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), C6.IsCut0 χ → (∀ x, x < δ → χ x = 0) → 0 < ε → 0 < ε₁ → ε₁ < δ * ε → B.CkOn ⊤ (B.GV P.k P.r) F → B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV P.k P.r (a.2 : ℂ) G) ((D.cutF p.T.base χ F ε₁)) w) (D.cutF p.T.base χ F ε) = B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV P.k P.r (a.2 : ℂ) G) (F) w) (D.cutF p.T.base χ F ε) := by
  first | exact @GlobalTheory.beta_fold_cut_eq_beta_fold_of_cut | exact GlobalTheory.beta_fold_cut_eq_beta_fold_of_cut | (intros; apply GlobalTheory.beta_fold_cut_eq_beta_fold_of_cut <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory.LevelZeroApprox

theorem ccle_sub {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {m : ℕ}
    {F F' : B.Mat k r → E} {c c' : ℝ} (h : B.CCle A m F c) (h' : B.CCle A m F' c') :
    B.CCle A m (F - F') (c + c') := by
  have h1 := Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add h (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul (-1 : ℂ) h')
  have e : (fun g => F g + (fun g => (-1 : ℂ) • F' g) g) = F - F' := by
    funext g; simp [sub_eq_add_neg]
  rw [e] at h1
  simpa using h1

theorem ckOn_sub {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞} {U : Set (B.Mat k r)}
    {F F' : B.Mat k r → E} (h : B.CkOn m U F) (h' : B.CkOn m U F') : B.CkOn m U (F - F') := by
  have h1 := Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add h (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_smul (-1 : ℂ) h')
  have e : (fun g => F g + (fun g => (-1 : ℂ) • F' g) g) = F - F' := by
    funext g; simp [sub_eq_add_neg]
  rwa [e] at h1

section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem ckOn_bump_smul {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {H : B.Mat k r → E} (h : B.CkOn ⊤ (B.GV k r) H) (n : ℕ) :
    B.CkOn ⊤ (B.GV k r) (fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • H g) := by
  have hcs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) := by
    have e : (fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) = fun g => 1 - Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g := by
      funext g
      rw [Formalism.FourierDecayAlt.P.JCx2.pdPsi, sub_sub_cancel]
      rfl
    rw [e]
    exact contDiff_const.sub (Formalism.FourierDecayAlt.P.JCx2.pd_psi_cd _)
  exact Formalism.FourierDecayAlt.P.JCx2.pd_smooth_smul hcs h
end

theorem threshold (k r N l : ℕ) (hl : l ≤ N) :
    B.AB k r + 1 + 2 * ((r : ℝ) + 1) * ((5 + l * (2 * r + k + 1) : ℕ) : ℝ) ≤
      20 * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) := by
  unfold B.AB
  push_cast
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have hlN : (l : ℝ) ≤ N := by exact_mod_cast hl
  set ρ : ℝ := (r : ℝ) + 1 with hρ
  set ν : ℝ := 2 * (r : ℝ) + k + 1 with hν
  have hρ1 : 1 ≤ ρ := by linarith
  have hν1 : 1 ≤ ν := by linarith
  have hkr : (k : ℝ) + r ≤ ν := by linarith
  have h4 : ρ ≤ ρ ^ 4 := le_self_pow₀ hρ1 (by norm_num)
  have h2 : ν ≤ ν ^ 2 := le_self_pow₀ hν1 (by norm_num)
  have h3 : ν ≤ ν ^ 3 := le_self_pow₀ hν1 (by norm_num)
  have hS : (l : ℝ) * ν + ν ≤ N * ν ^ 2 + ν ^ 3 :=
    add_le_add (mul_le_mul hlN h2 (by linarith) (by linarith)) h3
  have hlν : 0 ≤ (l : ℝ) * ν := by positivity
  have h5 : 20 * ρ * ((l : ℝ) * ν + ν) ≤ 20 * ρ ^ 4 * (N * ν ^ 2 + ν ^ 3) :=
    mul_le_mul (by linarith) hS (by linarith) (by positivity)
  refine le_trans ?_ h5
  have a1 : ((k : ℝ) + r) * ρ ≤ ν * ρ := mul_le_mul_of_nonneg_right hkr (by linarith)
  have a2 : ρ ≤ ν * ρ := le_mul_of_one_le_left (by linarith) hν1
  have a3 : 0 ≤ ρ * ((l : ℝ) * ν) := by positivity
  nlinarith

theorem beta_approx : ∃ Cc : ℝ, ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (s : ℂ) (w : List (Bool × ℝ)) (χ : ℝ → ℝ) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (A : ℝ) (N : ℕ), C6.IsCut0 χ → B.CkOn ⊤ (B.GV k r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A → w.length ≤ N → ∀ ε₁ ε₂ : ℝ, 0 < ε₁ → 0 < ε₂ → Tendsto (fun n : ℕ => B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₁ g)) w) ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₂ g))) atTop (𝓝 (B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) ((D.cutF Bs χ f ε₁)) w) (D.cutF Bs χ f ε₂))) ∧ ∃ K : ℝ, ∀ n m : ℕ, n ≤ m → ‖B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₁ g) - (fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((m : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₁ g)) w) ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₁ g) - (fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((m : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₁ g))‖ ≤ K / ((n : ℝ) + 1) := by
  refine ⟨20, ?_⟩
  intro k r Wp Wq _ _ _ _ _ _ Bs s w χ f A N hχ hf hfA hA hw ε₁ ε₂ h₁ h₂
  have hth := (threshold k r N w.length hw).trans hA
  obtain ⟨K₁, hK₁, hH₁, hX₁⟩ := GlobalTheory.T.cutoff_compact_approximants_converge_decay_class k r Wp Wq Bs χ f A ε₁ (B.AB k r) _ hχ h₁ hf hfA hth
  obtain ⟨K₂, hK₂, hH₂, hX₂⟩ := GlobalTheory.T.cutoff_compact_approximants_converge_decay_class k r Wp Wq Bs χ f A ε₂ (B.AB k r) _ hχ h₂ hf hfA hth
  obtain ⟨C, hC, hbd⟩ := GlobalTheory.T.capelliProduct_levelZeroPairing_norm_le k r Wp Wq Bs s w (B.AB k r) le_rfl
  have hsq := GlobalTheory.T.capelliProduct_levelZeroPairing_sesquilinear k r Wp Wq Bs s w (B.AB k r) le_rfl 1
  have hc₁ := Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF Bs hχ hf ε₁
  have hx₁ := ckOn_bump_smul hc₁
  have lo : ∀ {F : B.Mat k r → (Wq →L[ℂ] Wp)} {c : ℝ},
      B.CCle (B.AB k r) (5 + w.length * (2 * r + k + 1)) F c → B.CCle (B.AB k r) 5 F c :=
    fun h => Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono le_rfl (Nat.le_add_right _ _) h
  generalize D.cutF Bs χ f ε₁ = H₁ at *
  generalize D.cutF Bs χ f ε₂ = H₂ at *
  set X₁ : ℕ → B.Mat k r → (Wq →L[ℂ] Wp) := fun n g => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • H₁ g with hX₁def
  set X₂ : ℕ → B.Mat k r → (Wq →L[ℂ] Wp) := fun n g => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • H₂ g with hX₂def
  set b : (B.Mat k r → (Wq →L[ℂ] Wp)) → (B.Mat k r → (Wq →L[ℂ] Wp)) → ℂ := fun X Z =>
    B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) X w) Z with hb
  change ∀ n, B.CCle _ _ (X₁ n) K₁ ∧ B.CCle _ _ (X₁ n - H₁) _ at hX₁
  change ∀ n, B.CCle _ _ (X₂ n) K₂ ∧ B.CCle _ _ (X₂ n - H₂) _ at hX₂
  change ∀ n, B.CkOn _ _ (X₁ n) at hx₁
  change ∀ X Z c c', _ → _ → _ → ‖b X Z‖ ≤ _ at hbd
  change ∀ X X' Z Z', _ → _ → _ → _ → _ → _ → b (X + (1 : ℂ) • X') Z = b X Z + 1 * b X' Z ∧
    b X (Z + (1 : ℂ) • Z') = b X Z + (starRingEnd ℂ) 1 * b X Z' at hsq
  change Tendsto (fun n => b (X₁ n) (X₂ n)) atTop (𝓝 (b H₁ H₂)) ∧
    ∃ K : ℝ, ∀ n m : ℕ, n ≤ m → ‖b (X₁ n - X₁ m) (X₁ n - X₁ m)‖ ≤ K / ((n : ℝ) + 1)
  clear_value X₁ X₂ b
  constructor
  · have key : ∀ n : ℕ, ‖b (X₁ n) (X₂ n) - b H₁ H₂‖ ≤ 2 * C * K₁ * K₂ * (1 / ((n : ℝ) + 1)) := by
      intro n
      have hd := ckOn_sub (hx₁ n) hc₁
      have e1 := (hsq H₁ (X₁ n - H₁) (X₂ n) (X₂ n) hc₁ hd ⟨_, hH₁⟩ ⟨_, (hX₁ n).2⟩ ⟨_, lo (hX₂ n).1⟩
        ⟨_, lo (hX₂ n).1⟩).1
      have e2 := (hsq H₁ H₁ H₂ (X₂ n - H₂) hc₁ hc₁ ⟨_, hH₁⟩ ⟨_, hH₁⟩ ⟨_, lo hH₂⟩ ⟨_, lo (hX₂ n).2⟩).2
      simp only [one_smul, add_sub_cancel, one_mul, map_one] at e1 e2
      have b1 := hbd _ _ _ _ hd (hX₁ n).2 (lo (hX₂ n).1)
      have b2 := hbd _ _ _ _ hc₁ hH₁ (lo (hX₂ n).2)
      have e : b (X₁ n) (X₂ n) - b H₁ H₂ = b (X₁ n - H₁) (X₂ n) + b H₁ (X₂ n - H₂) := by
        rw [e1, e2]; ring
      rw [e]
      refine (norm_add_le _ _).trans ((add_le_add b1 b2).trans (le_of_eq ?_))
      ring
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) key ?_
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * C * K₁ * K₂)
  · refine ⟨4 * C * K₁ * K₁, fun n m hnm => ?_⟩
    have hd := ckOn_sub (hx₁ n) (hx₁ m)
    have c1 := ccle_sub (hX₁ n).2 (hX₁ m).2
    rw [sub_sub_sub_cancel_right] at c1
    have hle : K₁ / ((m : ℝ) + 1) ≤ K₁ / ((n : ℝ) + 1) := by
      have : (n : ℝ) ≤ m := by exact_mod_cast hnm
      exact div_le_div_of_nonneg_left hK₁ (by positivity) (by linarith)
    have c2 := Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c c1 (add_le_add_right hle (K₁ / ((n : ℝ) + 1)))
    have c3 := ccle_sub (hX₁ n).1 (hX₁ m).1
    refine (hbd _ _ _ _ hd c2 (lo c3)).trans (le_of_eq ?_)
    ring

end GlobalTheory.LevelZeroApprox
end
