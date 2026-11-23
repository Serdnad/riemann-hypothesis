module

public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle101
public import Formalism.FormalDegreeBessel.StatementG
public import Formalism.PeriodIntegrals.Bundle013
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle099
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
public import Formalism.LocalToGlobal.CharacterGerms.Bundle023
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle102
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle003
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Formalism.LocalToGlobal.Divisibility.Numbers

@[expose] public section

section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

theorem _root_.GlobalTheory.T.cpTransportedTaylorSeries_translate_norm_le : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ℓ : ℂ_[q]⟦X⟧) (φ : ℂ → ℂ) (t : ℂ) (B : ℝ), M.Chart ℓ → Ell M.L φ → AnalyticAt ℂ φ 0 → AnalyticAt ℂ φ t → (∀ p, meromorphicOrderAt φ p < 0 → ¬ M.Small p) → ¬ M.Small t → Bdd (hat M.ι ℓ (fun z => φ (z + t))) → Bd B (hat M.ι ℓ φ) → Bd B (hat M.ι ℓ (fun z => φ (z + t))) := by
  first | exact @GlobalTheory.MomOne.TransNorm.translate_norm_le | exact GlobalTheory.MomOne.TransNorm.translate_norm_le | (intros; apply GlobalTheory.MomOne.TransNorm.translate_norm_le <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.bessel_formal_degree_pairing : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (l : R.H → Wp) (l' : R.H → Wq) (dd : ℝ), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH D.μG R.σ w = dd) → ∀ x ∈ R.TK, ∀ y ∈ R.TK, ∀ x' ∈ R.TK, ∀ y' ∈ R.TK, ∀ X X' : Wq →L[ℂ] Wp, Integrable (B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X')) D.μSS ∧ ∫ p, B.xiTau D (1, 1) p * B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X') p ∂D.μSS = ⟪l x, X (l' y)⟫_ℂ * star ⟪l x', X' (l' y')⟫_ℂ / (dd : ℂ) := by
  first | exact @GlobalTheory.integral_xi_mul_Ph | exact GlobalTheory.integral_xi_mul_Ph | (intros; apply GlobalTheory.integral_xi_mul_Ph <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.bessel_tensor_projection_scalar_and_adjoint : Hyps → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (om : ι → ℂ) (l : R.H → Wp), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → SideG k r z π u μW μN μG νq → (∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ρ s *ᵥ om = om) → IsBeL R z π μW μN l → NzOn R l → ∀ I lI, IsBeL (RI I) z π μW μN lI → (∃ κ₀ : ℂ, ∀ v ∈ R.sm, lI (∑ c, pr I c (tm R om v c)) = κ₀ • l v) ∧ ∀ κ₀ : ℂ, (∀ v ∈ R.sm, lI (∑ c, pr I c (tm R om v c)) = κ₀ • l v) → ∀ y ∈ (RI I).sm, l (ev Γ R om (fun c => io I c y)) = ((ep I : ℂ) * star κ₀) • lI y := by
  first | exact @GlobalTheory.KappaDual.kappa_dual | exact GlobalTheory.KappaDual.kappa_dual | (intros; apply GlobalTheory.KappaDual.kappa_dual <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.exists_frame_conj_unitaryBlock_eq_unitaryComplement : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → ∃ g, PI.UpqRep.IsFrameW k r z g ∧ (∀ x ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), g * PI.UpqRep.blockW k r x * g⁻¹ ∈ Formalism.QuantumDeterminants.UWset k r z) ∧ ∀ y ∈ Formalism.QuantumDeterminants.UWset k r z, ∃ x ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), y = g * PI.UpqRep.blockW k r x * g⁻¹ := by
  first | exact @GlobalTheory.BesselFrame.frame_exists | exact GlobalTheory.BesselFrame.frame_exists | (intros; apply GlobalTheory.BesselFrame.frame_exists <;> assumption)
end

section

namespace GlobalTheory

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

theorem capelliFold_good {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : ℂ) :
    ∀ w : List (Bool × ℝ), Formalism.FourierDecayAlt.P.Qx2.Good k r 0 Set.univ
      (fun f : B.Mat k r → E => List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) f w)
  | [] => Formalism.FourierDecayAlt.P.Qx2.good_id
  | a :: w => (Formalism.FourierDecayAlt.P.Dx1.LZ.good_Tc (k := k) (r := r) (E := E) s (a.2 : ℂ)).comp (capelliFold_good s w)

theorem capelliFold_add_smul :
    ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (s : ℂ) (w : List (Bool × ℝ))
      (a : ℂ) (X Z : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ⊤ (B.GV k r) X → B.CkOn ⊤ (B.GV k r) Z →
      ∀ g ∈ B.GV k r,
        (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X + a • Z) w) g =
          (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X) w) g +
            a • (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (Z) w) g := by
  intro k r Wp Wq _ _ _ _ _ _ s w a X Z hX hZ g hg
  exact (capelliFold_good s w).lin X Z a (Formalism.FourierDecayAlt.P.Dx1.LZ.smooth_of_ck hX)
    (Formalism.FourierDecayAlt.P.Dx1.LZ.smooth_of_ck hZ) g (Formalism.FourierDecayAlt.P.Dx1.LZ.glev0 hg)

end GlobalTheory
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

section
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem smoothLev_finsum_smul {ι : Type} (t : Finset ι) (c : ι → ℂ) (f : ι → B.Mat k r → E)
    (hf : ∀ i, Q.SmoothLev k r 0 Set.univ (f i)) :
    Q.SmoothLev k r 0 Set.univ (fun y => ∑ i ∈ t, c i • f i y) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using Formalism.FourierDecayAlt.P.Qx2.smooth_zero
  | insert a t ha ih =>
    intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hf', he⟩ := ih g₀ hg₀
    obtain ⟨V, h', hV, hgV, hh', he'⟩ := hf a g₀ hg₀
    refine ⟨U ∩ V, fun y => c a • h' y + f' y, hU.inter hV, ⟨hgU, hgV⟩,
      ((hh'.mono Set.inter_subset_right).const_smul (c a)).add (hf'.mono Set.inter_subset_left), ?_⟩
    intro g hg hgG
    beta_reduce
    rw [Finset.sum_insert ha, he' g hg.2 hgG, ← he g hg.1 hgG]

theorem capelli_finsum_smul {ι : Type} (t : Finset ι) (c : ι → ℂ) (f : ι → B.Mat k r → E)
    (hf : ∀ i, Q.SmoothLev k r 0 Set.univ (f i)) (Y : ℂ) {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    Q.CV k r Y (fun y => ∑ i ∈ t, c i • f i y) g = ∑ i ∈ t, c i • Q.CV k r Y (f i) g := by
  classical
  have hT := Formalism.FourierDecayAlt.P.Dx1.LZ.good_CV (k := k) (r := r) (E := E) Y
  have hg' := Formalism.FourierDecayAlt.P.Dx1.LZ.glev0 hg
  induction t using Finset.induction_on with
  | empty => simpa using hT.map_zero hg'
  | insert a t ha ih =>
    have h := hT.lin _ (f a) (c a) (smoothLev_finsum_smul t c f hf) (hf a) g hg'
    simp only [Finset.sum_insert ha]
    rw [← ih, add_comm, ← h]
    congr 1
    funext y
    rw [add_comm]

end

theorem foldr_capelli_sum_eigen : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq →L[ℂ] Wp)) (ev : Fin N₀ → ℝ → ℂ) (s : ℂ) (F : B.Mat k r → (Wq →L[ℂ] Wp)), (∀ i, B.CkOn ⊤ (B.GV k r) (Fi i)) → (∀ i (Y : ℝ), ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g = ev i Y • Fi i g) → (∀ g ∈ B.GV k r, F g = ∑ i, Fi i g) → ∀ w : List (Bool × ℝ), ∀ g ∈ B.GV k r, (w.foldr (fun a H => s • Q.CV k r (a.2 : ℂ) H) F) g = ∑ i, (w.map fun a => s * ev i a.2).prod • Fi i g := by
  intro k r Wp Wq _ _ _ _ _ _ N₀ Fi ev s F hs hev hF w
  induction w with
  | nil => intro g hg; simpa using hF g hg
  | cons a w ih =>
    intro g hg
    have hT := Formalism.FourierDecayAlt.P.Dx1.LZ.good_CV (k := k) (r := r) (E := Wq →L[ℂ] Wp) (a.2 : ℂ)
    have h1 := hT.loc _ _ (fun y hy => ih y hy.1.1) g (Formalism.FourierDecayAlt.P.Dx1.LZ.glev0 hg)
    have h2 := capelli_finsum_smul Finset.univ (fun i => (w.map fun a => s * ev i a.2).prod) Fi
      (fun i => Formalism.FourierDecayAlt.P.Dx1.LZ.smooth_of_ck (hs i)) (a.2 : ℂ) hg
    simp only [List.foldr_cons, List.map_cons, List.prod_cons, Pi.smul_apply]
    rw [h1.trans h2, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hev i a.2 g hg, smul_smul, smul_smul]
    congr 1
    ring

end GlobalTheory
end

section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.exists_closedComplete_field_over_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)] (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∃ (C : Type) (_ : Field C) (_ : CharZero C) (V : VF C) (ι : T.Fr →+* C), V.l = resCharOf la ∧ EmbOK T V ι ∧ IsAlgClosed C ∧ (∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) ∧ (∀ x ∈ la.asIdeal, V.MM (ι (io ((x : 𝓞 c.F) : c.F)))) ∧ (∀ m : ℕ, ¬ resCharOf la ∣ m → V.v (m : C) = 0) ∧ ∀ (y : IntFr Xo c T io) (C3 : IntChart T io y) (k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (ν : ℝ), (((ramOverZ la : ℝ) * ν : ℝ) : EReal) ≤ nuLocC C3 e k a n → (ν : EReal) ≤ nuLocC C3 (eOf T V) k a n := by
  first | exact @GlobalTheory.PlaceClosedField.exists_closed_field_over_place | exact GlobalTheory.PlaceClosedField.exists_closed_field_over_place | (intros; apply GlobalTheory.PlaceClosedField.exists_closed_field_over_place <;> assumption)
end
