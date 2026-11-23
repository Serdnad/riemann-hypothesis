module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2200
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCosetsAndFixedPoints
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchoredWeightIndefiniteLiftGaps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle976
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle252
public import Formalism.LocalToGlobal.Divisibility.RecBridgeNum
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1840
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle043
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVacuumMultiplierConstantPerLattice
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle209
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle086
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1517
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2174
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2388
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle509
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1622
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1818
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle297
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle288
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle050
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.boundaryEffective_up_etale_tower_normal_local : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (n r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (x : Fin n → R) (φ : R →₀ ℚ) (θ : T →₀ ℚ),
  IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) → (∀ g ∈ φ.support, g ≠ 0) →
  (∀ g ∈ θ.support, (g : L) ≠ 0 ∧ 0 ≤ θ g) →
  EffAt cK n R (dForm cK (fun i => (x i : K))) (Finsupp.mapDomain (fun g : R => (g : K)) φ) →
  EffAt cL (r + n) T (dForm cL (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L))))
    (Finsupp.mapDomain (fun g : R => (ι g : L)) φ + Finsupp.mapDomain (fun g : T => (g : L)) θ) := by
  first | exact @GlobalTheory.FieldPair.effAt_etTower | exact GlobalTheory.FieldPair.effAt_etTower | (intros; apply GlobalTheory.FieldPair.effAt_etTower <;> assumption)
end

section

noncomputable section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

namespace GlobalTheory.HoweD.FockData

theorem incM_map_piInf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n m : Type}
    (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) : (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, inclR, compInf, infEmb_tmul]

theorem det_map_ne_zero {E : Type} [Field E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (τ : E →+* ℂ) (h : J.det ≠ 0) :
    (J.map τ).det ≠ 0 := by
  rw [show J.map τ = τ.mapMatrix J from rfl, ← RingHom.map_det]
  exact (map_ne_zero τ).2 h

theorem exists_fock_data : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) , IsCMExt F E σ → ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W), IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 → M.IsWeil ψ χX χW om → ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) → (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) → ∃ (P Q R S : InfinitePlace F → ℕ) (A : ∀ w : InfinitePlace F, Matrix (Fin n) (Ix (P w) (Q w)) ℂ) (C : ∀ w : InfinitePlace F, Matrix (Fin d) (Ix (R w) (S w)) ℂ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)) (c c' : InfinitePlace F → ℂ), FramedD τ (incM F X.J) (incM F W.J) 1 Complex.I A C ∧ Function.Injective Φ ∧ LinearMap.range Φ = M.Pol ψ τ ∧ ActsByD τ A (om.comp (MonoidHom.inl _ _)) Φ (fun w => fockAct1 (P w) (Q w) (R w) (S w)) c ∧ ActsByD τ C (om.comp (MonoidHom.inr _ _)) Φ (fun w => fockAct2 (P w) (Q w) (R w) (S w)) c' := by
  intro F E _ _ _ _ _ σ hCM n d X W M ψ χX χW om hψ hXh hXd hWs hWd hW τ hXc hWc

  have hX : ∀ w, ∃ (r s : ℕ) (A : Matrix (Fin n) (Ix r s) ℂ),
      IsFrame (X.J.map (τ w).1) A ∧ X.θ w * A = A * Jm r s := by
    intro w
    refine GlobalTheory.T.exists_signatureOrthonormalFrame_eigen_of_cartanInvolution n _ _ ?_ (det_map_ne_zero _ _ hXd) (hXc w)
    intro i j
    simp only [Matrix.map_apply]
    rw [← hCM.2.2.2 (τ w).1, hXh]
  have hW' : ∀ w, ∃ (r s : ℕ) (C : Matrix (Fin d) (Ix r s) ℂ),
      IsFrame (Complex.I • W.J.map (τ w).1) C ∧ W.θ w * C = C * Jm r s := by
    intro w
    refine GlobalTheory.T.exists_signatureOrthonormalFrame_eigen_of_cartanInvolution d _ _ ?_ ?_ (hWc w)
    · intro i j
      simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, star_mul']
      rw [← hCM.2.2.2 (τ w).1, hWs, map_neg, show star Complex.I = -Complex.I from Complex.conj_I]
      ring
    · rw [Matrix.det_smul]
      exact mul_ne_zero (pow_ne_zero _ Complex.I_ne_zero) (det_map_ne_zero _ _ hWd)
  choose P Q A hA hθA using hX
  choose R S C hC hθC using hW'

  have hF : FramedD τ (incM F X.J) (incM F W.J) 1 Complex.I A C := by
    refine ⟨one_mul _, fun w => ?_, fun w => ?_⟩
    · rw [one_smul, incM_map_piInf]
      exact hA w
    · rw [incM_map_piInf]
      exact hC w
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_fockMap_signatures_depend_on_place F E σ (Fin n) (Fin d) (Fin n × Fin d) P Q R S ψ τ _ _ M.co 1 Complex.I A C
    hCM hψ hF

  obtain ⟨hB, ⟨d', hd', hA'⟩, -⟩ := hW
  obtain ⟨c, hc⟩ := GlobalTheory.T.firstMember_lieAction_fock_plus_trace F E σ (Fin n) (Fin d) (Fin n × Fin d) P Q R S ψ τ _ _ M.co d' 1 Complex.I A C Φ
    (om.comp (MonoidHom.inl _ _)) hCM hψ hF hΦ hd' hA'.1
  obtain ⟨c', hc'⟩ := GlobalTheory.T.howeSplitting_acts_fockAction_plus_traceMultiples F E σ (Fin n) (Fin d) (Fin n × Fin d) P Q R S ψ τ _ _ M.co 1 Complex.I A C Φ
    (om.comp (MonoidHom.inr _ _)) hCM hψ hF hΦ hB.1
  exact ⟨P, Q, R, S, A, C, Φ, c, c', hF, hΦ.1,
    GlobalTheory.T.polynomialFockSpace_eq_range_fockMap_variable_signature F E σ n d P Q R S X W M ψ τ A C Φ hCM hψ hF hθA hθC hΦ, hc, hc'⟩

end GlobalTheory.HoweD.FockData

end
end

section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.exists_highestWeight_lift_mod_stable_subspace : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), Good act → ∀ N N' : Submodule ℂ V, KStable act N → KStable act N' → ∀ (μ : Ix p q → ℚ), ∀ v ∈ N', (∀ c, act (Eab c c) v - ((μ c : ℚ) : ℂ) • v ∈ N) → (∀ c d, posC c d → act (Eab c d) v ∈ N) → ∃ v' ∈ N', v' ∈ hwSub act μ ∧ v - v' ∈ N := by
  first | exact @GlobalTheory.HoweR.LiftMod.lift_mod | exact GlobalTheory.HoweR.LiftMod.lift_mod | (intros; apply GlobalTheory.HoweR.LiftMod.lift_mod <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
theorem _root_.GlobalTheory.T.orbital_integral_test_function_second : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), (∀ (y : grp G β) (h : G.GAf), f (h⁻¹ * toAfF G β x t hx y * h) ≠ 0 → (∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ∧ FixL G v β y z) → (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧ (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable) → sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → ∀ y₀ : grp G β, Set.Finite {q : Pts G v β x t hx L.K.toSubgroup K' | ∃ γ : grp G β, FixL G v β (γ * y₀ * γ⁻¹) (Quot.out q).2.1 ∧ f ((Quot.out q).1.1⁻¹ * toAfF G β x t hx (γ * y₀ * γ⁻¹) * (Quot.out q).1.1) * f' ((Quot.out q).1.2⁻¹ * toP1 G β (γ * y₀ * γ⁻¹) * (Quot.out q).1.2) ≠ 0} := by
  first | exact @GlobalTheory.FinPtsSep.finite_pts_conj_fixL_sep | exact GlobalTheory.FinPtsSep.finite_pts_conj_fixL_sep
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn

namespace GlobalTheory.LowMainTerm

theorem logHook_congr (n : ℕ) (a b : ℕ → ℝ) (h : ∀ i < n, a i = b i) :
    Formalism.BasicNotions.DV.logHook n a = Formalism.BasicNotions.DV.logHook n b := by
  unfold Formalism.BasicNotions.DV.logHook
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [h i (Finset.mem_range.mp hi)]
  · refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun l hl => ?_
    have hi' := Finset.mem_range.mp hi
    have hl' := (Finset.mem_Ioo.mp hl).2
    rw [h i hi', h l hl']

theorem pW_eq (D : D7) (j : Fin D.R.m) (ρ : D.what₂.Tau) :
    GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.pW D j ρ = (D.R.sigW ((j : ℕ) + 1)).1 := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.pW
  rw [GlobalTheory.RecGaps.sig_Wc]

theorem sigW_fst (D : D7) (j : Fin D.R.m) : (D.R.sigW ((j : ℕ) + 1)).1 = D.R.k + (j : ℕ) := by
  simp [Formalism.BasicNotions.Ranks.sigW]

theorem hook_term (D : D7) (j : Fin D.R.m) (ρ : D.what₂.Tau) :
    Real.log ((GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.pW D j ρ)
        (Formalism.IndefR.Links.aPl D j (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.pW D j ρ) ρ) : ℕ) : ℝ)
      = Formalism.BasicNotions.DV.logHook (D.R.sigW ((j : ℕ) + 1)).1 (Formalism.BasicNotions.DV.aPlus D ((j : ℕ) + 1) ρ) := by
  have h1 : 1 ≤ (j : ℕ) + 1 := Nat.le_add_left 1 _
  have h2 : (j : ℕ) + 1 ≤ D.R.m := j.isLt
  rw [pW_eq, sigW_fst]
  have key : ∀ n < D.R.k + (j : ℕ),
      ((Formalism.IndefR.Links.aPl D j (D.R.k + (j : ℕ)) ρ n : ℕ) : ℝ) = Formalism.BasicNotions.DV.aPlus D ((j : ℕ) + 1) ρ n := by
    intro n hn
    have := GlobalTheory.RecordWeightVec.aPl_eq_aPlusQ D j ρ n hn
    unfold Formalism.BasicNotions.DV.aPlus
    rw [← this]
    push_cast
    rfl
  have rs := (GlobalTheory.BlockRows.rows_sizes D ((j : ℕ) + 1) h1 h2 ρ).1
  have hanti : ∀ (x y : ℕ), x ≤ y → y < D.R.k + (j : ℕ) →
      Formalism.IndefR.Links.aPl D j (D.R.k + (j : ℕ)) ρ y ≤ Formalism.IndefR.Links.aPl D j (D.R.k + (j : ℕ)) ρ x := by
    intro x y hxy hy
    have hx : x < D.R.k + (j : ℕ) := lt_of_le_of_lt hxy hy
    have e : (D.R.sigW ((j : ℕ) + 1)).1 = D.R.k + (j : ℕ) := sigW_fst D j
    have hy' : y < (D.R.sigW ((j : ℕ) + 1)).1 := e ▸ hy
    have hx' : x < (D.R.sigW ((j : ℕ) + 1)).1 := e ▸ hx
    have ha := rs.1 (show (⟨x, hx'⟩ : Fin _) ≤ ⟨y, hy'⟩ from hxy)
    have ex := rs.2.2 ⟨x, hx'⟩
    have ey := rs.2.2 ⟨y, hy'⟩
    have r : ((Formalism.IndefR.Links.aPl D j (D.R.k + (j : ℕ)) ρ y : ℕ) : ℝ)
        ≤ ((Formalism.IndefR.Links.aPl D j (D.R.k + (j : ℕ)) ρ x : ℕ) : ℝ) := by
      rw [key y hy, key x hx]
      simp only at ex ey
      rw [← ex, ← ey]
      exact_mod_cast ha
    exact_mod_cast r
  rw [(GlobalTheory.HookDiagram.hookOf_pos_log _ _ hanti).2]
  exact logHook_congr _ _ _ key

end GlobalTheory.LowMainTerm

namespace GlobalTheory.LowMainTerm

theorem sum_logHook_eq (D : D7) (L : SizeData₂ D) (Del h0 : ℕ) (j : Fin D.R.m) :
    (∑ ρ, (ofRecord D L Del h0).logHook ((j : ℕ) + 1) ρ) = GlobalTheory.LiftLower.hookPlus D j := by
  have h1 : 1 ≤ (j : ℕ) + 1 := Nat.le_add_left 1 _
  have h2 : (j : ℕ) + 1 ≤ D.R.m := j.isLt
  have e1 : (∑ ρ, (ofRecord D L Del h0).logHook ((j : ℕ) + 1) ρ)
      = ∑ z : Bool × G.HH D, Formalism.BasicNotions.DV.logHook (D.R.sigW ((j : ℕ) + 1)).1
          (Formalism.BasicNotions.DV.aPlus D ((j : ℕ) + 1) (tauPl D z)) :=
    Finset.sum_congr rfl fun z _ => Formalism.L2.DIV.NumTieH.logHook_eq D L Del h0 h1 h2 z
  rw [e1, Function.Bijective.sum_comp (tauPl_bijective D)
    (fun τ => Formalism.BasicNotions.DV.logHook (D.R.sigW ((j : ℕ) + 1)).1 (Formalism.BasicNotions.DV.aPlus D ((j : ℕ) + 1) τ))]
  unfold GlobalTheory.LiftLower.hookPlus
  exact (Finset.sum_congr rfl fun ρ _ => hook_term D j ρ).symm

theorem main_le_lowB : ∀ (D : D7) (L : SizeData₂ D) (Del h0 : ℕ) (Csz : ℝ) (j : Fin D.R.m), 8 ≤ Csz → Sizes D j L.sc.b → (∑ ρ, (ofRecord D L Del h0).logHook ((j : ℕ) + 1) ρ) - Csz * ((D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * (ofRecord D L Del h0).Lp) ≤ lowB D j L.sc.b := by
  intro D L Del h0 Csz j hC hS
  rw [sum_logHook_eq]
  have hLp : (ofRecord D L Del h0).Lp = GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.Lp D L.sc.b := by
    rw [Formalism.L2.DIV.NumTieH.Lp_eq]; rfl
  have hpos : 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.Lp D L.sc.b := by
    have := (GlobalTheory.AdelicScalar.SizeBounds.sizes D j L.sc.b hS).1
    linarith
  rw [hLp]
  unfold GlobalTheory.BigOn.lowB
  have hX : 0 ≤ (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.Lp D L.sc.b := by positivity
  nlinarith

end GlobalTheory.LowMainTerm
end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_vacuum_multiplier_constant_per_lattice : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsPair ψ θ V W χV χW om → ∀ mu : GA D W → ℂ, Formalism.L2.Pj.MuVal W χV mu → ∀ (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsMod W hr X → IsSympl X bas → ∀ (H : Geo.Tor.Host D.host.E), (H.rt : D.host.E) = D.host.sqrtMinusD → ∀ (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), V.rank ≠ 0 → (ΛV : Set (Fin V.rank → D.host.E)) = L0c D V → (ΛW : Set (Fin W.rank → D.host.E)) = L0c D W → IsSelfDualC V ΛV → IsSelfDualC W ΛW → (ΛV : Set (Fin V.rank → D.host.E)) = (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E)) → SelfD X X.Λ → ∀ (x₀ : Frame X.Ψ r) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsONFr X x₀ → IsInvOf W hr X x₀ s → ∀ f, IsVacO ψ θ V W (fun _ => 1) s (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) f → ∀ v : TF V.rank g, IsVac X bas (H.w0 : D.host.E) (tens (stdL D.host.E V.rank) X.Λ) v → ∃ κ : ℂ, κ ≠ 0 ∧ (∀ x' ∈ X.dom, IsUnitFr X x' → ∀ (ϑ : (Fin g → ℂ) → ℂ) (κ' : ℂ), IsTheta1 X bas idx (H.w0 : D.host.E) x' X.Λ ϑ → MeanOne X bas idx x' X.Λ ϑ → (∀ z : Fin V.rank → Fin g → ℂ, ∏ b, ϑ (z b) = κ' * thA X bas idx v x' z) → ‖κ'‖ = ‖κ‖) ∧ ∀ k : GA D W, latR hr (Formalism.L2.Pj.latG W k) = X.Λ → IsONFr X (frMove θ W hr X k x₀) ∧ Reads θ V W hr X bas idx (om (1, k) f) ((κ * mu k) • v) (frMove θ W hr X k x₀) := by
  first | exact @GlobalTheory.VacFamily.exists_vacuum_multiplier | exact GlobalTheory.VacFamily.exists_vacuum_multiplier | (intros; apply GlobalTheory.VacFamily.exists_vacuum_multiplier <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.BCT.forms_decomp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → FiniteDimensional ℂ (forms S lam K') ∧ ∃ (ι : Type) (_ : Fintype ι) (π : ι → Submodule ℂ (UA E n → ℂ)), (∀ i, IsAutRepU (π i) ∧ (∀ v, HasWeightAt (π i) v.embedding (lam v)) ∧ π i ⊓ fixed (RF E n) (globLev S K') ≠ ⊥) ∧ iSupIndep (fun i => π i ⊓ fixed (RF E n) (globLev S K')) ∧ (⨆ i, π i ⊓ fixed (RF E n) (globLev S K')) = forms S lam K' ∧ ∀ π₀, IsAutRepU π₀ → (∀ v, HasWeightAt π₀ v.embedding (lam v)) → π₀ ⊓ fixed (RF E n) (globLev S K') ≠ ⊥ → ∃ i, ∀ w (σ : SmIrr (UL n w)), IsCompU π₀ w σ → IsCompU (π i) w σ := by
  intro E _ _ _ hU n _ S _ lam K' hK
  have hLo := GlobalTheory.T.isOpen_productOfLocalLevelsUnitary E hU n S K' hK
  obtain ⟨C, hCf, hC⟩ := GlobalTheory.T.exists_finiteDimensional_archRestriction_space_of_weight E n lam
  have hcls : ∀ L : Subgroup (finU (E := E) (n := n)), IsOpen (L : Set (finU (E := E) (n := n))) → ∃ S : Finset (UA E n), ∀ g : UA E n,
      ∃ γ ∈ ratU E n, ∃ s ∈ S, ∃ k ∈ L, ∃ y ∈ infU E n, g = γ * s * (k : UA E n) * y := by
    intro L hL
    obtain ⟨S₀, hS₀⟩ := GlobalTheory.DefU.ClassFin.classSet_finite E n L hL
    refine ⟨S₀, fun g => ?_⟩
    obtain ⟨γ, hγ, s, hs, x, hx, k, hk, rfl⟩ := hS₀ g
    exact ⟨γ, hγ, s, hs, k, hk, x, hx, by rw [mul_assoc (γ * s) x, ← GlobalTheory.DefU.fin_mul_inf k.2 hx, ← mul_assoc]⟩
  have hfin := GlobalTheory.UnitaryBC.finiteDimensional_levelForms E n hcls _ hLo C hCf
  have hmemF : ∀ φ : UA E n → ℂ, φ ∈ fixed (RF E n) (globLev S K') ↔ ∀ k ∈ globLev S K', RU E n (k : UA E n) φ = φ := by
    intro φ
    change (∀ h : globLev S K', _) ↔ _
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    exact ⟨fun h k hk => h ⟨k, hk⟩, fun h k => h k.1 k.2⟩
  have hle : forms S lam K' ≤ Submodule.span ℂ {ψ : UA E n → ℂ | (∀ γ ∈ ratU E n, ∀ g, ψ (γ * g) = ψ g) ∧
      (∀ k ∈ globLev S K', ∀ g, ψ (g * (k : UA E n)) = ψ g) ∧ ∀ g, (fun y : infU E n => ψ (g * (y : UA E n))) ∈ C} := by
    refine iSup₂_le fun π hπ φ hφ => Submodule.subset_span ⟨(hπ.1.aut φ hφ.1).left, fun k hk g => ?_, hC π hπ.1 hπ.2 φ hφ.1⟩
    exact congrFun ((hmemF φ).1 hφ.2 k hk) g
  haveI : FiniteDimensional ℂ (forms S lam K') := Submodule.finiteDimensional_of_le hle
  refine ⟨inferInstance, ?_⟩
  obtain ⟨ι, hι, π, h1, h2, h3, h4⟩ := GlobalTheory.T.fixed_vectors_irreducible_subrep_decomposition (RU E n) {x | ∃ k ∈ globLev S K', x = ((k : finU (E := E) (n := n)) : UA E n)}
    (fixed (RF E n) (globLev S K')) (fun φ => by
      rw [hmemF]
      exact ⟨fun h x ⟨k, hk, e⟩ => e ▸ h k hk, fun h k hk => h _ ⟨k, hk, rfl⟩⟩)
    {π | IsAutRepU π ∧ ∀ v, HasWeightAt π v.embedding (lam v)}
    (fun P hP => ⟨hP.1.ne_bot, hP.1.stable, hP.1.irred⟩) (by assumption)
  refine ⟨ι, hι, π, fun i => ⟨(h1 i).1.1, (h1 i).1.2, (h1 i).2⟩, h2, h3, fun π₀ hπ₀ hw₀ hne => ?_⟩
  obtain ⟨i, T, hT1, hT2, hT3⟩ := h4 π₀ ⟨hπ₀, hw₀⟩ hne
  refine ⟨i, fun w σ ⟨p, hp, hirr, f, hf0, hfπ, hfe⟩ => ⟨p, hp, hirr, T ∘ₗ f, fun h => hf0 ?_, fun v => hT1 _ (hfπ v), fun x v => ?_⟩⟩
  · ext v : 1
    exact hT2 _ (hfπ v) (LinearMap.congr_fun h v)
  · rw [LinearMap.comp_apply, hfe x v]
    exact hT3 _ _ (hfπ v)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.CentLev

theorem loc_cpt_part {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (n : ℕ) (w : Pl E)
    (y : UL n w) (hs : y.1.val.charpoly.Separable) :
    ∃ C : Set (UL n w), IsCompact C ∧ (cptPart (twCent (MonoidHom.id (UL n w)) y) : Set (UL n w)) ⊆ C := by
  obtain ⟨Ω, hΩ, hmem⟩ := GlobalTheory.CentCpt.main E hU n w y hs
  haveI : T2Space (GL (Fin n) (w.adicCompletion E)) := Units.isEmbedding_embedProduct.t2Space
  have hc : ∀ a ∈ twCent (MonoidHom.id (UL n w)) y, ∀ b ∈ twCent (MonoidHom.id (UL n w)) y, a * b = b * a := by
    intro a ha b hb
    have ha' : a * y = y * a := ha
    have hb' : b * y = y * b := hb
    have hav : (a : GLw n w).val * (y : GLw n w).val = (y : GLw n w).val * (a : GLw n w).val := by
      have := congrArg (fun z : UL n w => (z : GLw n w).val) ha'; simpa using this
    have hbv : (b : GLw n w).val * (y : GLw n w).val = (y : GLw n w).val * (b : GLw n w).val := by
      have := congrArg (fun z : UL n w => (z : GLw n w).val) hb'; simpa using this
    have := GlobalTheory.commute_of_commute_separable_charpoly _ n _ _ _ hs hav hbv
    apply Subtype.ext; apply Units.ext; simpa using this
  refine ⟨Ω, hΩ, fun z hz => ?_⟩
  obtain ⟨hzT, hzc⟩ := GlobalTheory.LocFinU.cptPart_subset_of_comm _ hc hz
  exact hmem z hzT hzc

theorem stab_le_cptPart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ γ : UE E n, γ.1.val.charpoly.Separable → ∀ x : finU (E := E) (n := n), twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ) ⊓ (globLev S (KL n)).map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ)) ∧ (twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ) ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ))) ≠ 0 := by
  intro E _ _ _ hU n hn S hS K' hK' γ hγ x
  set δ : finU (E := E) (n := n) := finPt γ with hδ
  set T := twCent (MonoidHom.id (finU (E := E) (n := n))) δ with hT
  let ρ : ∀ w : Pl E, finU (E := E) (n := n) →* UL n w := fun w =>
    { toFun := fun z => ⟨cLoc w (z : UA E n), GlobalTheory.BCT.ThBasic.cLoc_mem_UL hU n w _⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have hρv : ∀ w z, ((ρ w z : UL n w) : GLw n w) = cLoc w (z : UA E n) := fun _ _ => rfl
  have hρc : ∀ w, Continuous (ρ w) := fun w =>
    continuous_induced_rng.2 ((GlobalTheory.DefU.Inert.continuous_cLoc w).comp continuous_subtype_val)
  have hδw : ∀ w, ((ρ w δ : UL n w) : GLw n w) = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 := by
    intro w
    rw [hρv, hδ, FinPtLoc.finPt_eq]
    apply Units.ext
    refine Matrix.ext fun i j => ?_
    change pLoc E w (pFin E ((finGL E n (ratF E n γ.1)).val i j)) = algebraMap E _ (γ.1.val i j)
    rw [FinPtLoc.snd_entry]
    rfl
  have hsep : ∀ w, ((ρ w δ : UL n w) : GLw n w).val.charpoly.Separable := by
    intro w
    rw [hδw]
    have e : (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1).val = γ.1.val.map (algebraMap E _) := rfl
    rw [e, Matrix.charpoly_map]
    exact hγ.map
  have hsetK : ∀ K'' : ∀ w : Pl E, Subgroup (UL n w), (globLev S K'' : Set (finU (E := E) (n := n))) =
      {z : finU (E := E) (n := n) | ∀ w ∈ S, toSub (UL n w) (cLoc w (z : UA E n)) ∈ (K'' w : Set (UL n w))} := by
    intro K''
    ext z
    simp only [SetLike.mem_coe, Set.mem_setOf_eq, globLev, Subgroup.mem_iInf, Subgroup.mem_comap, Subgroup.mem_map,
      MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype]
    refine forall₂_congr fun w _ => ?_
    rw [FinPtLoc.toSub_of_mem _ _ (GlobalTheory.BCT.ThBasic.cLoc_mem_UL hU n w _)]
    constructor
    · rintro ⟨a, ha, e⟩
      have : a = ⟨_, GlobalTheory.BCT.ThBasic.cLoc_mem_UL hU n w (z : UA E n)⟩ := Subtype.ext e
      rwa [← this]
    · intro h
      exact ⟨_, h, rfl⟩
  have hKc : IsCompact (globLev S (KL n) : Set (finU (E := E) (n := n))) := by
    rw [hsetK]
    exact GlobalTheory.BCT.LocCpt.loc_cpt E hU n S hS (fun w => (KL n w : Set (UL n w)))
      (fun w => (GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w).2) (Filter.Eventually.of_forall fun _ => rfl)
  have hcf : ⇑((MulAut.conj x).toMonoidHom) = fun g : finU (E := E) (n := n) => x * g * x⁻¹ := by
    ext g; simp
  have hconj : ∀ H : Subgroup (finU (E := E) (n := n)), (H.map (MulAut.conj x).toMonoidHom : Set (finU (E := E) (n := n))) =
      (fun g => x⁻¹ * g * x) ⁻¹' (H : Set (finU (E := E) (n := n))) := by
    intro H; ext g
    rw [Subgroup.coe_map, hcf]
    constructor
    · rintro ⟨k, hk, rfl⟩
      simpa [mul_assoc] using hk
    · intro h
      exact ⟨_, h, by group⟩
  refine ⟨?_, ?_⟩
  · rintro t ⟨htT, htK⟩
    apply Subgroup.subset_closure
    refine ⟨htT, ?_⟩
    have hKx : IsCompact ((globLev S (KL n)).map (MulAut.conj x).toMonoidHom : Set (finU (E := E) (n := n))) := by
      rw [Subgroup.coe_map, hcf]
      exact hKc.image (by fun_prop)
    set_option synthInstance.maxHeartbeats 200000 in
      exact hKx.closure_of_subset fun s hs => Subgroup.zpowers_le.2 htK hs
  · have hUo : IsOpen ((globLev S K').map (MulAut.conj x).toMonoidHom : Set (finU (E := E) (n := n))) := by
      rw [hconj]
      exact (GlobalTheory.T.isOpen_productOfLocalLevelsUnitary E hU n S K' hK').preimage (by fun_prop)
    choose C0 hC0c hC0 using fun w => loc_cpt_part hU n w (ρ w δ) (hsep w)
    have hcof := GlobalTheory.T.centraliser_compactPart_le_integral_almostAll E hU n γ hγ
    let C : ∀ w : Pl E, Set (UL n w) := fun w =>
      if cptPart (twCent (MonoidHom.id (UL n w)) (ρ w δ)) ≤ KL n w then (KL n w : Set (UL n w)) else C0 w
    have hCc : ∀ w, IsCompact (C w) := by
      intro w
      by_cases h : cptPart (twCent (MonoidHom.id (UL n w)) (ρ w δ)) ≤ KL n w
      · simp only [C, if_pos h]; exact (GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w).2
      · simp only [C, if_neg h]; exact hC0c w
    have hCK : ∀ᶠ w in cofinite, C w = KL n w := by
      filter_upwards [hcof] with w hw
      have e : ρ w δ = locPt w γ := by
        rw [← GlobalTheory.BCT.locPt_finPt E hU n γ w, FinPtLoc.toSub_of_mem _ _ (GlobalTheory.BCT.ThBasic.cLoc_mem_UL hU n w _)]
        rfl
      have hw' : cptPart (twCent (MonoidHom.id (UL n w)) (ρ w δ)) ≤ KL n w := by rw [e]; exact hw
      simp only [C, if_pos hw']
    have hsub : ∀ w, (cptPart (twCent (MonoidHom.id (UL n w)) (ρ w δ)) : Set (UL n w)) ⊆ C w := by
      intro w
      by_cases h : cptPart (twCent (MonoidHom.id (UL n w)) (ρ w δ)) ≤ KL n w
      · simp only [C, if_pos h]; exact h
      · simp only [C, if_neg h]; exact hC0 w
    have hD := GlobalTheory.BCT.LocCpt.loc_cpt E hU n S hS C hCc hCK
    have hle : cptPart T ≤ ⨅ w : Pl E, (cptPart (twCent (MonoidHom.id (UL n w)) (ρ w δ))).comap (ρ w) := by
      rw [cptPart, Subgroup.closure_le]
      rintro t ⟨htT, htc⟩
      rw [SetLike.mem_coe, Subgroup.mem_iInf]
      intro w
      rw [Subgroup.mem_comap]
      apply Subgroup.subset_closure
      refine ⟨?_, ?_⟩
      · have ht' : t * δ = δ * t := htT
        show ρ w t * ρ w δ = ρ w δ * (MonoidHom.id _) (ρ w t)
        rw [MonoidHom.id_apply, ← map_mul, ht', map_mul]
      · have himc : IsCompact (ρ w '' closure (Subgroup.zpowers t : Set (finU (E := E) (n := n)))) := htc.image (hρc w)
        refine himc.closure_of_subset ?_
        rintro _ ⟨k, rfl⟩
        exact ⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩
    have hTD : (cptPart T : Set (finU (E := E) (n := n))) ⊆
        {z : finU (E := E) (n := n) | ∀ w ∈ S, toSub (UL n w) (cLoc w (z : UA E n)) ∈ C w} := by
      intro z hz w _
      have hzw := Subgroup.mem_iInf.1 (hle hz) w
      rw [Subgroup.mem_comap] at hzw
      rw [FinPtLoc.toSub_of_mem _ _ (GlobalTheory.BCT.ThBasic.cLoc_mem_UL hU n w _)]
      exact hsub w hzw
    have hUo' : IsOpen ((((globLev S K').map (MulAut.conj x).toMonoidHom).subgroupOf (cptPart T) : Subgroup _) :
        Set (cptPart T)) := by
      rw [Subgroup.coe_subgroupOf]
      exact hUo.preimage continuous_subtype_val
    have hfi := GlobalTheory.LocVec.finiteIndex_of_isOpen (cptPart T) hD hTD _ hUo'
    have hTc : cptPart T ≤ T := (Subgroup.closure_le T).2 fun t ht => ht.1
    have heq : (T ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom).subgroupOf (cptPart T) =
        ((globLev S K').map (MulAut.conj x).toMonoidHom).subgroupOf (cptPart T) := by
      ext z
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.2, fun h => ⟨hTc z.2, h⟩⟩
    rw [Subgroup.relIndex, heq]
    exact hfi.index_ne_zero

end GlobalTheory.BCT.CentLev
end
end
