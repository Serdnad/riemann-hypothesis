module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle029
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle048
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle032
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle052
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle101
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle084
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle102
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle103
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle095
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle037
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle089
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StableEigenTangentsPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle104
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle013
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle087
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm
  ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo
  GlobalTheory.CompanionTheory.Ar.PB

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp

section Lines

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isSmoothHerm_combLine {σ : Type} [Fintype σ] {A : σ → HermLine ι} (hA : ∀ a, IsSmoothHerm (A a))
    (n : σ → ℤ) : IsSmoothHerm (GlobalTheory.CompanionTheory.Ar.PB.combLine A n) := by
  refine contDiffOn_prod fun a _ => ?_
  intro z hz
  have h0 : (A a).h z ≠ 0 := ((A a).pos z hz).ne'
  have hf := hA a z hz
  have key : ∀ m : ℤ, ContDiffWithinAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => (A a).h z ^ m)
      {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} z := by
    intro m
    cases m with
    | ofNat k => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hf.pow k
    | negSucc k =>
      simp only [zpow_negSucc]
      exact (hf.pow (k + 1)).inv (pow_ne_zero _ h0)
  exact key _

theorem isC2At_of_isPotential {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {P : LocPot X}
    (hP : IsPotential A P) (x : X) : IsTwiceDifferentiableAt A P x := by
  intro j hj
  have hm : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x :=
    ⟨(A.chart j).map_source hj, by
      rw [Set.mem_preimage, (A.chart j).left_inv hj]; exact P.mem_U x⟩
  exact (contDiffAt_of_isPotential A P hP x j hm).of_le (by
    exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))

theorem mInt_potOf_eq_of_deg {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) {L L' : Fin e → HermLine ι}
    (hL : ∀ j, IsSmoothHerm (L j)) (hL' : ∀ j, IsSmoothHerm (L' j)) (ha : ∀ j, (L j).a = (L' j).a) :
    mInt R.A (fun j => potOf R (L j)) (fun _ => 1) = mInt R.A (fun j => potOf R (L' j)) (fun _ => 1) := by
  let B : Fin e → HermLine ι := fun j => GlobalTheory.CompanionTheory.Ar.PB.combLine ![L j, L' j] ![1, -1]
  have hB0 : ∀ j, (B j).a = 0 := fun j => by
    rw [(combLine_div (L j) (L' j)).1, ha j, sub_self]
  have hBs : ∀ j, IsSmoothHerm (B j) := fun j =>
    isSmoothHerm_combLine (fun a => by
      fin_cases a
      · exact hL j
      · exact hL' j) _
  let u : Fin e → R.X → ℝ := fun j x => Real.log ((B j).h (R.lift x x))
  have hu : ∀ j, R.A.Smooth (u j) := fun j => smooth_diag R (hBs j) (hB0 j)
  have h1 : mInt R.A (fun j => potOf R (L j)) (fun _ => 1) =
      mInt R.A (fun j => potOf R (L' j) + LocPot.ofFun (u j)) (fun _ => 1) := by
    refine mInt_congr _ (locDens_congr_of_eqOn R fun i x y hy => ?_) fun _ => rfl
    show Real.log ((L i).h (R.lift x y)) = Real.log ((L' i).h (R.lift x y)) + Real.log ((B i).h (R.lift y y))
    have hm := (R.mem x y hy).1
    rw [← h_eq_of_sameOrbit (hB0 i) (R.compat x y y ⟨hy, R.mem_U y⟩), (combLine_div (L i) (L' i)).2,
      Real.log_div ((L i).pos _ hm).ne' ((L' i).pos _ hm).ne']
    ring
  rw [h1]
  exact massIndep R.A _ u (fun i => isPotential_potOf R (hL' i)) hu

end Lines

section Coef

variable {Ψ : Type} [DecidableEq Ψ] {N : ℕ}

def rootCoef (r p : Ψ × Fin N) : ℤ :=
  (if p.1 = r.1 ∧ (p.2 : ℕ) + 1 = r.2 then 1 else 0) - (if p = r then 1 else 0)

theorem sum_rootCoef_mul [Fintype Ψ] (r : Ψ × Fin N) (f : Ψ × Fin N → ℤ) :
    ∑ p, rootCoef r p * f p =
      (if h : 0 < (r.2 : ℕ) then f (r.1, ⟨(r.2 : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) r.2.isLt⟩) else 0) - f r := by
  obtain ⟨τ, i⟩ := r
  simp only [rootCoef, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul]
  congr 1
  · split_ifs with h
    · rw [Finset.sum_eq_single (τ, ⟨(i : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩)]
      · rw [if_pos ⟨rfl, by simp only; omega⟩]
      · rintro ⟨τ', l⟩ - hne
        rw [if_neg]
        rintro ⟨h1, h2⟩
        simp only at h1 h2
        subst h1
        exact hne (by simp only [Prod.mk.injEq, true_and]; ext; simp only; omega)
      · simp
    · refine Finset.sum_eq_zero fun p _ => if_neg ?_
      rintro ⟨-, h2⟩
      have h2' : (p.2 : ℕ) + 1 = i := h2
      omega
  · simp

theorem sum_neg_mul_rootCoef [Fintype Ψ] (lam : Ψ × Fin N → ℝ) (p : Ψ × Fin N) :
    ∑ r, -lam r * (rootCoef r p : ℝ) = GlobalTheory.CompanionTheory.Ar.PB.gap lam p := by
  obtain ⟨τ, l⟩ := p
  have h2 : ∑ r : Ψ × Fin N, lam r * (if (τ, l) = r then (1 : ℝ) else 0) = lam (τ, l) := by simp
  have h1 : ∑ r : Ψ × Fin N, lam r * (if (τ, l).1 = r.1 ∧ (((τ, l).2 : Fin N) : ℕ) + 1 = r.2 then (1 : ℝ) else 0) =
      if h : (l : ℕ) + 1 < N then lam (τ, ⟨(l : ℕ) + 1, h⟩) else 0 := by
    split_ifs with h
    · rw [Finset.sum_eq_single (τ, ⟨(l : ℕ) + 1, h⟩)]
      · simp
      · rintro ⟨τ', m⟩ - hne
        rw [if_neg, mul_zero]
        rintro ⟨h1, h2⟩
        simp only at h1 h2
        subst h1
        exact hne (by simp only [Prod.mk.injEq, true_and]; ext; simp only; omega)
      · simp
    · refine Finset.sum_eq_zero fun r _ => ?_
      rw [if_neg, mul_zero]
      rintro ⟨-, h2⟩
      have := r.2.isLt
      simp only at h2
      omega
  have h3 : GlobalTheory.CompanionTheory.Ar.PB.gap lam (τ, l) =
      lam (τ, l) - if h : (l : ℕ) + 1 < N then lam (τ, ⟨(l : ℕ) + 1, h⟩) else 0 := by
    unfold GlobalTheory.CompanionTheory.Ar.PB.gap gapX
    split_ifs with h <;> simp [h]
  rw [h3, ← h1, ← h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [rootCoef]
  push_cast
  ring

end Coef

section Real

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem mInt_ref_eq {D : ℕ} {σ : Type} {S : AnSys D σ} {P : Ideal (MRing ι)} (Re : Realis S P) (w : Fin D → σ) :
    mInt Re.R.A (fun j => potOf Re.R (Re.ref (w j))) (fun _ => 1) = Re.deg * S.degNum w := by
  have hth : ∀ a, IsPotential S.A (S.th a) := fun a => (S.sing a).1
  have hpb : ∀ a, IsPotential Re.R.A ((S.th a).pullback Re.π Re.holo.1) := fun a =>
    isPotentialPullback S.A Re.R.A Re.π Re.holo (S.th a) (hth a)
  have h1 := (GlobalTheory.T.monge_ampere_integral_congr_potentials D Re.R.X Re.R.A Set.univ (fun j => potOf Re.R (Re.ref (w j)))
    (fun j => (S.th (w j)).pullback Re.π Re.holo.1) (fun _ => 1) (fun _ => 1)
    (fun j => by simp) (fun i => Re.ref_pot (w i)) (fun i x _ => isC2At_of_isPotential _ (hpb _) x)
    (fun _ _ => rfl)).1
  rw [h1]
  exact (degreeFormulaInt S.A Re.R.A Re.π Re.holo Re.deg Re.br Re.degree (fun j => S.th (w j)) (fun i => hth _)
    (fun _ => 1) (mIntegrableCont S.A _ (fun i => hth _) _ continuous_const)).2

theorem mInt_combLine_eq {D : ℕ} {σ : Type} [Fintype σ] {S : AnSys D σ} {P : Ideal (MRing ι)} (Re : Realis S P)
    (n : Fin D → σ → ℤ) :
    mInt Re.R.A (fun j => potOf Re.R (GlobalTheory.CompanionTheory.Ar.PB.combLine Re.ref (n j))) (fun _ => 1) =
      ∑ w : Fin D → σ, (∏ i, (n i (w i) : ℝ)) * (Re.deg * S.degNum w) := by
  have hP : ∀ a, IsPotential Re.R.A (potOf Re.R (Re.ref a)) := fun a => isPotential_potOf Re.R (Re.ref_smooth a)
  have h1 : mInt Re.R.A (fun j => potOf Re.R (GlobalTheory.CompanionTheory.Ar.PB.combLine Re.ref (n j))) (fun _ => 1) =
      mInt Re.R.A (fun j => sumPot (fun a => (n j a : ℝ)) fun a => potOf Re.R (Re.ref a)) (fun _ => 1) := by
    refine mInt_congr _ (fun j y hy => ?_) fun _ => rfl
    refine ReciprocityTheory.ChartRestriction.G.Geo.maDens_congr fun i => ?_
    filter_upwards [((Re.R.A.chart j).isOpen_inter_preimage_symm (Re.R.isOpen_U ((Re.R.A.chart j).symm y))).mem_nhds
      ⟨hy, Re.R.mem_U _⟩] with y' hy'
    have hm := (Re.R.mem _ _ hy'.2).1
    show Real.log (∏ a, (Re.ref a).h _ ^ n i a) = ∑ a, (n i a : ℝ) * Real.log ((Re.ref a).h _)
    rw [Real.log_prod fun a _ => (zpow_pos ((Re.ref a).pos _ hm) _).ne']
    exact Finset.sum_congr rfl fun a _ => Real.log_zpow _ _
  rw [h1, (GlobalTheory.T.monge_ampere_integral_multilinear_expansion D Re.R.X Re.R.A σ Set.univ (fun a => potOf Re.R (Re.ref a)) (fun j a => (n j a : ℝ))
    (fun _ => 1) (fun j => by simp) (fun a x _ => isC2At_of_isPotential _ (hP a) x)
    (fun w => mIntegrableCont _ _ (fun i => hP _) _ continuous_const)).2]
  exact Finset.sum_congr rfl fun w _ => by rw [mInt_ref_eq Re w]

end Real

section Main

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

end Main

end GlobalTheory.CompanionTheory.Ar.Cmp
end
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.flag_frames_generic_model_left : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) [Finite κ] (x : κ → Ω) (S : Type) [Fintype S] (r : S → ℕ) (V : S → Submodule Ω E) (L : S → Lat ξ E) (m n : S → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω r)) ⟶ X') (f : X' ⟶ X), CoordTie ℤ ξ x → (∀ q : X, genPt ξ ⤳ q) → (∀ s, (L s).IsVB (r s) (V s)) → (∀ s, IsTwistGen ξ x (L s) (m s) (φ s)) → (∀ s, LinearIndependent Ω (c s) ∧ Submodule.span Ω (Set.range (c s)) = V s) → CoordTie ℤ ξ' (flagCoord κ x φ c) → (∀ q : X', genPt ξ' ⤳ q) → Dominates ξ' ξ f (algebraMap Ω (GenField Ω r)) → (∀ (p' : Cpt ξ') (c₁ : κ) (h : genPt ξ ⤳ f p'.1), InChart ξ x c₁ ⟨f p'.1, h⟩ ↔ InChart ξ' (fun k => algebraMap Ω (GenField Ω r) (x k)) c₁ p') → ∀ s, ((L s).pull ξ' f (TensorProduct.mk Ω (GenField Ω r) E 1).toAddMonoidHom).IsFlagVBOn Set.univ (genB c s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Flags.pull_isFlagVB_genB | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Flags.pull_isFlagVB_genB | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Flags.pull_isFlagVB_genB <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem _root_.GlobalTheory.T.residue_hodge_lattice_adapted_basis : ∀ (E : Type) [Field E] [NumberField E] (C A : Type) [Field C] [CharZero C] [CommRing A] [Algebra A C]
    (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* C) (g p q : ℕ) (ρC : 𝓞 E →+* Module.End C (Fin g → C))
    (ρHC : 𝓞 E →+* Module.End C ((Fin g → C) × Module.Dual C (Fin g → C)))
    (HV : Submodule A ((Fin g → C) × Module.Dual C (Fin g → C)))
    (tC : Fin (p + q) → (Fin g → C) × Module.Dual C (Fin g → C)) (b₁ v : Fin p → Fin g → C) (b₂ w : Fin q → Fin g → C)
    (u : Fin (p + q) → (Fin g → C) × Module.Dual C (Fin g → C)) (Ap : Matrix (Fin (p + q)) (Fin (p + q)) C)
    (P : Matrix (Fin p) (Fin p) C) (Q : Matrix (Fin q) (Fin q) C) (gm : C),
    (∀ a y, (ρHC a y).1 = ρC a y.1) → (∀ a f, ρHC a (0, f) = (0, f ∘ₗ ρC (bar a))) →
    (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) →
    (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A C).range) → HT.IsFreeOn ρHC HV tC →
    IsAdapted ρHC σ b₁ b₂ u → (∀ i, v i = ∑ k, P i k • b₁ k) → (∀ i, w i = ∑ k, Q i k • b₂ k) →
    LinearIndependent C b₁ → (∀ i, HT.eigProj ρHC σ (tC i) = ∑ k, Ap i k • u k) →
    (∀ (v' : Fin p → Fin g → C) (w' : Fin q → Fin g → C)
      (u' : Fin (p + q) → (Fin g → C) × Module.Dual C (Fin g → C)) (B : Matrix (Fin (p + q)) (Fin (p + q)) C),
      LinearIndependent C v' → Submodule.span A (Set.range v') = HT.eigSub ρC σ (stdLat A C g) →
      LinearIndependent C w' → Submodule.span A (Set.range w') = HT.eigSub ρC σ' (stdLat A C g) →
      IsAdapted ρHC σ v' w' u' → LinearIndependent C (fun i => ∑ k, B i k • u' k) →
      Submodule.span A (Set.range fun i => ∑ k, B i k • u' k) = HT.eigQuot ρHC σ HV →
      ∃ ε : Aˣ, B.det = algebraMap A C ε * gm) →
    LinearIndependent C v → Submodule.span C (Set.range v) = HT.eigSp ρC σ →
    Submodule.span A (Set.range v) = HT.eigSub ρC σ (stdLat A C g) →
    LinearIndependent C w → Submodule.span C (Set.range w) = HT.eigSp ρC σ' →
    Submodule.span A (Set.range w) = HT.eigSub ρC σ' (stdLat A C g) →
    ∃ ε : Aˣ, Ap.det * Q.det = algebraMap A C ε * gm * P.det := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.det_evaluated_frame | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.det_evaluated_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.det_evaluated_frame <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.CompanionTheory.Ar.Flat.GagaC

theorem _root_.GlobalTheory.T.overlapping_analytic_charts_ratio : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (W U U' : X.Opens) (F : (Sp ℂ ⟶ X) → ℂ) (T T' : Ω) (d d' : ℕ) (B : Set (Fin d → ℂ)) (B' : Set (Fin d' → ℂ)) (Y : (Fin d → ℂ) → (Sp ℂ ⟶ X)) (Y' : (Fin d' → ℂ) → (Sp ℂ ⟶ X)) (H : (Fin d → ℂ) → ℂ) (H' : (Fin d' → ℂ) → ℂ) (b₁ : Fin d → ℂ) (b₂ : Fin d' → ℂ) (r : ℂ), IsCptGen ξ → HChart s ξ W U F T B Y H → HChart s ξ W U' F T' B' Y' H' → (∀ (q : X) (hq : genPt ξ ⤳ q), q ∈ U → q ∈ W → unitAt ξ ⟨q, hq⟩ T) → (∀ (q : X) (hq : genPt ξ ⤳ q), q ∈ U' → q ∈ W → unitAt ξ ⟨q, hq⟩ T') → b₁ ∈ B → b₂ ∈ B' → Y b₁ = Y' b₂ → ValAt ξ (Y b₁) (T' / T) r → H b₁ = r * H' b₂ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.GagaC.Compare.eq_val_mul | exact GlobalTheory.CompanionTheory.Ar.Flat.GagaC.Compare.eq_val_mul | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.GagaC.Compare.eq_val_mul <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj
open scoped ComplexOrder


theorem _root_.GlobalTheory.T.lie_metric_torus_pullback : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) (J : K → Type)
    (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y)
    (Z' : Scheme.{0}) (ρ : Z' ⟶ X) (G' : Over Z') [GrpObj G'] (Φ : G'.left ⟶ G.left), IsGrpPullback G' G ρ Φ →
    ∀ (Xc : Type) [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc] (u : splitTorus Z' Xc ⟶ G') [IsMonHom u] (r : ℕ)
    (β : Module.Basis (Fin r) ℤ (Xc →+ ℤ)) (zc : Sp ℂ ⟶ Z') (Mz : LieModel (splitTorus Z' Xc) zc (Xc →+ ℂ)), IsCocharLie Mz →
    (∀ δ, Mz.pt δ ≫ u = 1 → δ = 0) → ∀ v : Fin r → (epsAt (zc ≫ ρ) ⟶ G),
      (∀ a, (v a).left = (Mz.pt ((Int.castAddHom ℂ).comp (β a)) ≫ u).left ≫ Φ) → (RootHt.gramAt h (zc ≫ ρ) v).PosDef := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorusUnif.GramPos.gramAt_posDef_of_diff_injective | exact GlobalTheory.CompanionTheory.Ar.TorusUnif.GramPos.gramAt_posDef_of_diff_injective | (intros; apply GlobalTheory.CompanionTheory.Ar.TorusUnif.GramPos.gramAt_posDef_of_diff_injective <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.ArchB

theorem gen_chart_change (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    (y : (Σ k, J k) → Ω) (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ) (a : K → ℤ) (e₀ τ : Ω) (c₀ c₁ : (k : K) → J k) (u u' : ℂ)
    (hξ : IsCptGen ξ) (he : e₀ ≠ 0) (hw : CoordsAt ξ y z w) (h₀ : ∀ k, w ⟨k, c₀ k⟩ ≠ 0)
    (h₁ : ∀ k, w ⟨k, c₁ k⟩ ≠ 0) (hu : ValAt ξ z (τ / gen y a e₀ c₀) u)
    (hu' : ValAt ξ z (τ / gen y a e₀ c₁) u') :
    u * ∏ k, w ⟨k, c₀ k⟩ ^ a k = u' * ∏ k, w ⟨k, c₁ k⟩ ^ a k := by
  classical
  obtain ⟨hz, -⟩ := val_spec hu
  have hy₀ : ∀ k, y ⟨k, c₀ k⟩ ≠ 0 := fun k => (hw.2 k (c₀ k) (isUnit_iff_ne_zero.2 (h₀ k))).1
  have hy₁ : ∀ k, y ⟨k, c₁ k⟩ ≠ 0 := fun k => (hw.2 k (c₁ k) (isUnit_iff_ne_zero.2 (h₁ k))).1
  have hr : ∀ k, ∃ r : ℂ, ValAt ξ z (y ⟨k, c₀ k⟩ / y ⟨k, c₁ k⟩) r ∧ w ⟨k, c₀ k⟩ = r * w ⟨k, c₁ k⟩ :=
    fun k => (hw.2 k (c₁ k) (isUnit_iff_ne_zero.2 (h₁ k))).2 (c₀ k)
  choose r hrv hrw using hr
  have hr0 : ∀ k, r k ≠ 0 := fun k hk => h₀ k (by rw [hrw k, hk, zero_mul])
  have hprod : ∀ s : Finset K, ValAt ξ z (∏ k ∈ s, (y ⟨k, c₀ k⟩ / y ⟨k, c₁ k⟩) ^ a k) (∏ k ∈ s, r k ^ a k) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using val_one hz
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.prod_insert hk]
      exact val_mul (val_zpow (hr0 k) (hrv k) (a k)) ih
  have hg₀ : (∏ k, y ⟨k, c₀ k⟩ ^ a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy₀ k)
  have hg₁ : (∏ k, y ⟨k, c₁ k⟩ ^ a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy₁ k)
  have hΩ : τ / gen y a e₀ c₁ = (τ / gen y a e₀ c₀) * ∏ k, (y ⟨k, c₀ k⟩ / y ⟨k, c₁ k⟩) ^ a k := by
    have : ∏ k, (y ⟨k, c₀ k⟩ / y ⟨k, c₁ k⟩) ^ a k = (∏ k, y ⟨k, c₀ k⟩ ^ a k) / ∏ k, y ⟨k, c₁ k⟩ ^ a k := by
      rw [← Finset.prod_div_distrib]
      exact Finset.prod_congr rfl fun k _ => div_zpow _ _ _
    rw [this]
    unfold gen
    field_simp
  have hval : u' = u * ∏ k, r k ^ a k := by
    have h := val_mul hu (hprod Finset.univ)
    rw [← hΩ] at h
    exact val_unique hξ hu' h
  have hw₀ : ∏ k, w ⟨k, c₀ k⟩ ^ a k = (∏ k, r k ^ a k) * ∏ k, w ⟨k, c₁ k⟩ ^ a k := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [hrw k, mul_zpow]
  rw [hw₀, hval, _root_.mul_assoc]

end GlobalTheory.CompanionTheory.Ar.RootHt.ArchB
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.OverVal

theorem closedPoint_germ_const {X : Scheme.{0}} {F : Type} [Field F] {O : Type} [CommRing O]
    (s : X ⟶ Spec (CommRingCat.of O)) (z : Spec (CommRingCat.of F) ⟶ X) (φ : O →+* F)
    (hz : z ≫ s = Spec.map (CommRingCat.ofHom φ)) (o : O) :
    (Scheme.stalkClosedPointTo z).hom ((X.presheaf.germ ⊤ (centre z) trivial).hom
      (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) = φ o := by
  letI : Algebra O F := φ.toAlgebra
  have h := GlobalTheory.CompanionTheory.Ar.Flat.ConstReg.genMap_germ_const z s hz ⟨genPt z, specializes_rfl⟩ o
  have e : genMap z ⟨genPt z, specializes_rfl⟩ = (Scheme.stalkClosedPointTo z).hom := by
    ext t
    simp only [genMap, TopCat.Presheaf.stalkSpecializes_refl]
    exact congrArg (fun q : X.presheaf.stalk (genPt z) ⟶ CommRingCat.of F => q.hom t)
      (Category.id_comp (Scheme.stalkClosedPointTo z))
  rw [e] at h
  exact h

theorem val_const {X : Scheme.{0}} {Ω : Type} [Field Ω] {F : Type} [Field F] {O : Type} [CommRing O]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (all : ∀ q : X, genPt ξ ⤳ q)
    (s : X ⟶ Spec (CommRingCat.of O)) (ψ : O →+* Ω)
    (hs : ξ ≫ s = Spec.map (CommRingCat.ofHom ψ))
    (z : Spec (CommRingCat.of F) ⟶ X) (φ : O →+* F)
    (hz : z ≫ s = Spec.map (CommRingCat.ofHom φ)) (o : O) : ValAt ξ z (ψ o) (φ o) := by
  letI : Algebra O Ω := ψ.toAlgebra
  exact ⟨all _, _, GlobalTheory.CompanionTheory.Ar.Flat.ConstReg.genMap_germ_const ξ s hs ⟨centre z, all _⟩ o, closedPoint_germ_const s z φ hz o⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.OverVal

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

open GlobalTheory.CompanionTheory.Ar.RootHt.ArchB OverVal

theorem isOver_base {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
    {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω]
    {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {𝔐 : HodgeCpt Y S y} {z : Sp ℂ ⟶ 𝔐.X} {κ : c.F →+* ℂ}
    {p : Sp ℂ ⟶ Xo.X} (h : IsOver 𝔐 z κ p) :
    z ≫ 𝔐.f ≫ Y.s = spMap (κ.comp (algebraMap (𝓞 c.F) c.F)) := by
  obtain ⟨x, hx, -, hk⟩ := h
  have h1 : z ≫ 𝔐.f ≫ Y.s = x ≫ Y.j ≫ Y.s := by
    rw [← Category.assoc, ← hx, Category.assoc]
  rw [h1, Model.j, Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc, hk]
  exact (Spec.map_comp _ _).symm

theorem val_cst : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X) (κ : c.F →+* ℂ) (p : Sp ℂ ⟶ Xo.X), IsOver 𝔐 z κ p → ∀ x : c.F, ValAt 𝔐.ξ z (𝔐.cst x) (κ x) := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 z κ p h x
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  have hc : ∀ o : 𝓞 c.F, ValAt 𝔐.ξ z (𝔐.cst (algebraMap (𝓞 c.F) c.F o)) (κ (algebraMap (𝓞 c.F) c.F o)) := fun o =>
    val_const 𝔐.ξ 𝔐.all (𝔐.f ≫ Y.s) (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) 𝔐.cst_over z
      (κ.comp (algebraMap (𝓞 c.F) c.F)) (isOver_base h) o
  obtain ⟨a, n, hn, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 c.F) x
  have hn0 : algebraMap (𝓞 c.F) c.F n ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 c.F) c.F)).2 (nonZeroDivisors.ne_zero hn)
  have hk0 : κ (algebraMap (𝓞 c.F) c.F n) ≠ 0 := (map_ne_zero κ).2 hn0
  rw [map_div₀, map_div₀, div_eq_mul_inv, div_eq_mul_inv]
  exact val_mul (hc a) (by simpa only [map_inv₀] using val_inv₀ hk0 (hc n))

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights


theorem _root_.GlobalTheory.T.local_ratio_product_formula : ∀ (L : Type) [Field L] [NumberField L] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (a : K → ℤ) (w : (Σ k, J k) → L) (c₀ : (k : K) → J k) (u : L),
    (∀ k, ∃ c, w ⟨k, c⟩ ≠ 0) → (∀ k, w ⟨k, c₀ k⟩ ≠ 0) → u ≠ 0 →
    (∀ v, 0 < locRatio a w c₀ v) ∧ (Function.mulSupport (locRatio a w c₀)).Finite ∧
    ∑ᶠ v : FinitePlace L, (Real.log (locRatio a w c₀ v) - Real.log (v u)) =
      (∑ᶠ v : FinitePlace L, ∑ k, (a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩))) +
        ∑ σ : L →+* ℂ, (Real.log ‖σ u‖ + ∑ k, (a k : ℝ) * Real.log ‖σ (w ⟨k, c₀ k⟩)‖) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.RatioSum.ratio_sum | exact GlobalTheory.CompanionTheory.Ar.RootHt.RatioSum.ratio_sum | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.RatioSum.ratio_sum <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lie_model_projective_generic_fibre : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X) (V : Type) [AddCommGroup V] [Module (𝓞 L) V] [Module.Finite (𝓞 L) V] [Module.Projective (𝓞 L) V] (MB : LieModel G z V) (T : Type) [AddCommGroup T] [Module L T] [Module (𝓞 L) T] [IsScalarTower (𝓞 L) L T] (TL : LieModel G (spMap (algebraMap (𝓞 L) L) ≫ z) T) (j : V →ₗ[𝓞 L] T) (U : Submodule Ω Li), IsCptGen ξ → (∀ x, ((TL.pt (j x)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt x).left)) → IsBaseChange L j → Module.finrank (𝓞 L) V = Module.finrank L T ∧ Module.finrank (𝓞 L) (FlagFib.subFib M U z MB) = Module.finrank L (Submodule.span L {w | ∃ e ∈ U, M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (TL.pt w)}) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagFib.Bridge.finrank_subFib | exact GlobalTheory.CompanionTheory.Ar.FlagFib.Bridge.finrank_subFib | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagFib.Bridge.finrank_subFib <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

theorem _root_.GlobalTheory.T.stable_eigen_tangents_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : Type) [CommRing T] (y : Sp T ⟶ Xo.XF c) (A : Type) [CommRing A] (x₀ : Sp A ⟶ Y.X) (κ : c.F →+* A) (θ : A →+* T) (σ : E →+* ℂ) (r : ℕ) (e : Fin r → (epsAt x₀ ⟶ Y.t.G)), spMap θ ≫ x₀ = y ≫ Y.j → StableEig Y.t x₀ κ σ e → ∃ V : Fin r → (epsAt (under y) ⟶ Xo.univ.t.G), (∀ i, Tied Y y (V i).left (spMap (Formalism.L2.Pj.dualMap θ) ≫ (e i).left)) ∧ IsEigFrame Xo.univ.t.act (under y) ((θ.comp κ).comp (tauIn c σ)) V := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFn.exists_eigFrame_univ | exact GlobalTheory.CompanionTheory.Ar.LocFn.exists_eigFrame_univ | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFn.exists_eigFrame_univ <;> assumption)
end

section

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

theorem _root_.GlobalTheory.T.homog_relation_ratio_reindex : ∀ (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (i : Ω₀ →+* Ω) (q r : Σ k, J k) (n : ℕ) (c : ℕ → MRing J₀) (a : K₀ → ℕ), (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → q.1 = r.1 → y r ≠ 0 → (∀ j, IsMultiHomog (c j) a) → (∑ j ∈ Finset.range (n + 1), i (aeval y₀ (c j)) * (y q / y r) ^ j = 0) → ∀ z ∈ mcPts (mCoordIdeal y), z r ≠ 0 → ∀ w : (Σ k, J₀ k) → ℂ, SameOrbit (fun p => z (GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx p)) w → ∑ j ∈ Finset.range (n + 1), eval w (map (Int.castRingHom ℂ) (c j)) * (z q / z r) ^ j = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rel.ratio_relation_at_complex_points | exact GlobalTheory.CompanionTheory.Ar.Rel.ratio_relation_at_complex_points | (intros; apply GlobalTheory.CompanionTheory.Ar.Rel.ratio_relation_at_complex_points <;> assumption)
end
