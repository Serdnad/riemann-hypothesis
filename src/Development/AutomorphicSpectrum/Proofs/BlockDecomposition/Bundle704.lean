module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.Bundle001
public import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle556
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle531
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobiMapsExist
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHolds
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.EisE

variable {D : D7} {n r t a b : ℕ}

theorem good_rows {S : Finset (Pl D)} {e : AE D} {η : Fin a → Mx D 1 b → ℂ} (h : ∀ i, Good S e (η i)) :
    Good S e (fun y : Mx D a b => ∏ i, η i (y.submatrix (fun _ => i) id)) := by
  intro y
  by_cases hy : IntOff S y
  · rw [if_pos hy]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hi : IntOff S (y.submatrix (fun _ : Fin 1 => i) id) := fun v hv _ j => hy v hv i j
    have := h i (y.submatrix (fun _ : Fin 1 => i) id)
    rw [if_pos hi] at this
    exact this
  · rw [if_neg hy]
    simp only [IntOff] at hy
    push Not at hy
    obtain ⟨v, hv, i, j, hij⟩ := hy
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    have := h i (y.submatrix (fun _ : Fin 1 => i) id)
    rw [if_neg (fun hi => hij (hi v hv 0 j))] at this
    exact this

theorem prod_nonneg_real {ι : Type} (s : Finset ι) (w : ι → ℂ) (h : ∀ i, 0 ≤ (w i).re ∧ (w i).im = 0) :
    0 ≤ (∏ i ∈ s, w i).re ∧ (∏ i ∈ s, w i).im = 0 := by
  refine Finset.prod_induction w (fun x : ℂ => 0 ≤ x.re ∧ x.im = 0) ?_ (by simp) fun i _ => h i
  rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
  simp [Complex.mul_re, Complex.mul_im, hx', hy', mul_nonneg hx hy]

theorem blockMatrix_add_zero {R : Type} (A : Matrix (Fin t) (Fin t) R) (b' : Matrix (Fin t) (Fin 0) R) (c : Matrix (Fin 0) (Fin t) R)
    (d : Matrix (Fin 0) (Fin 0) R) : bl (add_zero t) A b' c d = A := by
  have h : ∀ i : Fin t, (finSumFinEquiv.trans (finCongr (add_zero t))).symm i = Sum.inl i := by
    intro i
    rw [Equiv.symm_apply_eq]
    ext
    simp only [Equiv.trans_apply, finSumFinEquiv_apply_left]
    rfl
  ext i j
  simp only [bl, Matrix.submatrix_apply, h, Matrix.fromBlocks_apply₁₁]

theorem exists_isW (D : D7) (t : ℕ) : ∃ w : G D t, IsW w := by
  obtain ⟨⟨M⟩, -⟩ := GlobalTheory.CompanionTheory.JacobiMaps.mapsExist D t t 0 (add_zero t)
  refine ⟨M.w, ?_⟩
  have := M.w_mat
  simp only [blockMatrix_add_zero] at this
  exact this

theorem rsec_inv {hn : r + t = n} (M : Maps D hn) (m : Meas D r t) (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D r)
    {θ : InfFam D} (ω : G D n →* Module.End ℂ (schwartzA θ a n)) (Φ : schwartzA θ a n) {Ω : G D t → Mx D r t → ℂ} (u : G D t)
    (h1 : ω (M.emb u) Φ = Φ) (h2 : ∀ h, Ω (h * u) = Ω h) (g : G D t) :
    Rsec M m ψ b₀ (fun g => (ω g Φ).1 0) 1 Ω (g * u) = Rsec M m ψ b₀ (fun g => (ω g Φ).1 0) 1 Ω g := by
  have hf : ∀ x, (ω (x * M.emb u) Φ).1 0 = (ω x Φ).1 0 := fun x => by
    rw [map_mul, Module.End.mul_apply, h1]
  have e1 : ∀ y z, M.w * M.nzx z 0 * (M.sh y * M.emb (g * u) * 1) =
      (M.w * M.nzx z 0 * (M.sh y * M.emb g * 1)) * M.emb u := fun y z => by
    rw [map_mul]
    simp only [mul_one, mul_assoc]
  simp only [Rsec, Wz, h2, e1, hf]

section Xi

variable (V : HSp D) (b₀ : HermE D r) (hn : r + t = n)

def xiP (Φ : Mx D V.rank n → ℂ) (η : Mx D r t → ℂ) (z : Mx D V.rank r × Mx D V.rank t) : ℂ :=
  Φ (jn hn z.1 z.2) * conj (η (yv V b₀ z))

variable {V b₀ hn}

theorem continuous_xiP {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {Φ : Mx D V.rank n → ℂ} {η : Mx D r t → ℂ}
    (hΦ : Continuous Φ) (hη : Continuous η) : Continuous (xiP V b₀ hn Φ η) := by
  have hy := (GlobalTheory.CompanionTheory.RCellCont.continuity_characters_projection (t := t) hψ V b₀ (0 : hermA D t)).2.1
  exact (hΦ.comp (continuous_jn hn)).mul (Complex.continuous_conj.comp (hη.comp hy))

theorem xiP_cond {S : Finset (Pl D)} {e : AE D} (he : e * e = e) (hc : cA D e = e) {Φ : Mx D V.rank n → ℂ} {η : Mx D r t → ℂ}
    (hΦ : Good S e Φ) (hη : Good S e η)
    (hy : ∀ z : Mx D V.rank r × Mx D V.rank t, IntOff S z.1 → IntOff S z.2 → IntOff S (yv V b₀ z))
    (p : Mx D V.rank r × Mx D V.rank t → ℂ) (hp : ∀ z, p (e • z.1, e • z.2) = p z) (z : Mx D V.rank r × Mx D V.rank t) :
    (IntOff S z.1 ∧ IntOff S z.2 → xiP V b₀ hn Φ η z * p z = xiP V b₀ hn Φ η (e • z.1, e • z.2) * p (e • z.1, e • z.2)) ∧
      (¬ (IntOff S z.1 ∧ IntOff S z.2) → xiP V b₀ hn Φ η z * p z = 0) := by
  refine ⟨fun ⟨h1, h2⟩ => ?_, fun h => ?_⟩
  · have a1 := hΦ (jn hn z.1 z.2)
    rw [if_pos ((intOff_jn hn _ _).2 ⟨h1, h2⟩), jn_smul] at a1
    have a2 := hη (yv V b₀ z)
    rw [if_pos (hy z h1 h2), ← yv_smul he hc] at a2
    rw [hp]
    simp only [xiP]
    rw [a1, a2]
  · have a1 := hΦ (jn hn z.1 z.2)
    rw [if_neg (fun hh => h ((intOff_jn hn _ _).1 hh))] at a1
    simp [xiP, a1]



theorem cell_id {S : Finset (Pl D)} {e : AE D} (he : e * e = e) (hc : cA D e = e) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsCharAF D.host.F ψ) [BorelSpace (Mx D V.rank r × Mx D V.rank t)]
    {P : Measure (Mx D V.rank r × Mx D V.rank t)} {σ : Measure (XS D V.rank r t e)}
    (hL : ∀ Ξ : Mx D V.rank r × Mx D V.rank t → ℂ, Continuous Ξ →
      (∀ z, (IntOff S z.1 ∧ IntOff S z.2 → Ξ z = Ξ (e • z.1, e • z.2)) ∧ (¬ (IntOff S z.1 ∧ IntOff S z.2) → Ξ z = 0)) →
      (Integrable Ξ P → Integrable (fun z : XS D V.rank r t e => Ξ z.1) σ) ∧ ∫ z, Ξ z ∂P = ∫ z : XS D V.rank r t e, Ξ z.1 ∂σ)
    (hy : ∀ z : Mx D V.rank r × Mx D V.rank t, IntOff S z.1 → IntOff S z.2 → IntOff S (yv V b₀ z))
    {Φ : Mx D V.rank n → ℂ} {η : Mx D r t → ℂ} (hΦc : Continuous Φ) (hηc : Continuous η) (hΦ : Good S e Φ) (hη : Good S e η)
    {B : ℝ} (hB : ∀ y, ‖η y‖ ≤ B) (hI : Integrable (fun z : Mx D V.rank r × Mx D V.rank t => Φ (jn hn z.1 z.2)) P) :
    Integrable (fun z : XS D V.rank r t e => xiP V b₀ hn Φ η z.1) σ ∧
      ∀ x : hermS D t e, ∫ z, xiP V b₀ hn Φ η z * pch ψ x.1.1 (qv V b₀ z) ∂P =
        ∫ z : XS D V.rank r t e, xiP V b₀ hn Φ η z.1 * pch ψ x.1.1 (qv V b₀ z.1) ∂σ := by
  have hx := continuous_xiP (b₀ := b₀) (hn := hn) hψ hΦc hηc
  haveI : OpensMeasurableSpace (Mx D V.rank r × Mx D V.rank t) := BorelSpace.opensMeasurable
  constructor
  · have hc1 := xiP_cond (hn := hn) he hc hΦ hη hy (fun _ => 1) (fun _ => rfl)
    simp only [mul_one] at hc1
    refine (hL _ hx hc1).1 ?_
    refine (hI.norm.const_mul B).mono' hx.aestronglyMeasurable (ae_of_all _ fun z => ?_)
    simp only [xiP, norm_mul, RCLike.norm_conj]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
  · intro x
    have hcp := (GlobalTheory.CompanionTheory.RCellCont.continuity_characters_projection (t := t) hψ V b₀ x.1).2.2.2.1
    refine (hL (fun z => xiP V b₀ hn Φ η z * pch ψ x.1.1 (qv V b₀ z)) (hx.mul hcp) ?_).2
    refine xiP_cond (hn := hn) he hc hΦ hη hy _ fun z => ?_
    rw [qv_smul he hc]
    exact pch_smul x.2 _

end Xi

end GlobalTheory.CompanionTheory.EisE

end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.FJE




theorem Wz_stronglyMeasurable : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (f : G D n → ℂ), Continuous f → ∀ {X : Type} [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (c : X → G D n), Continuous c → StronglyMeasurable fun v => Wz M m ψ b₀ f (c v) := by
  intro D n ρ p hn M m ψ hψ b₀ f hf X _ _ _ _ c hc
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D ρ ρ
  haveI : IsTopologicalAddGroup (Mx D ρ ρ) := i1
  haveI : LocallyCompactSpace (Mx D ρ ρ) := i2
  haveI : SecondCountableTopology (Mx D ρ ρ) := i3
  haveI : T2Space (Mx D ρ ρ) := i4
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : BorelSpace (hermA D ρ) := Subtype.borelSpace _
  haveI : SecondCountableTopology (hermA D ρ) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (hermA D ρ) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : LocallyCompactSpace (hermA D ρ) :=
    (GlobalTheory.CompanionTheory.FourierN.isClosed_hermA (D := D) (n := ρ)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI := m.hz.1
  haveI : SFinite m.lz := inferInstance
  have hchz : Continuous fun z : hermA D ρ => conj (chz ψ b₀ z) :=
    Complex.continuous_conj.comp
      (hψ.1.comp ((GlobalTheory.CompanionTheory.FourierN.continuous_pr b₀.1).comp continuous_subtype_val))
  have hcont : Continuous fun u : X × hermA D ρ => f (M.w * M.nzx u.2 0 * c u.1) * conj (chz ψ b₀ u.2) := by
    refine (hf.comp ((continuous_const.mul ?_).mul (hc.comp continuous_fst))).mul (hchz.comp continuous_snd)
    exact M.nzx_cont.comp (continuous_snd.prodMk continuous_const)
  exact hcont.stronglyMeasurable.integral_prod_right

end GlobalTheory.CompanionTheory.FJE
end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PcAdd

theorem iterated_sub {Z X : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    [TopologicalSpace X] [FirstCountableTopology X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (l : Measure Z) (u : Measure X) [IsFiniteMeasure l] [IsFiniteMeasure u] (a b : X → Z → ℂ) (A B : ℝ)
    (ha : ∀ x, Continuous (a x)) (hb : ∀ x, Continuous (b x))
    (ha' : ∀ z, Continuous fun x => a x z) (hb' : ∀ z, Continuous fun x => b x z)
    (hA : ∀ x z, ‖a x z‖ ≤ A) (hB : ∀ x z, ‖b x z‖ ≤ B) :
    ∫ x, ∫ z, (a x z - b x z) ∂l ∂u = (∫ x, ∫ z, a x z ∂l ∂u) - ∫ x, ∫ z, b x z ∂l ∂u := by
  have key : ∀ c : X → Z → ℂ, ∀ C : ℝ, (∀ x, Continuous (c x)) → (∀ z, Continuous fun x => c x z) →
      (∀ x z, ‖c x z‖ ≤ C) → (∀ x, Integrable (c x) l) ∧ Integrable (fun x => ∫ z, c x z ∂l) u := by
    intro c C hc hc' hC
    have hi : ∀ x, Integrable (c x) l := fun x =>
      Integrable.of_bound (hc x).aestronglyMeasurable C (Eventually.of_forall (hC x))
    refine ⟨hi, ?_⟩
    have hcont : Continuous fun x => ∫ z, c x z ∂l :=
      continuous_of_dominated (bound := fun _ => C) (fun x => (hc x).aestronglyMeasurable)
        (fun x => Eventually.of_forall (hC x)) (integrable_const C) (Eventually.of_forall hc')
    refine Integrable.of_bound hcont.aestronglyMeasurable (C * l.real Set.univ)
      (Eventually.of_forall fun x => ?_)
    exact norm_integral_le_of_norm_le_const (Eventually.of_forall (hC x))
  obtain ⟨i1, j1⟩ := key a A ha ha' hA
  obtain ⟨i2, j2⟩ := key b B hb hb' hB
  rw [← integral_sub j1 j2]
  exact integral_congr_ae (Eventually.of_forall fun x => integral_sub (i1 x) (i2 x))

theorem firstCountable_of_second (X : Type*) [TopologicalSpace X] [SecondCountableTopology X] :
    FirstCountableTopology X := inferInstance

theorem pc_sub : PcBound → ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p)
    (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (F F' : G D n → ℂ), Continuous F →
    LeftInv (GF D n) F → Continuous F' → LeftInv (GF D n) F' → ∀ (y : Mx D ρ p) (g : G D n),
    pc M m ψ b₀ (F - F') (M.sh y * g) = pc M m ψ b₀ F (M.sh y * g) - pc M m ψ b₀ F' (M.sh y * g) := by
  intro hP D n ρ p hn M m ψ hψ b₀ F F' hF hFi hF' hFi' y g
  obtain ⟨C, hC, hCm, -⟩ := (hP D n ρ p hn M m ψ hψ b₀).2 (g)
  haveI : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : BorelSpace (hermA D ρ) := Subtype.borelSpace _
  haveI : SecondCountableTopology (Mx D ρ p) := (GlobalTheory.MixModel.lattice_Mx D ρ p).2.2.1
  haveI : FirstCountableTopology (Mx D ρ p) := firstCountable_of_second _
  haveI h1 : IsFiniteMeasure (m.lz.restrict m.𝓖) :=
    ⟨by rw [Measure.restrict_apply_univ, m.hz.2.2]; exact ENNReal.one_lt_top⟩
  haveI h2 : IsFiniteMeasure (m.μ.restrict m.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, m.hμ.2.2]; exact ENNReal.one_lt_top⟩
  have hchz : Continuous fun z : hermA D ρ => conj (chz ψ b₀ z) :=
    Complex.continuous_conj.comp
      (hψ.1.comp ((GlobalTheory.CompanionTheory.FourierN.continuous_pr b₀.1).comp continuous_subtype_val))
  have hnorm : ∀ z, ‖conj (chz ψ b₀ z)‖ = 1 := fun z => by
    rw [RCLike.norm_conj]
    exact hψ.2.1 _
  have hz : ∀ x, Continuous fun z : hermA D ρ => M.nzx z 0 * (M.nzx 0 x * (M.sh y * g)) := fun x =>
    (M.nzx_cont.comp (continuous_id.prodMk continuous_const)).mul continuous_const
  have hx : ∀ z, Continuous fun x : Mx D ρ p => M.nzx z 0 * (M.nzx 0 x * (M.sh y * g)) := fun z =>
    continuous_const.mul ((M.nzx_cont.comp (continuous_const.prodMk continuous_id)).mul continuous_const)
  have bd : ∀ Φ : G D n → ℂ, Continuous Φ → LeftInv (GF D n) Φ →
      ∃ B : ℝ, ∀ x z, ‖Φ (M.nzx z 0 * (M.nzx 0 x * (M.sh y * g))) * conj (chz ψ b₀ z)‖ ≤ B := by
    intro Φ hΦ hi
    obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hΦ.continuousOn
    refine ⟨B, fun x z => ?_⟩
    obtain ⟨γ, hγ, hc⟩ := hCm z x y
    rw [norm_mul, hnorm, mul_one, ← hi γ hγ]
    exact hB _ hc
  obtain ⟨A, hA⟩ := bd F hF hFi
  obtain ⟨B, hB⟩ := bd F' hF' hFi'
  have key := iterated_sub (m.lz.restrict m.𝓖) (m.μ.restrict m.𝓕)
    (fun x z => F (M.nzx z 0 * (M.nzx 0 x * (M.sh y * g))) * conj (chz ψ b₀ z))
    (fun x z => F' (M.nzx z 0 * (M.nzx 0 x * (M.sh y * g))) * conj (chz ψ b₀ z)) A B
    (fun x => (hF.comp (hz x)).mul hchz) (fun x => (hF'.comp (hz x)).mul hchz)
    (fun z => (hF.comp (hx z)).mul continuous_const) (fun z => (hF'.comp (hx z)).mul continuous_const) hA hB
  simp only [PositivityTheory.Rg.Rsw.pc, PositivityTheory.Rg.Rsw.zc, Pi.sub_apply, sub_mul]
  exact key

end GlobalTheory.CompanionTheory.PcAdd

end
end

section

open PositivityTheory.Rg.Rsw

theorem _root_.GlobalTheory.T.jacobi_maps_exist : MapsExist := by
  first | exact @GlobalTheory.CompanionTheory.JacobiMaps.mapsExist | exact GlobalTheory.CompanionTheory.JacobiMaps.mapsExist | (intros; apply GlobalTheory.CompanionTheory.JacobiMaps.mapsExist <;> assumption)
end
