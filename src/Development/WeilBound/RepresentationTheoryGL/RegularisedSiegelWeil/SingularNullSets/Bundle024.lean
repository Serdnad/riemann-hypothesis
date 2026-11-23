module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle273
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle093
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHolds
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCutIdA
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle502
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle352
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle701
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle702
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle023
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF

@[expose] public section

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LCutId

variable {D : D7} {n : ℕ}

theorem omega_fix {W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ θ} {μ : Measure (Mx D W.rank n)}
    {ω : G D n →* Module.End ℂ (schwartzA θ W.rank n)} (hω : IsWeilSch ψ χ θ W μ ω)
    {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D} (Ψ : schwartzA θ W.rank n) (hΨ : ∀ k ∈ KAt D n v, ω k Ψ = Ψ)
    {g : G D n} (hg : proj D.sp.cm.sig (Jst D n) v g = 1) {y : hermA D n} (hy : IntAt v y) (X : Mx D W.rank n) :
    (ω g Ψ).1 X = pch ψ y.1 (ip W X X) * (ω g Ψ).1 X := by
  have e1 : ω (nb y * g) Ψ = ω g Ψ := by
    rw [nb_comm hnb hy.1 hy.2.1 hg, map_mul, Module.End.mul_apply, hΨ _ (nb_mem_KAt hnb hy)]
  have e2 := hω.unip (nb y) y.1 (hnb y) (ω g Ψ) X
  rw [map_mul, Module.End.mul_apply] at e1
  rw [e1] at e2
  exact e2

theorem ip_orbit (W : HSp D) (h : GA D W) (x : Matrix (Fin W.rank) (Fin n) D.host.E) :
    ip W (mm (Formalism.L2.Theta.mt W h) (rat x)) (mm (Formalism.L2.Theta.mt W h) (rat x)) = rat (gramQ W x) := by
  rw [show gramQ W x = GlobalTheory.Unf.gramQ W x from rfl, GlobalTheory.Unf.FB.rat_gramQ]
  simp only [ip, mm]
  rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA W) (Formalism.L2.Theta.mt W h),
    ← Matrix.mul_assoc (adj (Formalism.L2.Theta.mt W h)), GlobalTheory.MixModel.mt_unitary]

theorem rank_gram_le (W : HSp D) (x : Matrix (Fin W.rank) (Fin n) D.host.E) : (gramQ W x).rank ≤ x.rank := by
  exact (Matrix.rank_mul_le_right _ _).trans (Matrix.rank_mul_le_right _ _)

theorem law0 {B : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ θ} {μ : Measure (Mx D B.rank n)}
    {ω : G D n →* Module.End ℂ (schwartzA θ B.rank n)} (hω : IsWeilSch ψ χ θ B μ ω)
    (Φ : schwartzA θ B.rank n) (s : ℂ) (hs : (B.rank : ℂ) / 2 = s + (n : ℂ) / 2) :
    IsLaw χ s (fun g => (ω g Φ).1 0) := by
  intro q hq a ha g
  obtain ⟨m, u, b, e, hm, hu⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_levi_unip hq a ha
  show (ω (q * g) Φ).1 0 = _ * _ * (ω g Φ).1 0
  have e' : ω (q * g) Φ = ω m (ω u (ω g Φ)) := by
    rw [e, map_mul, map_mul]; rfl
  have z1 : ∀ a : Mx D n n, ((0 : Mx D B.rank n) ⬝ a : Mx D B.rank n) = 0 := fun a => Matrix.zero_mul a
  have z2 : GlobalTheory.StdUnn.inner B (0 : Mx D B.rank n) 0 = 0 := by rw [GlobalTheory.StdUnn.inner, adj_zero, Matrix.zero_mul]
  rw [e', hω.levi m a hm, z1, hω.unip u b hu, z2, ← hs]
  simp [halfTr]

theorem resEta_add {χ : (AE D)ˣ →* Circle} {r : ℕ} (h : ResEta D χ r) (k : ℕ) : ResEta D χ (r + 2 * k) :=
  ⟨h.1, fun η hη a => by rw [h.2 η hη a, pow_add, pow_mul, Formalism.L2.Theta.eta_sq hη a, one_pow, mul_one]⟩

theorem conj_pch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (x : hermA D n) (β : HermE D n) :
    conj (pch ψ x.1 (rat β.1)) = ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) x.1 : Mx D n n))) := by
  have ht : Matrix.trace (mm x.1 (rat β.1)) =
      Matrix.trace (HMul.hMul (β.1.map (incA D)) x.1 : Mx D n n) :=
    Matrix.trace_mul_comm _ _
  change conj (ψ (halfTr (Matrix.trace (mm x.1 (rat β.1))))) = _
  rw [ht, AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.2.1 _)]

theorem fc_eq {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (lam : Measure (hermA D n)) (𝓖 : Set (hermA D n))
    (nb : hermA D n → G D n) (F : G D n → ℂ) (β : HermE D n) (g : G D n) :
    fc ψ lam 𝓖 nb F β g = ∫ x in 𝓖, F (nb x * g) * conj (pch ψ x.1 (rat β.1)) ∂lam := by
  change (∫ b in 𝓖, F (nb b * g) * ψ (-halfTr ((β.1.map (incA D) * b.1).trace)) ∂lam) = _
  congr 1
  funext x
  rw [conj_pch hψ]

theorem cont_conj_pch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (β : HermE D n) :
    Continuous fun x : hermA D n => conj (pch ψ x.1 (rat β.1)) :=
  Complex.continuous_conj.comp (hψ.1.comp (GlobalTheory.CompanionTheory.FourierN.continuous_halfTr.comp
    ((continuous_subtype_val.matrix_mul continuous_const).matrix_trace)))

theorem norm_conj_pch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (x : hermA D n) (β : HermE D n) :
    ‖conj (pch ψ x.1 (rat β.1))‖ ≤ 1 := by
  rw [Complex.norm_conj]
  exact (hψ.2.1 _).le

theorem intOn {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} (h : IsCovolOneH lam 𝓖) {f c : hermA D n → ℂ}
    (hf : Continuous f) (hp : ∀ γ ∈ ratHerm D n, ∀ x, f (γ + x) = f x) (hc : Continuous c) (hc1 : ∀ x, ‖c x‖ ≤ 1) :
    IntegrableOn (fun x => f x * c x) 𝓖 lam := by
  haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
  haveI : BorelSpace (hermA D n) := Subtype.borelSpace _
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.CompanionTheory.FourierN.exists_compact_cover (D := D) (n := n)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  have hb : ∀ x, ‖f x * c x‖ ≤ M := fun x => by
    obtain ⟨γ, hγ, hx⟩ := hcov x
    rw [norm_mul, ← hp γ hγ x]
    calc ‖f (γ + x)‖ * ‖c x‖ ≤ ‖f (γ + x)‖ * 1 := mul_le_mul_of_nonneg_left (hc1 x) (norm_nonneg _)
      _ ≤ M := by rw [mul_one]; exact hM _ hx
  refine Measure.integrableOn_of_bounded (M := M) ?_ (hf.mul hc).aestronglyMeasurable ?_
  · rw [h.2.2]; exact ENNReal.one_ne_top
  · exact Eventually.of_forall hb

end PositivityTheory.Rg.Rsw.L.LCutId

end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LCutLow

open GlobalTheory.CompanionTheory.PcFc (chn)

variable {D : D7} {n : ℕ}

theorem chn_eq (ψ : AddChar (AF D.host.F) ℂ) (β : HermE D n) (b : hermA D n) :
    chn ψ β b = ψ (-GlobalTheory.CompanionTheory.FourierN.pr β.1 b.1) := rfl

theorem chn_cont {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (β : HermE D n) : Continuous (chn ψ β) :=
  hψ.1.comp ((GlobalTheory.CompanionTheory.FourierN.continuous_pr β.1).neg.comp continuous_subtype_val)

theorem chn_per {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (β : HermE D n) (γ : hermA D n)
    (hγ : γ ∈ ratHerm D n) (x : hermA D n) : chn ψ β (γ + x) = chn ψ β x := by
  rw [chn_eq, chn_eq, show (γ + x).1 = γ.1 + x.1 from rfl, GlobalTheory.CompanionTheory.FourierN.pr_add_right, neg_add, AddChar.map_add_eq_mul,
    GlobalTheory.CompanionTheory.FourierN.ker_of_rat hψ γ hγ, one_mul]

theorem per_nb {F : G D n → ℂ} (hinv : LeftInv (GF D n) F) {nb : hermA D n → G D n} (hnb : IsNMap nb) (g : G D n)
    (γ : hermA D n) (hγ : γ ∈ ratHerm D n) (x : hermA D n) : F (nb (γ + x) * g) = F (nb x * g) := by
  rw [GlobalTheory.CompanionTheory.FourierN.nb_add hnb, mul_assoc]
  exact hinv _ (GlobalTheory.CompanionTheory.FourierN.nb_rat hnb γ hγ) _

theorem cont_nb {F : G D n → ℂ} (hF : Continuous F) {nb : hermA D n → G D n} (hnb : IsNMap nb) (g : G D n) :
    Continuous (fun b => F (nb b * g)) :=
  hF.comp ((GlobalTheory.CompanionTheory.FourierN.continuous_nb hnb).mul continuous_const)

theorem pch_rat (ψ : AddChar (AF D.host.F) ℂ) (x : Mx D n n) (β : HermE D n) :
    pch ψ x (rat β.1) = ψ (GlobalTheory.CompanionTheory.FourierN.pr β.1 x) := by
  show ψ (halfTr (Matrix.trace (x * β.1.map (incA D)))) = ψ (halfTr (Matrix.trace (β.1.map (incA D) * x)))
  rw [Matrix.trace_mul_comm]

theorem fc_eq (ψ : AddChar (AF D.host.F) ℂ) (lam : Measure (hermA D n)) (𝓖 : Set (hermA D n)) (nb : hermA D n → G D n)
    (F : G D n → ℂ) (β : HermE D n) (g : G D n) :
    fc ψ lam 𝓖 nb F β g = ∫ b in 𝓖, F (nb b * g) * chn ψ β b ∂lam := rfl

theorem chn_shift (ψ : AddChar (AF D.host.F) ℂ) (β : HermE D n) (b x : hermA D n) :
    chn ψ β b = chn ψ β (b + x) * pch ψ x.1 (rat β.1) := by
  rw [chn_eq, chn_eq, pch_rat, ← AddChar.map_add_eq_mul]
  congr 1
  rw [show (b + x).1 = b.1 + x.1 from rfl, GlobalTheory.CompanionTheory.FourierN.pr_add_right]
  abel


theorem fc_nb_mul {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {nb : hermA D n → G D n}
    {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} (hC : CoefData (D := D) (n := n) nb lam 𝓖) {F : G D n → ℂ}
    (hinv : LeftInv (GF D n) F) (β : HermE D n) (x : hermA D n) (g : G D n) :
    fc ψ lam 𝓖 nb F β (nb x * g) = pch ψ x.1 (rat β.1) * fc ψ lam 𝓖 nb F β g := by
  obtain ⟨hnb, hlam, hFD, -⟩ := hC
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D n n
  have : BorelSpace (Mx D n n) := ⟨rfl⟩
  have : BorelSpace (hermA D n) := Subtype.borelSpace _
  have : SecondCountableTopology (hermA D n) := TopologicalSpace.Subtype.secondCountableTopology _
  have : LocallyCompactSpace (hermA D n) := GlobalTheory.CompanionTheory.FourierN.isClosed_hermA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : DiscreteTopology (ratHerm D n) := GlobalTheory.CompanionTheory.FourierN.discrete_ratHerm
  have : Countable (ratHerm D n) := countable_of_Lindelof_of_discrete
  have hper : ∀ γ ∈ ratHerm D n, ∀ b, F (nb (γ + b) * g) * chn ψ β (γ + b) = F (nb b * g) * chn ψ β b := fun γ hγ b => by
    rw [per_nb hinv hnb g γ hγ b, chn_per hψ β γ hγ b]
  have h : ∫ b in 𝓖, F (nb (b + x) * g) * chn ψ β (b + x) ∂lam = ∫ b in 𝓖, F (nb b * g) * chn ψ β b ∂lam :=
    GlobalTheory.CompanionTheory.ConstN.setIntegral_add_right (ratHerm D n) lam hFD (fun b => F (nb b * g) * chn ψ β b) hper x
  rw [fc_eq, fc_eq, ← h, ← integral_const_mul]
  refine integral_congr_ae (.of_forall fun b => ?_)
  show F (nb b * (nb x * g)) * chn ψ β b = pch ψ x.1 (rat β.1) * (F (nb (b + x) * g) * chn ψ β (b + x))
  rw [GlobalTheory.CompanionTheory.FourierN.nb_add hnb, mul_assoc, chn_shift ψ β b x]
  ring


theorem integrableOn_fc {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {nb : hermA D n → G D n}
    {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} (hC : CoefData (D := D) (n := n) nb lam 𝓖) {F : G D n → ℂ}
    (hF : Continuous F) (hinv : LeftInv (GF D n) F) (β : HermE D n) (h : G D n) :
    IntegrableOn (fun b => F (nb b * h) * chn ψ β b) 𝓖 lam := by
  obtain ⟨hnb, hlam, hFD, h1⟩ := hC
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D n n
  have : BorelSpace (Mx D n n) := ⟨rfl⟩
  have : BorelSpace (hermA D n) := Subtype.borelSpace _
  have : SecondCountableTopology (hermA D n) := TopologicalSpace.Subtype.secondCountableTopology _
  have : LocallyCompactSpace (hermA D n) := GlobalTheory.CompanionTheory.FourierN.isClosed_hermA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : DiscreteTopology (ratHerm D n) := GlobalTheory.CompanionTheory.FourierN.discrete_ratHerm
  have : Countable (ratHerm D n) := countable_of_Lindelof_of_discrete
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.CompanionTheory.FourierN.exists_compact_cover (D := D) (n := n)
  obtain ⟨M, hM⟩ := GlobalTheory.CompanionTheory.PcFc.exists_bound_of_periodic (ratHerm D n) hK hcov _ (cont_nb hF hnb h)
    (per_nb hinv hnb h)
  refine Measure.integrableOn_of_bounded (M := M) (by rw [h1]; exact ENNReal.one_ne_top)
    ((cont_nb hF hnb h).mul (chn_cont hψ β)).aestronglyMeasurable (.of_forall fun b => ?_)
  rw [norm_mul, show ‖chn ψ β b‖ = 1 from hψ.2.1 _, mul_one]
  exact hM b

theorem fc_fix {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {nb : hermA D n → G D n}
    {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} (hC : CoefData (D := D) (n := n) nb lam 𝓖) {F : G D n → ℂ}
    (hinv : LeftInv (GF D n) F) {v : Pl D} (hK : ∀ k ∈ KAt D n v, ∀ g, F (g * k) = F g) (β : HermE D n)
    {x : hermA D n} (hx : IntAt v x) {g : G D n} (hg : proj D.sp.cm.sig (Jst D n) v g = 1) :
    fc ψ lam 𝓖 nb F β g = pch ψ x.1 (rat β.1) * fc ψ lam 𝓖 nb F β g := by
  rw [← fc_nb_mul hψ hC hinv β x g, fc_eq, fc_eq]
  refine integral_congr_ae (.of_forall fun b => ?_)
  show F (nb b * g) * _ = F (nb b * (nb x * g)) * _
  rw [commute_of_atPts (nb_mem_atPts hC.1 v hx.1 hx.2.1) hg, ← mul_assoc, hK _ (nb_mem_KAt hC.1 v hx) _]

theorem fc_cutR {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {nb : hermA D n → G D n}
    {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} (hC : CoefData (D := D) (n := n) nb lam 𝓖) {F : G D n → ℂ}
    (hF : Continuous F) (hinv : LeftInv (GF D n) F) {v : Pl D} (C : Cut D n v) (β : HermE D n) {g : G D n}
    (hg : proj D.sp.cm.sig (Jst D n) v g = 1) :
    fc ψ lam 𝓖 nb (cutR nb C F) β g = cutF ψ C (rat β.1) * fc ψ lam 𝓖 nb F β g := by
  have e : ∀ b, cutR nb C F (nb b * g) * chn ψ β b =
      ∑ x ∈ C.s, C.co x * (F (nb b * (nb x * g)) * chn ψ β b) := fun b => by
    unfold cutR
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [mul_assoc (nb b) g, ← commute_of_atPts (nb_mem_atPts hC.1 v (C.inf x hx) (C.off x hx)) hg, mul_assoc]
  calc fc ψ lam 𝓖 nb (cutR nb C F) β g
      = ∫ b in 𝓖, ∑ x ∈ C.s, C.co x * (F (nb b * (nb x * g)) * chn ψ β b) ∂lam :=
        integral_congr_ae (.of_forall e)
    _ = ∑ x ∈ C.s, ∫ b in 𝓖, C.co x * (F (nb b * (nb x * g)) * chn ψ β b) ∂lam :=
        integral_finsetSum _ fun x _ => (integrableOn_fc hψ hC hF hinv β (nb x * g)).const_mul _
    _ = ∑ x ∈ C.s, C.co x * fc ψ lam 𝓖 nb F β (nb x * g) :=
        Finset.sum_congr rfl fun x _ => integral_const_mul _ _
    _ = ∑ x ∈ C.s, C.co x * (pch ψ x.1 (rat β.1) * fc ψ lam 𝓖 nb F β g) :=
        Finset.sum_congr rfl fun x _ => by rw [fc_nb_mul hψ hC hinv]
    _ = cutF ψ C (rat β.1) * fc ψ lam 𝓖 nb F β g := by
        rw [cutF, Finset.sum_mul]
        exact Finset.sum_congr rfl fun x _ => by ring

end PositivityTheory.Rg.Rsw.L.LCutLow

end
end
