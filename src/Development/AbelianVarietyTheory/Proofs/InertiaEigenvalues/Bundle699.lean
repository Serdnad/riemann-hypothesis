module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralWittElementOfEvaluation
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle587
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle635
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle686
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle336
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle334
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle599
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle648
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle514
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RayClassFieldInfModulusEqSup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle681
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle257
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle021
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle680
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle312
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
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl

@[expose] public section

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.OEStable

variable {l : ℕ} [hl : Fact l.Prime]

theorem perfect_Cb : PerfectRing (Cb l) l := by
  refine PerfectRing.ofSurjective _ _ fun x => ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
  refine ⟨algebraMap _ _ ((frobeniusEquiv (OCb l) l).symm a) /
    algebraMap _ _ ((frobeniusEquiv (OCb l) l).symm b), ?_⟩
  rw [frobenius_def, div_pow, ← map_pow (algebraMap (OCb l) (Cb l)),
    ← map_pow (algebraMap (OCb l) (Cb l)), frobeniusEquiv_symm_pow_p,
    frobeniusEquiv_symm_pow_p]

theorem eq_zero_of_forall_dvd (z : WCb l) (h : ∀ n, ((l : ℕ) : WCb l) ^ n ∣ z) : z = 0 := by
  ext m
  obtain ⟨y, hy⟩ := h (m + 1)
  rw [hy, mul_comm, WittVector.mul_pow_charP_coeff_zero _ (Nat.lt_succ_self m)]
  simp

private theorem sigmaA_eq_map_pt (g : GQ l) (a : Ainf l) : Per.σA g a = WittVector.map (Per.σF g) a := by
  apply GlobalTheory.Prism.inclW_injective
  rw [← galW_inclW]
  exact WittVector.ext fun n => autCb_alg l (galTilt l g) (a.coeff n)

variable {K : FinExt l} (bk : BK K)

theorem sat (w : WCb l) (hw : ((l : ℕ) : WCb l) * w ∈ bk.OE) : w ∈ bk.OE := by
  apply GlobalTheory.BSP.HeightSInt.mem_of_l_mul_mem <;> assumption

theorem closed (w : WCb l) (h : ∀ n : ℕ, ∃ v ∈ bk.OE, ((l : ℕ) : WCb l) ^ n ∣ w - v) : w ∈ bk.OE := by
  intro n
  obtain ⟨v, hv, z, hz⟩ := h n
  obtain ⟨m, s, y, hy⟩ := hv n
  exact ⟨m, s, y + bk.evW X ^ m * z, by linear_combination hy + bk.evW X ^ m * hz⟩

theorem frob (w : WCb l) (hw : w ∈ bk.OE) : frobW l w ∈ bk.OE := by
  intro n
  obtain ⟨m, s, y, h⟩ := hw n
  have key : ∀ t : bk.S, frobW l (bk.evW t) = bk.evW (frobS l bk.a t) := fun t => by
    rw [BK.evW, RingHom.comp_apply, RingHom.comp_apply, frobW_inclW, bk.ev_frob]
  refine ⟨l * m, frobS l bk.a s, frobW l y, ?_⟩
  have h' := congrArg (frobW l) h
  simp only [map_mul, map_add (f := _), map_pow, map_natCast, key, frobS_X] at h'
  rw [pow_mul]
  linear_combination h'

theorem gal (g : ↥(GK K)) (hg : bk.FixFlat g) (w : WCb l) (hw : w ∈ bk.OE) : galW l (g : GQ l) w = w := by
  obtain ⟨-, -, -, hflat, -, hcomp, -⟩ := GlobalTheory.T.ainf_divisibility_breuilKisin_facts l K bk
  haveI := (GlobalTheory.T.wittVector_teichmuller_isAdicComplete_of_perfect l (OCb l) bk.flat hflat hcomp).1
  have hteich : Per.σA (g : GQ l) (WittVector.teichmuller l bk.flat) = WittVector.teichmuller l bk.flat := by
    rw [sigmaA_eq_map_pt, WittVector.map_teichmuller]
    exact congrArg _ hg
  have hfix : (Per.σA (g : GQ l)).comp bk.ev = bk.ev := by
    refine ringHom_ext_of_sep _ _ (fun r => ?_) ?_ ?_
    · rw [RingHom.comp_apply, bk.ev_C, bk.gal_w]
    · rw [RingHom.comp_apply, bk.ev_X, hteich]
    · intro x hx
      rw [RingHom.comp_apply, bk.ev_X, hteich] at hx
      refine IsHausdorff.haus' (I := Ideal.span {WittVector.teichmuller l bk.flat}) x fun n => ?_
      simp only [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact hx n
  have hW : ∀ t : bk.S, galW l (g : GQ l) (bk.evW t) = bk.evW t := fun t => by
    change galW l _ (inclW l (bk.ev t)) = inclW l (bk.ev t)
    rw [galW_inclW, ← RingHom.comp_apply (Per.σA _) bk.ev, hfix]
  obtain ⟨-, -, hu, -, -⟩ := GlobalTheory.T.breuilKisin_OE_mod_prime_laurent_field l K bk
  apply sub_eq_zero.1
  apply eq_zero_of_forall_dvd
  intro n
  obtain ⟨m, s, y, h⟩ := hw n
  have h' := congrArg (galW l (g : GQ l)) h
  simp only [map_mul, map_add (f := _), map_pow, map_natCast, hW] at h'
  obtain ⟨u, hu'⟩ := hu.pow m
  have e : (u : WCb l) * (galW l (g : GQ l) w - w) =
      ((l : ℕ) : WCb l) ^ n * (galW l (g : GQ l) y - y) := by
    rw [hu']; linear_combination h' - h
  refine ⟨(↑u⁻¹ : WCb l) * (galW l (g : GQ l) y - y), ?_⟩
  calc galW l (g : GQ l) w - w = (↑u⁻¹ : WCb l) * ((u : WCb l) * (galW l (g : GQ l) w - w)) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = _ := by rw [e]; ring

theorem inv (w : WCb l) (hw : w ∈ bk.OE) (hu : IsUnit w) : ∃ w' ∈ bk.OE, w * w' = 1 := by
  haveI := perfect_Cb (l := l)
  obtain ⟨-, -, -, -, hinv⟩ := GlobalTheory.T.breuilKisin_OE_mod_prime_laurent_field l K bk
  obtain ⟨u, rfl⟩ := hu
  have hy : WittVector.constantCoeff (p := l) (R := Cb l) u ∈
      bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)) := Subring.mem_map.2 ⟨u, hw, rfl⟩
  obtain ⟨v, hv, hvy⟩ := Subring.mem_map.1 (hinv _ hy)
  have hne : WittVector.constantCoeff (p := l) (R := Cb l) u ≠ 0 := by
    intro h0
    have h1 := congrArg (WittVector.constantCoeff (p := l) (R := Cb l)) u.mul_inv
    rw [map_mul, h0, zero_mul, map_one] at h1
    exact zero_ne_one h1
  have h1 : (u : WCb l) * v - 1 ∈ RingHom.ker (WittVector.constantCoeff (p := l) (R := Cb l)) := by
    rw [RingHom.mem_ker, RingHom.map_sub, map_mul, hvy, map_one, mul_inv_cancel₀ hne, sub_self]
  rw [WittVector.ker_constantCoeff, Ideal.mem_span_singleton] at h1
  obtain ⟨z, hz⟩ := h1
  have hz' : z ∈ bk.OE := sat bk z (by
    rw [← hz]; exact sub_mem (mul_mem hw hv) (one_mem _))
  have huv : (u : WCb l) * v = 1 - (-((l : ℕ) : WCb l) * z) := by linear_combination hz
  have hi : (↑u⁻¹ : WCb l) * u = 1 := Units.inv_mul u
  refine ⟨↑u⁻¹, closed bk _ fun n => ⟨v * ∑ i ∈ Finset.range n, (-((l : ℕ) : WCb l) * z) ^ i,
    mul_mem hv (sum_mem fun i _ => pow_mem (mul_mem (neg_mem (natCast_mem _ l)) hz') i),
    ⟨(↑u⁻¹ : WCb l) * (-z) ^ n, ?_⟩⟩, u.mul_inv⟩
  have hgeom := geom_sum_mul_neg (-((l : ℕ) : WCb l) * z) n
  have hq : (-((l : ℕ) : WCb l) * z) ^ n = ((l : ℕ) : WCb l) ^ n * (-z) ^ n := by
    rw [neg_mul, ← mul_neg, mul_pow]
  linear_combination (-(↑u⁻¹ : WCb l)) * hgeom - ((↑u⁻¹ : WCb l) * ∑ i ∈ Finset.range n,
    (-((l : ℕ) : WCb l) * z) ^ i) * huv + (v * ∑ i ∈ Finset.range n, (-((l : ℕ) : WCb l) * z) ^ i) * hi
    - (↑u⁻¹ : WCb l) * hq

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ w : WCb l, ((l : ℕ) : WCb l) * w ∈ bk.OE → w ∈ bk.OE) ∧ (∀ w : WCb l, (∀ n : ℕ, ∃ v ∈ bk.OE, ((l : ℕ) : WCb l) ^ n ∣ w - v) → w ∈ bk.OE) ∧ (∀ w ∈ bk.OE, frobW l w ∈ bk.OE) ∧ (∀ g : ↥(GK K), bk.FixFlat g → ∀ w ∈ bk.OE, galW l (g : GQ l) w = w) ∧ ∀ w ∈ bk.OE, IsUnit w → ∃ w' ∈ bk.OE, w * w' = 1 := by
  intro l _ K bk
  exact ⟨sat bk, closed bk, frob bk, fun g hg w hw => gal bk g hg w hw, inv bk⟩

end GlobalTheory.OEStable
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.howeDuality_compactPair_polynomialFock_allRealPlaces : ∀ (D : D7) (n m : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (BS : GlobalTheory.ExportSeries.GLR D n) (K : Type) [Group K] (r : K →* GlobalTheory.ExportSeries.GLR D n), (∀ (k : K) (τ : D.what₂.Tau), ((GlobalTheory.ExportSeries.inBasis BS (r k) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → (∀ g : GlobalTheory.ExportSeries.GLR D n, (∀ τ, ((GlobalTheory.ExportSeries.inBasis BS g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∃ k, r k = g) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : K →* Module.End ℂ W), (∀ U : Submodule ℂ W, (∀ k, U.map (ρ k) ≤ U) → U = ⊥ ∨ U = ⊤) → ∀ M : Submodule ℂ (W →ₗ[ℂ] PolF D m n), (∀ ψ ∈ M, ∀ (k : K) (w' : W), ψ (ρ k w') = GlobalTheory.ExportSeries.fockGL m w BS (r k) (ψ w')) → (∀ ψ ∈ M, ∀ (τ : D.what₂.Tau) (Z : Matrix (Fin m) (Fin m) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) Z ∘ₗ ψ ∈ M) → M ≠ ⊥ → ∀ φ : W →ₗ[ℂ] PolF D m n, (∀ (k : K) (w' : W), φ (ρ k w') = GlobalTheory.ExportSeries.fockGL m w BS (r k) (φ w')) → φ ∈ M := by
  first | exact @GlobalTheory.HoweCompactAlg.mem_of_equivariant | exact GlobalTheory.HoweCompactAlg.mem_of_equivariant | (intros; apply GlobalTheory.HoweCompactAlg.mem_of_equivariant <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

theorem GlobalTheory.semistable_class_of_pair : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v : V, Continuous fun g => ρ g v) → ∀ x ∈ Dst P ρ, ∀ y ∈ Dst P ρ, (l : ℚ_[l]) • phiV P ℚ_[l] V x - x = monV P ℚ_[l] V y → ∃ (z : V ⊗[ℚ_[l]] Bst P) (c : ↥(GK K) → V), c ∈ continuousCocycles ρ ∧ (∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z) ∧ monV P ℚ_[l] V z = x := by
  intro l _ P AI T K V _ _ _ _ _ _ _ ρ hρ x hx y hy hxy
  obtain ⟨ι, hιC, hιact⟩ := GlobalTheory.T.exists_equivariant_log_semistable_to_deRham l P AI T
  obtain ⟨hιst, -, -⟩ := GlobalTheory.T.lTensor_semistable_to_deRham_equivariant l P ι hιC hιact K V ρ
  obtain ⟨z, hNz, hφz, hFz⟩ := GlobalTheory.T.exists_monodromy_frobenius_solution_fil l P AI T ι hιC K V x y hxy
  have hx' := (mem_Dst P ρ).mp hx
  have hy' := (mem_Dst P ρ).mp hy
  have hw : ∀ g : ↥(GK K), ∃ v : V, stRep P ρ g z - z = v ⊗ₜ[ℚ_[l]] (1 : Bst P) := by
    intro g
    refine GlobalTheory.T.exists_eq_tmul_one_of_monodromy_frobenius_filtration l P AI T ι hιC K V (stRep P ρ g z - z) ?_ ?_ ?_
    · rw [map_sub, ← Module.End.mul_apply, monV_stRep, Module.End.mul_apply, hNz, hx', sub_self]
    · have hφz' : phiV P ℚ_[l] V z = z + y := by rw [← hφz]; abel
      rw [map_sub, ← Module.End.mul_apply, phiV_stRep, Module.End.mul_apply, hφz', map_add (f := _), hy']
      abel
    · rw [map_sub, hιst]
      exact Submodule.sub_mem _ (GlobalTheory.T.actVdR_mem_tensorDeRhamFiltration l P K V ρ 0 g _ hFz) hFz
  choose c hc using hw
  have hc' : ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z := fun g => (hc g).symm
  exact ⟨z, c, GlobalTheory.T.continuousCocycle_of_semistable_coboundary l P AI T K V ρ hρ z c hc', hc', hNz⟩
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
  Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.CoefDuty
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FormInner

variable {D : D7} {V : HSp D} {n : ℕ}

def RatFrame (P : principalLevelFrame.RowPsi V n) : Prop :=
  ∀ h, h ∈ ReciprocityTheory.Aut.GQ D.host.E n ↔ ∃ γ ∈ Formalism.L2.Theta.GQ V, finHom V γ = finHom V (P.ψ h)

theorem ratF_injective (V : HSp D) : Function.Injective (Bridge.ratF V) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨γ, γ₀, h₀, e⟩ h
  have h1 : finHom V γ = 1 := congrArg Subtype.val h
  have h2 : γ₀ = 1 := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    have h3 : ((finHom V γ).1 i j) = inclR (F := D.host.F) (Af D.host.F) (γ₀.1 i j) := by
      have : (matHom V γ).1 i j = inclR (F := D.host.F) (AF D.host.F) (γ₀.1 i j) :=
        (congrArg (fun g : GL (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E) => g.1 i j) e).symm
      show Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) ((matHom V γ).1 i j) = _
      rw [this]
      simp [inclR]
    have hi : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (Af D.host.F)) := by
      haveI : Nontrivial (Af D.host.F) := Formalism.L2.DIV.af_nontrivial D.host.F
      exact Algebra.TensorProduct.includeRight_injective (RingHom.injective _)
    apply hi
    rw [← h3, h1]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  subst h2
  exact Subtype.ext (Subtype.ext (e.symm.trans (map_one _)))

def frameEquiv (P : principalLevelFrame.RowPsi V n) : GAf D.host.E n ≃* Bridge.Gf V :=
  MulEquiv.ofBijective ((finHom V).rangeRestrict.comp P.ψ)
    ⟨fun a b e => P.inj (TopMult.lift_unique (P.into a) (P.into b) e), fun y => by
      obtain ⟨h, hh, e⟩ := TopMult.exists_lift y
      obtain ⟨g, rfl⟩ := P.onto h hh
      exact ⟨g, e⟩⟩

theorem frameEquiv_apply (P : principalLevelFrame.RowPsi V n) (g) : frameEquiv P g = (finHom V).rangeRestrict (P.ψ g) := rfl

theorem RatFrame.iff {P : principalLevelFrame.RowPsi V n} (h : RatFrame P) (g) :
    g ∈ ReciprocityTheory.Aut.GQ D.host.E n ↔ ∃ γ, Bridge.ratF V γ = frameEquiv P g :=
  (h g).trans ⟨fun ⟨γ, hγ, e⟩ => ⟨⟨γ, hγ⟩, Subtype.ext e⟩, fun ⟨γ, e⟩ => ⟨γ.1, γ.2, congrArg Subtype.val e⟩⟩

theorem comap_le_Umax {hF : D.host.F = maximalRealSubfield D.host.E} {P : principalLevelFrame.RowPsi V n} (hP : GlobalTheory.Mem.R3.StdFrame hF P)
    {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsBaseFrame V β Λ 1)
    (Lv : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) :
    (levEnv V β Lv).J.comap (frameEquiv P).toMonoidHom ≤ ReciprocityTheory.Aut.Umax D.host.E n := fun κ hκ =>
  (hP.2 κ).2 ((GlobalTheory.FinZeta.LevelOff.finE_mem_St_iff hβ (P.into κ)).1
    (GlobalTheory.FinZeta.LevelOff.finE_mem_St_of_mem_levG (Lv := flag1L Lv) ⟨P.into κ, hκ⟩))

section Read

variable {μ : D.what₂.Tup} {j : ℕ} (X : MtReal D μ j) {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W]
  [InnerProductSpace ℂ W] (ι : Γ →* G) (φ : GAf D.host.E D.R.nV ≃* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ)
  (e : X.wt.W ≃ₗ[ℂ] W) (Fm : D.what₂.Mt μ j → G → W)

theorem weight_match (hFm : ∀ x, Fm x ∈ Bridge.AdForms ι ρ J χ) (hread : ∀ x g, e (X.real x g) = Fm x (φ g))
    {x₀ : D.what₂.Mt μ j} (h₀ : x₀ ≠ 0) (γ : ReciprocityTheory.Aut.GQ D.host.E D.R.nV) (δ : Γ) (hδ : ι δ = φ γ) (v : X.wt.W) :
    e (X.wt.ρ γ v) = ρ δ (e v) := by
  have hA : ∀ x, X.real x ∈ NG.TypeSp X.wt.ρ X.J X.χ := fun x => X.real_range ▸ LinearMap.mem_range_self _ x
  let U : Subrepresentation X.wt.ρ := ⟨Submodule.span ℂ (Set.range (X.real x₀)), fun g w hw => by
    refine Submodule.span_induction (p := fun w _ => X.wt.ρ g w ∈ Submodule.span ℂ (Set.range (X.real x₀))) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨h, rfl⟩
      exact Submodule.subset_span ⟨g * h, (hA x₀).1.1 g h⟩
    · simp
    · intro a b _ _ ha hb
      rw [map_add]; exact add_mem ha hb
    · intro c a _ ha
      rw [map_smul]; exact Submodule.smul_mem _ c ha⟩
  have hU : U = ⊤ := by
    haveI := X.wt.irr
    refine (eq_bot_or_eq_top U).resolve_left fun hb => h₀ (X.real_inj ?_)
    rw [map_zero]
    funext g
    have : X.real x₀ g ∈ U.toSubmodule := Submodule.subset_span ⟨g, rfl⟩
    rw [hb] at this
    exact this
  have hv : v ∈ Submodule.span ℂ (Set.range (X.real x₀)) := by
    show v ∈ U.toSubmodule
    rw [hU]
    exact Submodule.mem_top
  refine Submodule.span_induction (p := fun v _ => e (X.wt.ρ γ v) = ρ δ (e v)) ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨h, rfl⟩
    have := hFm x₀ δ (φ h) 1
    rw [← (hA x₀).1.1 γ h, hread, hread, map_mul, ← hδ]
    simpa using this
  · simp
  · intro a b _ _ ha hb
    simp only [map_add (f := _), ha, hb]
  · intro c a _ ha
    simp only [map_smul, ha]

def pullForm : X.wt.W →ₗ⋆[ℂ] X.wt.W →ₗ[ℂ] ℂ := ((innerₛₗ ℂ : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ).comp e.toLinearMap).compl₂ e.toLinearMap

theorem pullForm_apply (a b : X.wt.W) : pullForm X e a b = inner ℂ (e a) (e b) := rfl

theorem classSum_of_read {I : Type} [Fintype I] (y : I → G) (hy : Bridge.IsReps ι J y) (hι : Function.Injective ι)
    (hrat : ∀ h, h ∈ ReciprocityTheory.Aut.GQ D.host.E D.R.nV ↔ ∃ γ, ι γ = φ h) (hρ : ∀ δ (a b : W), inner ℂ (ρ δ a) (ρ δ b) = inner ℂ a b)
    (hJ : IsBounded (J.comap φ.toMonoidHom)) (hX : IsBounded X.J)
    (hFm : ∀ x, Fm x ∈ Bridge.AdForms ι ρ J χ) (hread : ∀ x g, e (X.real x g) = Fm x (φ g))
    (c : ℝ) (hc : 0 < c) (hip : ∀ x x' : D.what₂.Mt μ j, inner ℂ x x' = (c : ℂ) * Bridge.adInner ι J y (Fm x) (Fm x'))
    (h0 : (∀ x : D.what₂.Mt μ j, x = 0) → ∃ β, IsInvForm X.wt β) : ClassSum X := by
  have hA : ∀ x, X.real x ∈ NG.TypeSp X.wt.ρ X.J X.χ := fun x => X.real_range ▸ LinearMap.mem_range_self _ x
  obtain ⟨N, hN, hNJ⟩ := X.J_open
  obtain ⟨T', hT', htr⟩ := classSum_transport (W := W) ι hι φ hrat J y hy
  refine ⟨hX, ?_⟩
  by_cases hz : ∀ x : D.what₂.Mt μ j, x = 0
  · obtain ⟨β, hβ⟩ := h0 hz
    obtain ⟨T, c', hT, -, -⟩ := classSum_compare hβ hX hN (fun κ h => (hNJ κ h).1) hJ hT'
    refine ⟨β, T, 1, hβ, hT, one_pos, fun x x' => ?_⟩
    rw [hz x]
    simp [classSum]
  · obtain ⟨x₀, h₀⟩ := not_forall.1 hz
    have hβ : IsInvForm X.wt (pullForm X e) := by
      refine ⟨fun a b => by rw [pullForm_apply, pullForm_apply, inner_conj_symm], fun a ha => ?_, fun γ a b => ?_⟩
      · rw [pullForm_apply]
        exact (re_inner_self_pos (𝕜 := ℂ) (x := e a)).2 (fun h => ha (e.map_eq_zero_iff.1 h))
      · obtain ⟨δ, hδ⟩ := (hrat _).1 γ.2
        have hw := weight_match X ι φ ρ J χ e Fm hFm hread h₀ γ δ hδ
        exact (congrArg₂ (inner ℂ) (hw a) (hw b)).trans (hρ δ _ _)
    obtain ⟨T, c', hT, hc', hcmp⟩ := classSum_compare hβ hX hN (fun κ h => (hNJ κ h).1) hJ hT'
    have hB : ∀ x, X.real x ∈ NG.TypeSp X.wt.ρ (J.comap φ.toMonoidHom) (χ.comp (φ.toMonoidHom.subgroupComap J)) := fun x =>
      ⟨(hA x).1, fun κ => funext fun g => e.injective (by
        have := hFm x 1 (φ g) ⟨φ κ, κ.2⟩
        show e (X.real x (g * κ)) = e (((χ ⟨φ κ, κ.2⟩ : ℂˣ) : ℂ) • X.real x g)
        rw [map_smul, hread, hread, map_mul]
        simpa using this)⟩
    refine ⟨_, T, c * c', hβ, hT, mul_pos hc hc', fun x x' => ?_⟩
    rw [hip, ← htr X.wt (pullForm X e) (X.real x) (X.real x') _ _ fun g => by rw [pullForm_apply, hread, hread],
      hcmp _ _ _ _ (hA x) (hA x') (hB x) (hB x')]
    push_cast
    ring

end Read

end GlobalTheory.FormInner

end
end

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

theorem _root_.GlobalTheory.T.exists_whittaker_bump_extension_schur_complement : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (β : GA E (m + 1) → ℂ),
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, β (u * g) = GlobalTheory.JSW.psiN u * β g) →
    (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 →
      ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) →
    (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
      ∀ u ∈ U, ∀ g, β (g * finGL E (m + 1) u) = β g) →
    (∀ g, ContDiffOn ℝ ∞ (chart β g) (invSet E (m + 1))) →
    ∃ b : GA E (m + r + 1 + 1) → ℂ,
      (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + r + 1 + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) ∧
      (∃ C : Set (GA E (m + r + 1 + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := (m + r + 1) + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) (m + r + 1)), b p ≠ 0 →
        ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + r + 1 + 1)), u⁻¹ * p ∈ C) ∧
      (∃ U : Subgroup (GL (Fin (m + r + 1 + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + r + 1 + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, b (g * finGL E (m + r + 1 + 1) u) = b g) ∧
      (∀ g, ContDiffOn ℝ ∞ (chart b g) (invSet E (m + r + 1 + 1))) ∧
      ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, b (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) = β h := by
  first | (exact @GlobalTheory.SchurExt.exists_ext) | (exact GlobalTheory.SchurExt.exists_ext) | (intros; apply GlobalTheory.SchurExt.exists_ext <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat


theorem _root_.GlobalTheory.T.exists_factor_components_of_adelic_invariant_function : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (hr : V.rank = r) (U : Unf Xo c σ r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ), IotaOK Dw V io → 1 ≤ Dw.p + Dw.q → l.A = 1 → GoodEmb c σ → (∀ k, ModelW V hr (U.X k)) → DictLat U V hr dict io e F ik φ th x₀ → (∀ h, (dict h).2 ∈ (U.X (dict h).1).dom) → ∀ w : GA D V → c.F, (∀ h h' : GA D V, finHom V h = finHom V h' → w h = w h') → (∀ γ ∈ GQ V, ∀ h, w (γ * h) = w h) → (∀ u : GA D V, gLat V u = latHat V → FinCong V l.M u → ∀ h, w (h * u) = w h) → ∃ v : U.Comp → c.F, ∀ h : GA D V, w h = v (dict h).1 := by
  first | exact @GlobalTheory.CompFactor.exists_factor_comp | exact GlobalTheory.CompFactor.exists_factor_comp | (intros; apply GlobalTheory.CompFactor.exists_factor_comp <;> assumption)
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.rayClassField_inf_modulus_eq_sup : ∀ {K H H₁ H₂ : Type} [Field K] [NumberField K] [Field H] [NumberField H] [Algebra K H] [IsAbelianGalois K H] [Field H₁] [NumberField H₁] [Algebra K H₁] [IsAbelianGalois K H₁] [Field H₂] [NumberField H₂] [Algebra K H₂] [IsAbelianGalois K H₂], (∀ u : (𝓞 K)ˣ, u = 1 ∨ u = -1) → ∀ {𝔞 𝔟 : Ideal (𝓞 K)}, 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → ∀ {q : ℕ}, q.Prime → q ≠ 2 → 𝔞 ≤ Ideal.span {(q : 𝓞 K)} → 𝔟 ≤ Ideal.span {(q : 𝓞 K)} → GlobalTheory.FieldSize.IsRay H (𝔞 ⊓ 𝔟) → GlobalTheory.FieldSize.IsRay H₁ 𝔞 → GlobalTheory.FieldSize.IsRay H₂ 𝔟 → ∀ (f₁ : H₁ →ₐ[K] H) (f₂ : H₂ →ₐ[K] H), f₁.fieldRange ⊔ f₂.fieldRange = ⊤ := by
  first | exact @GlobalTheory.RayCompositum.fieldRange_sup_eq_top | exact GlobalTheory.RayCompositum.fieldRange_sup_eq_top | (intros; apply GlobalTheory.RayCompositum.fieldRange_sup_eq_top <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.unitLemma_lieAlgebra_unitaryGroup_of_jacquetRallis : (∀ r : ℕ, GlobalTheory.JR.UnitMatch r) → UnitLemmaLie ∧ UnitLemmaGroup := by
  first | exact @GlobalTheory.UnitLemma.unitLemma_lie_and_group | exact GlobalTheory.UnitLemma.unitLemma_lie_and_group | (intros; apply GlobalTheory.UnitLemma.unitLemma_lie_and_group <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.noDetectedSubgroupTowerRat_proof : NoTowerQ := by
  first | exact @GlobalTheory.PMon.Ram.noTowerQ_holds | exact GlobalTheory.PMon.Ram.noTowerQ_holds | (intros; apply GlobalTheory.PMon.Ram.noTowerQ_holds <;> assumption)
end

section

namespace GlobalTheory.WachUse

open GlobalTheory.WachUse Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n}

theorem additive_of_sumFor (hW : GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.SumFor W) : Additive W := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.SumFor at hW
  intro T T' S f g hT hT' hb hs z hz
  obtain ⟨σ, hσ, -, -, hmem⟩ := hW T T' S hT hT' f g (by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.IsSumLat
    exact ⟨hb, hs⟩)

  set p := σ.symm z with hp
  have hz' : σ (p.1, p.2) = z := by simp [hp]
  rw [← hz'] at hz
  obtain ⟨hx, hy⟩ := (hmem p.1 p.2).1 hz
  exact ⟨p.1, hx, p.2, hy, by rw [← hz', hσ]⟩

end Generic

theorem additive_of_caseA : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (H : LocHW l P)
    (E : LocFon l P AI H) (C : LocCmpT l P AI H E), ∀ (K LL : FinExt l) (h : CaseA K LL),
    Additive (H.W K 1 LL h.2.2) := by
  intro l _ P _ H _ _ K LL h

  exact additive_of_sumFor (GlobalTheory.WachSum.sumPart l P H K 1 LL h.2.2)

end GlobalTheory.WachUse
end
