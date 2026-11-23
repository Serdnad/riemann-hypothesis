module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallySmall
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle093
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2075
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle181
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle001
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Unfold2
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle490
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle489
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle511
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle488
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle706
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle534
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZarhinDualPolarisation.FlatFiniteFibres.FlatOfFibresFinite
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle707
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle545
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle522
public import Development.AutomorphicSpectrum.Proofs.HermitianForms.ExistsIsCharAFOfStd
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle705
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle350
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle655
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle003
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutantReductionReal
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle708
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs

@[expose] public section

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ResMu

open Set GlobalTheory.Eis

variable {D : D7} {p : ℕ}

theorem hecke_one : IsHeckeChar D 1 := ⟨continuous_const, fun _ => rfl⟩

theorem hecke_mul_inv {χ' : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ') : IsHeckeChar D (1 * χ'⁻¹) := by
  refine ⟨?_, fun x => ?_⟩
  · have e : (⇑((1 : (AE D)ˣ →* Circle) * χ'⁻¹)) = fun x => (χ' x)⁻¹ := by
      funext x; simp
    rw [e]
    exact h.1.inv
  · simpa using h.2 x

theorem fj_smul {n ρ p' : ℕ} {hn : ρ + p' = n} (M : Maps D hn) (m : Meas D ρ p') (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ)
    (c : ℂ) (F : G D n → ℂ) (g : G D n) (φ : Mx D ρ p' → ℂ) :
    FJ M m ψ b₀ (c • F) g φ = c * FJ M m ψ b₀ F g φ := by
  simp only [FJ, PositivityTheory.Rg.Rsw.pc, PositivityTheory.Rg.Rsw.zc, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

theorem eis_pole_free (hRS : RSec) (hEH : EisHol) (hp : 2 ≤ p) {p' : ℕ} (hn : 1 + p' = p) (M : Maps D hn) (m : Meas D 1 p')
    (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D 1) (hdet : b₀.1.det ≠ 0)
    {χ' : (AE D)ˣ →* Circle} (hχ' : IsHeckeChar D χ') {θ : InfFam D} (hθ : IsInfFam θ) {Ω : G D p' → Mx D 1 p' → ℂ}
    (hΩ : IsTh ψ χ' θ b₀ m.μ Ω) {H : G D p → ℝ≥0} (hH : IsHt H) {f : G D p → ℂ} (hf : IsRho f) (g : G D p) :
    Tendsto (fun σ : ℝ => ((σ - p / 2 : ℝ) : ℂ) * eisS (Rsec M m ψ b₀ (fam H f ((p : ℂ) / 2) (σ : ℂ)) g Ω) 1)
      (𝓝[>] ((p : ℝ) / 2)) (𝓝 0) := by
  obtain ⟨c1, c2, c3⟩ := hRS D p 1 p' hn M m ψ hψ b₀ hdet 1 χ' hecke_one hχ' θ hθ Ω hΩ H hH ((p : ℂ) / 2) f hf.1 hf.2 g
  have hd := hEH D p' (1 * χ'⁻¹) (hecke_mul_inv hχ') _ (fun z => Rsec M m ψ b₀ (fam H f ((p : ℂ) / 2) z) g Ω) c1 c2 c3 1
  have hopen : IsOpen {z : ℂ | (((1 : ℕ) : ℝ) - p') / 2 < z.re ∧ (p' : ℝ) / 2 < z.re} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt continuous_const Complex.continuous_re)
  have hpp : (p : ℝ) = 1 + p' := by rw [← hn]; push_cast; ring
  have hp' : (1 : ℝ) ≤ p' := by
    have : 1 ≤ p' := by omega
    exact_mod_cast this
  have hmem : ((((p : ℝ) / 2 : ℝ)) : ℂ) ∈ {z : ℂ | (((1 : ℕ) : ℝ) - p') / 2 < z.re ∧ (p' : ℝ) / 2 < z.re} := by
    simp only [mem_setOf_eq, Complex.ofReal_re, hpp, Nat.cast_one]
    constructor <;> linarith
  have hcont := (hd.differentiableAt (hopen.mem_nhds hmem)).continuousAt
  have h1 := (hcont.tendsto.comp (Complex.continuous_ofReal.continuousAt (x := (p : ℝ) / 2))).mono_left
    (nhdsWithin_le_nhds (s := Ioi ((p : ℝ) / 2)))
  have h2 : Tendsto (fun σ : ℝ => ((σ - p / 2 : ℝ) : ℂ)) (𝓝[>] ((p : ℝ) / 2)) (𝓝 0) := by
    have : Continuous fun σ : ℝ => ((σ - p / 2 : ℝ) : ℂ) := by fun_prop
    have h3 := (this.tendsto ((p : ℝ) / 2)).mono_left (nhdsWithin_le_nhds (s := Ioi ((p : ℝ) / 2)))
    simpa using h3
  simpa using h2.mul h1

theorem pc_vanish (hHE : HeckeEta) (hFJ : FJEis) (hPB : PcBound) (hRS : RSec) (hEH : EisHol) (hTT : ThTotal) (hS : SphBound)
    (hp : 2 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) {p' : ℕ} (hn : 1 + p' = p) (M : Maps D hn)
    (m : Meas D 1 p') (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) {θ : InfFam D} (hθ : IsInfFam θ)
    (b₀ : HermE D 1) (hb : IsDiagInv b₀) (g : G D p) : pc M m ψ b₀ (resA H f) g = 0 := by
  have hp1 : 1 ≤ p := by omega
  obtain ⟨χ', hχ', hres⟩ := hHE D 1
  have hAc := resA_cont hS hp1 hH hC hcov hf
  have hAl := resA_leftInv hS hp1 hH hC hcov hf
  have hU := ufil_le p
  have key : ∀ g₀ : G D p, (fun y => pc M m ψ b₀ (resA H f) (M.sh y * g₀)) = 0 := fun g₀ => by
    refine hTT D 1 p' m ψ hψ b₀ hb χ' hχ' hres (fun h => absurd h one_ne_zero) θ hθ _ ?_ ?_ ?_
    · exact ((hPB D p 1 p' hn M m ψ hψ b₀).1 _ hAc hAl).comp (M.sh_cont.mul continuous_const)
    · obtain ⟨C₁, hC₁, -, hb₁⟩ := (hPB D p 1 p' hn M m ψ hψ b₀).2 g₀
      obtain ⟨B, hB⟩ := hC₁.exists_bound_of_continuousOn hAc.continuousOn
      exact ⟨B, hb₁ _ hAc hAl B hB⟩
    · intro Ω hΩ
      have hint : Integrable (Ω 1) m.μ := GlobalTheory.SchwartzAInt.integrable_of_mem D θ hθ 1 p' m.μ m.𝓕 m.hμ (Ω 1) (hΩ.mem 1)
      have hFl : ∀ᶠ σ in ((ufil p : Ultrafilter ℝ) : Filter ℝ), Continuous (res H f σ) ∧ LeftInv (GF D p) (res H f σ) := by
        refine hU ?_
        filter_upwards [ev_Ioc p] with σ hσ using ⟨res_cont hS hp1 hH hC hcov hf hσ, res_leftInv hH hf σ⟩
      have hlim := GlobalTheory.T.partial_coefficient_uniform_limit hPB D p 1 p' hn M m ψ hψ b₀ ((ufil p : Ultrafilter ℝ) : Filter ℝ) (fun σ => res H f σ) (resA H f)
        hAc hAl hFl (fun C' hC' ε hε => resA_unif hS hp1 hH hC hcov hf hC' hε)
        (hFl.mono fun σ hσ y g' => GlobalTheory.T.partial_coefficient_sub hPB D p 1 p' hn M m ψ hψ b₀ _ _ hσ.1 hσ.2 hAc hAl y g') g₀ (Ω 1) hint
      have hzero : Tendsto (fun σ => FJ M m ψ b₀ (res H f σ) g₀ (Ω 1)) ((ufil p : Ultrafilter ℝ) : Filter ℝ) (𝓝 0) := by
        refine ((eis_pole_free hRS hEH hp hn M m ψ hψ b₀ hb.2 hχ' hθ hΩ hH hf g₀).mono_left hU).congr' ?_
        refine hU ?_
        filter_upwards [ev_Ioc p] with σ hσ
        have e : res H f σ = ((σ - p / 2 : ℝ) : ℂ) • eisS (fam H f ((p : ℂ) / 2) (σ : ℂ)) := rfl
        rw [e, fj_smul, hFJ D p 1 p' hn M m ψ hψ b₀ hb.2 1 χ' hecke_one hχ' θ hθ Ω hΩ (σ : ℂ) _
          (fam_cont_at hH hf.1 _ σ) (fam_law_real hH hf σ) (by simpa using hσ.1) g₀]
      exact tendsto_nhds_unique hlim hzero
  have := congrFun (key ((M.sh 0)⁻¹ * g)) 0
  simpa [← mul_assoc] using this

theorem resA_n_inv (hME : MapsExist) (hHE : HeckeEta) (hFJ : FJEis) (hPB : PcBound) (hRS : RSec) (hEH : EisHol) (hTT : ThTotal)
    (hPF : PcFc) (hS : SphBound) (hp : 2 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) {nb : hermA D p → G D p}
    {lam : Measure (hermA D p)} {𝓖 : Set (hermA D p)} (hCd : CoefData (D := D) (n := p) nb lam 𝓖) (b : hermA D p) (g : G D p) :
    resA H f (nb b * g) = resA H f g := by
  have hp1 : 1 ≤ p := by omega
  have hAc := resA_cont hS hp1 hH hC hcov hf
  have hAl := resA_leftInv hS hp1 hH hC hcov hf
  obtain ⟨ψ, hψ⟩ := GlobalTheory.CompanionTheory.AdelicChar.exists_isCharAF D.host.F D.sp.cm.totReal
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  have hn : 1 + (p - 1) = p := by omega
  obtain ⟨⟨M⟩, ⟨m⟩⟩ := hME D p 1 (p - 1) hn
  obtain ⟨⟨M0⟩, ⟨m0⟩⟩ := hME D p 0 p (zero_add p)
  have hr : RankLT ψ (resA H f) 1 := (hPF D p 1 (p - 1) hn M m ψ hψ _ hAc hAl).1 fun b₀ hb g =>
    pc_vanish hHE hFJ hPB hRS hEH hTT hS hp hH hC hcov hf hn M m ψ hψ hθ b₀ hb g
  let b0 : HermE D 0 := ⟨0, by ext i; exact i.elim0⟩
  let β : HermE D p := ⟨0, by simp⟩
  have hdet : b0.1.det ≠ 0 := by simp [b0]
  have hβ : IsExt (zero_add p) b0 β := by
    ext i j
    simp only [bl, Matrix.submatrix_apply, β]
    generalize (finSumFinEquiv.trans (finCongr (zero_add p))).symm i = a
    generalize (finSumFinEquiv.trans (finCongr (zero_add p))).symm j = c
    rcases a with a | a
    · exact a.elim0
    · rcases c with c | c
      · exact c.elim0
      · simp
  have h2 := (hPF D p 0 p (zero_add p) M0 m0 ψ hψ _ hAc hAl).2 hr b0 hdet β hβ nb lam 𝓖 hCd
  exact GlobalTheory.T.invariance_of_constant_fourier_coefficient D p ψ nb lam 𝓖 hCd _ hAc hAl β rfl (fun g => by
    rw [← h2 g]; exact GlobalTheory.T.partial_coefficient_rank_zero D p (zero_add p) M0 m0 ψ b0 _ g) b g

theorem resMu_main : MapsExist → HtExist → HeckeEta → FJEis → PcBound → RSec → EisHol → ThTotal → PcFc → SphBound →
    PositivityTheory.PfSWUS.FourierZero → PositivityTheory.PfSWUS.CoefDataExists → ResMu := by
  intro hME hHt hHE hFJ hPB hRS hEH hTT hPF hS _ hCE D p hp
  have hp1 : 1 ≤ p := by omega
  obtain ⟨⟨H, hH⟩, C, hC, hcov⟩ := hHt D p
  refine ⟨fun f => resA H f 1, ?_⟩
  exact
    { add := fun f f' hf hf' => resA_add hS hp1 hH hC hcov hf hf' 1
      smul := fun c f hf => resA_smul hS hp1 hH hC hcov hf c 1
      pos := fun f hf h => resA_pos hS hp1 hH hC hcov hf h 1
      bound := fun H' hH' => resA_bound hS hp1 hH hC hcov H' hH'
      inv_n := fun x b hx f hf => by
        have hb : adj b = b := (GlobalTheory.StdUnn.Model.exists_unip b).1 ⟨x, hx⟩
        obtain ⟨nb, lam, 𝓖, hCd⟩ := hCE D p
        have e : x = nb ⟨b, hb⟩ * 1 := GlobalTheory.StdUnn.LeftInvSect.mat_inj (by rw [mul_one, hx, hCd.1])
        have h1 := resA_translate hS hp1 hH hC hcov hf x
        have h2 := resA_n_inv hME hHE hFJ hPB hRS hEH hTT hPF hS hp hH hC hcov hf hCd ⟨b, hb⟩ 1
        rw [← e] at h2
        exact h1.symm.trans h2
      inv_rat := fun γ hγ f hf => by
        have h1 := resA_translate hS hp1 hH hC hcov hf γ
        have h2 := resA_leftInv hS hp1 hH hC hcov hf γ hγ 1
        rw [mul_one] at h2
        exact h1.symm.trans h2
      lim := fun f hc hl a ha => (resA_lim hS hp1 hH hC hcov f hc hl a ha).2 }

end GlobalTheory.CompanionTheory.ResMu
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.theta_sum_invariant_weyl_involution : ∀ (D : D7) (n : ℕ) (V : HSp D) ψ χ θ μ ω, HidaSetting D n V ψ χ θ μ ω →
  ∀ g : G D n, mat g = blk4 0 1 (-1) 0 →
  ∀ Φ : schwartzA θ V.rank n,
    ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω g Φ).1 (ξ.map (incA D)) =
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  first | exact @GlobalTheory.CompanionTheory.ThetaPoisson.theta_weyl | exact GlobalTheory.CompanionTheory.ThetaPoisson.theta_weyl | (intros; apply GlobalTheory.CompanionTheory.ThetaPoisson.theta_weyl <;> assumption)
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold

theorem unfold2 : Unfold2 := by
  intro D ψ hψ θ hθ V n r hrn μ 𝓕 hμ μr h𝓕r c a hca b Φ hΦ
  obtain ⟨𝓕r, hμr⟩ := h𝓕r
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hrn
  obtain ⟨μs, 𝓕s, hμs⟩ := exists_isCovolOne D V.rank s
  obtain ⟨hΦc, B, hB⟩ := GlobalTheory.T.schwartz_lattice_sum_bounded D θ hθ V.rank (r + s) Φ hΦ
  have ha : IsUnit a.det := hca.1

  let e : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E ≃
      Matrix (Fin V.rank) (Fin (r + s)) D.host.E :=
    joinEquiv.trans
      { toFun := fun ξ => ξ * a
        invFun := fun ξ => ξ * a⁻¹
        left_inv := fun ξ => Matrix.mul_nonsing_inv_cancel_right a ξ ha
        right_inv := fun ξ => Matrix.nonsing_inv_mul_cancel_right a ξ ha }
  set T : Mx D V.rank (r + s) → ℂ := fun y => ∑' ξ : Matrix (Fin V.rank) (Fin (r + s)) D.host.E,
    Heisenberg₂ ψ V (HMul.hMul (zy y) ((repMat (D.sp.cm.sig : D.host.E →+* D.host.E) b.1 a).map (incA D))) Φ
      (ξ.map (incA D)) with hT
  have hform : ∀ y₁ y₂, T (colJoin y₁ y₂) =
      ∑' pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
        cellTerm ψ V b.1 a Φ pq.1 pq.2 y₁ y₂ := by
    intro y₁ y₂
    obtain ⟨hx, hy⟩ := GlobalTheory.T.weil_action_block_matrix_components D V.rank r s b.1 a y₁ y₂
    rw [hT]
    dsimp only
    rw [← e.tsum_eq]
    exact tsum_congr fun pq => GlobalTheory.T.block_weil_action_theta_unfolding D ψ hψ V r s b.1 b.2 a ha Φ y₁ y₂ _ hx hy pq.1 pq.2
  have hper : ∀ γ ∈ ratMx D V.rank (r + s), ∀ y, T (γ + y) = T y := by
    intro γ hγ y
    obtain ⟨g, rfl⟩ := mem_ratMx.1 hγ
    rw [← colJoin_colL_colR g, ← colJoin_colL_colR y, rat_colJoin, ← colJoin_add, hform, hform,
      add_comm (rat (colL g)), add_comm (rat (colR g))]
    exact GlobalTheory.T.lattice_sum_shift_invariant D ψ hψ V r s b.1 a Φ (colL g) (colR g) (colL y) (colR y)
  have hE := GlobalTheory.T.covolume_one_column_join_product D V.rank r s μr 𝓕r μs 𝓕s hμr hμs
  show ∫ y in 𝓕, T y ∂μ = _
  rw [covolOne_integral_eq hE hμ T hper]
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D V.rank r
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := lattice_Mx D V.rank s
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := lattice_Mx D V.rank (r + s)
  haveI : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  haveI : BorelSpace (Mx D V.rank s) := ⟨rfl⟩
  haveI : BorelSpace (Mx D V.rank (r + s)) := ⟨rfl⟩
  have hc : Continuous fun z : Mx D V.rank r × Mx D V.rank s => colJoin z.1 z.2 := by
    refine continuous_matrix fun i k => ?_
    simp only [colJoin, Matrix.of_apply]
    rcases finSumFinEquiv.symm k with j | j
    · exact (continuous_apply_apply i j).comp continuous_fst
    · exact (continuous_apply_apply i j).comp continuous_snd
  have hc' : Continuous fun y : Mx D V.rank (r + s) => ((colL y, colR y) : Mx D V.rank r × Mx D V.rank s) := by
    refine Continuous.prodMk (continuous_matrix fun i j => ?_) (continuous_matrix fun i j => ?_)
    · exact continuous_apply_apply i (Fin.castAdd s j)
    · exact continuous_apply_apply i (Fin.natAdd r j)
  let hj : (Mx D V.rank r × Mx D V.rank s) ≃ₜ Mx D V.rank (r + s) :=
    { (joinEquiv : (Mx D V.rank r × Mx D V.rank s) ≃ Mx D V.rank (r + s)) with
      continuous_toFun := hc
      continuous_invFun := hc' }
  have hmp : MeasurePreserving hj.toMeasurableEquiv (μr.prod μs)
      ((μr.prod μs).map fun z => colJoin z.1 z.2) := ⟨hj.toMeasurableEquiv.measurable, rfl⟩
  have h1 := hmp.setIntegral_image_emb hj.toMeasurableEquiv.measurableEmbedding T (𝓕r ×ˢ 𝓕s)
  erw [h1]
  have h2 : ∀ z : Mx D V.rank r × Mx D V.rank s, T (hj.toMeasurableEquiv z) =
      ∑' pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
        cellTerm ψ V b.1 a Φ pq.1 pq.2 z.1 z.2 := fun z => hform z.1 z.2
  simp only [h2]
  rw [GlobalTheory.T.eisenstein_coefficient_block_unfolding D ψ hψ V r s μr 𝓕r μs 𝓕s hμr hμs b.1 a ha Φ hΦc B hB]
  exact GlobalTheory.T.eisenstein_hermitian_integral_unfolding D ψ V r s μr 𝓕r hμr c a hca b Φ

end GlobalTheory.CompanionTheory.EisUnfold

end
end

section


theorem _root_.GlobalTheory.T.factor_through_finite_flat : PositivityTheory.Tls2.Zar3.Ch1.FactorThroughFF := by
  first | exact @GlobalTheory.CompanionTheory.FlatFactor.factorThroughFF | exact GlobalTheory.CompanionTheory.FlatFactor.factorThroughFF | (intros; apply GlobalTheory.CompanionTheory.FlatFactor.factorThroughFF <;> assumption)
end

section


theorem _root_.GlobalTheory.T.finite_of_finite_fibres : PositivityTheory.Tls2.Zar3.Ch1.FiniteOfFibres := by
  first | exact @GlobalTheory.CompanionTheory.AbFibre.finiteOfFibres | exact GlobalTheory.CompanionTheory.AbFibre.finiteOfFibres | (intros; apply GlobalTheory.CompanionTheory.AbFibre.finiteOfFibres <;> assumption)
end

section


theorem _root_.GlobalTheory.T.flat_of_fibres_finite : PositivityTheory.Tls2.Zar3.Ch1.FlatOfFibresFinite := by
  first | exact @GlobalTheory.CompanionTheory.FlatFib.flatOfFibresFinite | exact GlobalTheory.CompanionTheory.FlatFib.flatOfFibresFinite | (intros; apply GlobalTheory.CompanionTheory.FlatFib.flatOfFibresFinite <;> assumption)
end

section


theorem _root_.GlobalTheory.T.kernel_finite_flat : PositivityTheory.Tls2.Zar3.Ch1.KernelFinFlat := by
  first | exact @GlobalTheory.CompanionTheory.Ar.KerFF.kernelFinFlat | exact GlobalTheory.CompanionTheory.Ar.KerFF.kernelFinFlat | (intros; apply GlobalTheory.CompanionTheory.Ar.KerFF.kernelFinFlat <;> assumption)
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegSocle

theorem dec_injective {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) :
    Function.Injective (dec Δ) :=
  (GlobalTheory.T.segment_term_injective hA Δ).comp Fin.rev_injective

theorem ncard_perm_dec_le_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) :
    Set.ncard {e : Fin Δ.len ≃ Fin Δ.len | ∀ a, dec Δ a = dec Δ (e a)} ≤ 1 := by
  rw [Set.ncard_le_one_iff_subsingleton]
  intro e₁ h₁ e₂ h₂
  ext a
  have i₁ := dec_injective hA Δ (h₁ a)
  have i₂ := dec_injective hA Δ (h₂ a)
  rw [← i₁, ← i₂]

theorem exists_isSocle_prodIrr_dec : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) {N : ℕ}
    (hd : ∑ a, (dec Δ a).1 = N), ∃ τ : IrrRep (GL (Fin N) k), IsSocle τ.ρ (prodIrr (dec Δ) hd) := by
  intro k _ _ _ _ hA Δ N hd
  apply GlobalTheory.CompanionTheory.SocleJm.exists_isSocle_of_jm_le_one hA (dec Δ) hd
  have hc : ∀ a, (dec Δ a).IsCusp := fun a => Δ.isCusp_term (Fin.rev a)
  rw [GlobalTheory.T.jacquet_multiplicity_cuspidal_product hA (dec Δ) (dec Δ) hd hd hc hc]
  exact_mod_cast ncard_perm_dec_le_one hA Δ

end GlobalTheory.CompanionTheory.SegSocle

end
end

section

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

theorem _root_.GlobalTheory.T.commutant_reduction_real : PositivityTheory.RgBcC.RealD.LeviCommutantWordReduction := by
  first | exact @GlobalTheory.CompanionTheory.BlockCapelliWords.commutant_block_capelli_words | exact GlobalTheory.CompanionTheory.BlockCapelliWords.commutant_block_capelli_words | (intros; apply GlobalTheory.CompanionTheory.BlockCapelliWords.commutant_block_capelli_words <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.centre_character_continuous_unit : ∀ (D : D7) (ρ : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ,
  Continuous (chz ψ b₀) ∧ ∀ z, ‖chz ψ b₀ z‖ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.CentreChar.continuous_and_norm_chz | exact GlobalTheory.CompanionTheory.CentreChar.continuous_and_norm_chz | (intros; apply GlobalTheory.CompanionTheory.CentreChar.continuous_and_norm_chz <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.centre_character_properties : ∀ {D : D7} {ρ : ℕ} (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ, (∀ z z' : hermA D ρ, chz ψ b₀ (z + z') = chz ψ b₀ z * chz ψ b₀ z') ∧ (∀ z, ‖chz ψ b₀ z‖ = 1) ∧ (∀ z ∈ ratHerm D ρ, chz ψ b₀ z = 1) ∧ Continuous (chz ψ b₀) := by
  first | exact @GlobalTheory.CompanionTheory.FJE.CentralChar.chz_facts | exact GlobalTheory.CompanionTheory.FJE.CentralChar.chz_facts | (intros; apply GlobalTheory.CompanionTheory.FJE.CentralChar.chz_facts <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.height_pullback_first_block : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (ι : G D ρ →* G D n), Continuous ι →
  (∀ (h : G D ρ) (a b c d : Mx D ρ ρ), mat h = blk4 a b c d →
    mat (ι h) = blk4 (bl hn a 0 0 1) (bl hn b 0 0 0) (bl hn c 0 0 0) (bl hn d 0 0 1)) →
  ∀ H : G D n → ℝ≥0, IsHt H → IsHt (fun h : G D ρ => H (ι h)) := by
  first | exact @GlobalTheory.CompanionTheory.HtPull.isHt_blockPull | exact GlobalTheory.CompanionTheory.HtPull.isHt_blockPull | (intros; apply GlobalTheory.CompanionTheory.HtPull.isHt_blockPull <;> assumption)
end
