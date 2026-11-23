module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle011
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle010
public import Formalism.LocalToGlobal.InertKernelTheory.DefsRepFrame
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle012
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle009
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle003
public import Formalism.LocalRingCardinality.Bundle002
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.GlobalOrthonormalBasisFour
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntWAPlaces
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.Bundle003
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle005
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThickLetterWordLatticeSurjectionHypotheses
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle088
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle185
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle020
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle186
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle174
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle133
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalTwistRamifiedCharNeSelf
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Formalism.LocalToGlobal.HermitianForms.Bundle011
public import Formalism.LocalToGlobal.GroupLattices.StdSubAtOfRing
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle149
import Formalism.LocalToGlobal.KernelLattices.Bundle001
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.IsComplRatCompl
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.NrmAMemAdForms
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

theorem _root_.GlobalTheory.T.isUnitarySphericalSatake_of_unitarisable_hasSatake : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ), letI := GlobalTheory.LocalData.complRel w; haveI := GlobalTheory.LocalData.isLocalField w; ∀ (π : Irr (w.adicCompletion E) n) (α : Fin n → ℂˣ), HasSatake π.π α → IsUnitarisable π.π → GlobalTheory.RowSatakeBound.IsUnitarySatakeAt w n (Finset.univ.val.map fun i => (α i : ℂ)) := by
  first | exact @GlobalTheory.SatHecke.isUnitarySatakeAt_of_hasSatake | exact GlobalTheory.SatHecke.isUnitarySatakeAt_of_hasSatake | (intros; apply GlobalTheory.SatHecke.isUnitarySatakeAt_of_hasSatake <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

theorem _root_.GlobalTheory.T.standardSeries_scaled_eq_orthonormalBasisSeries : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' r : ℕ) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hz : Fin r → MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]), (∀ i, MvPowerSeries.constantCoeff (hz i) = 0) → (∀ k, ∑ i, MvPowerSeries.C (Formalism.L2.KerInert.RepFrame.lamB D lam b k i) * hz i = ∑ j : OrbitPlaces.Pl D × Fin N × Fin N', MvPowerSeries.C (chgB D lam P P' k ((0 : ZMod 1), (tauPl D j.1, j.2))) * MvPowerSeries.X j) → ∀ (c : ℂ_[p]) (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]), (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => (MvPowerSeries.C c * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) (stdSer D lam (fun _ => 1) P P' G) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) = MvPowerSeries.subst hz (thOrth D lam c b G) := by
  first | exact @GlobalTheory.KerStd.HypCoord.stdSer_scaled_eq_thOrth | exact GlobalTheory.KerStd.HypCoord.stdSer_scaled_eq_thOrth | (intros; apply GlobalTheory.KerStd.HypCoord.stdSer_scaled_eq_thOrth <;> assumption)
end

section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd.HostInert


open Formalism.InvariantFactorPaths.G7 (lgF at1) in
open Formalism.L2.G.Pend (k0ToC wittFractionAlgebraCp) in
theorem inParamK_eq {l : ℕ} [Fact l.Prime] {ι : Type} (f : MvPowerSeries ι ℂ_[l]) :
    @Formalism.MainNotions.FormalGroupSystem.inParamK l _ ι ℂ_[l] _ (wittFractionAlgebraCp l) f = MvPowerSeries.subst (fun i => at1 i (lgF ℂ_[l] l)) f := by
  unfold Formalism.MainNotions.FormalGroupSystem.inParamK
  have hlog : PowerSeries.map (k0ToC l) (Formalism.MainNotions.FormalGroupSystem.logF l) = lgF ℂ_[l] l := by
    ext n
    rw [PowerSeries.coeff_map]

    simp only [Formalism.MainNotions.FormalGroupSystem.logF, lgF, PowerSeries.coeff_mk, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_mul]
    split_ifs <;> simp
  congr 1
  funext i
  rw [show @algebraMap (Formalism.MainNotions.FormalGroupSystem.K0 l) ℂ_[l] _ _ (wittFractionAlgebraCp l) = k0ToC l from rfl, hlog]
  rfl

theorem jacobi_of_class (D : D7) (p : ℕ) [Fact p.Prime] (h : IsResidueClassZero D p ∨ IsSg D p) :
    jacobiSym (-(D.host.d : ℤ)) p = -1 := by
  have hp : p.Prime := Fact.out
  have hd : D.host.d.Prime := D.host.hyp.2.1
  have key : p ≠ D.host.d ∧ jacobiSym (-(D.host.d : ℤ)) p ≠ 1 := by
    have h' : D.host.cls p = PrimeClass.inertClass ∨
        D.host.cls p = PrimeClass.signal := h
    rcases h' with h' | h'
    · obtain ⟨-, -, h3, h4, -⟩ := (primeClass_eq_inert_iff _).1 h'
      exact ⟨h3, h4⟩
    · obtain ⟨-, -, h3, h4, -⟩ := (primeClass_eq_signal_iff _).1 h'
      exact ⟨h3, h4⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rcases jacobiSym.trichotomy (-(D.host.d : ℤ)) p with h0 | h1 | h1
  · exfalso
    rw [jacobiSym.eq_zero_iff_not_coprime] at h0
    apply h0
    have : Nat.Coprime D.host.d p := (Nat.coprime_primes hd hp).2 key.1.symm
    simpa [Int.gcd_neg, Int.gcd_natCast_natCast] using this
  · exact absurd h1 key.2
  · exact h1

theorem hostAt_inert : Formalism.L2.KerInert.GenusOneModelExistsLattice → Formalism.L2.KerInert.Rep.CurveDict → Formalism.L2.KerInert.IntInert → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), 5 ≤ p → (IsResidueClassZero D p ∨ IsSg D p) → HostAt B χ p lam := by
  intro h1 h2 h3 D cc δ B χ hc hδ hχ p _ lam h5 hcl
  have hin := jacobi_of_class D p hcl
  obtain ⟨cc', δ', g, -, -, hL, hlam, hAt, hM, hLT⟩ := h1 D cc δ hc hδ p h5 hin lam
  obtain ⟨g2, g3, ε, s2, -, -, -, -, hn, ⟨a1, a2, a3, a4, a5, -, F, hF, -⟩, hD⟩ := h2 D cc' δ' p g hLT hAt h5 hin hM
  obtain ⟨σ, hσ, -⟩ := Formalism.L2.Th1.D.fieldDataCM p h5
  refine ⟨_, g2, g3, s2, ε, σ, F, hn, ⟨h5, a1, a2, a3, a4, hσ, hF, a5 σ hσ⟩, ?_⟩
  intro N N' L L' hA
  obtain ⟨r, b, hb, ho⟩ := Formalism.L2.KerInert.orthBasisExists_of Formalism.L2.KerInert.global_orthonormal_basis_four
    Formalism.L2.KerInert.weakApprox_of_approx_and_separation D p h5 hin N N' L L' hA
  refine ⟨r, b, hb, ho, fun G hG => ?_⟩
  obtain ⟨C, wq, hC, hw, hd⟩ := hD D
  have hΛ : g.abelian₂ = B.tor.abelian₂ := hAt.2.2.2.1.trans hL
  subst hlam
  rw [hΛ] at hC hw hd
  have := hd N N' r b G (h3 D cc δ B hc hδ χ hχ p h5 hin g.lam N N' L L' hA G hG C wq r b hC hw hb ho)
  rw [HostLog.iff_phSum]
  rw [inParamK_eq] at this
  exact this

end GlobalTheory.KerStd.HostInert
end
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.RecS

theorem famJ_CLw_eq {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) :
    (Fm.params x hx i).CLw = Fm.PK.getD 7 0 := by
  rw [← Fm.params_K x hx i]
  rfl

theorem famJ_eps_pos {eps : ℝ} (Fm : FamP eps) : 0 < eps := by
  obtain ⟨i⟩ := Fm.Ix_zero
  rw [← Fm.L_eps 0 i]
  exact (Fm.L 0 i).sc.eps_pos

theorem famJ_ez_pos {eps : ℝ} (Fm : FamP eps) : 0 < Fm.ez := by
  obtain ⟨i⟩ := Fm.Ix_zero
  rw [← Fm.L_ez 0 i]
  exact (Fm.L 0 i).sc.ez_pos

theorem fam_joints : ∀ {eps : ℝ} (Fm : FamP eps) (C₂ : ℝ), (∀ D : D7, LocalSituation.adm7 D) →
    (∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) →
    ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (i : Fm.Ix x) (HW : HWOf (Fm.D x i).loc),
      LJ.ConclusionJa (Fm.D x i) → RecS.JointB (Fm.L x i) HW C₂ ∧ RecS.JointCD (Fm.L x i) HW := by
  intro eps Fm C₂ h7 hF
  obtain ⟨xB, hB⟩ := GlobalTheory.T.inertLongOrbitWordConditions_of_large_scale eps Fm.ez C₂ (Fm.PK.getD 7 0) (famJ_eps_pos Fm) (famJ_ez_pos Fm)
  obtain ⟨xC, hC⟩ := GlobalTheory.T.inertPrimeWordConditions_of_large_scale eps Fm.ez (Fm.PK.getD 7 0) (famJ_eps_pos Fm) (famJ_ez_pos Fm)
  refine ⟨max xB xC, fun x hx h1 i HW hJ => ⟨?_, ?_⟩⟩
  · refine hB _ _ (Fm.params x h1 i) HW (Fm.L_eps x i) (Fm.L_ez x i) (famJ_CLw_eq Fm x h1 i).le ?_ (h7 _) (hF _) hJ
    rw [Fm.L_x x i h1]
    exact (le_max_left _ _).trans hx
  · refine hC _ _ (Fm.params x h1 i) HW (Fm.L_eps x i) (Fm.L_ez x i) (famJ_CLw_eq Fm x h1 i).le ?_ (h7 _) (hF _) hJ
    rw [Fm.L_x x i h1]
    exact (le_max_right _ _).trans hx

end GlobalTheory.HTW.RecS
end

section

open Matrix

namespace GlobalTheory.Hk3.HoweG

theorem sum_charSum_eq_card_filter {B ι M : Type} [AddCommGroup B] [Fintype B] [AddCommGroup M] [Module ℂ M]
    (Y : Finset ι) (x : ι) (hx : x ∈ Y) (χ : B → ι → ℂ)
    (hmul : ∀ b b', ∀ y ∈ Y, χ (b + b') y = χ b y * χ b' y) (hne : ∀ b, ∀ y ∈ Y, χ b y ≠ 0) (v : ι → M)
    [DecidablePred (fun y => ∀ b, χ b y = χ b x)] :
    ∑ b, (χ b x)⁻¹ • ∑ y ∈ Y, χ b y • v y =
      (Fintype.card B : ℂ) • ∑ y ∈ Y.filter (fun y => ∀ b, χ b y = χ b x), v y := by
  have h0 : ∀ y ∈ Y, χ 0 y = 1 := by
    intro y hy
    have e := hmul 0 0 y hy
    rw [add_zero] at e
    exact mul_left_cancel₀ (hne 0 y hy) (by rw [mul_one]; exact e.symm)
  have key : ∀ y ∈ Y, ∑ b, (χ b x)⁻¹ * χ b y =
      if (∀ b, χ b y = χ b x) then (Fintype.card B : ℂ) else 0 := by
    intro y hy
    split_ifs with hP
    · simp [hP, inv_mul_cancel₀ (hne _ x hx)]
    · let φ : AddChar B ℂ :=
        { toFun := fun b => (χ b x)⁻¹ * χ b y
          map_zero_eq_one' := by simp [h0 x hx, h0 y hy]
          map_add_eq_mul' := by
            intro b b'
            show (χ (b + b') x)⁻¹ * χ (b + b') y = ((χ b x)⁻¹ * χ b y) * ((χ b' x)⁻¹ * χ b' y)
            rw [hmul b b' x hx, hmul b b' y hy, mul_inv]
            ring }
      have hφ : φ ≠ 1 := by
        intro h1
        apply hP
        intro b
        have e : φ b = 1 := by rw [h1, AddChar.one_apply]
        exact ((inv_mul_eq_one₀ (hne b x hx)).mp e).symm
      show ∑ b, φ b = 0
      exact AddChar.sum_eq_zero_of_ne_one hφ
  calc ∑ b, (χ b x)⁻¹ • ∑ y ∈ Y, χ b y • v y = ∑ y ∈ Y, (∑ b, (χ b x)⁻¹ * χ b y) • v y := by
        simp_rw [Finset.smul_sum, smul_smul, Finset.sum_smul]; exact Finset.sum_comm
    _ = ∑ y ∈ Y, (if (∀ b, χ b y = χ b x) then (Fintype.card B : ℂ) else 0) • v y :=
        Finset.sum_congr rfl (fun y hy => by rw [key y hy])
    _ = _ := by
        rw [Finset.smul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        split_ifs <;> simp

end GlobalTheory.Hk3.HoweG

namespace GlobalTheory.Hk3.HoweG

open GlobalTheory.Hk3

theorem gramClass_sum_mem_span_selfDual_vac : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, GlobalTheory.Hk3.LocVac ρ s → ∀ x : Matrix (Fin n') (Fin n) L,
    (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    ∃ C : Finset (Matrix (Fin n') (Fin n) L), ∃ c : Matrix (Fin n') (Fin n) L → ℂ, x ∈ C ∧
      (∀ y ∈ C, c y ≠ 0 ∧ GlobalTheory.Hk3.HoweG.HomA σ JS JT x y ∧ GlobalTheory.Hk3.HoweG.GramEq σ JT x y) ∧
      (∀ y ∈ C, ∀ y' ∈ C, y ≠ y' → y - y' ∉ GlobalTheory.Hk3.HoweDuality.intMat L n' n) ∧
      ∑ y ∈ C, c y • ρ y s ∈ Submodule.span ℂ {w : M | ∃ a : GL (Fin n) L, GlobalTheory.Hk3.HoweG.SelfDual σ JS a ∧
        ∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) → ρ (u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) w = w} := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP s hvac x hx
  classical
  have hP' := hP
  obtain ⟨hU, hodd, hSint, hTint, hS, hT, hδ, hpsi_int, hpsi_ne, -, hρ, -, -, -⟩ := hP'
  obtain ⟨a, ha1, ha2, ha3, ha4⟩ := GlobalTheory.T.selfDual_lattice_of_integral_gramMatrix L ϖ σ q n n' JS JT hU hodd hSint hTint hS hT x hx
  obtain ⟨Y, hxY, hYA, hYd, B, _, _, b0, l, hb0, hl, hcov, hmul, hsep⟩ :=
    GlobalTheory.T.exists_gramClass_reps_selfDualLattice_group L ϖ σ q δ n n' JS JT ψ hU hodd hSint hTint hS hT hδ hpsi_int hpsi_ne x hx a ⟨ha1, ha2, ha3, ha4⟩
  have hψinv : ∀ a, ψ a * ψ (-a) = 1 := fun a => by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have hshift : ∀ y u, u ∈ HoweDuality.intMat L n' n →
      ρ (y + u) s = ψ (-((locH σ δ JS JT y u + σ (locH σ δ JS JT y u)) / 2)) • ρ y s := by
    intro y u hu
    have h1 : ρ y s = ψ ((locH σ δ JS JT y u + σ (locH σ δ JS JT y u)) / 2) • ρ (y + u) s := by
      have := congrArg (fun f => f s) (hρ y u)
      simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
      rwa [hvac u hu] at this
    rw [h1, smul_smul, mul_comm, hψinv, one_smul]
  set χ : B → Matrix (Fin n') (Fin n) L → ℂ :=
    fun b y => ψ (-((locH σ δ JS JT y (l b y) + σ (locH σ δ JS JT y (l b y))) / 2)) with hχ
  have hne : ∀ b, ∀ y ∈ Y, χ b y ≠ 0 := by
    intro b y _ h0
    have := hψinv (-((locH σ δ JS JT y (l b y) + σ (locH σ δ JS JT y (l b y))) / 2))
    rw [show ψ (-((locH σ δ JS JT y (l b y) + σ (locH σ δ JS JT y (l b y))) / 2)) = χ b y from rfl, h0,
      zero_mul] at this
    exact zero_ne_one this
  set Spn := Submodule.span ℂ {w : M | ∃ a : GL (Fin n) L, SelfDual σ JS a ∧
        ∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) →
          ρ (u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) w = w} with hSpn

  have hvacb : ∀ b, ∑ y ∈ Y, χ b y • ρ y s ∈ Spn := by
    intro b
    have hinj : Set.InjOn (fun y => y + l b y) Y := by
      intro y hy y' hy' e
      refine hYd y hy y' hy' ?_
      have e' : y - y' = l b y' - l b y := by
        have := congrArg (fun z => z - l b y - y') e
        simp only at this
        rw [show y + l b y - l b y - y' = y - y' by abel, show y' + l b y' - l b y - y' = l b y' - l b y by abel] at this
        exact this
      rw [e']
      exact (HoweDuality.intMat L n' n).sub_mem (hl b y' hy').1 (hl b y hy).1
    have hsum : ∑ y ∈ Y, χ b y • ρ y s = ∑ z ∈ Y.image (fun y => y + l b y), ρ z s := by
      rw [Finset.sum_image hinj]
      exact Finset.sum_congr rfl (fun y hy => (hshift y (l b y) (hl b y hy).1).symm)
    rw [hsum]
    refine Submodule.subset_span ⟨b0 b, hb0 b, ?_⟩
    refine GlobalTheory.T.vacuumTranslateSum_selfDualLattice_fixed L ϖ σ q δ n n' JS JT ψ M ρ ω hP s hvac (b0 b) (hb0 b) _ ?_ ?_ ?_
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      exact (hl b y hy).2
    · intro z hz z' hz' hzz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hz'
      have : y = y' := by
        refine hYd y hy y' hy' ?_
        have e : y - y' = (y + l b y - (y' + l b y')) + (l b y' - l b y) := by abel
        rw [e]
        exact (HoweDuality.intMat L n' n).add_mem hzz
          ((HoweDuality.intMat L n' n).sub_mem (hl b y' hy').1 (hl b y hy).1)
      rw [this]
    · intro u hu
      obtain ⟨y, hy, hm⟩ := hcov b u hu
      exact ⟨y + l b y, Finset.mem_image_of_mem _ hy, hm⟩
  have hF := sum_charSum_eq_card_filter Y x hxY χ hmul hne (fun y => ρ y s)
  have hcard : (Fintype.card B : ℂ) ≠ 0 := by
    have : 0 < Fintype.card B := Fintype.card_pos
    exact_mod_cast this.ne'
  refine ⟨Y.filter (fun y => ∀ b, χ b y = χ b x), fun _ => 1, ?_, ?_, ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨hxY, fun _ => rfl⟩
  · intro y hy
    obtain ⟨hy1, hy2⟩ := Finset.mem_filter.mp hy
    exact ⟨one_ne_zero, hYA y hy1, (hsep y hy1).mpr hy2⟩
  · intro y hy y' hy' hne' hm
    exact hne' (hYd y (Finset.mem_filter.mp hy).1 y' (Finset.mem_filter.mp hy').1 hm)
  · simp only [one_smul]
    have e : ∑ y ∈ Y.filter (fun y => ∀ b, χ b y = χ b x), ρ y s =
        (Fintype.card B : ℂ)⁻¹ • ∑ b, (χ b x)⁻¹ • ∑ y ∈ Y, χ b y • ρ y s := by
      rw [hF, smul_smul, inv_mul_cancel₀ hcard, one_smul]
    rw [e]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (hvacb b))

end GlobalTheory.Hk3.HoweG
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_homLattice_iff_integralMatrix_splitChart : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ (S T : HSp D) (βS : GL (Fin S.rank) (Fv D.host.F v)) (βT : GL (Fin T.rank) (Fv D.host.F v)), Frame S e π βS → Frame T e π βT → ∃ c : Fv D.host.F v, c ≠ 0 ∧ ∀ u : WO S T, IsHalf e u → (u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True) ↔ IntM (Ov D v) (c • ((βT⁻¹).1 * Matrix.map u π * βS.1))) := by
  first | exact @GlobalTheory.SplitHomLattice.mem_latO_iff_intM | exact GlobalTheory.SplitHomLattice.mem_latO_iff_intM | (intros; apply GlobalTheory.SplitHomLattice.mem_latO_iff_intM <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff

namespace GlobalTheory.CxForm

def holCount {n : ℕ} (S : Finset (Fin (n + n))) : ℕ := (S.filter (·.val < n)).card

def holGe (n p : ℕ) : Submodule ℂ (Alt n) :=
  Submodule.span ℂ (bas n '' {S | p ≤ holCount S})

theorem mem_holGe_iff {n p : ℕ} (β : Alt n) :
    β ∈ holGe n p ↔ ∀ S, (bas n).repr β S ≠ 0 → p ≤ holCount S := by
  rw [holGe, Module.Basis.mem_span_image]
  constructor
  · intro h S hS
    exact h (Finsupp.mem_support_iff.2 hS)
  · intro h S hS
    exact h S (Finsupp.mem_support_iff.1 hS)

end GlobalTheory.CxForm
end
end

section

set_option autoImplicit false

noncomputable section

open MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff

namespace GlobalTheory.CxForm.HolAtlas

variable {M : Type} [TopologicalSpace M] {n k : ℕ} (A : HolAtlas M n)

def TypeGe (p : ℕ) (α : A.Fld) : Prop :=
  ∀ x S, (bas n).repr (α x) S ≠ 0 → p ≤ (S.filter (·.val < n)).card

end GlobalTheory.CxForm.HolAtlas
end
end

section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep

theorem _root_.GlobalTheory.T.cuspidal_twist_ramified_char_ne_self : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (π : CG E a) (η : HChar E) (v : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ), π.HasSat v B → ¬ η.UnrAt v → π.twist η ≠ π := by
  first | exact @GlobalTheory.TwistRamified.twist_ne | exact GlobalTheory.TwistRamified.twist_ne | (intros; apply GlobalTheory.TwistRamified.twist_ne <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.hServTwoSidesJoint0 : ∀ {D : D7} (Gt : GatTies D) (c : LatCmp D) (g : GroupCompatibilityAll D Gt c) (C : ColsTiedSym D) (full : ColsFullS C), g.herm = full.1.to0 → (g.forms = fun u => (C.forms u).to0) → ∀ u, Joint0 g.herm.lev0 u (g.forms u) := by
  intro D Gt c g C full hh hf u
  rw [hh, hf]
  have e : full.1.to0.lev0 = C.herm.base.lev0 :=
    congrArg (fun X : Formalism.L2.Herm.ColsHermS D => X.base.lev0) full.2
  rw [e]
  exact C.joint0 u
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.involution_spherical_hecke_anti : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D), IsIdemAt e P → (∃ θ : GA D V → GA D V, (∀ g, SuppAt e V g → SuppAt e V (θ g)) ∧ (∀ x y, SuppAt e V x → SuppAt e V y → θ (x * y) = θ y * θ x) ∧ (∀ x, SuppAt e V x → θ (θ x) = x) ∧ (∀ k ∈ locPart V (KsphC V ∅) e, θ k ∈ KsphC V ∅) ∧ ∀ g, SuppAt e V g → ∃ a ∈ locPart V (KsphC V ∅) e, ∃ b ∈ locPart V (KsphC V ∅) e, θ g = a * g * b) ∧ (∀ g, SuppAt e V g → ∃ R : Finset (GA D V), (∀ γ ∈ R, SuppAt e V γ) ∧ IsCosetRep V (locPart V (KsphC V ∅) e) g R) ∧ ∀ ϖ : 𝓞 D.host.E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → (∀ k, k ≤ V.rank → ∃ α, IsHeckeElt V e (ϖ : D.host.E) k α) ∧ ∀ k α, IsHeckeElt V e (ϖ : D.host.E) k α → IsHeckeElt V (cA D e) (star (ϖ : D.host.E)) k α⁻¹ ∧ ∀ (ϖ' : 𝓞 D.host.E) α', ϖ' ∈ P.asIdeal → ϖ' ∉ P.asIdeal ^ 2 → IsHeckeElt V e (ϖ' : D.host.E) k α' → ∃ a ∈ locPart V (KsphC V ∅) e, ∃ b ∈ locPart V (KsphC V ∅) e, α' = a * α * b := by
  first | exact @GlobalTheory.SplitPlace.split_local | exact GlobalTheory.SplitPlace.split_local | (intros; apply GlobalTheory.SplitPlace.split_local <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem chTw_DGam_dvd_mem_DGam : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup), (D.chTw u μ).DGam ∣ (D.mem u).C.DGam := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ
  exact (ex.err.dgam.one u u μ).dvd

end GlobalTheory
end
