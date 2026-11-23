module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle272
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle008
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle072
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle344
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle012
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle157
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle345
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatBesselToFourierJacobiRowMulLaws
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
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBicharPairing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.StepVacForm

section Gen

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem theta_comb (hψ : IsStdChar D ψ (-1)) {c : WO S T →₀ ℂ} (hc : IsFinComb c) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (comb ψ S T c f) :=
  Finset.sum_induction _ (IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add) GlobalTheory.OrientedHeis.theta_zero
    fun u hu => GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 hf (hc u hu))

theorem comb_smul (c : WO S T →₀ ℂ) (a : ℂ) (f : WO S T → ℂ) :
    comb ψ S T c (a • f) = a • comb ψ S T c f := by
  funext w
  simp only [GlobalTheory.FrComb.comb_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem vac_mono {LS : GlobalTheory.FinPl.Lat S} {LT : GlobalTheory.FinPl.Lat T} (P : GlobalTheory.FinPl.Pl D → Prop) {f : WO S T → ℂ}
    (h : GlobalTheory.FinPl.Vac ψ S T LS LT (fun _ => True) f) : GlobalTheory.FinPl.Vac ψ S T LS LT P f := by
  have hle : latO S T (LS : Set _) (LT : Set _) P ≤ latO S T (LS : Set _) (LT : Set _) fun _ => True :=
    AddSubgroup.closure_mono fun w ⟨α, hα, _, hw⟩ => ⟨α, hα, fun _ h => absurd trivial h, hw⟩
  exact ⟨h.1, fun u hu => h.2.1 u (hle hu), fun e he u hu hh => h.2.2 e he u (hle hu) hh⟩

theorem real_fock {χS χT : (AE D)ˣ →* Circle} {om : Om S T} (hθ : IsInfFam θ) (hW : IsWeilDatumO ψ S T χS χT om) (sS sT BS BT)
    {e : WO S T →₀ ℂ} (he : IsFinComb e) {f₀ : WO S T → ℂ} (hf₀ : IsThetaFunO ψ S T f₀) (P) {a : GA D S} (ha : a ∈ GinfC S)
    {a' : GA D T} (ha' : a' ∈ GinfC T) :
    om (a, a') (pureTensorO ψ θ S T sS sT BS BT (comb ψ S T e f₀) P) =
      comb ψ S T e (om (a, a') (pureTensorO ψ θ S T sS sT BS BT f₀ P)) := by
  have h1 : om (1, 1) (comb ψ S T e f₀) = (1 : ℂ) • comb ψ S T e f₀ := by
    rw [one_smul, show ((1, 1) : GA D S × GA D T) = 1 from rfl, map_one, Module.End.one_apply]
  have := (GlobalTheory.FockComb.om_pureTensorO_comb D ψ θ S T χS χT om hθ hW sS sT BS BT e f₀ _ 1 he hf₀ (theta_comb hW.std he hf₀)
    1 (one_mem _) 1 (one_mem _) h1 P a ha a' ha').1
  rwa [mul_one, mul_one, one_smul] at this

theorem step {χS χT : (AE D)ˣ →* Circle} {om : Om S T} (hθ : IsInfFam θ) (hW : IsWeilDatumO ψ S T χS χT om) (sS sT BS BT)
    {P Q : GlobalTheory.FinPl.Pl D → Prop} (hd : ∀ p, P p → ¬ Q p) {LS : GlobalTheory.FinPl.Lat S} {LT : GlobalTheory.FinPl.Lat T} {vac : WO S T → ℂ}
    (hv : GlobalTheory.FinPl.Vac ψ S T LS LT (fun _ => True) vac) {dG dQ eG eQ : WO S T →₀ ℂ} (hdG : GlobalTheory.FinPl.CombAt P dG)
    (hdQ : GlobalTheory.FinPl.CombAt Q dQ) (heG : GlobalTheory.FinPl.CombAt P eG) (heQ : GlobalTheory.FinPl.CombAt Q eQ)
    {b : GA D S} (hb : b ∈ GfC S) {b' : GA D T} (hb' : b' ∈ GfC T) {a : GA D S} (ha : a ∈ GinfC S)
    {a' : GA D T} (ha' : a' ∈ GinfC T)
    (hQ : ∀ g, GlobalTheory.FinPl.Vac ψ S T LS LT Q g → om (b, b') (comb ψ S T dQ g) = comb ψ S T eQ (om (b, b') g))
    (Pol) {c : ℂ} {Ψ : WO S T → ℂ}
    (hG : IsThetaFunO ψ S T (comb ψ S T dG (pureTensorO ψ θ S T sS sT BS BT vac Pol)) →
      om (a * b, a' * b') (comb ψ S T dG (pureTensorO ψ θ S T sS sT BS BT vac Pol)) = c • comb ψ S T eG Ψ) :
    om (a * b, a' * b') (pureTensorO ψ θ S T sS sT BS BT (comb ψ S T dQ (comb ψ S T dG vac)) Pol) =
      c • comb ψ S T eG (comb ψ S T eQ Ψ) := by
  have hψ : IsStdChar D ψ (-1) := hW.std
  have hPQ := GlobalTheory.DisjComb.main D ψ hψ S T P Q hd
  have hQP := GlobalTheory.DisjComb.main D ψ hψ S T Q P (fun p h h' => hd p h' h)
  have fG : IsFinComb dG := (hPQ.2.1 dG hdG).1
  have fQ : IsFinComb dQ := (hQP.2.1 dQ hdQ).1
  have h1 : om (1, 1) (comb ψ S T dG vac) = (1 : ℂ) • comb ψ S T dG vac := by
    rw [one_smul, show ((1, 1) : GA D S × GA D T) = 1 from rfl, map_one, Module.End.one_apply]
  have hvac := fun a ha a' ha' => (GlobalTheory.FockComb.om_pureTensorO_comb D ψ θ S T χS χT om hθ hW sS sT BS BT dG vac _ 1 fG hv.1
    (theta_comb hψ fG hv.1) 1 (one_mem _) 1 (one_mem _) h1 Pol a ha a' ha').2 LS LT hv
  have hth : IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT vac Pol) := by
    have := (hvac 1 (one_mem _) 1 (one_mem _)).1
    rwa [show ((1, 1) : GA D S × GA D T) = 1 from rfl, map_one, Module.End.one_apply] at this
  have hg := (hPQ.2.1 dG hdG).2 LS LT _ (vac_mono Q (hvac a ha a' ha'))
  have e1 : ((a * b, a' * b') : GA D S × GA D T) = (b, b') * (a, a') := by
    rw [Formalism.IndefR.Eqv.Act.comm_inf_fin ha hb, Formalism.IndefR.Eqv.Act.comm_inf_fin ha' hb']
    rfl
  have hG' := hG (theta_comb hψ fG hth)
  rw [e1, map_mul, Module.End.mul_apply, GlobalTheory.FrComb.om_comb hW ha ha' fG hth] at hG'
  rw [e1, map_mul, Module.End.mul_apply, real_fock hθ hW sS sT BS BT fQ (theta_comb hψ fG hv.1) Pol ha ha',
    real_fock hθ hW sS sT BS BT fG hv.1 Pol ha ha', hQ _ hg, hG', comb_smul, hPQ.1 eG eQ heG heQ]

end Gen

theorem under_ne {D : D7} {T : Type} (L : LevCh D T) {μ0 : T} (hL : L.Is μ0) (t : T) {PP PP' : Pl D.host.E} (h : PP ∈ L.Pg)
    (h' : PP' ∈ L.Q t) : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') := by
  intro e
  obtain ⟨i, hi⟩ := (hL.Pg PP).1 h
  obtain ⟨⟨q, hq, hcard, -, hqg⟩, -⟩ := hL.Q_pl t PP' h'
  have hg : ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    have h0 := L.C.P.pb_over i
    rw [← hi] at h0
    have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g i : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal := h0
    rwa [map_natCast] at h2
  have hq' : (q : 𝓞 D.host.E) ∈ PP'.asIdeal := by
    have h1 : Nat.card (kP PP') • (1 : kP PP') = 0 := card_nsmul_eq_zero'
    rw [hcard, nsmul_one] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.1 ((map_natCast _ q).trans h1)
  have hqF : (q : 𝓞 D.host.F) ∈ ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP')).asIdeal := by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) q ∈ PP'.asIdeal
    rwa [map_natCast]
  rw [← e] at hqF
  have hqP : (q : 𝓞 D.host.E) ∈ PP.asIdeal := by
    have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) q ∈ PP.asIdeal := hqF
    rwa [map_natCast] at h2
  obtain ⟨a, b, hab⟩ : IsCoprime ((D.host.g i : ℕ) : 𝓞 D.host.E) q :=
    Nat.Coprime.cast ((Nat.coprime_primes (D.host.g_prime i) hq).2 fun h => hqg i h.symm)
  exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ PP.asIdeal.add_mem (PP.asIdeal.mul_mem_left _ hg) (PP.asIdeal.mul_mem_left _ hqP)))

end GlobalTheory.StepVacForm

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BesFrameCols

theorem cols_pair : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ρ : ℕ) (B : BesLev D ρ) (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (s : k) (FA : Frame k B.A.rank n) (F : Frame k B.V.rank (n ⊕ Fin c)), p.IsBesFrame B s FA F → ∀ i : Fin ρ, ∃ m₀ m₁ : n ⊕ Fin c, (∀ r, F.β r m₀ = s * p.xi ^ (ρ - i.val) * p.pr (B.d.e r i)) ∧ (∀ r, F.β r m₁ = s * (-p.hz B / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val) * p.pr (B.d.e' r i)) ∧ ∀ m, m ≠ m₁ → ∑ r, ∑ r', p.pr (star (B.d.e r i)) * p.pr (B.V.gram r r') * F.β r' m = 0 := by
  intro D k _ _ _ _ p ρ B n _ _ c s FA F hF i
  obtain ⟨hc, h1, h2, h3, h4⟩ := hF
  subst hc
  set G := B.V.gram with hGdef
  have hGh : Gᴴ = G := by
    refine Matrix.ext fun a b => ?_
    simp only [G, Matrix.conjTranspose_apply]
    exact GlobalTheory.DualPairCheck.gram_star B.V b a
  have heG0 : (B.d.e)ᴴ * G * B.d.i₀ = 0 := by
    have h := congrArg Matrix.conjTranspose B.d.i₀e
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero] at h
    rw [← hGdef, hGh] at h
    rw [← h, Matrix.mul_assoc]
  have heGe : (B.d.e)ᴴ * G * B.d.e = 0 := B.d.ee
  have heGe' : (B.d.e)ᴴ * G * B.d.e' = 1 := by
    have h := congrArg Matrix.conjTranspose B.d.e'e
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one] at h
    rw [← hGdef, hGh] at h
    rw [← h, Matrix.mul_assoc]
  have key : ∀ x : Fin B.V.rank → D.host.E, ∑ r, ∑ r', p.pr (star (B.d.e r i)) * p.pr (G r r') * p.pr (x r') =
      p.pr ((((B.d.e)ᴴ * G) *ᵥ x) i) := by
    intro x
    change ∑ r, ∑ r', LocMod.Witness.prH p _ * LocMod.Witness.prH p _ * LocMod.Witness.prH p _ = LocMod.Witness.prH p _

    simp only [← map_mul, ← map_sum]
    congr 1
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have keyc : ∀ (a : k) (x : Fin B.V.rank → D.host.E), ∑ r, ∑ r', p.pr (star (B.d.e r i)) * p.pr (G r r') * (a * p.pr (x r')) =
      a * p.pr ((((B.d.e)ᴴ * G) *ᵥ x) i) := by
    intro a x
    rw [← key, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r' _ => ?_
    ring
  have colM : ∀ {κ : Type} (M : Matrix (Fin B.V.rank) κ D.host.E) (j : κ), (((B.d.e)ᴴ * G) *ᵥ fun r => M r j) i = ((B.d.e)ᴴ * G * M) i j := by
    intro κ M j
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  refine ⟨Sum.inr ⟨i.val, by omega⟩, Sum.inr ⟨2 * ρ - i.val, by omega⟩, fun r => h2 i _ rfl r,
    fun r => h4 i _ (by simp only; omega) r, ?_⟩
  rintro (a | ⟨j, hj⟩) hm
  · have hM : ((B.d.e)ᴴ * G * (B.d.i₀ * B.o.iA)) = 0 := by rw [← Matrix.mul_assoc, heG0, Matrix.zero_mul]
    generalize B.d.i₀ * B.o.iA = M at h1 hM
    calc ∑ r, ∑ r', p.pr (star (B.d.e r i)) * p.pr (G r r') * F.β r' (Sum.inl a)
        = ∑ u, FA.β u a * ∑ r, ∑ r', p.pr (star (B.d.e r i)) * p.pr (G r r') * p.pr (M r' u) := by
          simp_rw [h1 _ a, Matrix.mul_apply, Matrix.map_apply, Finset.mul_sum]
          conv_rhs => rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun r _ => ?_
          conv_rhs => rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun r' _ => ?_
          refine Finset.sum_congr rfl fun u _ => ?_
          ring
      _ = 0 := by
          refine Finset.sum_eq_zero fun u _ => ?_
          rw [key (fun r' => M r' u), colM, hM]
          simp [LocMod.Place.pr]
  · have hne : j ≠ 2 * ρ - i.val := fun h => hm (by subst h; rfl)
    rcases lt_trichotomy j ρ with hlt | heq | hgt
    · simp_rw [h2 ⟨j, hlt⟩ ⟨j, hj⟩ rfl]
      refine (keyc _ (fun r' => B.d.e r' ⟨j, hlt⟩)).trans ?_
      rw [colM, heGe]
      simp [LocMod.Place.pr]
    · simp_rw [h3 ⟨j, hj⟩ heq]
      refine (keyc _ (B.d.i₀ *ᵥ vecB B.o B.ζ)).trans ?_
      rw [Matrix.mulVec_mulVec, heG0, Matrix.zero_mulVec]
      simp [LocMod.Place.pr]
    · have hlt' : 2 * ρ - j < ρ := by omega
      simp_rw [h4 ⟨2 * ρ - j, hlt'⟩ ⟨j, hj⟩ (by simp only; omega)]
      refine (keyc _ (fun r' => B.d.e' r' ⟨2 * ρ - j, hlt'⟩)).trans ?_
      rw [colM, heGe', Matrix.one_apply_ne (fun h => hne (by rw [Fin.ext_iff] at h; simp only at h; omega))]
      simp [LocMod.Place.pr]

end GlobalTheory.BesFrameCols
end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LocModU

theorem upAdd {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}
    (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (x x' : Matrix Y Y' k) :
    p.up FS FT (x + x') = p.up FS FT x + p.up FS FT x' := by
  unfold Place.up
  rw [Matrix.mul_add, Matrix.add_mul]
  ext i j
  simp [Matrix.map_apply]

theorem upZero {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}
    (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) : p.up FS FT 0 = 0 := by
  unfold Place.up
  ext i j
  simp [Matrix.map_apply]

theorem charZero_of_place {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : Place D k) : CharZero k :=
  (RingHom.charZero_iff (ϕ := p.π.comp (incA D)) (RingHom.injective _)).1 inferInstance

theorem localModel_uniq_transport_exist : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → (∀ T₁ T₂, p.IsModel ψ FS FT T₁ → p.IsModel ψ FS FT T₂ → ∀ Φ₀, Φ₀ ≠ 0 → T₁ Φ₀ = T₂ Φ₀ → T₁ = T₂) ∧ (∀ T₁, p.IsModel ψ FS FT T₁ → ∀ A : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), (∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (A f)) → (∀ f, IsThetaFunO ψ S T f → ∀ y : WO S T, IsHalf (p.e + cA D p.e) y → A (heisO ψ S T y f) = heisO ψ S T y (A f)) → p.IsModel ψ FS FT (A ∘ₗ T₁)) ∧ ∀ f₀, IsThetaFunO ψ S T f₀ → (∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) → heisO ψ S T (p.up FS FT x) f₀ = f₀) → (∀ y : WO S T, IsHalf (cA D p.e) y → (∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) → ψ (symplO S T (p.up FS FT x) y) = 1) → heisO ψ S T y f₀ = f₀) → ∃ T₁, p.IsModel ψ FS FT T₁ ∧ ∀ Φ : SB (Matrix Y Y' k), Φ.1 = Set.indicator {x | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) → T₁ Φ = f₀ := by
  intro D k _ _ _ _ p Y Y' _ _ _ _ S T FS FT ψ hψ
  haveI : CharZero k := charZero_of_place p
  obtain ⟨⟨ψk, hψk⟩, hcn, -, -, -⟩ := GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial D k p ψ hψ
  obtain ⟨hcont, hne⟩ := hcn ψk hψk
  obtain ⟨hup, -, -, hsymk, hsurj⟩ := GlobalTheory.T.heisenberg_frame_half_inverse D k p Y Y' S T FS FT ψ ψk hψk
  obtain ⟨-, hec, -⟩ := p.split
  have hce : cA D p.e * p.e = 0 := by rw [mul_comm, hec]
  have hcce : cA D (cA D p.e) * cA D p.e = 0 := by rw [GlobalTheory.DualPairCheck.cA_cA, hec]
  have halfSum1 : ∀ u : WO S T, IsHalf p.e u → IsHalf (p.e + cA D p.e) u := fun u hu i j => by
    rw [add_mul, hu i j, ← hu i j, ← mul_assoc, hce, zero_mul, add_zero, hu i j]
  have halfSum2 : ∀ u : WO S T, IsHalf (cA D p.e) u → IsHalf (p.e + cA D p.e) u := fun u hu i j => by
    rw [add_mul, hu i j, ← hu i j, ← mul_assoc, hec, zero_mul, zero_add, hu i j]
  refine ⟨?_, ?_, ?_⟩
  ·
    intro T₁ T₂ h₁ h₂ Φ₀ hΦ₀ h12
    let W : Submodule ℂ (Matrix Y Y' k → ℂ) := (LinearMap.ker (T₁ - T₂)).map (SB (Matrix Y Y' k)).subtype
    have memW : ∀ Φ : SB (Matrix Y Y' k), Φ.1 ∈ W ↔ T₁ Φ = T₂ Φ := by
      intro Φ
      constructor
      · rintro ⟨Ψ, hΨ, hΨe⟩
        have : Ψ = Φ := Subtype.ext hΨe
        subst this
        simpa [sub_eq_zero] using hΨ
      · intro h
        exact ⟨Φ, by simpa [sub_eq_zero] using h, rfl⟩
    have hWle : W ≤ SB (Matrix Y Y' k) := by
      rintro _ ⟨Ψ, -, rfl⟩
      exact Ψ.2
    have hWeq := GlobalTheory.T.schwartzBruhat_matrix_translation_modulation_irreducible k Y Y' ψk hcont hne W hWle
      (by
        rintro _ ⟨Φ, hΦ, rfl⟩ x hx
        have hΦ' : T₁ Φ = T₂ Φ := (memW Φ).1 ⟨Φ, hΦ, rfl⟩
        refine (memW ⟨_, hx⟩).2 ?_
        rw [h₁.trans x Φ ⟨_, hx⟩ (fun t => rfl), h₂.trans x Φ ⟨_, hx⟩ (fun t => rfl), hΦ'])
      (by
        rintro _ ⟨Φ, hΦ, rfl⟩ b hb
        have hΦ' : T₁ Φ = T₂ Φ := (memW Φ).1 ⟨Φ, hΦ, rfl⟩
        obtain ⟨y, hy, hyb⟩ := hsurj b
        have hmod : ∀ t, (⟨_, hb⟩ : SB (Matrix Y Y' k)).1 t = ψ (symplO S T (p.up FS FT t) y) * Φ.1 t := by
          intro t
          show _ = _
          rw [hsymk t y hy, hyb t]
          rfl
        refine (memW ⟨_, hb⟩).2 ?_
        rw [h₁.modul y hy Φ _ hmod, h₂.modul y hy Φ _ hmod, hΦ'])
      Φ₀.1 ((memW Φ₀).2 h12) (fun h => hΦ₀ (Subtype.ext h))
    ext1 Φ
    have hm : Φ.1 ∈ W := by rw [hWeq]; exact Φ.2
    exact (memW Φ).1 hm
  ·
    intro T₁ h₁ A hA1 hA2
    refine ⟨fun Φ => hA1 _ (h₁.theta Φ), fun x Φ Φ' h => ?_, fun y hy Φ Φ' h => ?_⟩
    · show A (T₁ Φ') = heisO ψ S T (p.up FS FT x) (A (T₁ Φ))
      rw [h₁.trans x Φ Φ' h, hA2 _ (h₁.theta Φ) _ (halfSum1 _ (hup x).1)]
    · show A (T₁ Φ') = heisO ψ S T y (A (T₁ Φ))
      rw [h₁.modul y hy Φ Φ' h, hA2 _ (h₁.theta Φ) _ (halfSum2 _ hy)]
  ·
    intro f₀ hf₀ hfx hfy
    let Z := GlobalTheory.PlaceModel.half S T (cA D p.e)
    let χ : Matrix Y Y' k → Z → ℂ := fun t z => ψ (symplO S T (p.up FS FT t) z.1)
    have hZ : ∀ z : Z, IsHalf (cA D p.e) z.1 := fun z => (GlobalTheory.PlaceModel.isHalf_iff S T).2 z.2
    obtain ⟨Tm, htr, hmo, hvac, hspan⟩ := GlobalTheory.T.exists_schrodinger_intertwiner_integralMatrices k Y Y' Z χ
      (fun a b z => by simp only [χ, upAdd, GlobalTheory.PlaceModel.symplO_add_left, AddChar.map_add_eq_mul])
      (fun a z z' => by simp only [χ, AddSubgroup.coe_add, GlobalTheory.PlaceModel.symplO_add_right, AddChar.map_add_eq_mul])
      (fun z => by simp only [χ, upZero, GlobalTheory.PlaceModel.symplO_zero_left, AddChar.map_zero_eq_one])
      (fun a => by simp only [χ, ZeroMemClass.coe_zero, GlobalTheory.PlaceModel.symplO_zero_right, AddChar.map_zero_eq_one])
      (fun n hn z => by
        obtain ⟨z', hz', e⟩ := GlobalTheory.PlaceModel.half_div S T (cA D p.e) n hn z.1 z.2
        exact ⟨⟨z', hz'⟩, Subtype.ext (by rw [AddSubgroup.coe_nsmul]; exact e)⟩)
      (fun n hn z z' h => by
        apply Subtype.ext
        have h' : n • z.1 = n • z'.1 := by
          have := congrArg Subtype.val h
          simpa only [AddSubgroup.coe_nsmul] using this
        rw [← GlobalTheory.PlaceModel.inv_smul_nsmul S T hn z.1, h', GlobalTheory.PlaceModel.inv_smul_nsmul S T hn])
      (fun x hx => GlobalTheory.T.matrix_integral_of_addChar_trace_dual k Y Y' ψk hcont hne x fun b hb => by
        obtain ⟨y, hy, hyb⟩ := hsurj b
        have key : ∀ t, χ t ⟨y, (GlobalTheory.PlaceModel.isHalf_iff S T).1 hy⟩ = ((ψk (∑ r, ∑ q, b r q * t r q) : Circle) : ℂ) := by
          intro t
          show ψ _ = _
          rw [hsymk t y hy, hyb t]
        have := hx ⟨y, (GlobalTheory.PlaceModel.isHalf_iff S T).1 hy⟩ (fun u hu => by
          rw [key, hb u hu, Circle.coe_one])
        rw [key] at this
        exact Circle.ext (by simpa using this))
      (WO S T → ℂ) (fun x => GlobalTheory.PlaceModel.heisL S T ψ (p.up FS FT x)) (fun z => GlobalTheory.PlaceModel.heisL S T ψ z.1)
      (fun x x' f => by
        rw [GlobalTheory.PlaceModel.heisL_half S T ψ hce _ ((GlobalTheory.PlaceModel.isHalf_iff S T).1 (hup x).1) _
          ((GlobalTheory.PlaceModel.isHalf_iff S T).1 (hup x').1), upAdd])
      (fun z z' f => by
        rw [GlobalTheory.PlaceModel.heisL_half S T ψ hcce _ z.2 _ z'.2]
        rfl)
      (fun x z f => GlobalTheory.PlaceModel.heisL_comm S T ψ _ _ f)
      (fun f => by
        rw [upZero]
        funext w
        show ψ (symplOH S T w 0) * f (w + 0) = f w
        rw [symplOH, GlobalTheory.PlaceModel.symplO_zero_right, mul_zero, AddChar.map_zero_eq_one, one_mul, add_zero])
      (fun f => by
        funext w
        show ψ (symplOH S T w 0) * f (w + 0) = f w
        rw [symplOH, GlobalTheory.PlaceModel.symplO_zero_right, mul_zero, AddChar.map_zero_eq_one, one_mul, add_zero])
      f₀ (fun u hu => hfx u hu)
      (fun z hz => hfy z.1 (hZ z) hz)
    have hsplit := p.split
    have hstd : IsCharAF D.host.F ψ := hψ.1
    refine ⟨Tm, ⟨fun Φ => ?_, fun x Φ Φ' h => htr x Φ Φ' h, fun y hy Φ Φ' h =>
      hmo ⟨y, (GlobalTheory.PlaceModel.isHalf_iff S T).1 hy⟩ Φ Φ' h⟩, hvac⟩
    have hfin {a : WO S T} (ha : a.map (infPart D) = 0) {f : WO S T → ℂ}
        (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (heisO ψ S T a f) := by
      simpa using GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hstd f hf
        Unit Finset.univ (fun _ => a) (fun _ => 1) (fun _ _ => ha)
    have hzero : IsThetaFunO ψ S T 0 := by
      refine ⟨?_, ?_, continuous_const, ?_⟩
      · intro γ w; simp only [Pi.zero_apply, mul_zero]
      · exact ⟨⊤, isOpen_univ, fun u _ _ => by funext w; simp only [heisO, Pi.zero_apply, mul_zero]⟩
      · intro k L _ _ w; exact contDiff_const
    have hadd {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
        IsThetaFunO ψ S T (f + g) := by
      refine ⟨?_, ?_, hf.cont.add hg.cont, ?_⟩
      · intro γ w; simp only [Pi.add_apply, hf.quasi, hg.quasi, mul_add]
      · obtain ⟨U, hU, h1⟩ := hf.level
        obtain ⟨U', hU', h2⟩ := hg.level
        refine ⟨U ⊓ U', hU.inter hU', fun u hu h0 => ?_⟩
        funext w
        have e1 := congrFun (h1 u hu.1 h0) w
        have e2 := congrFun (h2 u hu.2 h0) w
        unfold heisO at e1 e2 ⊢
        rw [Pi.add_apply, Pi.add_apply, mul_add, e1, e2]
      · intro k L h1 h2 w; exact (hf.smooth k L h1 h2 w).add (hg.smooth k L h1 h2 w)
    have hsmul (c : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
        IsThetaFunO ψ S T (c • f) := by
      refine ⟨?_, ?_, hf.cont.const_smul c, ?_⟩
      · intro γ w; rw [Pi.smul_apply, Pi.smul_apply, hf.quasi, smul_eq_mul, smul_eq_mul, mul_left_comm]
      · obtain ⟨U, hU, h1⟩ := hf.level
        refine ⟨U, hU, fun u hu h0 => ?_⟩
        funext w
        have e1 := congrFun (h1 u hu h0) w
        unfold heisO at e1 ⊢
        rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, e1]
      · intro k L h1 h2 w; exact contDiff_const.mul (hf.smooth k L h1 h2 w)
    have hs := hspan Φ
    generalize Tm Φ = g at hs
    induction hs using Submodule.span_induction with
    | mem _ hw =>
      obtain ⟨w, rfl⟩ := hw
      exact hfin (GlobalTheory.SplitScalar.half_fin hsplit (hup w.1).1)
        (hfin
          (GlobalTheory.SplitScalar.half_fin (GlobalTheory.SplitScalar.isSplitIdem_conj hsplit) (hZ w.2)) hf₀)
    | zero => exact hzero
    | add _ _ _ _ h1 h2 => exact hadd h1 h2
    | smul c _ _ h1 => exact hsmul c h1

end GlobalTheory.LocModU
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocEmb

theorem exists_gl : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (V : HSp D) (Y : Type) [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k V.rank Y),
    ∃ gl : GL Y k →* GA D V, Continuous gl ∧ (∀ x, SuppAt q.e V (gl x) ∧ (mt V (gl x)).map q.pr = F.β * x.val * F.γ) ∧
      ∀ g x, SuppAt q.e V g → (mt V g).map q.pr = F.β * x.val * F.γ → g = gl x := by
  intro D k _ _ _ _ q V Y _ _ F
  obtain ⟨h1, -, h3⟩ := (GlobalTheory.T.splitPlace_localGroupElements_jacobi_bessel D k (GlobalTheory.LocMod.ofSplit q)).1 V Y F
  choose f hf hu using h1
  have hmul : ∀ x y, f (x * y) = f x * f y := fun x y => (hu (x * y) _ (h3 _ _ _ _ (hf x) (hf y))).symm
  have hone : f 1 = 1 := by
    have h := hmul 1 1
    rw [mul_one] at h
    exact (mul_eq_left.1 h.symm)
  let gl : GL Y k →* GA D V := { toFun := f, map_one' := hone, map_mul' := hmul }
  let fr : GlobalTheory.FinPl.Frame q V Y := ⟨F.β, F.γ, F.βγ, F.γβ, gl, fun x => (hf x).1, fun x => (hf x).2⟩
  refine ⟨gl, GlobalTheory.FrameCont.continuous_gl D k q V Y fr, fun x => hf x, fun g x hs hm => hu x g ⟨hs, hm⟩⟩

end GlobalTheory.LocEmb
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

theorem _root_.GlobalTheory.T.flat_bessel_to_fourierJacobi_row_mul_laws : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (st : StepBF ψ B J) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FV : Frame k B.V.rank (n' ⊕ Fin (c + 1))) (G₀ : Frame k J.W₀.rank n) (FW : Frame k J.W.rank (n ⊕ Fin c)), p.IsCoreFrame B s FA F₀ → p.IsBesFrame B s FA FV → p.IsJacFrame J s (p.hz B) G₀ FW → ∀ (Tm : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (WO B.V J.W → ℂ)), p.IsModel ψ FV FW Tm → ∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ l, r = Sum.inr l ∧ ρ ≤ l.val ∧ ∀ i, q = Sum.inr i → i.val = ρ) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψk (b * (t r q - GlobalTheory.RootEx.basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → flatBF st (Tm Φ') = flatBF st (Tm Φ) := by
  first | exact @GlobalTheory.FlatRow.flatBF_mul_row | exact GlobalTheory.FlatRow.flatBF_mul_row | (intros; apply GlobalTheory.FlatRow.flatBF_mul_row <;> assumption)
end
