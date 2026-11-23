module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuaDenseThetaFunctions
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionUnitaryGroupHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralEqOfNorms
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle043
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle352
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle067
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle339
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelADef
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle198
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle195
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle197
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle009
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams

@[expose] public section

section

noncomputable section

namespace GlobalTheory.FockRealOrth

section Coord

open Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift GlobalTheory.Size GlobalTheory.FockDensity
open scoped ENNReal ComplexOrder

theorem inner_coord {κ : Type} [Fintype κ] [DecidableEq κ] {Q s : Matrix κ κ ℂ} (hQ : Qᴴ = Q) (hs : s * s = 1)
    (hp : (Q * s).PosDef) {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    {ρ : (κ → ℂ) → B →L[ℂ] B} (h : IsHeis (fun x y => (star y ⬝ᵥ Q *ᵥ x).im) ρ) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (Φ : B →L[ℂ] H) (hΦ : ∀ v f, ‖Φ (ρ v f)‖ = ‖Φ f‖) {Y : Type}
    (T : Y → B →L[ℂ] B) (hT : ∀ y v f, T y (ρ v f) = ρ v (T y f)) (S F : Submodule ℂ B)
    (hS : ∀ f, f ∈ S ↔ Sm ρ f ∧ ∀ y, T y f = f)
    (hF : ∀ z, ∀ f ∈ S, f ∈ F → dH ρ z f - I • dH ρ (I • s *ᵥ z) f ∈ F) {v : B} (hvS : v ∈ S) (hvF : v ∈ F)
    (hv : ∀ z, dH ρ z v + I • dH ρ (I • s *ᵥ z) v = 0) {y : H} (hy : ∀ x ∈ F, inner ℂ y (Φ x) = 0) (w : κ → ℂ) :
    inner ℂ y (Φ (ρ w v)) = 0 := by
  obtain ⟨E, J, hJ, hE, hom⟩ := GlobalTheory.T.exists_euclideanCoords_hermitian_cartanInvolution κ Q s hQ hs hp
  have hρ : IsHeis (omJ J) fun v => ρ (E v) :=
    UnitaryOsc.isHeis_comp h (E : EuclideanSpace ℂ κ →L[ℝ] (κ → ℂ)) fun x y => hom x y
  have hm : ∀ G, G ∈ S ↔ Sm (fun v => ρ (E v)) G ∧ ∀ y, T y G = G :=
    fun G => (hS G).trans (and_congr_left' (UnitaryOsc.sm_comp_iff E _ G).symm)
  have hd : ∀ z, dH (fun v => ρ (E v)) z = dH ρ (E z) := fun z => funext fun G => by
    have := E.comp_right_fderiv (f := fun v => ρ v G) (x := 0)
    rw [map_zero] at this
    exact DFunLike.congr_fun this z
  have a1 : ∀ G ∈ S, Sm (fun v => ρ (E v)) G := fun G hG => ((hm G).1 hG).1
  have a2 : ∀ v, ∀ G ∈ S, dH (fun v => ρ (E v)) v G ∈ S := fun v G hG =>
    (hm _).2 ⟨VacBd.sm_dH hρ (a1 G hG) v, fun y => by
      rw [← (dH_comm (T y) (fun v => hT y (E v)) (a1 G hG)).2, ((hm G).1 hG).2]⟩
  have := inner_translate hJ hρ (fun v => hΦ (E v)) a1 a2 (F.comap S.subtype)
    (fun z x hx => by
      rw [Submodule.mem_comap, Submodule.subtype_apply, coe_cE, hd, hd, hE]
      exact hF (E z) x x.2 hx) (v := ⟨v, hvS⟩) hvF
    (fun z => (aE_eq_zero a1 a2 z _).2 (by rw [hd, hd, hE]; exact hv (E z))) (y := y)
    (fun x hx => hy x hx) (E.symm w)
  simpa only [E.apply_symm_apply] using this

end Coord

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isUnit_det_of_onb {k : ℕ} {G s B : Matrix (Fin k) (Fin k) ℂ} {p : ℕ} (h : IsONBasis G s B p) : IsUnit B.det := by
  obtain ⟨ε, h1, h2, -⟩ := h
  have h3 := congrArg Matrix.det h2
  rw [Matrix.det_mul, Matrix.det_diagonal] at h3
  refine isUnit_iff_ne_zero.2 fun h0 => ?_
  rw [h0, mul_zero] at h3
  obtain ⟨a, -, ha⟩ := Finset.prod_eq_zero_iff.1 h3.symm
  rcases h1 a with ⟨e, -⟩ | ⟨e, -⟩ <;> simp [e] at ha

theorem cplxO_pm {m n : ℕ} {s : Matrix (Fin n) (Fin n) ℂ} {t : Matrix (Fin m) (Fin m) ℂ} (hs : s = 1 ∨ s = -1)
    (ht : t = 1 ∨ t = -1) : ∃ b : Bool, ∀ z, cplxO s t z = ((if b then 1 else -1 : ℂ) * Complex.I) • z := by
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · exact ⟨true, fun z => by simp [cplxO]⟩
  · exact ⟨false, fun z => by simp [cplxO]⟩
  · exact ⟨false, fun z => by simp [cplxO]⟩
  · exact ⟨true, fun z => by simp [cplxO]⟩

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem crea_fock (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {x : DefSp S} {y : DefSp T} (hx : x.Is) (hy : y.Is)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    ∃ Q, pureTensorO ψ θ S T x.s y.s x.B y.B f Q =
      crea (heisO ψ S T) θ τ (cplxO (x.s τ) (y.s τ)) z (pureTensorO ψ θ S T x.s y.s x.B y.B f P) := by
  have hadd : ∀ g g', IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → IsThetaFunO ψ S T (g + g') :=
    fun _ _ => GlobalTheory.OrientedHeis.theta_add
  have hsm : ∀ (a : ℂ) g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (a • g) :=
    fun a _ => GlobalTheory.OrientedHeis.theta_smul a
  have hth : ∀ v g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T
      (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (x.s τ) (y.s τ)) x.B y.B v g) :=
    fun _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h
  have hX : ∀ v Q,
      pureTensorL (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (x.s τ) (y.s τ)) x.B y.B) f (MvPolynomial.X v * Q) =
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO (x.s τ) (y.s τ)) x.B y.B v
        (pureTensorL (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (x.s τ) (y.s τ)) x.B y.B) f Q) := fun v Q => by
    refine GlobalTheory.FockIndep.pure_X_mul (P := IsThetaFunO ψ S T) hadd hsm hth ?_ ?_ ?_ hf Q v
    · exact fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' hψ hθ i.1 _ hx.cart hy.cart j.1 _ h
    · exact fun _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ h h'
    · exact fun _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ a h
  have hg : IsThetaFunO ψ S T (pureTensorO ψ θ S T x.s y.s x.B y.B f P) :=
    GlobalTheory.FockIndep.pure_mem (P := IsThetaFunO ψ S T) hadd hsm hth hf P
  obtain ⟨c, rfl⟩ : ∃ c : Fin T.rank → Fin S.rank → ℂ,
      z = ∑ i, ∑ j, c i j • Formalism.IndefR.Datum.unitMap (x.B τ) (y.B τ) i j :=
    ⟨_, GlobalTheory.FockCreaDir.eq_sum_unitMap (isUnit_det_of_onb (hy.onb τ).choose_spec)
      (isUnit_det_of_onb (hx.onb τ).choose_spec) z⟩
  obtain ⟨b, hb⟩ := cplxO_pm (hx.pm τ) (hy.pm τ)
  refine ⟨((fockScale D τ : ℝ) : ℂ) • ∑ i, ∑ j, (if b then c i j else starRingEnd ℂ (c i j)) •
    (MvPolynomial.X (τ, i, j) * P), Eq.symm ?_⟩
  have h1 : ∀ (u : Matrix (Fin T.rank) (Fin S.rank) ℂ) g,
      crea (heisO ψ S T) θ τ (cplxO (x.s τ) (y.s τ)) u g =
        ((fockScale D τ : ℝ) : ℂ) • Formalism.IndefR.Datum.aPlus (heisO ψ S T) θ τ (cplxO (x.s τ) (y.s τ)) u g := fun u g => by
    rw [Formalism.IndefR.Datum.aPlus, smul_smul, mul_inv_cancel₀ (GlobalTheory.FockCreaDir.fockScale_ne_zero D τ), one_smul]
  rw [h1]
  have h2 : pureTensorO ψ θ S T x.s y.s x.B y.B f (((fockScale D τ : ℝ) : ℂ) • ∑ i, ∑ j,
      (if b then c i j else starRingEnd ℂ (c i j)) • (MvPolynomial.X (τ, i, j) * P)) =
      ((fockScale D τ : ℝ) : ℂ) • ∑ i, ∑ j, (if b then c i j else starRingEnd ℂ (c i j)) •
        Formalism.IndefR.Datum.aPlus (heisO ψ S T) θ τ (cplxO (x.s τ) (y.s τ))
          (Formalism.IndefR.Datum.unitMap (x.B τ) (y.B τ) i j) (pureTensorO ψ θ S T x.s y.s x.B y.B f P) := by
    unfold pureTensorO

    simp only [map_smul, map_sum, hX]
    rfl
  rw [h2]
  congr 1
  rw [GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ τ _ _ hg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ τ _ _ hg]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact GlobalTheory.FockSubst.aPlus_dir_smul hψ hθ τ _ _ hg b _ (hb _)


open GlobalTheory.RealWeil GlobalTheory.FockDensity in
theorem inner_toL2_eq_theta_pairing (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) [BorelSpace (WO S T)] [SecondCountableTopology (WO S T)]
    [IsFiniteMeasure (μ.restrict 𝓕)] (G G' : BB ψ S T) :
    inner ℂ (toL2 _ _ (μ.restrict 𝓕) G') (toL2 _ _ (μ.restrict 𝓕) G) = thPair μ 𝓕 (coeL ψ S T G) (coeL ψ S T G') :=
  BoundedContinuousFunction.inner_toLp (μ.restrict 𝓕) G'.1 G.1


open GlobalTheory.RealWeil GlobalTheory.FockDensity GlobalTheory.Mem.Lift GlobalTheory.ChainFr Classical in
theorem orth_real_translate : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ vac, IsVacO ψ θ S T x.s y.s x.L y.L vac → ∀ (v : VolM D T.rank S.rank) f, IsThetaFunO ψ S T f → (∀ P, thPair v.μ v.𝓕 f (pureTensorO ψ θ S T x.s y.s x.B y.B vac P) = 0) → ∀ u : WO S T, u.map (finPart D) = 0 → thPair v.μ v.𝓕 f (heisO ψ S T u vac) = 0 := by
  intro D ψ θ hθ S T x y hx hy vac hvac v f hf ho u hu
  have hψ := hvac.1
  have hv := hvac.2.theta
  have hm := v.covol
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨U, hU, hl⟩ := hv.level
  obtain ⟨-, i2, i3, i4, i5, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : IsFiniteMeasure (v.μ.restrict v.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, hm.2.2]; exact ENNReal.one_lt_top⟩
  have e0 : coeL ψ S T (toB hψ vac hv) = vac := coe_toB hψ vac hv
  have e1 : coeL ψ S T (toB hψ f hf) = f := coe_toB hψ f hf
  have e2 : ∀ G : BB ψ S T, inner ℂ (toL2 _ _ (v.μ.restrict v.𝓕) (toB hψ f hf)) (toL2 _ _ (v.μ.restrict v.𝓕) G) = 0 ↔
      thPair v.μ v.𝓕 f (coeL ψ S T G) = 0 := fun G => by
    rw [inner_eq_zero_symm, inner_toL2_eq_theta_pairing, e1]
  have hF : toB hψ vac hv ∈ (GlobalTheory.Size.thetaLevel ψ S T U).comap (coeL ψ S T) := by
    rw [Submodule.mem_comap, e0]
    exact ⟨hv, hl⟩
  have hc := HM_cartan hx.cart hy.cart
  have key := inner_coord HM_herm hc.1 hc.2 (isHeis_rhoB h hψ) (toL2 _ _ (v.μ.restrict v.𝓕))
    (fun w G => by
      rw [← enorm_sq_inj, ← lintegral_norm_sq_eq_toL2, ← lintegral_norm_sq_eq_toL2]
      exact lintegral_rhoB hψ v.μ v.𝓕 hm.1 hm.2.1 _ G)
    (fun u : {u : WO S T // u ∈ U ∧ u.map (infPart D) = 0} => rhoB hψ u.1) (fun u => rhoB_comm h hψ u.2.2) _
    ((LinearMap.range (pureTensorO ψ θ S T x.s y.s x.B y.B vac)).comap (coeL ψ S T))
    (fun G => (mem_level h hψ hU G).trans
      (and_congr_right' ⟨fun a u => a u.1 u.2.1 u.2.2, fun a u h1 h2 => a ⟨u, h1, h2⟩⟩))
    (fun z G hG hF => by
      have hs := ((mem_level h hψ hU G).1 hG).1
      rw [Submodule.mem_comap, map_sub, map_smul, coe_dH h hψ hs, coe_dH h hψ hs, Finset.smul_sum,
        ← Finset.sum_sub_distrib]
      refine sum_mem fun τ _ => ?_
      obtain ⟨P, hP⟩ := hF
      rw [cpt_cplx, ← hP]
      exact crea_fock hψ hθ hx hy hv τ _ P)
    hF ⟨1, (GlobalTheory.FockIndep.pure_one _).trans e0.symm⟩
    (fun z => fderiv_vac h hψ _ ((mem_level h hψ hU _).1 hF).1 x.s y.s
      (by rw [coe_toB]; exact hvac.2.fock) z)
    (y := toL2 _ _ (v.μ.restrict v.𝓕) (toB hψ f hf))
    (fun G hG => by
      obtain ⟨P, hP⟩ := hG
      rw [e2, ← hP]
      exact ho P) (vecL (GlobalTheory.FockCompare.piW θ T S u))
  rw [e2] at key
  have e3 : iotaV σ S T (vecL (GlobalTheory.FockCompare.piW θ T S u)) = u :=
    h.real_ext (V := T) (W := S) (real_iotaV h _) hu (h.pi_iota T S _)
  have e4 := coe_rhoV (σ := σ) hψ (vecL (GlobalTheory.FockCompare.piW θ T S u)) (toB hψ vac hv)
  rw [e3, coe_toB] at e4
  rw [← e4]
  exact key

end GlobalTheory.FockRealOrth

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealZetaSmoothHi

theorem exists_smooth_highestUnit : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau), ∃ w : M.H τ, w ∈ M.sm τ ∧ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ ∧ IsHighestUnit (M.ε τ) (M.lam τ) (M.σ τ) w := by
  intro h D V S M τ
  obtain ⟨hC, hN, hU, hI, -, ⟨K, hK⟩, -⟩ := M.ds τ
  haveI := hC
  obtain ⟨v, hv, hv0, hw⟩ := hK.2.2.2.1
  have hwS : ((‖v‖⁻¹ : ℝ) : ℂ) • v ∈ K := K.smul_mem _ hv
  have hKf : IsKFin (M.ε τ) (M.σ τ) (((‖v‖⁻¹ : ℝ) : ℂ) • v) := ⟨K, hK.1, hwS, hK.2.1⟩
  refine ⟨((‖v‖⁻¹ : ℝ) : ℂ) • v, ?_, ?_, ?_, ?_, ?_⟩
  · refine Submodule.subset_span ?_
    exact h.smoothVec hU hI hKf (M.fr_unit τ) (M.fr_gram τ)
  · exact Submodule.subset_span hKf
  · rw [norm_smul, Complex.norm_real, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.2 hv0)
  · exact (le_sSup hK : K ≤ lowKSub (M.ε τ) (M.lam τ) (M.σ τ)) hwS
  · intro θ hθ
    rw [map_smul, hw θ hθ, smul_comm]

end GlobalTheory.RealZetaSmoothHi
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.AdelicU Formalism.UG

noncomputable section

namespace GlobalTheory.Core.Rk.IwGlob

open GlobalTheory.MixModel
open scoped TensorProduct

theorem tens_prod_ext {F E A B : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [CommRing B] [Algebra F A]
    [Algebra F B] {z z' : (A × B) ⊗[F] E}
    (a : Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z')
    (b : Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z') : z = z' := by
  have hz : ∀ z : (A × B) ⊗[F] E, z = LinearMap.rTensor E (LinearMap.inl F A B)
        (Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z) +
      LinearMap.rTensor E (LinearMap.inr F A B)
        (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z) := by
    intro z
    induction z with
    | tmul x y => simp [← TensorProduct.add_tmul]
    | add x y hx hy =>
      simp only [map_add (f := _)]
      rw [add_add_add_comm, ← hx, ← hy]
  rw [hz z, hz z', a, b]

theorem adTens_ext {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {z z' : AF F ⊗[F] E}
    (h1 : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.compInf F E w z = GlobalTheory.AdelicU.compInf F E w z')
    (h2 : Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z') : z = z' := by
  refine tens_prod_ext (A := Ainf F) (B := Af F) (GlobalTheory.AutFunCompare.infTens_ext fun w => ?_) h2
  have e : ∀ y : AF F ⊗[F] E, Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E)
      (Algebra.TensorProduct.map (AlgHom.fst F (Ainf F) (Af F)) (AlgHom.id F E) y) =
      GlobalTheory.AdelicU.compInf F E w y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => erw [map_zero]
    | tmul a x => rfl
    | add x y hx hy => erw [map_add, map_add, map_add, hx, hy]
  rw [e, e]
  exact h1 w

theorem map_mul_eq_of_keeps {A R : Type} [CommRing A] [CommRing R] (φ : A →+* R) {n r : ℕ}
    (M : Matrix (Fin n) (Fin n) A) (X : Matrix (Fin n) (Fin r) A) (P : Matrix (Fin r) (Fin n) A)
    (hPX : P * X = 1) (β : Matrix (Fin r) (Fin r) R) (h : M.map φ * X.map φ = X.map φ * β) :
    (M * X).map φ = (X * (P * M * X)).map φ := by
  have hPX' : P.map φ * X.map φ = 1 := by
    rw [← Matrix.map_mul, hPX, Matrix.map_one _ (map_zero φ) (map_one φ)]
  simp only [Matrix.map_mul]
  rw [h, Matrix.mul_assoc (P.map φ), h, ← Matrix.mul_assoc (P.map φ), hPX', Matrix.one_mul]

theorem mat_projArch {D : D7} {T : HSp D} (q : GA D T) (w : InfinitePlace D.host.F) :
    (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig T.gram (GlobalTheory.AdelicU.projArch D.sp.cm.sig T.gram w q)).1 =
                 (Formalism.L2.Theta.mt T q).map (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) :=
  Matrix.ext fun _ _ => rfl

theorem mt_inv_mul_self {D : D7} {T : HSp D} (q : GA D T) :
    Formalism.L2.Theta.mt T q⁻¹ * Formalism.L2.Theta.mt T q = 1 := by
  show (Formalism.L2.Theta.matHom T q⁻¹).1 * (Formalism.L2.Theta.matHom T q).1 = 1
  rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

theorem keeps_map {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (q : GA D T) (w : InfinitePlace D.host.F)
    (β : Matrix (Fin r) (Fin r) (TensorProduct D.host.F w.Completion D.host.E))
    (h : (matHom _ D.sp.cm.sig T.gram (projArch D.sp.cm.sig T.gram w q)).1 * Matrix.map d.jX (compInf D.host.F D.host.E w) = Matrix.map d.jX (compInf D.host.F D.host.E w) * β) :
    (Formalism.L2.Theta.mt T q).map (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) * Matrix.map d.jX (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) =
      Matrix.map d.jX (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) * β := by
  rw [← mat_projArch q w]
  exact h

theorem arch_comp {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (q : GA D T) (w : InfinitePlace D.host.F)
    (β : Matrix (Fin r) (Fin r) (TensorProduct D.host.F w.Completion D.host.E))
    (h : (matHom _ D.sp.cm.sig T.gram (projArch D.sp.cm.sig T.gram w q)).1 * Matrix.map d.jX (compInf D.host.F D.host.E w) = Matrix.map d.jX (compInf D.host.F D.host.E w) * β)
    (i : Fin T.rank) (j : Fin r) :
    GlobalTheory.AdelicU.compInf D.host.F D.host.E w ((Formalism.L2.Theta.mt T q ⬝ d.jX) i j) =
      GlobalTheory.AdelicU.compInf D.host.F D.host.E w ((d.jX ⬝ (d.pX ⬝ Formalism.L2.Theta.mt T q ⬝ d.jX)) i j) := by
  have h2 := keeps_map d q w β h
  have h3 := map_mul_eq_of_keeps (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) (Formalism.L2.Theta.mt T q) d.jX d.pX
    d.pX_jX β h2
  rw [← Matrix.map_apply (f := GlobalTheory.AdelicU.compInf D.host.F D.host.E w), h3]
  rfl

theorem mul_jX_eq {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (q : GA D T) (hq : q ∈ GinfC T)
    (hw : ∀ w : InfinitePlace D.host.F, ∃ β : Matrix (Fin r) (Fin r) (TensorProduct D.host.F w.Completion D.host.E), (matHom _ D.sp.cm.sig T.gram (projArch D.sp.cm.sig T.gram w q)).1 * Matrix.map d.jX (compInf D.host.F D.host.E w) = Matrix.map d.jX (compInf D.host.F D.host.E w) * β) :
    Formalism.L2.Theta.mt T q ⬝ d.jX = d.jX ⬝ (d.pX ⬝ Formalism.L2.Theta.mt T q ⬝ d.jX) := by
  let φf : AE D →+* Af D.host.F ⊗[D.host.F] D.host.E :=
    (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
  have hf : (Formalism.L2.Theta.mt T q).map φf = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hq)
  have hfin := map_mul_eq_of_keeps φf (Formalism.L2.Theta.mt T q) d.jX d.pX d.pX_jX 1
    (by rw [hf, Matrix.one_mul, Matrix.mul_one])
  funext i j
  exact adTens_ext (F := D.host.F) (E := D.host.E) (fun w => Exists.elim (hw w) fun β hβ => arch_comp d q w β hβ i j)
    (congrFun (congrFun hfin i) j)

theorem mem_stab_of_keeps : ∀ {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (q : GA D T), q ∈ GinfC T → (∀ w : InfinitePlace D.host.F, ∃ β : Matrix (Fin r) (Fin r) (TensorProduct D.host.F w.Completion D.host.E), (matHom _ D.sp.cm.sig T.gram (projArch D.sp.cm.sig T.gram w q)).1 * Matrix.map d.jX (compInf D.host.F D.host.E w) = Matrix.map d.jX (compInf D.host.F D.host.E w) * β) → q ∈ stab d := by
  intro D T T₀ r d q hq hw
  have hPX : d.pX ⬝ d.jX = 1 := d.pX_jX
  have key := mul_jX_eq d q hq hw
  have hinv : Formalism.L2.Theta.mt T q⁻¹ ⬝ Formalism.L2.Theta.mt T q = 1 := mt_inv_mul_self q
  have h1 : (d.pX ⬝ Formalism.L2.Theta.mt T q⁻¹ ⬝ d.jX) ⬝ (d.pX ⬝ Formalism.L2.Theta.mt T q ⬝ d.jX) = 1 := by
    calc (d.pX ⬝ Formalism.L2.Theta.mt T q⁻¹ ⬝ d.jX) ⬝ (d.pX ⬝ Formalism.L2.Theta.mt T q ⬝ d.jX)
        = (d.pX ⬝ Formalism.L2.Theta.mt T q⁻¹) ⬝ (d.jX ⬝ (d.pX ⬝ Formalism.L2.Theta.mt T q ⬝ d.jX)) := by
          rw [Matrix.mul_assoc]
      _ = (d.pX ⬝ Formalism.L2.Theta.mt T q⁻¹) ⬝ (Formalism.L2.Theta.mt T q ⬝ d.jX) := by rw [← key]
      _ = d.pX ⬝ ((Formalism.L2.Theta.mt T q⁻¹ ⬝ Formalism.L2.Theta.mt T q) ⬝ d.jX) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hinv, Matrix.one_mul, hPX]
  exact ⟨⟨_, _, mul_eq_one_comm.mp h1, h1⟩, key⟩

end GlobalTheory.Core.Rk.IwGlob
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

namespace GlobalTheory

theorem integral_normSq_coef_ne_zero : ∀ (D : D7) (V : HSp D), V.SigOK → V.IsPosDef → ∀ (c : CoefA V), c.Is → ∀ w : c.W, w ≠ 0 → ∀ mR : Measure (GinfC V), mR.IsHaarMeasure → ∫ b : GinfC V, ‖⟪w, c.ρ (b : GA D V) w⟫_ℂ‖ ^ 2 ∂mR ≠ 0 := by
  intro D V hS hp c hc w hw mR hR
  have : CompactSpace (GinfC V) :=
    isCompact_iff_compactSpace.1 (Formalism.IndefR.Eqv.isCompact_GinfC hS fun τ => Or.inl (hp τ))
  set f : GinfC V → ℝ := fun b => ‖⟪w, c.ρ (b : GA D V) w⟫_ℂ‖ ^ 2 with hfdef
  have hcont : Continuous f := by
    have h1 : Continuous fun b : GinfC V => c.ρ (b : GA D V) w := (hc.2.2.1 w).comp continuous_subtype_val
    exact ((continuous_const.inner h1).norm).pow 2
  have hnn : 0 ≤ f := fun b => by positivity
  have hint : Integrable f mR := hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have h1 : f 1 ≠ 0 := by
    simp only [hfdef, OneMemClass.coe_one, map_one, Module.End.one_apply]
    exact pow_ne_zero _ (norm_ne_zero_iff.2 (inner_self_ne_zero.2 hw))
  have hpos : 0 < ∫ b, f b ∂mR := by
    rw [integral_pos_iff_support_of_nonneg hnn hint]
    exact hcont.isOpen_support.measure_pos mR ⟨1, h1⟩
  exact hpos.ne'

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_inner_product_smooth_vectors_tensor : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), ∃ ipD : SmT M →ₗ[ℂ] SmT M →ₗ⋆[ℂ] ℂ, (∀ v v' : M.Vec, ipD (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v') = ∏ τ, ⟪(v' τ : M.H τ), (v τ : M.H τ)⟫_ℂ) ∧ (∀ w w', ipD w w' = conj (ipD w' w)) ∧ ∀ w, w ≠ 0 → 0 < (ipD w w).re := by
  first | exact @GlobalTheory.ChainOnto.exists_ipD_smT | exact GlobalTheory.ChainOnto.exists_ipD_smT | (intros; apply GlobalTheory.ChainOnto.exists_ipD_smT <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.heckeChar_tameAt_of_factors_through_residue : ∀ (D : D7) (H : Formalism.L2.Host.HChar D.host.E) (PP : Pl D.host.E) (a : (kP PP)ˣ →* ℂˣ), IsRes H PP a → H.TameAt PP := by
  first | exact @GlobalTheory.ChainOnto.TameRes.tameAt_of_isRes | exact GlobalTheory.ChainOnto.TameRes.tameAt_of_isRes | (intros; apply GlobalTheory.ChainOnto.TameRes.tameAt_of_isRes <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.exists_unitary_finiteAdelic_map_selfDual_completions : ∀ (D : D7) (A : HSp D) (L L' : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)),
    IsSelfDualC A L → IsSelfDualC A L' →
    ∃ b ∈ HR (Af D.host.F) D.sp.cm.sig A.gram, ∀ w : Fin A.rank → TensorProduct D.host.F (Af D.host.F) D.host.E,
      w ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L : Set (Fin A.rank → D.host.E)) ↔
        b.val *ᵥ w ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L' : Set (Fin A.rank → D.host.E)) := by
  first | exact @GlobalTheory.Core.Rk.OrthIsom.exists_unitary_latHat | exact GlobalTheory.Core.Rk.OrthIsom.exists_unitary_latHat | (intros; apply GlobalTheory.Core.Rk.OrthIsom.exists_unitary_latHat <;> assumption)
end

section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

theorem _root_.GlobalTheory.T.kernel_expansion_absolute_convergence_equal_words : Formalism.L2.SG.ThmSOwn.KExpTied ∧ AbsConvTied := by
  first | exact @GlobalTheory.Core.Diag.kExp_absConv_tied | exact GlobalTheory.Core.Diag.kExp_absConv_tied | (intros; apply GlobalTheory.Core.Diag.kExp_absConv_tied <;> assumption)
end
