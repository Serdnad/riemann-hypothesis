module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LeftInvOfUnitary
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle137
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle103
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle084
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle014
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MulPowTwoLeTripleProdOfGe
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IteratedFDerivAlgebraicDirectionsJetTransport
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle002
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerLattices
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
import Formalism.LocalToGlobal.KernelLattices.LateralTheory

@[expose] public section

section

open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

noncomputable section

namespace GlobalTheory.RealOrbitMap

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_homeomorph (h : IsCMExt F E σ) {I : Type} [Fintype I] {τ : I → (E →+* ℂ)} (hτ : IsCMFam τ)
    {θ : I → (Ainf F ⊗[F] E →+* ℂ)} (hθ : ∀ ρ, IsInfEmb (τ ρ) (θ ρ)) :
    ∃ Φ : (Ainf F ⊗[F] E) ≃ₜ (I → ℂ), ∀ z ρ, Φ z ρ = θ ρ z := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Ainf F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Ainf F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_infiniteAdele F
  obtain ⟨e₀⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Ainf F)
  haveI : LocallyCompactSpace (Ainf F ⊗[F] E) := e₀.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Ainf F ⊗[F] E) := e₀.secondCountableTopology
  have hb := infEmb_bijective h hτ hθ
  let Θ : Ainf F ⊗[F] E →+ (I → ℂ) := (Pi.ringHom θ).toAddMonoidHom
  have hΘ : Continuous Θ := continuous_pi fun ρ => infEmb_continuous (hθ ρ)
  have ho : IsOpenMap Θ := AddMonoidHom.isOpenMap_of_sigmaCompact Θ hb.2 hΘ
  exact ⟨(Equiv.ofBijective Θ hb).toHomeomorphOfContinuousOpen hΘ ho, fun _ _ => rfl⟩

theorem mat_inv_mul {P Q : ℕ} (t : UpqT P Q) : UpqT.mat t⁻¹ * UpqT.mat t = 1 :=
  Units.inv_mul (show Formalism.UG.Upq P Q from t).1

theorem theta_projInf {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb τ θ) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (h : HA (AF F) σ J) (x : Fin 1 → Fin M → E) :
    (fun i => θ (projInf (h • ratTup (F := F) (AF F) x) 0 i)) = infMat σ J θ h *ᵥ fun i => τ (x 0 i) := by
  funext i
  let p : AF F ⊗[F] E →+* Ainf F ⊗[F] E := (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom
  have e := RingHom.map_mulVec (θ.comp p) (HA.mat (AF F) σ J h).1 (ratTup (F := F) (AF F) x 0) i
  refine e.trans ?_
  have e2 : (θ.comp p) ∘ ratTup (F := F) (AF F) x 0 = fun i => τ (x 0 i) := by
    funext j
    rw [← hθ.1]
    show θ (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (1 ⊗ₜ x 0 j)) = _
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl
  rw [e2]
  rfl

theorem realOrbit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (I : Type) [Fintype I] (τ : I → (E →+* ℂ)), IsCMFam τ → ∀ (θ : I → (Ainf F ⊗[F] E →+* ℂ)), (∀ ρ, IsInfEmb (τ ρ) (θ ρ)) → ∀ (M P Q : ℕ) (J : Matrix (Fin M) (Fin M) E) (A : I → Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ) (N : I → Matrix (Fin M) (Fin P ⊕ Fin Q) ℂ), (∀ ρ, N ρ * A ρ = 1) → (∀ ρ, A ρ * N ρ = 1) → ∀ x : Fin 1 → Fin M → E, AllSome (fun pt : (I → UpqT P Q) → (Fin 1 → Fin M → Ainf F ⊗[F] E) => ∀ g ρ, infCoord (θ ρ) (A ρ) (pt g) = UpqT.mat (g ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => τ ρ (x 0 i))) fun pt => Measurable pt ∧ (∀ g g', (∀ ρ, UpqT.mat (g ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => τ ρ (x 0 i)) = UpqT.mat (g' ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => τ ρ (x 0 i))) → pt g = pt g') ∧ ∀ (h : HA (AF F) σ J) (t : I → UpqT P Q), (∀ ρ, UpqT.mat (t ρ) * A ρ = A ρ * infMat σ J (θ ρ) h) → pt t = projInf (h⁻¹ • ratTup (F := F) (AF F) x) := by
  intro F E _ _ _ _ _ σ hcm I _ τ hτ θ hθ M P Q J A N hl hr x
  obtain ⟨Φ, hΦ⟩ := exists_homeomorph hcm hτ hθ
  let v : (I → UpqT P Q) → I → Fin P ⊕ Fin Q → ℂ := fun g ρ => UpqT.mat (g ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => τ ρ (x 0 i))
  have key : ∀ (Y : Fin 1 → Fin M → Ainf F ⊗[F] E) (w : I → Fin P ⊕ Fin Q → ℂ),
      (∀ ρ, infCoord (θ ρ) (A ρ) Y = w ρ) ↔ Y = fun _ i => Φ.symm fun ρ => (N ρ *ᵥ w ρ) i := by
    intro Y w
    constructor
    · intro hY
      funext a i
      obtain rfl : a = 0 := Subsingleton.elim _ _
      apply Φ.injective
      rw [Φ.apply_symm_apply]
      funext ρ
      rw [hΦ, ← hY ρ, infCoord, Matrix.mulVec_mulVec, hl, Matrix.one_mulVec]
    · rintro rfl ρ
      have : (fun i => θ ρ (Φ.symm fun ρ => (N ρ *ᵥ w ρ) i)) = N ρ *ᵥ w ρ := by
        funext i
        rw [← hΦ, Φ.apply_symm_apply]
      rw [infCoord, this, Matrix.mulVec_mulVec, hr, Matrix.one_mulVec]
  refine ⟨⟨fun g _ i => Φ.symm fun ρ => (N ρ *ᵥ v g ρ) i, fun g => (key _ (v g)).2 rfl⟩, fun pt hpt => ?_⟩
  have hpt' : ∀ g, pt g = fun _ i => Φ.symm fun ρ => (N ρ *ᵥ v g ρ) i := fun g => (key _ (v g)).1 (hpt g)
  refine ⟨?_, fun g g' hg => ?_, fun h t ht => ?_⟩
  · haveI : IsTopologicalGroup (UpqT P Q) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))
    haveI : BorelSpace (UpqT P Q) := ⟨rfl⟩
    haveI : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
    haveI : SecondCountableTopology (UpqT P Q) :=
      (GlobalTheory.UpqUnimodular.modelEquiv P Q).toHomeomorph.secondCountableTopology
    rw [show pt = _ from funext hpt']
    refine Measurable.of_eval fun _ => Measurable.of_eval fun i => Continuous.measurable ?_
    refine Φ.symm.continuous.comp (continuous_pi fun ρ => (continuous_apply i).comp (f := fun a => N ρ *ᵥ v a ρ) ?_)
    exact continuous_const.matrix_mulVec
      ((GlobalTheory.VolPairExists.continuous_mat.comp (continuous_apply ρ).inv).matrix_mulVec continuous_const)
  · rw [hpt', hpt', show v g = v g' from funext hg]
  · rw [hpt']
    refine ((key _ (v t)).1 fun ρ => ?_).symm
    have e : A ρ * infMat σ J (θ ρ) h⁻¹ = UpqT.mat (t ρ)⁻¹ * A ρ := by
      calc A ρ * infMat σ J (θ ρ) h⁻¹
          = UpqT.mat (t ρ)⁻¹ * (UpqT.mat (t ρ) * A ρ) * infMat σ J (θ ρ) h⁻¹ := by
            rw [← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]
        _ = UpqT.mat (t ρ)⁻¹ * A ρ := by
            rw [ht, Matrix.mul_assoc, Matrix.mul_assoc, ← Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.infMat_mul, mul_inv_cancel,
              Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.infMat_one, Matrix.mul_one]
    rw [infCoord, theta_projInf (hθ ρ), Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec]

end GlobalTheory.RealOrbitMap
end
end

section

noncomputable section
open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate Topology

namespace GlobalTheory.MomN.ThetaQuot

variable {q : ℕ} [Fact q.Prime]

theorem bdd_hat_quot (M : Mdl q) (ℓ : ℂ_[q]⟦X⟧) (hC : M.Chart ℓ) (F H : ℂ → ℂ)
    (hF : Differentiable ℂ F) (hH : Differentiable ℂ H) (h0 : H 0 ≠ 0)
    (hper : ∀ l ∈ M.L.lattice, ∀ z, F (z + l) / H (z + l) = F z / H z)
    (hz : ∀ p, H p = 0 → ¬ M.Small p) :
    Bdd (hat M.ι ℓ fun z => F z / H z) := by
  refine EllBdd.bdd_hat_of_ell q M ℓ _ hC ⟨fun z => ?_, hper⟩ ((hF.analyticAt 0).div (hH.analyticAt 0) h0)
    fun p hp => hz p ?_
  · exact (hF.analyticAt z).meromorphicAt.div (hH.analyticAt z).meromorphicAt
  · by_contra hne
    exact absurd hp (not_lt.2 ((hF.analyticAt p).div (hH.analyticAt p) hne).meromorphicOrderAt_nonneg)

theorem not_inOK_half {d : ℕ} (hd : 0 < d) : ¬ InOK d (1 / 2) := by
  rintro ⟨u, v, h⟩
  have hs : Real.sqrt d ≠ 0 := by positivity
  have h2 := congrArg Complex.im h
  have h1' := congrArg Complex.re h
  simp [wK, hs] at h1' h2
  subst h2
  have : (1 : ℝ) = 2 * u := by linarith
  have : (1 : ℤ) = 2 * u := by exact_mod_cast this
  omega

theorem bd_one_hat_of_theta_level : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ G : ℂ → ℂ) (a : ℕ), d.Prime → d % 16 = 7 → Split d q → q ≠ 2 → IsOK d M.L → M.MChart ω → IsTh d θ → Differentiable ℂ G → G 0 = 1 → (∀ x, InOK d x → ∀ z, G (z + x) * (Complex.exp ((Real.pi : ℂ) * Complex.I * ((Complex.normSq x : ℝ) : ℂ)) * Complex.exp (-(Real.pi : ℂ) * h1 d z x - (Real.pi : ℂ) / 2 * h1 d x x)) ^ a = G z) → (∀ z, G z = 0 → PrimeTo d q z) → Bd 1 (hat M.ι (C ω * logS) G) := by
  intro d q _ M ω θ G a hd hd16 hsp hq2 hOK hMC hθ hG hG0 hGW hGz
  have hθB := theta_series_integral d q M ω θ hd hd16 hsp hOK hMC hθ
  have hC : M.Chart (C ω * logS) := hMC
  set ℓ := C ω * logS with hℓ
  have hOk := hC.1
  have hℓ0 : constantCoeff ℓ = 0 := hC.2.1
  obtain ⟨hθd, hθ0, -, hθW, hθz⟩ := hθ
  set E : ℂ → ℂ → ℂ := fun z x => Complex.exp ((Real.pi : ℂ) * Complex.I * ((Complex.normSq x : ℝ) : ℂ)) *
    Complex.exp (-(Real.pi : ℂ) * h1 d z x - (Real.pi : ℂ) / 2 * h1 d x x) with hE
  have hE0 : ∀ z x, E z x ≠ 0 := fun z x => mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
  have hθE : ∀ x, InOK d x → ∀ z, θ (z + x) * E z x = θ z := by
    intro x hx z
    have := congrFun (hθW x hx) z
    simp only [W1, U1] at this
    rw [← this]; simp only [hE]; ring
  have hGE : ∀ x, InOK d x → ∀ z, G (z + x) * E z x ^ a = G z := hGW
  have hlat : ∀ l, l ∈ M.L.lattice ↔ InOK d l := hOK
  have hper1 : ∀ l ∈ M.L.lattice, ∀ z, G (z + l) / θ (z + l) ^ a = G z / θ z ^ a := by
    intro l hl z
    rw [hlat] at hl
    rw [← hGE l hl z, ← hθE l hl z, mul_pow (θ (z + l)) (E z l) a, mul_div_mul_right _ _ (pow_ne_zero _ (hE0 z l))]
  have hper2 : ∀ l ∈ M.L.lattice, ∀ z, θ (z + l) ^ a / G (z + l) = θ z ^ a / G z := by
    intro l hl z
    rw [hlat] at hl
    rw [← hGE l hl z, ← hθE l hl z, mul_pow (θ (z + l)) (E z l) a, mul_div_mul_right _ _ (pow_ne_zero _ (hE0 z l))]
  have hnsθ : ∀ p, θ p = 0 → ¬ M.Small p := by
    intro p hp
    have hm : p - 1 / 2 ∈ M.L.lattice := (hlat _).2 (hθz p hp)
    have h1m : (1 : ℂ) ∈ M.L.lattice := (hlat _).2 ⟨1, 0, by simp⟩
    have h2 : ((2 : ℕ) : ℂ) * p ∈ M.L.lattice := by
      have : ((2 : ℕ) : ℂ) * p = (p - 1 / 2) + (p - 1 / 2) + 1 := by push_cast; ring
      rw [this]; exact add_mem (add_mem hm hm) h1m
    have hnot : p ∉ M.L.lattice := fun h => not_inOK_half hd.pos ((hlat _).1 (by
      have : (1 / 2 : ℂ) = p - (p - 1 / 2) := by ring
      rw [this]; exact sub_mem h hm))
    have hcop : Nat.Coprime 2 q := (Nat.coprime_primes Nat.prime_two Fact.out).2 (Ne.symm hq2)
    have hx := (TorsionReduction.torsion_integral_and_distinct q M 2 hOk hcop).1 p h2 hnot
    rintro (h | h)
    · exact hnot h
    · linarith
  have hnsG : ∀ p, G p = 0 → ¬ M.Small p := by
    intro p hp
    obtain ⟨s, -, hsq, hsp'⟩ := hGz p hp
    have hm : (s : ℂ) * p ∈ M.L.lattice := (hlat _).2 hsp'
    have hnot : p ∉ M.L.lattice := fun h => by
      have := hGE p ((hlat _).1 h) 0
      rw [zero_add, hp, zero_mul, hG0] at this
      exact zero_ne_one this
    have hx := (TorsionReduction.torsion_integral_and_distinct q M s hOk hsq).1 p hm hnot
    rintro (h | h)
    · exact hnot h
    · linarith
  have hθa : Differentiable ℂ (fun z => θ z ^ a) := hθd.pow a
  have hθa0 : θ 0 ^ a ≠ 0 := by rw [hθ0, one_pow]; exact one_ne_zero
  have hG0' : G 0 ≠ 0 := by rw [hG0]; exact one_ne_zero
  have hφ := bdd_hat_quot M ℓ hC G (fun z => θ z ^ a) hG hθa hθa0 hper1
    (fun p hp => by
      rcases eq_or_ne a 0 with rfl | ha
      · simp at hp
      · exact hnsθ p ((pow_eq_zero_iff ha).1 hp))
  have hψ := bdd_hat_quot M ℓ hC (fun z => θ z ^ a) G hθa hG hG0' hper2 hnsG
  obtain ⟨hL1, hL2, -, hL4, -, -, -⟩ := TaylorRead.hat_laws q M.ι ℓ hℓ0
  obtain ⟨gl1, -, -, -, gl5, -⟩ := sup_norm_laws q
  have haφ : AnalyticAt ℂ (fun z => G z / θ z ^ a) 0 := (hG.analyticAt 0).div (hθa.analyticAt 0) hθa0
  have haψ : AnalyticAt ℂ (fun z => θ z ^ a / G z) 0 := (hθa.analyticAt 0).div (hG.analyticAt 0) hG0'
  have hθne : ∀ᶠ z in 𝓝 0, θ z ≠ 0 := hθd.continuous.continuousAt.eventually_ne (by rw [hθ0]; exact one_ne_zero)
  have hGne : ∀ᶠ z in 𝓝 0, G z ≠ 0 := hG.continuous.continuousAt.eventually_ne hG0'
  have hprod : hat M.ι ℓ (fun z => G z / θ z ^ a) * hat M.ι ℓ (fun z => θ z ^ a / G z) = 1 := by
    have e1 := (hL1 (fun z => G z / θ z ^ a * (θ z ^ a / G z)) (fun _ => 1) (haφ.mul haψ) analyticAt_const).2.2.1
      (eventually_nhdsWithin_of_eventually_nhds (by
        filter_upwards [hθne, hGne] with z h1 h2
        rw [div_mul_div_comm, mul_comm (G z), div_self (mul_ne_zero (pow_ne_zero _ h1) h2)]))
    rw [← (hL1 _ _ haφ haψ).2.1, e1, hL2]; simp
  have hcc : constantCoeff (hat M.ι ℓ (fun z => G z / θ z ^ a)) = 1 := by
    rw [hL4]; simp [hG0, hθ0]
  have hφ1 : Bd 1 (hat M.ι ℓ (fun z => G z / θ z ^ a)) := (gl5 _ _ hφ hψ hprod hcc).1
  have eG : hat M.ι ℓ G = hat M.ι ℓ (fun z => G z / θ z ^ a) * hat M.ι ℓ (fun z => θ z ^ a) := by
    rw [← (hL1 _ _ haφ (hθa.analyticAt 0)).2.1]
    exact (hL1 G _ (hG.analyticAt 0) (haφ.mul (hθa.analyticAt 0))).2.2.1
      (eventually_nhdsWithin_of_eventually_nhds (by
        filter_upwards [hθne] with z h1
        exact (div_mul_cancel₀ _ (pow_ne_zero _ h1)).symm))
  have hpow : ∀ n : ℕ, hat M.ι ℓ (fun z => θ z ^ n) = hat M.ι ℓ θ ^ n ∧ Bd 1 (hat M.ι ℓ θ ^ n) := by
    intro n
    induction n with
    | zero =>
      refine ⟨by simpa using hL2 1, fun k => ?_⟩
      rw [pow_zero, coeff_one]; split_ifs <;> simp
    | succ n ih =>
      have e : (fun z => θ z ^ (n + 1)) = fun z => θ z ^ n * θ z := funext fun z => pow_succ _ _
      rw [e, (hL1 (fun z => θ z ^ n) θ ((hθd.pow n).analyticAt 0) (hθd.analyticAt 0)).2.1, ih.1, pow_succ]
      refine ⟨rfl, ?_⟩
      simpa using (gl1 _ _ 1 1 ih.2 hθB).2
  rw [eG, (hpow a).1]
  simpa using (gl1 _ _ 1 1 hφ1 (hpow a).2).2

end GlobalTheory.MomN.ThetaQuot
end
end

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

theorem _root_.GlobalTheory.T.iteratedFDeriv_algebraic_directions_jet_transport : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' : ℕ) (G : VC D N N' → ℂ), ContDiff ℂ ⊤ G → CoefIn D G Qbar → ∀ (m : ℕ) (y : Fin m → Matrix (Fin N') (Fin N) D.host.E), iteratedFDeriv ℂ m G 0 (fun j => embV D (tor0 D cc δ) (y j)) ∈ Qbar ∧ jet D lam y (pSer D lam G) = lamC lam (iteratedFDeriv ℂ m G 0 fun j => embV D (tor0 D cc δ) (y j)) := by
  first | exact @GlobalTheory.JetTransport.jet_pSer | exact GlobalTheory.JetTransport.jet_pSer | (intros; apply GlobalTheory.JetTransport.jet_pSer <;> assumption)
end

end

section

@[expose] public section

open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

theorem _root_.GlobalTheory.T.exists_measurable_realOrbitMap_of_adelicOrbit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (I : Type) [Fintype I] (τ : I → (E →+* ℂ)), IsCMFam τ → ∀ (θ : I → (Ainf F ⊗[F] E →+* ℂ)), (∀ ρ, IsInfEmb (τ ρ) (θ ρ)) → ∀ (M P Q : ℕ) (J : Matrix (Fin M) (Fin M) E) (A : I → Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ) (N : I → Matrix (Fin M) (Fin P ⊕ Fin Q) ℂ), (∀ ρ, N ρ * A ρ = 1) → (∀ ρ, A ρ * N ρ = 1) → ∀ x : Fin 1 → Fin M → E, AllSome (fun pt : (I → UpqT P Q) → (Fin 1 → Fin M → Ainf F ⊗[F] E) => ∀ g ρ, infCoord (θ ρ) (A ρ) (pt g) = UpqT.mat (g ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => τ ρ (x 0 i))) fun pt => Measurable pt ∧ (∀ g g', (∀ ρ, UpqT.mat (g ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => τ ρ (x 0 i)) = UpqT.mat (g' ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => τ ρ (x 0 i))) → pt g = pt g') ∧ ∀ (h : HA (AF F) σ J) (t : I → UpqT P Q), (∀ ρ, UpqT.mat (t ρ) * A ρ = A ρ * infMat σ J (θ ρ) h) → pt t = projInf (h⁻¹ • ratTup (F := F) (AF F) x) := by
  first | exact @GlobalTheory.RealOrbitMap.realOrbit | exact GlobalTheory.RealOrbitMap.realOrbit | (intros; apply GlobalTheory.RealOrbitMap.realOrbit <;> assumption)

end
end
