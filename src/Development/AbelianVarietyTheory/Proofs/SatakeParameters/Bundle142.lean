module

public import Formalism.LocalRingCardinality.DataForced
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.Bundle002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle094
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle130
import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle003
import Formalism.LocalRingCardinality.Bundle002
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SqrtInUnramifiedCompletion
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Formalism.LocalToGlobal.Columns.Bundle023
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Formalism.LocalToGlobal.Columns.ChainInst
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle004
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle010
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Formalism.LocalToGlobal.KernelLattices.Bundle001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle133
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual addC thetaInZ sumE)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd

open GlobalTheory.InertCompare GlobalTheory.Proof.IdempotentLatticeSequence

theorem exists_aut_of_algHoms {E K : Type} [Field E] [NumberField E] [IsGalois ℚ E] [Field K] [CharZero K]
    (f g : E →ₐ[ℚ] K) : ∃ u : E ≃ₐ[ℚ] E, ∀ x, g x = f (u x) := by
  have hmem : ∀ x, ∃ y, f y = g x := fun x => by
    have hs := Normal.splits (inferInstance : Normal ℚ E) x
    have hi : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
    have hr : (((minpoly ℚ x).map (algebraMap ℚ E)).map (f : E →+* K)).IsRoot (g x) := by
      rw [Polynomial.map_map, AlgHom.comp_algebraMap_of_tower, Polynomial.IsRoot, Polynomial.eval_map_algebraMap,
        Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    exact hs.mem_range_of_isRoot (Polynomial.map_ne_zero (minpoly.ne_zero hi)) hr
  choose v hv using hmem
  have hf : Function.Injective f := f.toRingHom.injective
  let w : E →ₐ[ℚ] E :=
    { toFun := v
      map_one' := hf (by rw [hv, map_one, map_one])
      map_mul' := fun a b => hf (by rw [hv, map_mul, map_mul, hv, hv])
      map_zero' := hf (by rw [hv, map_zero, map_zero])
      map_add' := fun a b => hf (by rw [hv, map_add (f := _), map_add (f := _), hv, hv])
      commutes' := fun r => hf (by
        rw [hv, AlgHom.commutes, AlgHom.commutes]) }
  exact ⟨AlgEquiv.ofBijective w (AlgHom.normal_bijective ℚ E E w), fun x => (hv x).symm⟩

theorem exists_aut_of_embeddings {E K : Type} [Field E] [NumberField E] [IsGalois ℚ E] [Field K] [CharZero K]
    (f g : E →+* K) : ∃ u : E ≃ₐ[ℚ] E, ∀ x, g x = f (u x) :=
  exists_aut_of_algHoms f.toRatAlgHom g.toRatAlgHom

theorem padic_mem_Kur (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) : algebraMap ℚ_[p] ℂ_[p] x ∈ MaximalUnramifiedExtension p := by
  have hc : Continuous (algebraMap ℚ_[p] ℂ_[p]) := (algebraMap_isometry ℚ_[p] ℂ_[p]).continuous
  refine (Padic.denseRange_ratCast p).induction_on (p := fun x => algebraMap ℚ_[p] ℂ_[p] x ∈ MaximalUnramifiedExtension p) x ?_ ?_
  · exact Formalism.L2.Th1.D.GaussNormEstimates.isClosed_Kur.preimage hc
  · intro q
    simp

theorem coe_mem_Kur (p : ℕ) [Fact p.Prime] {x : PadicAlgCl p} (hx : x ∈ Formalism.BasicNotions.Loc.MaximalUnramifiedExtension p) :
    algebraMap (PadicAlgCl p) ℂ_[p] x ∈ MaximalUnramifiedExtension p := by
  unfold Formalism.BasicNotions.Loc.MaximalUnramifiedExtension at hx
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨m, hm, hpm, h1⟩ := hx
    exact Formalism.L2.Th1.D.GaussNormEstimates.mu_mem_Kur hm hpm (by rw [← map_pow, h1, map_one])
  | algebraMap x =>
    rw [← IsScalarTower.algebraMap_apply]
    exact padic_mem_Kur p x
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem host_image_mem_Kur_complex {R : Ranks} (H : Host R) (p : ℕ) [Fact p.Prime] (h2 : p ∉ H.small) (hq : p ≠ H.q)
    (hd : p ≠ H.d) (ρ : H.E →+* ℂ_[p]) (x : H.E) : ρ x ∈ MaximalUnramifiedExtension p := by
  have : IsGalois ℚ H.E := H.hostE_isGalois
  let c : H.E →+* PadicAlgCl p := (IsAlgClosed.lift : H.E →ₐ[ℚ] PadicAlgCl p)
  obtain ⟨u, hu⟩ := exists_aut_of_embeddings ((algebraMap (PadicAlgCl p) ℂ_[p]).comp c) ρ
  rw [hu, RingHom.comp_apply]
  exact coe_mem_Kur p (GlobalTheory.HostKur.host_image_mem_Kur H p h2 hq hd c _)

theorem exists_kur_frob_tauEmb_posPl : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → (IsResidueClassZero D p ∨ IsSg D p) → ∀ (z : Bool × HH D) (y : D.host.E), ∃ a : MaximalUnramifiedExtension p, (a : ℂ_[p]) = tauEmb D lam (tauPl D z) y ∧ ((σ a : MaximalUnramifiedExtension p) : ℂ_[p]) = tauEmb D lam (tauPl D (posPl D p z 1)) (D.host.conj y) := by
  intro D p _ lam σ hσ h z y
  have ⟨h2, hq, hd⟩ : p ∉ D.host.small ∧ p ≠ D.host.q ∧ p ≠ D.host.d := by
    rcases h with h | h
    · have k := (primeClass_eq_inert_iff D.host.toHostRaw).1 h
      exact ⟨k.1, k.2.1, k.2.2.1⟩
    · have k := (primeClass_eq_signal_iff D.host.toHostRaw).1 h
      exact ⟨k.1, k.2.1, k.2.2.1⟩
  have : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = rhoH D lam (tauPl D z) := ⟨_, rfl⟩
  have hK : ∀ x, ρ x ∈ MaximalUnramifiedExtension p := host_image_mem_Kur_complex D.host p h2 hq hd ρ
  let ρ' : D.host.E →+* MaximalUnramifiedExtension p := ρ.codRestrict (MaximalUnramifiedExtension p) hK
  have hρ' : ∀ x, ((ρ' x : MaximalUnramifiedExtension p) : ℂ_[p]) = ρ x := fun _ => rfl
  let ρ2 : D.host.E →+* ℂ_[p] := (MaximalUnramifiedExtension p).subtype.comp (σ.comp ρ')
  obtain ⟨g, hg⟩ := exists_aut_of_embeddings ρ ρ2
  have := primeOf_isPrime ρ
  have hL := primeOf_liesOver ρ
  have hc : Nat.card (ℤ ⧸ Ideal.under ℤ (primeOf ρ)) = p := by
    rw [← hL.over, Int.card_ideal_quot]
  have hgF : IsArithFrobAt ℤ g (primeOf ρ) := by
    intro x
    rw [hc, mem_primeOf]
    have hx : ‖ρ' (x : D.host.E)‖ ≤ 1 := norm_int_le ρ x
    have h3 := hσ.2.2.2.2 _ hx
    have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
    refine lt_of_le_of_lt ?_ hp1
    refine le_of_eq_of_le ?_ h3
    have e1 : ρ (algebraMap (𝓞 D.host.E) D.host.E ((MulSemiringAction.toAlgHom ℤ (𝓞 D.host.E) g) x - x ^ p)) =
        ((σ (ρ' (x : D.host.E)) - ρ' (x : D.host.E) ^ p : MaximalUnramifiedExtension p) : ℂ_[p]) := by
      have e0 : algebraMap (𝓞 D.host.E) D.host.E ((MulSemiringAction.toAlgHom ℤ (𝓞 D.host.E) g) x) = g (x : D.host.E) := rfl
      rw [map_sub, map_sub, e0, ← hg, map_pow, map_pow]
      rfl
    rw [e1]
    rfl
  obtain ⟨φ, hφ⟩ := (D.host.der.frob p (UpperTheory.Small.not_dvd_condN D.host Fact.out h2 hq hd) (primeOf ρ)).1
  have hgφ : g = φ := by
    have hI := hgF.mul_inv_mem_inertia hφ
    have h1 := ((D.host.der.frob p (UpperTheory.Small.not_dvd_condN D.host Fact.out h2 hq hd) (primeOf ρ)).2.2.2 (g * φ⁻¹)).1 (fun x => hI x)
    exact mul_inv_eq_one.1 h1
  have hcc : D.host.conj (D.host.conj y) = y := D.host.φ₀.injective (by
    rw [D.host.conjE_apply, D.host.conjE_apply, Complex.conj_conj])
  refine ⟨ρ' y, ?_, ?_⟩
  · rw [hρ', hρ, ← coe_rhoH]
  · have hplGG : ∀ z : Bool × HH D, plGG D (posPl D p z 1) = plGG D z * D.host.galE φ * D.R.cc := by
      have hC := factClassFrob D.R D.host p (UpperTheory.Small.not_dvd_condN D.host Fact.out h2 hq hd) (primeOf ρ) φ hφ
      have hc := (Nat.Prime.coprime_iff_not_dvd Fact.out).2 (UpperTheory.Small.not_dvd_condN D.host Fact.out h2 hq hd)
      have hne : ∃ g, g ∈ Formalism.MainNotions.G.frobSet D p := ⟨_, primeOf ρ, inferInstance, inferInstance, φ, hφ, rfl⟩
      obtain ⟨P₀, hP₀, hL₀, σ₀, hσ₀, hg₀⟩ := Classical.epsilon_spec hne
      have e1 := (D.host.toHostAx.frob_iff p hc (primeOf ρ) φ).1 hφ
      have e2 := (@Formalism.HC.HostAx.frob_iff _ D.host.toHostAx p _ hc P₀ hP₀ hL₀ σ₀).1 hσ₀
      have hH : (D.host.galE φ).2 = D.R.iota (G.hP D p) := by
        unfold Formalism.MainNotions.G.hP
        rw [Formalism.HC.Frame.iota_iotaInv, ← hg₀]
        exact congrArg Prod.snd (e1.trans e2.symm)
      have hp : ∀ z : Bool × HH D, plGG D z = ((if z.1 then -1 else 1, 1), D.R.iota z.2) := by
        rintro ⟨b, t⟩
        cases b <;> rfl
      intro z
      rw [hp, hp]
      refine Prod.ext ?_ ?_
      · rcases h with h | h
        · have h1 := hC.2.2.1 h
          have hs : ¬ IsSg D p := fun hs => by have := h.symm.trans hs; cases this
          simp only [Prod.fst_mul, h1, Formalism.HC.Frame.cc, Formalism.FrobeniusOrbits.c0, posPl, partner, hs]
          cases z.1 <;> simp
        · have h1 := hC.2.1.1 h
          have hp : (partner D p z.2 1).1 = true := decide_eq_true ⟨h, odd_one⟩
          simp only [Prod.fst_mul, h1, Formalism.HC.Frame.cc, Formalism.FrobeniusOrbits.c0, posPl, hp]
          cases z.1 <;> simp
      · simp only [Prod.snd_mul, Formalism.HC.Frame.cc, mul_one, hH, posPl, partner, one_smul]
        rw [Formalism.HC.Frame.iota_add]
    have hemb : ∀ (g : _ ) (σ : D.host.E ≃ₐ[ℚ] D.host.E) (x : D.host.E), D.host.emb (g * D.host.galE σ) x = D.host.emb g (σ x) := by
      intro g σ x
      have he : D.host.sigmaOf (g * D.host.galE σ) = D.host.sigmaOf g * σ := by
        unfold Host.sigmaOf
        rw [map_mul, MulEquiv.symm_apply_apply]
      change D.host.φ₀ (D.host.sigmaOf (g * D.host.galE σ) x) = D.host.φ₀ ((D.host.sigmaOf g * σ) x)
      rw [he]
    have het : ∀ z : Bool × HH D, embT D (tauPl D z) = D.host.emb (plGG D z) := by
      intro z
      unfold embT tauPl
      rw [Equiv.apply_symm_apply]
    have h4 : rhoH D lam (tauPl D (posPl D p z 1)) (D.host.conj y) = rhoH D lam (tauPl D z) (φ (D.host.conj (D.host.conj y))) := by
      rw [rhoH_apply, rhoH_apply, het, het, hplGG, ← D.host.galE_conjE, hemb, hemb]
    rw [hcc] at h4
    rw [← coe_rhoH, h4, ← hρ, ← hgφ, ← hg]
    rfl

end GlobalTheory.KerStd
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep

noncomputable section

namespace GlobalTheory.PrincipalCongruenceLevelK1

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))

theorem intAt_shift {m c : ℕ} (hm : m ≤ c) {a d : E}
    (ha : IntAt P (((qOf P : E) ^ (m : ℤ))⁻¹ * a)) (hd : IntAt P d) :
    IntAt P (((qOf P : E) ^ (m : ℤ))⁻¹ * (a + (qOf P : E) ^ c * d)) := by
  have hq : ((qOf P : ℕ) : E) ≠ 0 := qOf_ne_zero (P := P)
  have e : ((qOf P : E) ^ (m : ℤ))⁻¹ * (a + (qOf P : E) ^ c * d) =
      ((qOf P : E) ^ (m : ℤ))⁻¹ * a + (qOf P : E) ^ (c - m) * d := by
    rw [zpow_natCast]
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [Nat.add_sub_cancel_left, pow_add]
    field_simp
  rw [e]
  exact ha.add ((intAt_pow (P := P) (intAt_nat (P := P) (qOf P)) _).mul hd)

theorem prinCong_maps {N c : ℕ} {e : ℕ → ℤ} (he : ∀ l, 0 ≤ e l ∧ e l ≤ c) {k : GLint E N P}
    (hk : k ∈ prinCong N P c) {x : Sp E N} (hx : x ∈ LocE.sclLat P (qOf P) N e) :
    (k : Sp E N ≃ₗ[E] Sp E N) x ∈ LocE.sclLat P (qOf P) N e := by
  have hq : ((qOf P : ℕ) : E) ≠ 0 := qOf_ne_zero (P := P)
  rw [ciMem_sclLat] at hx ⊢
  have hxs : x ∈ stdAt E N P := by
    rw [ciMem_stdAt]
    intro l
    obtain ⟨m, hm⟩ : ∃ m : ℕ, e l.1 = m := ⟨(e l.1).toNat, by have := he l.1; omega⟩
    have h1 := (intAt_pow (P := P) (intAt_nat (P := P) (qOf P)) m).mul (hx l)
    rw [hm, zpow_natCast] at h1
    rwa [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq), one_mul] at h1
  have hd := mem_stdAt.1 (hk x hxs)
  intro l
  obtain ⟨m, hm⟩ : ∃ m : ℕ, e l.1 = m := ⟨(e l.1).toNat, by have := he l.1; omega⟩
  have hmc : m ≤ c := by have := he l.1; omega
  have e1 : (k : Sp E N ≃ₗ[E] Sp E N) x l = x l + (qOf P : E) ^ c * ((((qOf P : E) ^ c)⁻¹ • (k.1 x - x)) l) := by
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq), one_mul]
    show _ = x l + ((k : Sp E N ≃ₗ[E] Sp E N) x l - x l)
    ring
  rw [e1, hm]
  have hxl := hx l
  rw [hm] at hxl
  exact intAt_shift P hmc hxl (hd l)

theorem prinCong_stab {N c : ℕ} {e : ℕ → ℤ} (he : ∀ l, 0 ≤ e l ∧ e l ≤ c) {k : GLint E N P}
    (hk : k ∈ prinCong N P c) : (k : Sp E N ≃ₗ[E] Sp E N) ∈ stabL E N (LocE.sclLat P (qOf P) N e) := by
  intro x
  refine ⟨fun h => ?_, prinCong_maps P he hk⟩
  have h1 := prinCong_maps P he ((prinCong N P c).inv_mem hk) h
  have e2 : ((k⁻¹ : GLint E N P) : Sp E N ≃ₗ[E] Sp E N) ((k : Sp E N ≃ₗ[E] Sp E N) x) = x :=
    LinearEquiv.symm_apply_apply _ x
  rwa [e2] at h1

theorem principal_congruence_le_level_k1_at {N : ℕ} (r c : ℕ) (hc : 0 < c) : prinCong N P c ≤ twK1H P N r c := by
  intro k hk
  have hq : ((qOf P : ℕ) : E) ≠ 0 := qOf_ne_zero (P := P)
  refine ⟨⟨k.2, ?_⟩, prinCong_stab P (fun l => ?_) hk, prinCong_stab P (fun l => ?_) hk, fun w hw => ?_⟩
  · exact prinCong_stab P (N := N + 0) (fun l => by split_ifs <;> omega) hk
  · unfold kOneLastExponents; split_ifs <;> omega
  · unfold twistedLevelExponent; split_ifs <;> omega
  · have hws : w ∈ stdAt E N P := by
      have h0 := prinCong_maps P (e := fun _ => 0) (fun _ => by omega) ((prinCong N P c).one_mem) (x := w) ?_
      · rw [ciMem_sclLat] at h0; rw [ciMem_stdAt]; intro l; simpa using h0 l
      · rw [ciMem_sclLat] at hw ⊢
        intro l
        have h1 := hw l
        unfold twistedLevelExponent at h1
        split_ifs at h1 with hl
        · simpa using h1
        · have h2 := (intAt_pow (P := P) (intAt_nat (P := P) (qOf P)) c).mul h1
          rw [zpow_natCast, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq), one_mul] at h2
          simpa using h2
    have hd := mem_stdAt.1 (hk w hws)
    rw [ciMem_sclLat]
    intro l
    have := hd l
    simp only [Pi.smul_apply, smul_eq_mul, zpow_natCast] at this ⊢
    exact this

theorem principal_congruence_le_level_k1 : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {N : ℕ} (r c : ℕ),
    0 < c → prinCong N P c ≤ twK1H P N r c :=
  by
  intro E _ _ _ P N r c hc
  exact principal_congruence_le_level_k1_at P r c hc

end GlobalTheory.PrincipalCongruenceLevelK1
end
end

section

open Filter Topology

noncomputable section

namespace GlobalTheory.TeichImage

variable {p : ℕ} [hp : Fact p.Prime]

theorem coprime_pow_sub_one {n : ℕ} (hn : 0 < n) : Nat.Coprime (p ^ n - 1) p := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out]
  intro h
  have h1 : p ∣ p ^ n := dvd_pow_self p hn.ne'
  have h2 : 1 ≤ p ^ n := Nat.one_le_pow _ _ hp.out.pos
  have h3 : p ∣ p ^ n - (p ^ n - 1) := Nat.dvd_sub h1 h
  rw [show p ^ n - (p ^ n - 1) = 1 by omega] at h3
  exact hp.out.one_lt.ne' (Nat.dvd_one.1 h3)

theorem mem_range_of_pow_eq {n : ℕ} (hn : 0 < n) {τ : ℂ_[p]} (hτ : τ ^ (p ^ n) = τ) :
    τ ∈ Set.range (Formalism.L2.G.Pend.wToC p) := by
  by_cases h0 : τ = 0
  · exact ⟨0, by rw [h0, map_zero]⟩
  have hq : 2 ≤ p ^ n := le_trans hp.out.two_le (Nat.le_self_pow hn.ne' p)
  have h1 : τ ^ (p ^ n - 1) = 1 := by
    have : τ ^ (p ^ n - 1) * τ = 1 * τ := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega), hτ, one_mul]
    exact mul_right_cancel₀ h0 this
  exact Formalism.L2.G.Pend.root_mem_range p (by omega) (coprime_pow_sub_one hn) h1

theorem exists_lim {n : ℕ} (hn : 0 < n) (a : ℂ_[p])
    (ha : ∀ M : ℕ, ‖a ^ ((p ^ n) ^ (M + 1)) - a ^ ((p ^ n) ^ M)‖ ≤ ((p : ℝ)⁻¹) ^ (M + 1)) :
    ∃ τ ∈ Set.range (Formalism.L2.G.Pend.wToC p), ∀ N : ℕ, ‖a ^ ((p ^ n) ^ N) - τ‖ ≤ ((p : ℝ)⁻¹) ^ (N + 1) := by
  set r : ℝ := (p : ℝ)⁻¹ with hr
  have hr0 : 0 ≤ r := Formalism.L2.G.Pend.r_nonneg p
  have hr1 : r < 1 := Formalism.L2.G.Pend.r_lt_one p
  set u : ℕ → ℂ_[p] := fun M => a ^ ((p ^ n) ^ M) with hu
  have hcau : CauchySeq u := by
    refine cauchySeq_of_le_geometric r r hr1 fun m => ?_
    rw [dist_eq_norm, norm_sub_rev, ← pow_succ']
    exact ha m
  obtain ⟨τ, hτ⟩ := cauchySeq_tendsto_of_complete hcau
  have hball : ∀ N M : ℕ, N ≤ M → ‖u M - u N‖ ≤ r ^ (N + 1) := by
    intro N M hNM
    induction M, hNM using Nat.le_induction with
    | base => rw [sub_self, norm_zero]; exact pow_nonneg hr0 _
    | succ M hNM ih =>
      have : u (M + 1) - u N = (u (M + 1) - u M) + (u M - u N) := by ring
      rw [this]
      refine Formalism.L2.G.Pend.nadd p ((ha M).trans ?_) ih
      exact pow_le_pow_of_le_one hr0 hr1.le (by omega)
  have hlim : ∀ N : ℕ, ‖u N - τ‖ ≤ r ^ (N + 1) := by
    intro N
    have hmem : τ ∈ Metric.closedBall (u N) (r ^ (N + 1)) :=
      Metric.isClosed_closedBall.mem_of_tendsto hτ
        (eventually_atTop.2 ⟨N, fun M hM => by rw [Metric.mem_closedBall, dist_eq_norm]; exact hball N M hM⟩)
    rw [Metric.mem_closedBall, dist_eq_norm] at hmem
    rw [norm_sub_rev]; exact hmem
  have hsucc : ∀ M, u (M + 1) = u M ^ (p ^ n) := by
    intro M
    show a ^ ((p ^ n) ^ (M + 1)) = (a ^ ((p ^ n) ^ M)) ^ (p ^ n)
    rw [← pow_mul a ((p ^ n) ^ M) (p ^ n), ← pow_succ]
  have h1 : Tendsto (fun M => u (M + 1)) atTop (𝓝 τ) := hτ.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun M => u (M + 1)) atTop (𝓝 (τ ^ (p ^ n))) := by
    simp only [hsucc]; exact hτ.pow _
  have hfix : τ ^ (p ^ n) = τ := tendsto_nhds_unique h2 h1
  exact ⟨τ, mem_range_of_pow_eq hn hfix, hlim⟩

section Ring

variable {W : Type} [CommRing W] {n : ℕ}

theorem dvd_pow_iter (hW : ∀ x : W, (p : W) ∣ x ^ (p ^ n) - x) (N : ℕ) (x : W) :
    (p : W) ∣ x ^ ((p ^ n) ^ N) - x := by
  induction N with
  | zero => rw [pow_zero, pow_one, sub_self]; exact dvd_zero _
  | succ N ih =>
    have e : x ^ ((p ^ n) ^ (N + 1)) = (x ^ ((p ^ n) ^ N)) ^ (p ^ n) := by
      rw [← pow_mul x ((p ^ n) ^ N) (p ^ n), ← pow_succ]
    rw [e, show (x ^ ((p ^ n) ^ N)) ^ (p ^ n) - x =
      ((x ^ ((p ^ n) ^ N)) ^ (p ^ n) - x ^ ((p ^ n) ^ N)) + (x ^ ((p ^ n) ^ N) - x) by ring]
    exact dvd_add (hW _) ih

theorem dvd_pow_iter_succ (hn : 0 < n) (hW : ∀ x : W, (p : W) ∣ x ^ (p ^ n) - x) (M : ℕ) (x : W) :
    (p : W) ^ (M + 1) ∣ x ^ ((p ^ n) ^ (M + 1)) - x ^ ((p ^ n) ^ M) := by
  have h := dvd_sub_pow_of_dvd_sub (hW x) (n * M)
  have e1 : (x ^ (p ^ n)) ^ (p ^ (n * M)) = x ^ ((p ^ n) ^ (M + 1)) := by
    rw [← pow_mul, pow_succ, ← pow_mul, mul_comm]
  have e2 : x ^ (p ^ (n * M)) = x ^ ((p ^ n) ^ M) := by rw [← pow_mul]
  rw [e1, e2] at h
  exact (pow_dvd_pow _ (by have := Nat.le_mul_of_pos_left M hn; omega)).trans h

theorem norm_map_pow_mul (φ : W →+* ℂ_[p]) (hφ : ∀ x, ‖φ x‖ ≤ 1) (k : ℕ) (c : W) :
    ‖φ ((p : W) ^ k * c)‖ ≤ ((p : ℝ)⁻¹) ^ k := by
  rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow, Formalism.L2.G.Pend.norm_p_C]
  exact mul_le_of_le_one_right (pow_nonneg (Formalism.L2.G.Pend.r_nonneg p) k) (hφ c)

end Ring

end GlobalTheory.TeichImage

namespace GlobalTheory

theorem mem_range_wToC_of_pow_congr : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (W : Type) [CommRing W], 0 < n →
    (∀ x : W, (p : W) ∣ x ^ (p ^ n) - x) → IsAdicComplete (Ideal.span {(p : W)}) W →
    ∀ φ : W →+* ℂ_[p], (∀ x, ‖φ x‖ ≤ 1) → ∀ x, φ x ∈ Set.range (Formalism.L2.G.Pend.wToC p) := by
  intro p _ n W _ hn hW _ φ hφ x
  have hr0 : 0 ≤ ((p : ℝ)⁻¹) := Formalism.L2.G.Pend.r_nonneg p
  have key : ∀ k : ℕ, ∀ x : W, ∃ w, ‖φ x - Formalism.L2.G.Pend.wToC p w‖ ≤ ((p : ℝ)⁻¹) ^ k := by
    intro k
    induction k with
    | zero => intro x; exact ⟨0, by rw [map_zero, sub_zero, pow_zero]; exact hφ x⟩
    | succ k ih =>
      intro x
      obtain ⟨τ, ⟨wτ, hwτ⟩, hτ⟩ := TeichImage.exists_lim hn (φ x) (fun M => by
        obtain ⟨c, hc⟩ := TeichImage.dvd_pow_iter_succ hn hW M x
        rw [← map_pow, ← map_pow, ← map_sub, hc]
        exact TeichImage.norm_map_pow_mul φ hφ (M + 1) c)
      obtain ⟨c, hc⟩ := TeichImage.dvd_pow_iter hW k x
      obtain ⟨w₁, hw₁⟩ := ih (-c)
      refine ⟨wτ + (p : Formalism.L2.G.Pend.WW p) * w₁, ?_⟩
      have hx : x = x ^ ((p ^ n) ^ k) + (p : W) * (-c) := by linear_combination -hc
      have e : φ x - Formalism.L2.G.Pend.wToC p (wτ + (p : Formalism.L2.G.Pend.WW p) * w₁) =
          (φ x ^ ((p ^ n) ^ k) - τ) + (p : ℂ_[p]) * (φ (-c) - Formalism.L2.G.Pend.wToC p w₁) := by
        conv_lhs => rw [hx]
        rw [map_add (f := _), map_add (f := _), map_mul, map_mul, map_pow, map_natCast, map_natCast, hwτ]
        ring
      rw [e]
      refine Formalism.L2.G.Pend.nadd p ((hτ k)) ?_
      rw [norm_mul, Formalism.L2.G.Pend.norm_p_C, pow_succ']
      exact mul_le_mul_of_nonneg_left hw₁ hr0
  apply Formalism.L2.G.Pend.mem_range_of_closure p
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (Formalism.L2.G.Pend.r_lt_one p)
  obtain ⟨w, hw⟩ := key N x
  exact ⟨_, ⟨w, rfl⟩, by rw [dist_eq_norm]; exact lt_of_le_of_lt hw hN⟩

end GlobalTheory
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.natCard_left_kernel_matrices_eq_pow : ∀ (k : Type) [Field k] [Finite k] (m n j : ℕ) (A : Matrix (Fin n) (Fin n) k), Module.finrank k (LinearMap.range A.mulVecLin) + j = n → Nat.card {w : Matrix (Fin m) (Fin n) k // w * A = 0} = Nat.card k ^ (j * m) := by
  first | exact @GlobalTheory.natCard_matrices_mul_eq_zero | exact GlobalTheory.natCard_matrices_mul_eq_zero | (intros; apply GlobalTheory.natCard_matrices_mul_eq_zero <;> assumption)
end
