module

public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealSymplecticFormAlternatingInvariantDefinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle150
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasSign
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle168
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHeckeCharTrivOnRealSubfieldInfinityType
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle163
public import Development.AutomorphicArithmetic.WeightCongruences.IsRootOfIntegral
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FillPreservesIdempotent
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle216
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT NumberField Matrix
open scoped Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockIndep

section Mat

variable {m n : ℕ} {G B : Matrix (Fin n) (Fin n) ℂ} {H t B' : Matrix (Fin m) (Fin m) ℂ} {δ : Fin m → ℂ}

theorem trace_unitMap (hB : Bᴴ * G * B = 1) (hB' : B'ᴴ * H * B' = diagonal δ) (a c : Fin m) (b d : Fin n) :
    (G⁻¹ * (unitMap B B' c d)ᴴ * H * unitMap B B' a b).trace = if (a, b) = (c, d) then δ a else 0 := by
  have hu : IsUnit B.det := Matrix.isUnit_det_of_left_inverse hB
  have hG : G⁻¹ = B * Bᴴ := by
    apply Matrix.inv_eq_right_inv
    rw [← Matrix.mul_assoc]
    exact mul_eq_one_comm.1 (by rw [← Matrix.mul_assoc, hB])
  have h1 : Bᴴ * (B⁻¹)ᴴ = 1 := by rw [← conjTranspose_mul, Matrix.nonsing_inv_mul _ hu, conjTranspose_one]
  have e : G⁻¹ * (unitMap B B' c d)ᴴ * H * unitMap B B' a b =
      B * ((Bᴴ * (B⁻¹)ᴴ) * (Matrix.single c d (1 : ℂ))ᴴ * (B'ᴴ * H * B') * Matrix.single a b (1 : ℂ) * B⁻¹) := by
    simp only [hG, unitMap, conjTranspose_mul, Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, Matrix.nonsing_inv_mul_cancel_right _ _ hu, h1, hB', Matrix.one_mul,
    Matrix.conjTranspose_single, star_one, Matrix.single_mul_mul_single, Matrix.diagonal_apply]
  by_cases h : c = a
  · subst h
    by_cases h' : d = b
    · subst h'; simp
    · simp [Matrix.trace_single_eq_of_ne _ _ _ h', Ne.symm h']
  · simp [h, Ne.symm h]

theorem cplxO_unitMap (ht : t * B' = B' * diagonal δ) (a : Fin m) (b : Fin n) :
    cplxO 1 t (unitMap B B' a b) = (Complex.I * δ a) • unitMap B B' a b := by
  have e : diagonal δ * Matrix.single a b (1 : ℂ) = δ a • Matrix.single a b (1 : ℂ) := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply]
    split_ifs with h
    · rw [h.1, smul_eq_mul]
    · simp
  rw [cplxO, unitMap, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ht, Matrix.mul_assoc B', e,
    Matrix.mul_smul, Matrix.smul_mul, smul_smul]

end Mat

theorem pureTensorO_injective : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (S' : D.what₂.Tau → SPar) (M : DSModel T S') (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ), IsStdChar D ψ (-1) → IsInfFam θ → (∀ τ, IsCartanInv (gramAt D S τ) 1) → (∀ τ, IsONBasis (gramAt D S τ) 1 (BS τ) S.rank) → IsThetaFunO ψ S T f → f ≠ 0 → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 (cart M τ)) f) → Function.Injective (pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f) := by
  intro D ψ θ S T S' M BS f hψ hθ hS hBS hf f0 hv
  have hT := GlobalTheory.Chain.VacVec.cart_isCartanInv M
  have hB : ∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1 := fun τ => by
    obtain ⟨ε, h1, h2, -⟩ := hBS τ
    rw [h2, ← Matrix.diagonal_one]
    congr 1
    funext a
    rcases h1 a with h | h
    · rw [h.1, Complex.ofReal_one]
    · exact absurd a.2 (not_lt.2 h.2)
  have hu := fun τ => (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hB' : ∀ τ, (onb M τ)ᴴ * gramAt D T τ * onb M τ = diagonal fun a => if M.ε τ a then (1 : ℂ) else -1 := fun τ => by
    rw [← M.fr_gram τ, onb, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul,
      Matrix.mul_nonsing_inv _ (hu τ), conjTranspose_one, Matrix.one_mul,
      Matrix.mul_nonsing_inv_cancel_right _ _ (hu τ)]
    rfl
  have ht : ∀ τ, cart M τ * onb M τ = onb M τ * diagonal fun a => if M.ε τ a then (1 : ℂ) else -1 := fun τ => by
    rw [cart, onb, Matrix.mul_nonsing_inv_cancel_right _ _ (hu τ)]
    rfl
  unfold pureTensorO aPlusAll
  refine pure_injective (P := IsThetaFunO ψ S T)
    (B := fun k => annih (heisO ψ S T) θ k.1 (cplxO 1 (cart M k.1)) (unitMap (BS k.1) (onb M k.1) k.2.1 k.2.2))
    (c := fun k => (fockScale D k.1 : ℂ)⁻¹ * (-(4 * π * Complex.I) *
      (Complex.I * (-2 * (tauE D k.1 D.host.xi0).im : ℝ))))
    (fun _ _ => GlobalTheory.OrientedHeis.theta_add) (fun a _ => GlobalTheory.OrientedHeis.theta_smul a)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hf f0 ?_
  · exact fun _ _ h => aPlus_theta hψ hθ _ _ _ h
  · exact fun _ _ h => annih_theta hψ hθ _ _ _ h
  · exact fun i j _ h => aPlus_comm' (sS := fun _ => 1) hψ hθ i.1 _ hS hT j.1 _ h
  · exact fun _ _ _ h h' => aPlus_add hψ hθ _ _ _ h h'
  · exact fun _ a _ h => aPlus_smul hψ hθ _ _ _ a h
  · exact fun _ _ _ h h' => annih_add hψ hθ _ _ _ h h'
  · exact fun _ a _ h => annih_smul hψ hθ _ _ _ a h
  · rintro ⟨τ, a, b⟩ ⟨τ', c, d⟩ g hg
    refine (annih_aPlus (sS := fun _ => 1) hψ hθ τ _ hS hT τ' _ hg).trans ?_
    refine congrArg₂ (· + ·) rfl (congrArg (· • g) ?_)
    unfold omDir
    by_cases h : τ = τ'
    · subst h
      simp only [if_true, cplxO_unitMap (ht τ), Matrix.mul_smul, Matrix.trace_smul, trace_unitMap (hB τ) (hB' τ),
        Prod.mk.injEq, true_and]
      have hre := GlobalTheory.RealSymplForm.realPlace_imaginaryGenerator_re_eq_zero D τ
      split_ifs <;> simp [Complex.mul_re, hre]
    · simp [h]
  · intro i
    have him := xi_zero_im_pos D i.1
    have hn : 0 < ‖tauE D i.1 D.host.xi0‖ := norm_pos_iff.2 fun h => by simp [h] at him
    have hfs : 0 < fockScale D i.1 := by
      unfold fockScale
      have := Real.pi_pos
      positivity
    simp [hfs.ne', him.ne', Real.pi_ne_zero]
  · exact fun i => hv i.1 _

end GlobalTheory.FockIndep
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.BVal

open Formalism.L2.Host
open scoped nonZeroDivisors

section General

variable {L : Type} [Field L] [NumberField L]

theorem onId_mul (χ : HChar L) {I J : FractionalIdeal (𝓞 L)⁰ L} (hI : I ≠ 0) (hJ : J ≠ 0) :
    χ.onId (I * J) = χ.onId I * χ.onId J := by
  have hf : ∀ K : FractionalIdeal (𝓞 L)⁰ L,
      (Function.mulSupport fun v : HeightOneSpectrum (𝓞 L) => χ.val v ^ FractionalIdeal.count L v K).Finite := fun K => by
    refine (FractionalIdeal.finite_factors (K := L) K).subset fun v hv h => hv ?_
    have h' : FractionalIdeal.count L v K = 0 := h
    simp [h']
  unfold HChar.onId
  rw [← finprod_mul_distrib (hf I) (hf J)]
  refine finprod_congr fun v => ?_
  rw [FractionalIdeal.count_mul L v hI hJ, _root_.zpow_add]

theorem onId_one (χ : HChar L) : χ.onId 1 = 1 := by
  unfold HChar.onId
  simp [FractionalIdeal.count_one]

theorem onId_prime (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) :
    χ.onId (v.asIdeal : FractionalIdeal (𝓞 L)⁰ L) = χ.val v := by
  unfold HChar.onId
  rw [finprod_eq_single _ v fun w hw => by rw [FractionalIdeal.count_maximal_coprime L w hw.symm, zpow_zero],
    FractionalIdeal.count_self, zpow_one]

theorem mem_of_primes (χ : HChar L) (M : IntermediateField ℚ ℂ) (b : 𝓞 L)
    (h : ∀ v : HeightOneSpectrum (𝓞 L), b ∉ v.asIdeal →
      ((χ.val v : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ) ∈ M)
    (cc : Ideal (𝓞 L)) (h0 : cc ≠ ⊥) (h1 : cc ⊔ Ideal.span {b} = ⊤) :
    ((χ.onId (cc : FractionalIdeal (𝓞 L)⁰ L) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm cc : ℝ) : ℝ) : ℂ) ∈ M := by
  induction cc using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl h0
  | h₂ x hx =>
    obtain rfl : x = ⊤ := Ideal.isUnit_iff.1 hx
    simp [onId_one]
  | h₃ a p ha hp ih =>
    let v : HeightOneSpectrum (𝓞 L) := ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
    have hb : b ∉ v.asIdeal := fun hb => v.isPrime.ne_top
      (top_le_iff.1 (h1.ge.trans (sup_le Ideal.mul_le_left ((Ideal.span_singleton_le_iff_mem _).2 hb))))
    have ha1 : a ⊔ Ideal.span {b} = ⊤ := top_le_iff.1 (h1.ge.trans (sup_le_sup_right Ideal.mul_le_right _))
    have := mul_mem (h v hb) (ih ha ha1)
    rw [FractionalIdeal.coeIdeal_mul, onId_mul χ (FractionalIdeal.coeIdeal_ne_zero.2 hp.ne_zero)
      (FractionalIdeal.coeIdeal_ne_zero.2 ha), map_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _),
      show χ.onId (p : FractionalIdeal (𝓞 L)⁰ L) = χ.val v from onId_prime χ v]
    convert this using 1
    push_cast
    ring

theorem val_mul_sqrt (α β γ : HChar L) (v : HeightOneSpectrum (𝓞 L)) :
    (((α * β * γ⁻¹).val v : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ) =
      α.valTw 0 v * β.valTw 0 v * (γ.valTw (1 / 2) v)⁻¹ := by
  have e : (α * β * γ⁻¹).val v = α.val v * β.val v * (γ.val v)⁻¹ := rfl
  have e2 : ((Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ) = (Ideal.absNorm v.asIdeal : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast]
  rw [e, e2]
  simp only [HChar.valTw, Complex.cpow_neg, Complex.ofReal_zero, Complex.cpow_zero, inv_one, mul_one, mul_inv, inv_inv,
    Units.val_mul, Units.val_inv_eq_inv_val, mul_assoc]

end General

theorem exists_field_BIs : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m) (t : T0), ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ (M' : IntermediateField ℚ ℂ), M ≤ M' → ∀ bad : ℕ, D.host.g 0 * D.host.g 1 ∣ bad → (∀ PP ∈ R.Q t, ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → ∃ B : Ideal (𝓞 D.host.E) → M', BIs R i M'.val.toRingHom t bad B := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL i t
  obtain ⟨M₁, hM₁, -, -, hmu, heta, -⟩ := GlobalTheory.Mem.FrameVal.frame_values D.R D.host (eExp D)
    ⟨R.C.P, R.C.W, R.C.mu0, R.C.eta, R.C.chiPsi, R.C.del, R.C.del', R.C.isMu0, R.C.isEta, R.C.isChi, R.C.isDel, R.C.isDel'⟩
    fun j τ => (D.hc _).e_int j
  obtain ⟨M₂, hM₂, hxi⟩ := GlobalTheory.Mem.FrameVal.exists_of_order (hL.xi_fin t)
  refine ⟨M₁ ⊔ M₂, inferInstance, fun M' hM bad hg hQ => ?_⟩
  have key : ∀ v : HeightOneSpectrum (𝓞 D.host.E), ((bad : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal →
      (((R.C.mu0 i * R.xiH t * R.C.eta⁻¹).val v : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ) ∈ M' := by
    intro v hv
    have u1 : (R.C.mu0 i).UnrAt v := (R.C.isMu0 i).unr v fun k hk => hv (by
      have hk' : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal := hk
      have hd : D.host.g k ∣ bad := by
        refine dvd_trans ?_ hg
        fin_cases k
        · exact dvd_mul_right _ _
        · exact dvd_mul_left _ _
      obtain ⟨c, rfl⟩ := hd
      rw [Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ hk')
    have u2 : (R.xiH t).UnrAt v := by
      by_contra h
      rcases (hL.Q_ram t v).1 h with h | ⟨P', hP', h⟩
      · exact hv (hQ v h)
      · obtain ⟨c', hc', e⟩ := h _ (hQ P' hP')
        have e' : c' = (bad : 𝓞 D.host.E) := RingOfIntegers.ext (by
          rw [e]
          change star ((bad : 𝓞 D.host.E) : D.host.E) = ((bad : 𝓞 D.host.E) : D.host.E)
          rw [show ((bad : 𝓞 D.host.E) : D.host.E) = (bad : D.host.E) from
            map_natCast (algebraMap (𝓞 D.host.E) D.host.E) bad, star_natCast])
        exact hv (e' ▸ hc')
    obtain ⟨y1, hy1⟩ := hmu i v u1
    obtain ⟨y2, hy2⟩ := hxi v u2
    obtain ⟨y3, hy3⟩ := heta v (R.C.isEta.unr v)
    rw [val_mul_sqrt, ← hy1, ← hy2, ← hy3]
    exact mul_mem (mul_mem (hM (le_sup_left (b := M₂) y1.2)) (hM (le_sup_right (a := M₁) y2.2)))
      (inv_mem (hM (le_sup_left (b := M₂) y3.2)))
  classical
  refine ⟨fun cc => if h : cc ≠ ⊥ ∧ cc ⊔ Ideal.span {((bad : ℕ) : 𝓞 D.host.E)} = ⊤ then
    ⟨_, mem_of_primes _ M' _ key cc h.1 h.2⟩ else 0, fun cc h0 h1 => ?_⟩
  simp only [dif_pos (And.intro h0 h1)]
  rfl

end GlobalTheory.Mem.BVal
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.heckeDoubleCosetOperators_standardFacts : HeckeStdPlain := by
  first | exact @GlobalTheory.HeckeStdFacts.heckeStdPlain | exact GlobalTheory.HeckeStdFacts.heckeStdPlain | (intros; apply GlobalTheory.HeckeStdFacts.heckeStdPlain <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.ChiPsiExist


open Classical in
theorem exists_chiPsi : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), ∃ χ : _root_.Formalism.L2.Host.HChar H.E, _root_.Formalism.L2.Host.IsChiPsi H χ := by
  intro R H
  obtain ⟨c, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  obtain ⟨χ, hu, ht, hi, -, hunr, -⟩ :=
    GlobalTheory.Mem.Chr.AntiExist.exists_hecke_trivOn H.F H.E c (R.Psi) (_root_.Formalism.L2.Host.embPsi H) hcm (fun _ => -1) ∅ (fun _ => 1)
      (fun w hw => absurd hw (Finset.notMem_empty w))
      (by
        intro ζ hζ
        rw [Finset.prod_empty, mul_one]
        exact UpperTheory.Mu.prod_emb_zpow H (Equiv.refl _) hζ _)
  exact ⟨χ, hu, fun v => hunr v (Finset.notMem_empty v) (fun w hw => absurd hw (Finset.notMem_empty w)), ht, hi⟩

end GlobalTheory.Mem.ChiPsiExist
end

section

noncomputable section

namespace GlobalTheory.SemisimplificationExists

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem exists_semisimplification : ∀ {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k),
    ∃ ρ' : Γ →* GL (Fin a) k, IsSSRep ρ' ∧ ρ.ker ≤ ρ'.ker ∧
      ∀ g, (ρ' g : Matrix (Fin a) (Fin a) k).charpoly = (ρ g : Matrix (Fin a) (Fin a) k).charpoly :=
  fun ρ => GlobalTheory.RowPar.exists_ss ρ

end GlobalTheory.SemisimplificationExists
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial


theorem _root_.GlobalTheory.T.splits_completely_over_intermediate_of_splits_over_rat : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (p : ℕ), p.Prime →
    ((Ideal.span {(p : ℤ)}).primesOver (𝓞 L)).ncard = Module.finrank ℚ L →
      ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ 𝔭.asIdeal → (𝔭.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L := by
  first | exact @GlobalTheory.SplitTower.splits_completely_of_intermediate | exact GlobalTheory.SplitTower.splits_completely_of_intermediate | (intros; apply GlobalTheory.SplitTower.splits_completely_of_intermediate <;> assumption)
end
