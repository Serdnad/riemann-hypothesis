module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.Bundle002
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle010
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.Bundle003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.Bundle003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.RationalPointsDense
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.LatticeClassesFiniteRefinement
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.EquivFunLinOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.GmapLeLocS
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.UJClassMassOfDeep
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField PI.UJClassFin PI.UnitaryGroupMassFormula.UJClassFin IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {M : ℕ}

theorem stabT (L : Set (Fin M → E)) {u k : ℕ} (hu : ∀ x ∈ L, ∀ i, IsIntegral ℤ ((u : F) • x i))
    (hk : ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((k : F) • e) ∈ L) {a : Af F} (ha : a ∈ intAf F)
    (Y : Matrix (Fin M) (Fin M) (Af F ⊗[F] E))
    (hY : ∀ i j, ∃ o ∈ Oh F E, (a ⊗ₜ[F] (1 : E)) * (Y - 1) i j = (u * k) • o)
    {y : Fin M → Af F ⊗[F] E} (hy : y ∈ latHat F E L) :
    (a ⊗ₜ[F] (1 : E)) • Y.mulVec y ∈ latHat F E L := by
  choose o ho hoe using hY
  have hYy : Y.mulVec y = y + (Y - 1).mulVec y := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  have e1 : (a ⊗ₜ[F] (1 : E)) • (Y - 1).mulVec y = k • fun i => ∑ j, o i j * (u • y j) := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, hoe i j]
    simp only [nsmul_eq_mul]
    push_cast
    ring
  rw [hYy, smul_add, e1]
  exact add_mem (latHat_smul L ha hy)
    (low_vec L hk fun i => AddSubgroup.sum_mem _ fun j _ => Oh_mul (ho i j) (up_Oh L hu hy j))

theorem locCmpT (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (L : Set (Fin M → E)) {k : ℕ} (hkpos : 0 < k)
    (hk : ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((k : F) • e) ∈ L)
    (T : Set (HeightOneSpectrum (𝓞 F))) (p : ℕ) (hp0 : p ≠ 0) (hp : p ≠ 1)
    (hpT : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ T → (p : 𝓞 F) ∉ w.asIdeal) (g1 g2 : HA (AF F) σ J)
    (hC : ∀ y ∈ latHat F E L, (evT T ⊗ₜ[F] (1 : E)) • (finMat σ J (g2⁻¹ * g1)).mulVec y ∈ latHat F E L)
    {x : Fin M → E} (hx : x ∈ abelian₂ σ J L g1) : ∃ m2 : ℕ, ¬ p ∣ m2 ∧ (m2 : E) • x ∈ abelian₂ σ J L g2 := by
  classical
  set z := (finMat σ J g2⁻¹).mulVec (vinc (F := F) x) with hz
  have hzC : (evT T ⊗ₜ[F] (1 : E)) • z ∈ latHat F E L := by
    have : z = (finMat σ J (g2⁻¹ * g1)).mulVec ((finMat σ J g1⁻¹).mulVec (vinc (F := F) x)) := by
      rw [Matrix.mulVec_mulVec, ← finMat_mul, mul_assoc, mul_inv_cancel, mul_one]
    rw [this]; exact hC _ hx
  have hden : ∃ m : ℕ, 0 < m ∧ m • z ∈ latHat F E L := by
    choose mf hmf hmO using fun i => den (F := F) (E := E) (z i)
    refine ⟨k * ∏ i, mf i, Nat.mul_pos hkpos (Finset.prod_pos fun i _ => hmf i), ?_⟩
    rw [mul_smul]
    apply low_vec L hk
    intro i
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem mf (Finset.mem_univ i)
    show (∏ i, mf i) • z i ∈ Oh F E
    rw [hq, mul_comm, mul_smul]
    exact AddSubgroup.nsmul_mem _ (hmO i) _
  obtain ⟨m, hm, hmz⟩ := hden
  obtain ⟨a, m2, hm2, hmeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' p hp
  refine ⟨m2, hm2, ?_⟩
  show (finMat σ J g2⁻¹).mulVec (vinc (F := F) ((m2 : E) • x)) ∈ latHat F E L
  have e2 : (finMat σ J g2⁻¹).mulVec (vinc (F := F) ((m2 : E) • x)) = m2 • z := by
    rw [Nat.cast_smul_eq_nsmul, hz]
    have : vinc (F := F) (m2 • x) = m2 • vinc (F := F) x := by funext i; simp [vinc]
    rw [this, Matrix.mulVec_smul]
  rw [e2]
  set c : Af F := (1 - evT T) * algebraMap F (Af F) ((algebraMap (𝓞 F) F ((p : 𝓞 F) ^ a))⁻¹) with hc
  have hcI : c ∈ intAf F := one_sub_evT_inv_int T ((p : 𝓞 F) ^ a)
    (fun w hw hpw => hpT w hw (w.isPrime.mem_of_pow_mem a hpw))
  have hpa : algebraMap (𝓞 F) F ((p : 𝓞 F) ^ a) ≠ 0 := by
    rw [map_pow, map_natCast]; exact pow_ne_zero _ (by exact_mod_cast hp0)
  have hA : algebraMap F (Af F) ((algebraMap (𝓞 F) F ((p : 𝓞 F) ^ a))⁻¹) * ((p : Af F) ^ a) = 1 := by
    rw [show ((p : Af F) ^ a) = algebraMap F (Af F) (algebraMap (𝓞 F) F ((p : 𝓞 F) ^ a)) by simp,
      ← map_mul, inv_mul_cancel₀ hpa, map_one]
  have hsc : (m2 : Af F) = m2 * evT T + c * (m : Af F) := by
    rw [hmeq, hc]; push_cast at hA ⊢
    linear_combination (-(1 - evT T) * (m2 : Af F)) * hA
  have e3 : m2 • z = m2 • ((evT T ⊗ₜ[F] (1 : E)) • z) + (c ⊗ₜ[F] (1 : E)) • (m • z) := by
    have hι := congrArg (Algebra.TensorProduct.includeLeftRingHom : Af F →+* Af F ⊗[F] E) hsc
    simp only [map_add (f := _), map_mul, map_natCast] at hι
    rw [← Nat.cast_smul_eq_nsmul (Af F ⊗[F] E) m2 z, ← Nat.cast_smul_eq_nsmul (Af F ⊗[F] E) m2,
      ← Nat.cast_smul_eq_nsmul (Af F ⊗[F] E) m z, smul_smul, smul_smul, ← add_smul]
    congr 1
  rw [e3]
  exact add_mem (AddSubgroup.nsmul_mem _ hzC _) (latHat_smul L hcI hmz)

theorem sigR_tmul_one (σ : E →ₐ[F] E) (e : Af F) :
    PI.UJClassFin.sigR (Af F) σ (e ⊗ₜ[F] (1 : E)) = e ⊗ₜ[F] (1 : E) := by
  simp [PI.UJClassFin.sigR]

theorem invSmall (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (hJ : J.det ≠ 0) {dI dJ : ℕ}
    (hdI : ∀ i j, IsIntegral ℤ ((dI : E) * J⁻¹ i j)) (hdJ : ∀ i j, IsIntegral ℤ ((dJ : E) * J i j))
    (e : Af F) (kk : HA (AF F) σ J) (N : ℕ)
    (h : ∀ i j, ∃ o ∈ Oh F E, (e ⊗ₜ[F] (1 : E)) * (finMat σ J kk⁻¹ - 1) i j = (dI * dJ * N) • o) :
    ∀ i j, ∃ o ∈ Oh F E, (e ⊗ₜ[F] (1 : E)) * (finMat σ J kk - 1) i j = N • o := by
  choose o ho hoe using h
  set U := finMat σ J kk with hUd
  set W := finMat σ J kk⁻¹ with hWd
  set JI := (J⁻¹).map (inclR (F := F) (Af F)) with hJId
  set JA := JR (F := F) (Af F) J with hJAd
  set sg := PI.UJClassFin.sigR (Af F) σ with hsg
  have hJI : JI * JA = 1 := by
    rw [hJId, hJAd, JR, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hJ), Matrix.map_one _ (map_zero _) (map_one _)]
  have hWU : W * U = 1 := by rw [hWd, hUd, ← finMat_mul, inv_mul_cancel, finMat_one]
  have hunit : PI.UJClassFin.cT sg W * JA * W = JA := finMat_unitary σ J kk⁻¹
  have hU : U = JI * PI.UJClassFin.cT sg W * JA := by
    calc U = JI * JA * U := by rw [hJI, Matrix.one_mul]
      _ = JI * (PI.UJClassFin.cT sg W * JA * W) * U := by rw [hunit]
      _ = JI * PI.UJClassFin.cT sg W * JA * (W * U) := by simp only [Matrix.mul_assoc]
      _ = JI * PI.UJClassFin.cT sg W * JA := by rw [hWU, Matrix.mul_one]
  have hcs : PI.UJClassFin.cT sg (W - 1) = PI.UJClassFin.cT sg W - 1 := by
    have h1 := PI.UJClassFin.cT_one (n := Fin M) sg
    unfold PI.UJClassFin.cT at h1 ⊢
    rw [Matrix.map_sub _ (map_sub _), Matrix.transpose_sub, h1]
  have hU1 : U - 1 = JI * PI.UJClassFin.cT sg (W - 1) * JA := by
    rw [hU, hcs, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hJI]
  have key : ∀ a b, (e ⊗ₜ[F] (1 : E)) * sg ((W - 1) b a) = (dI * dJ * N) • sg (o b a) := by
    intro a b
    calc (e ⊗ₜ[F] (1 : E)) * sg ((W - 1) b a) = sg (e ⊗ₜ[F] (1 : E)) * sg ((W - 1) b a) := by
          rw [hsg, sigR_tmul_one]
      _ = sg ((e ⊗ₜ[F] (1 : E)) * (W - 1) b a) := (map_mul _ _ _).symm
      _ = sg ((dI * dJ * N) • o b a) := by rw [hoe b a]
      _ = (dI * dJ * N) • sg (o b a) := map_nsmul _ _ _
  intro i j
  refine ⟨∑ a, ∑ b, inclR (F := F) (Af F) ((dI : E) * J⁻¹ i a) * sg (o b a) *
      inclR (F := F) (Af F) ((dJ : E) * J b j),
    AddSubgroup.sum_mem _ fun a _ => AddSubgroup.sum_mem _ fun b _ =>
      Oh_mul (Oh_mul (incl_mem_Oh (hdI i a)) (sigR_Oh σ (ho b a))) (incl_mem_Oh (hdJ b j)), ?_⟩
  rw [hU1]
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have hk := key a b
  have hX : PI.UJClassFin.cT sg (W - 1) a b = sg ((W - 1) b a) := rfl
  have hJI' : JI i a = inclR (F := F) (Af F) (J⁻¹ i a) := rfl
  have hJA' : JA b j = inclR (F := F) (Af F) (J b j) := rfl
  rw [hX, hJI', hJA', map_mul, map_mul, map_natCast, map_natCast]
  calc (e ⊗ₜ[F] (1 : E)) * (inclR (F := F) (Af F) (J⁻¹ i a) * sg ((W - 1) b a) * inclR (F := F) (Af F) (J b j))
      = inclR (F := F) (Af F) (J⁻¹ i a) * ((e ⊗ₜ[F] (1 : E)) * sg ((W - 1) b a)) *
          inclR (F := F) (Af F) (J b j) := by ring
    _ = _ := by
      rw [hk]
      simp only [nsmul_eq_mul]
      push_cast
      ring

end Loc

end PI.UnitaryGroupMassFormula.UJClassMass
end
end

section

open NumberField PI.UJClassFin PI.UnitaryGroupMassFormula.UJClassFin IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

section Apx

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem Psi_sigR (v : HeightOneSpectrum (𝓞 F)) (x : Af F ⊗[F] E) :
    Psi v (PI.UJClassFin.sigR (Af F) σ x) = PI.UnitaryApproxDefs.sigR σ (Fv F v) (Psi v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    have e1 : PI.UJClassFin.sigR (Af F) σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := by simp [PI.UJClassFin.sigR]
    rw [e1, Psi_tmul, Psi_tmul]
    simp [PI.UnitaryApproxDefs.sigR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem Psi_inclR (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    Psi v (inclR (F := F) (Af F) e) = PI.UnitaryApproxDefs.inclE (F := F) (Fv F v) e := by
  show Psi v ((1 : Af F) ⊗ₜ[F] e) = e ⊗ₜ[F] (1 : Fv F v)
  rw [Psi_tmul]; rfl

def finU (g : HA (AF F) σ J) : GL (Fin M) (Af F ⊗[F] E) :=
  ⟨finMat σ J g, finMat σ J g⁻¹, by rw [← finMat_mul, mul_inv_cancel, finMat_one],
    by rw [← finMat_mul, inv_mul_cancel, finMat_one]⟩

def gLoc (g : HA (AF F) σ J) (v : HeightOneSpectrum (𝓞 F)) : GL (Fin M) (E ⊗[F] Fv F v) :=
  Units.map ((Psi (E := E) v).toRingHom.mapMatrix : Matrix (Fin M) (Fin M) (Af F ⊗[F] E) →+*
    Matrix (Fin M) (Fin M) (E ⊗[F] Fv F v)).toMonoidHom (finU σ J g)

theorem gLoc_val (g : HA (AF F) σ J) (v : HeightOneSpectrum (𝓞 F)) :
    ((gLoc σ J g v : GL (Fin M) (E ⊗[F] Fv F v)) : Matrix (Fin M) (Fin M) (E ⊗[F] Fv F v)) =
      (finMat σ J g).map (Psi v) := rfl

theorem gLoc_mem (g : HA (AF F) σ J) (v : HeightOneSpectrum (𝓞 F)) :
    gLoc σ J g v ∈ PI.UnitaryApproxDefs.UPts σ J (Fv F v) := by
  show PI.UnitaryApproxDefs.cT (PI.UnitaryApproxDefs.sigR σ (Fv F v)) ((gLoc σ J g v : GL (Fin M) (E ⊗[F] Fv F v)) : Matrix (Fin M) (Fin M) _) *
      J.map (PI.UnitaryApproxDefs.inclE (F := F) (Fv F v)) * ((gLoc σ J g v : GL (Fin M) (E ⊗[F] Fv F v)) : Matrix (Fin M) (Fin M) _) =
    J.map (PI.UnitaryApproxDefs.inclE (F := F) (Fv F v))
  rw [gLoc_val]
  have hU := congrArg (fun X => X.map (Psi (E := E) v)) (finMat_unitary σ J g)
  beta_reduce at hU
  rw [mapAlg_mul, mapAlg_mul] at hU
  have hcT : ∀ X : Matrix (Fin M) (Fin M) (Af F ⊗[F] E),
      (PI.UJClassFin.cT (PI.UJClassFin.sigR (Af F) σ) X).map (Psi v) = PI.UnitaryApproxDefs.cT (PI.UnitaryApproxDefs.sigR σ (Fv F v)) (X.map (Psi v)) := by
    intro X; ext i j; simp [PI.UJClassFin.cT, PI.UnitaryApproxDefs.cT, Psi_sigR]
  have hJ : (JR (Af F) J).map (Psi (E := E) v) = J.map (PI.UnitaryApproxDefs.inclE (F := F) (Fv F v)) := by
    ext i j; simp [JR, Psi_inclR]
  rw [hcT, hJ] at hU
  exact hU

theorem approxT (hσσ : ∀ e, σ (σ e) = e) (hθ : ∃ θ, σ θ ≠ θ) (hH : PI.UnitaryApproxDefs.IsHerm (σ : E →+* E) J)
    (hdet : IsUnit J.det) (g : HA (AF F) σ J) (T : Finset (HeightOneSpectrum (𝓞 F))) (N0 : ℕ)
    (hN0 : 0 < N0) :
    ∃ γ : PI.UJClassFin.UJ (σ : E →+* E) J, ∀ i j, ∃ o ∈ Oh F E,
      (evT (T : Set (HeightOneSpectrum (𝓞 F))) ⊗ₜ[F] (1 : E)) *
        (finMat σ J g i j - inclR (F := F) (Af F) (((γ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) i j)) =
        N0 • o := by
  classical
  have hD : ((N0 : 𝓞 F)) ≠ 0 := by exact_mod_cast hN0.ne'
  obtain ⟨γ, hγ, hc⟩ := unitary_approximation_finite F E (Fin M) σ J hσσ hθ hH hdet T
    (fun w => gLoc σ J g w) (fun w _ => gLoc_mem σ J g w) (N0 : 𝓞 F) hD
  refine ⟨⟨γ, hγ⟩, fun i j => ?_⟩
  show ∃ o ∈ Oh F E, (evT (T : Set (HeightOneSpectrum (𝓞 F))) ⊗ₜ[F] (1 : E)) *
        (finMat σ J g i j - inclR (F := F) (Af F) ((γ : Matrix (Fin M) (Fin M) E) i j)) = N0 • o
  have hc' : ∀ w : T, ∃ s ∈ PI.UnitaryApproxDefs.tensInt (F := F) (Fv F w.1) (PI.UnitaryApproxDefs.intOE E) (w.1.adicCompletionIntegers F).toSubring,
      Psi w.1 (finMat σ J g i j) - PI.UnitaryApproxDefs.inclE (F := F) (Fv F w.1) ((γ : Matrix (Fin M) (Fin M) E) i j) =
        PI.UnitaryApproxDefs.inclE (F := F) (Fv F w.1) (algebraMap F E ((N0 : 𝓞 F) : F)) * s := fun w => hc w.1 w.2 i j
  choose s hs hse using hc'
  refine ⟨∑ w : T, (sgl w.1 1 ⊗ₜ[F] (1 : E)) * Phi w.1 (s w),
    AddSubgroup.sum_mem _ fun w _ => Oh_mul (tmul_mem_Oh (sgl_int _ (one_mem _)) isIntegral_one) (Phi_int _ (hs w)), ?_⟩
  rw [evT_eq_sum, TensorProduct.sum_tmul, Finset.sum_mul, ← Finset.sum_coe_sort T, Finset.smul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← Phi_Psi, map_sub, Psi_inclR, hse w, Phi_mul, Phi_inclE]
  have e0 : ((N0 : 𝓞 F) : F) = (N0 : F) := by simp
  have e1 : sgl w.1 1 ⊗ₜ[F] (algebraMap F E ((N0 : 𝓞 F) : F)) = N0 • (sgl w.1 1 ⊗ₜ[F] (1 : E)) := by
    rw [e0, show algebraMap F E (N0 : F) = (N0 : F) • (1 : E) by rw [Algebra.smul_def, mul_one],
      TensorProduct.tmul_smul, Nat.cast_smul_eq_nsmul]
  rw [e1, smul_mul_assoc]

end Apx

end PI.UnitaryGroupMassFormula.UJClassMass
end
end

section

open NumberField PI.UJClassMass Formalism.HermitianLatticesTheory PI.UnitaryGroupMassFormula.UJClassFin

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

section Lin

variable {E V : Type} [Field E] [AddCommGroup V] [Module E V] {M : ℕ}

theorem linOf_mul (b : Module.Basis (Fin M) E V) (u w : GL (Fin M) E) :
    linOf b (u * w) = linOf b u * linOf b w := by
  apply LinearEquiv.ext
  intro v
  apply b.equivFun.injective
  rw [equivFun_linOf, LinearEquiv.mul_apply, equivFun_linOf, equivFun_linOf, Units.val_mul,
    Matrix.mulVec_mulVec]

theorem linOf_one (b : Module.Basis (Fin M) E V) : linOf b (1 : GL (Fin M) E) = 1 := by
  apply LinearEquiv.ext
  intro v
  apply b.equivFun.injective
  rw [equivFun_linOf, Units.val_one, Matrix.one_mulVec]
  rfl

end Lin

theorem gmap_one {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] (X : Submodule (𝓞 E) V) : gmap (1 : V ≃ₗ[E] V) X = X := by
  ext v
  simp [gmap, Submodule.mem_map]

theorem lattices_close_locally : LatClose := by
  intro F E _ _ _ _ _ σ V _ _ _ _ _ M J b L0 hσσ hH hdet hL0 g hg
  classical
  obtain ⟨⟨c1, hc1, hup⟩, ⟨c2, hc2, hlow⟩⟩ := crdBounds F E V M b L0 hL0
  obtain ⟨u, hu, hu'⟩ := up_nat (crdOf b L0) ⟨c1, hc1, hup⟩
  obtain ⟨k, hk, hk'⟩ := low_nat (crdOf b L0) ⟨c2, hc2, hlow⟩
  obtain ⟨dJ, hdJ, hdJi⟩ := mat_den J
  obtain ⟨dI, hdI, hdIi⟩ := mat_den J⁻¹
  obtain ⟨dg, hdg, hdgi⟩ := mat_den ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)
  set Nn : ℕ := dg * dI * dJ * (u * k) with hNn
  have hNpos : 0 < Nn := by positivity
  refine ⟨(Nn : 𝓞 F), by exact_mod_cast hNpos.ne', fun D' hD' γ hγ S hS hcong => ?_⟩
  obtain ⟨c, rfl⟩ := hD'
  choose r hr y hy using hcong
  set R : 𝓞 E := ∏ q : Fin M × Fin M, r q.1 q.2 with hRd
  have hRS : R ∈ S := Submonoid.prod_mem _ fun q _ => hr q.1 q.2
  set cE : E := algebraMap F E ((c : 𝓞 F) : F) with hcE
  have hcEi : IsIntegral ℤ cE := c.isIntegral_coe.algebraMap
  have hz : ∀ i j, ∃ z : E, IsIntegral ℤ z ∧
      (R : E) * ((g : Matrix (Fin M) (Fin M) E) i j - (γ : Matrix (Fin M) (Fin M) E) i j) = (Nn : E) * cE * z := by
    intro i j
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem (fun q : Fin M × Fin M => r q.1 q.2) (Finset.mem_univ (i, j))
    refine ⟨(q : E) * (y i j : E), q.isIntegral_coe.mul (y i j).isIntegral_coe, ?_⟩
    have e1 : (R : E) = (r i j : E) * (q : E) := by rw [hRd, hq]; push_cast; rfl
    rw [e1, mul_comm (r i j : E) (q : E), mul_assoc, hy i j]
    have e2 : algebraMap F E (((Nn : 𝓞 F) * c : 𝓞 F) : F) = (Nn : E) * cE := by
      have e5 : (((Nn : 𝓞 F) * c : 𝓞 F) : F) = (Nn : F) * ((c : 𝓞 F) : F) := by push_cast; ring
      rw [e5, map_mul, map_natCast]
    rw [e2]; ring
  choose z hzi hze using hz
  set gi : Matrix (Fin M) (Fin M) E := ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) with hgi
  set K : GL (Fin M) E := g⁻¹ * γ with hKd
  set Km : Matrix (Fin M) (Fin M) E := (K : Matrix (Fin M) (Fin M) E) with hKm
  have hgig : gi * (g : Matrix (Fin M) (Fin M) E) = 1 := by
    rw [hgi, ← Units.val_mul, inv_mul_cancel, Units.val_one]

  set e0 : Fin M → Fin M → E := fun i j => -cE * ∑ l, ((dg : E) * gi i l) * z l j with he0d
  have he0i : ∀ i j, IsIntegral ℤ (e0 i j) := fun i j =>
    (hcEi.neg).mul (IsIntegral.sum _ fun l _ => (hdgi i l).mul (hzi l j))
  have hK1 : ∀ i j, (algebraMap (𝓞 E) E R) * (Km - 1) i j = ((u * k : ℕ) : E) * (((dI * dJ : ℕ) : E) * e0 i j) := by
    intro i j
    have eK : Km - 1 = gi * ((γ : Matrix (Fin M) (Fin M) E) - (g : Matrix (Fin M) (Fin M) E)) := by
      rw [hKm, hKd, Units.val_mul, Matrix.mul_sub, hgig]
    rw [eK, Matrix.mul_apply, Finset.mul_sum, he0d]
    simp only [Matrix.sub_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have := hze l j
    change (R : E) * (gi i l * ((γ : Matrix (Fin M) (Fin M) E) l j - (g : Matrix (Fin M) (Fin M) E) l j)) = _
    have e3 : (R : E) * (gi i l * ((γ : Matrix (Fin M) (Fin M) E) l j - (g : Matrix (Fin M) (Fin M) E) l j)) =
        -(gi i l * ((R : E) * ((g : Matrix (Fin M) (Fin M) E) l j - (γ : Matrix (Fin M) (Fin M) E) l j))) := by ring
    rw [e3, this, hNn]
    push_cast
    ring

  have hKu : K ∈ PI.UnitaryApproxDefs.UJ (σ : E →+* E) J := (PI.UnitaryApproxDefs.UJ (σ : E →+* E) J).mul_mem ((PI.UnitaryApproxDefs.UJ (σ : E →+* E) J).inv_mem hg) hγ
  have hKu' : PI.UnitaryApproxDefs.cT (σ : E →+* E) Km * J * Km = J := hKu
  have hJJ : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul _ hdet
  set KImage : Matrix (Fin M) (Fin M) E := ((K⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) with hKim
  have hKK : Km * KImage = 1 := by rw [hKm, hKim, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hKinv : KImage = J⁻¹ * PI.UnitaryApproxDefs.cT (σ : E →+* E) Km * J := by
    calc KImage = J⁻¹ * J * KImage := by rw [hJJ, Matrix.one_mul]
      _ = J⁻¹ * (PI.UnitaryApproxDefs.cT (σ : E →+* E) Km * J * Km) * KImage := by rw [hKu']
      _ = J⁻¹ * PI.UnitaryApproxDefs.cT (σ : E →+* E) Km * J * (Km * KImage) := by simp only [Matrix.mul_assoc]
      _ = J⁻¹ * PI.UnitaryApproxDefs.cT (σ : E →+* E) Km * J := by rw [hKK, Matrix.mul_one]
  have hcs : PI.UnitaryApproxDefs.cT (σ : E →+* E) (Km - 1) = PI.UnitaryApproxDefs.cT (σ : E →+* E) Km - 1 := by
    have h1 := PI.UnitaryApproxDefs.cT_one (n := Fin M) (σ : E →+* E)
    unfold PI.UnitaryApproxDefs.cT at h1 ⊢
    rw [Matrix.map_sub _ (map_sub _), Matrix.transpose_sub, h1]
  have hKi1 : KImage - 1 = J⁻¹ * PI.UnitaryApproxDefs.cT (σ : E →+* E) (Km - 1) * J := by
    rw [hKinv, hcs, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hJJ]
  have hR0 : σ (algebraMap (𝓞 E) E R) = algebraMap (𝓞 E) E R := hS R hRS
  have hK2 : ∀ i j, (algebraMap (𝓞 E) E R) * (KImage - 1) i j = ((u * k : ℕ) : E) *
      (∑ a, ∑ b', ((dI : E) * J⁻¹ i a) * σ (e0 b' a) * ((dJ : E) * J b' j)) := by
    intro i j
    rw [hKi1]
    simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b' _ => ?_
    have hσK : (algebraMap (𝓞 E) E R) * σ ((Km - 1) b' a) = ((u * k : ℕ) : E) * (((dI * dJ : ℕ) : E) * σ (e0 b' a)) := by
      rw [← hR0, ← map_mul, hK1 b' a, map_mul, map_mul, map_natCast, map_natCast]
    have hX : PI.UnitaryApproxDefs.cT (σ : E →+* E) (Km - 1) a b' = σ ((Km - 1) b' a) := rfl
    rw [hX]
    calc (algebraMap (𝓞 E) E R) * (J⁻¹ i a * σ ((Km - 1) b' a) * J b' j)
        = J⁻¹ i a * ((algebraMap (𝓞 E) E R) * σ ((Km - 1) b' a)) * J b' j := by ring
      _ = _ := by rw [hσK]; push_cast; ring

  have h1 : gmap (linOf b K) L0 ≤ locS S L0 := gmap_le_locS b L0 S K fun x hx =>
    ⟨R, hRS, glob_stab (F := F) b L0 hu' hk' Km R _ (fun i j => (isIntegral_natCast _).mul (he0i i j)) hK1 hx⟩
  have h2 : gmap (linOf b K⁻¹) L0 ≤ locS S L0 := gmap_le_locS b L0 S K⁻¹ fun x hx =>
    ⟨R, hRS, glob_stab (F := F) b L0 hu' hk' KImage R _ (fun i j => IsIntegral.sum _ fun a _ =>
      IsIntegral.sum _ fun b' _ => ((hdIi i a).mul (int_sigma (σ : E →+* E) (he0i b' a))).mul (hdJi b' j)) hK2 hx⟩
  have h3 : L0 ≤ locS S (gmap (linOf b K) L0) := by
    have e4 : gmap (linOf b K) (gmap (linOf b K⁻¹) L0) = L0 := by
      rw [← gmap_comp, ← linOf_mul, mul_inv_cancel, linOf_one, gmap_one]
    calc L0 = gmap (linOf b K) (gmap (linOf b K⁻¹) L0) := e4.symm
      _ ≤ gmap (linOf b K) (locS S L0) := Submodule.map_mono h2
      _ = locS S (gmap (linOf b K) L0) := gmap_locS _ S L0
  have hKeq : locS S (gmap (linOf b K) L0) = locS S L0 := locS_eq_of S h1 h3
  have hγK : γ = g * K := by rw [hKd, mul_inv_cancel_left]
  rw [hγK, linOf_mul, gmap_comp, ← gmap_locS, hKeq, gmap_locS]

end PI.UnitaryGroupMassFormula.UJClassMass
end
end
