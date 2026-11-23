module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1556
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1605
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1571
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionModuleStructure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1638
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1534
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1591
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1572
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1618
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1598
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1640
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

theorem _root_.GlobalTheory.T.quasiReflectionPair_truncation_mem_closure : (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ e₁ e₂ : Fin M → E, hE σ J e₁ e₂ = 0 → hE σ J e₁ e₁ ≠ 0 → hE σ J e₂ e₂ ≠ 0 → (∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J e₁ e₁ / hE σ J e₂ e₂)) = 0) → ∀ g ∈ SUAdelic σ J, (∀ v : Fin M → E, hE σ J e₁ v = 0 → hE σ J e₂ v = 0 → Matrix.mulVec ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) (fun i => inclR (AF F) (v i)) = (fun i => inclR (AF F) (v i))) → g ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h}) → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ (η : AF F) (hη : η * η = η) (x y z : Fin M → E) (u : E), u * σ u = 1 → hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → hE σ J z z ≠ 0 → (hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J x x / hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x))) = 0) → (hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J z z / hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z))) = 0) → ∃ p : Formalism.UG.UJ (σ : E →+* E) J, (p.1 : Matrix (Fin M) (Fin M) E) = GlobalTheory.SUAssemble.qr σ J x u * GlobalTheory.SUAssemble.qr σ J y (σ u) ∧ GlobalTheory.SUAssemble.trunc σ J η hη p ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} := by
  first | exact @GlobalTheory.SUPair.trunc_pair_mem | exact GlobalTheory.SUPair.trunc_pair_mem | (intros; apply GlobalTheory.SUPair.trunc_pair_mem <;> assumption)
end

section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf

theorem coeff_isIntV_eventually (p : ℕ) [Fact p.Prime] (G : HTGroup p) (f : Polynomial G.F) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)),
      ∀ i, IsIntV G v ((1 : Qv v) ⊗ₜ[ℚ] algebraMap G.F G.C (f.coeff i)) := by
  have h := Filter.eventually_all.2 fun i : Fin (f.natDegree + 1) =>
    GlobalTheory.OrbFinAfFixed.isIntV_one_tmul_eventually p G (algebraMap G.F G.C (f.coeff i))
  filter_upwards [h] with v hv i
  by_cases hi : i ≤ f.natDegree
  · exact hv ⟨i, Nat.lt_succ_of_le hi⟩
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.1 hi), map_zero, TensorProduct.tmul_zero]
    exact isIntV_zero G v

theorem split_eventually : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (γ : G.C), (minpoly G.F γ).natDegree = G.n → (minpoly G.F γ).Separable → ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∃ (K : Type) (_ : CommRing K) (R : Subring K) (Φ : Matrix (Fin G.n) (Fin G.n) K ≃+* Qv v ⊗[ℚ] G.C), Set.Finite {I : Ideal R | I.IsMaximal} ∧ (∀ a : Qv v ⊗[ℚ] G.C, IsIntV G v a ↔ ∀ i j, Φ.symm a i j ∈ R) ∧ ∃ Q : Polynomial R, Q.Separable ∧ Q.map R.subtype = (Φ.symm ((1 : Qv v) ⊗ₜ[ℚ] γ)).charpoly := by
  intro p _ G γ hdeg hsep
  obtain ⟨a, b, hab⟩ := hsep
  filter_upwards [intV_order_eventually p G, GlobalTheory.T.eventually_integral_matrix_units_at_places p G, coeff_isIntV_eventually p G (minpoly G.F γ),
    coeff_isIntV_eventually p G a, coeff_isIntV_eventually p G b] with v hO hEE hP ha hb
  obtain ⟨h1, hm, -⟩ := hO
  obtain ⟨E, hE, hE1, hEi⟩ := hEE
  obtain ⟨hinj, hcen, hdim⟩ := GlobalTheory.T.localTensorCenterInclusion_injective_central_finrank p G v
  obtain ⟨Φ, hΦ, hΦs⟩ := GlobalTheory.T.matrix_units_give_matrix_algebra_iso (Qv v) (Qv v ⊗[ℚ] G.F) (Qv v ⊗[ℚ] G.C) G.n (iotaF G v) hinj hcen hdim E hE hE1
  let φ0 : G.F →+* Qv v ⊗[ℚ] G.F :=
    (Algebra.TensorProduct.includeRight : G.F →ₐ[ℚ] Qv v ⊗[ℚ] G.F).toRingHom
  have hφ : ∀ x, iotaF G v (φ0 x) = (1 : Qv v) ⊗ₜ[ℚ] algebraMap G.F G.C x := fun x => rfl
  have hsub : ∀ f : Polynomial G.F, (∀ i, IsIntV G v ((1 : Qv v) ⊗ₜ[ℚ] algebraMap G.F G.C (f.coeff i))) →
      (↑(f.map φ0).coeffs : Set (Qv v ⊗[ℚ] G.F)) ⊆ (intF G v h1 hm : Set (Qv v ⊗[ℚ] G.F)) := by
    intro f hf c hc
    obtain ⟨i, -, rfl⟩ := Polynomial.mem_coeffs_iff.1 hc
    rw [Polynomial.coeff_map]
    show IsIntV G v (iotaF G v (φ0 (f.coeff i)))
    rw [hφ]; exact hf i
  have hsc : ∀ z : Qv v ⊗[ℚ] G.F,
      Φ (algebraMap (Qv v ⊗[ℚ] G.F) (Matrix (Fin G.n) (Fin G.n) (Qv v ⊗[ℚ] G.F)) z) = iotaF G v z := by
    intro z
    rw [hΦ, ← mul_one (iotaF G v z), ← hE1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp [Matrix.algebraMap_matrix_apply]
    · intro j _ hj; simp [Matrix.algebraMap_matrix_apply, Ne.symm hj]
    · simp
  refine ⟨Qv v ⊗[ℚ] G.F, inferInstance, intF G v h1 hm, Φ, GlobalTheory.T.integralLocalCenter_finite_maximal_ideals p G v h1 hm,
    fun x => ⟨fun hx i j => ?_, fun hx => ?_⟩, ?_⟩
  · show IsIntV G v (iotaF G v (Φ.symm x i j))
    rw [hΦs]
    exact isIntV_sum G v _ _ fun c _ => hm _ _ (hm _ _ (hEi c i) hx) (hEi j c)
  · rw [← Φ.apply_symm_apply x, hΦ]
    exact isIntV_sum G v _ _ fun i _ => isIntV_sum G v _ _ fun j _ => hm _ _ (hx i j) (hEi i j)
  · refine ⟨((minpoly G.F γ).map φ0).toSubring _ (hsub _ hP), ?_, ?_⟩
    · refine ⟨(a.map φ0).toSubring _ (hsub _ ha), (b.map φ0).toSubring _ (hsub _ hb), ?_⟩
      apply Polynomial.map_injective (intF G v h1 hm).subtype Subtype.val_injective
      rw [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_one,
        ← Polynomial.derivative_map, Polynomial.map_toSubring, Polynomial.map_toSubring, Polynomial.map_toSubring,
        Polynomial.derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add, hab,
        Polynomial.map_one]
    · rw [Polynomial.map_toSubring]
      have hmon : (minpoly G.F γ).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral γ)
      have hX : Φ (Φ.symm ((1 : Qv v) ⊗ₜ[ℚ] γ)) = (1 : Qv v) ⊗ₜ[ℚ] γ := Φ.apply_symm_apply _
      symm
      apply GlobalTheory.T.charpoly_eq_of_monic_aeval_powers_linearIndependent
      · exact hmon.map φ0
      · rw [hmon.natDegree_map, hdeg]
      · apply Φ.injective
        rw [map_zero, Polynomial.aeval_def]
        have h3 := Polynomial.hom_eval₂ ((minpoly G.F γ).map φ0)
          (algebraMap (Qv v ⊗[ℚ] G.F) (Matrix (Fin G.n) (Fin G.n) (Qv v ⊗[ℚ] G.F)))
          (Φ : Matrix (Fin G.n) (Fin G.n) (Qv v ⊗[ℚ] G.F) →+* Qv v ⊗[ℚ] G.C) (Φ.symm ((1 : Qv v) ⊗ₜ[ℚ] γ))
        rw [RingEquiv.coe_toRingHom] at h3
        rw [h3, hX, Polynomial.eval₂_map]
        have e : ((Φ : Matrix (Fin G.n) (Fin G.n) (Qv v ⊗[ℚ] G.F) →+* Qv v ⊗[ℚ] G.C).comp
            (algebraMap (Qv v ⊗[ℚ] G.F) _)).comp φ0 =
            (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] Qv v ⊗[ℚ] G.C).toRingHom.comp (algebraMap G.F G.C) := by
          ext x
          simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom]
          rw [hsc, hφ]; rfl
        rw [e]
        have h4 := Polynomial.hom_eval₂ (minpoly G.F γ) (algebraMap G.F G.C)
          (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] Qv v ⊗[ℚ] G.C).toRingHom γ
        have e2 : Polynomial.eval₂ (algebraMap G.F G.C) γ (minpoly G.F γ) = 0 := minpoly.aeval G.F γ
        rw [e2, map_zero] at h4
        exact h4.symm
      · rw [Fintype.linearIndependent_iff]
        intro g hg
        have := GlobalTheory.T.powers_linearIndependent_over_localTensorCenter p G γ hdeg v g (by
          have h2 := congrArg Φ hg

          rw [map_sum, map_zero] at h2
          rw [← h2]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Algebra.smul_def, map_mul, map_pow, hsc, hX, Algebra.TensorProduct.tmul_pow, one_pow])
        intro i; rw [this]; rfl

end GlobalTheory.OrbFinAf
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.psi_p_neighborhood_in_level_subgroup : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r₂ : Gr G 1), letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] G.C) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C); ∃ O : Set ((ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ), IsOpen O ∧ 1 ∈ O ∧ ∀ z ∈ O, r₂⁻¹ * psiP G z * r₂ ∈ KHT p G.m G.n 1 G.Fw := by
  first | (exact @GlobalTheory.TorCls.OpenP.openp) | (exact GlobalTheory.TorCls.OpenP.openp) | (intros; apply GlobalTheory.TorCls.OpenP.openp  <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CxUnfold.OrbitSumGen

variable {p : ℕ} [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ)
  (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (Kf : Subgroup G.GAf) (K' : Subgroup (Gr G 1))

theorem posV_ne_zero (z : PosV G v β) : z.1 ≠ 0 := by
  intro h
  have := z.2
  rw [h] at this
  simp at this

def lineOf (z : Fin G.n → ℂ) (hz : z ≠ 0) : PLv G v β := Projectivization.mk ℂ z hz

def pairOfDat (d : Dat G v β) : Ys G v β x t hx Kf K' :=
  (LeftCosets.mk _ _ d.1, lineOf G v β d.2.1 (posV_ne_zero G v β d.2))

variable {G v β}

theorem smul_line_mk (y : grp G β) (z : Fin G.n → ℂ) (hz : z ≠ 0) :
    y • lineOf G v β z hz =
      lineOf G v β ((toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z)
        (fun h => hz (toV_injective G v β y (by rw [Matrix.toLin'_apply, h, map_zero]))) := by
  change Projectivization.map _ _ (Projectivization.mk ℂ z hz) = _
  rw [Projectivization.map_mk]
  congr 1

theorem smul_line_eq_iff (y : grp G β) (z : Fin G.n → ℂ) (hz : z ≠ 0) :
    y • lineOf G v β z hz = lineOf G v β z hz ↔
      FixL G v β y z := by
  rw [smul_line_mk]
  change Projectivization.mk ℂ _ _ = Projectivization.mk ℂ _ _ ↔ _
  rw [Projectivization.mk_eq_mk_iff]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, by rw [← hu, Units.smul_def]⟩
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hz
      apply toV_injective G v β y
      rw [Matrix.toLin'_apply, hc, zero_smul, map_zero]
    exact ⟨Units.mk0 c hc0, by rw [Units.smul_def, Units.val_mk0, hc]⟩

theorem fixL_smul_iff (y : grp G β) (z : Fin G.n → ℂ) (c : ℂ) (hc : c ≠ 0) :
    FixL G v β y (c • z) ↔ FixL G v β y z := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    rw [Matrix.mulVec_smul, smul_smul] at he
    have := congrArg (fun w => c⁻¹ • w) he
    simp only [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    rw [this]
    congr 1
    field_simp
  · rintro ⟨e, he⟩
    exact ⟨e, by rw [Matrix.mulVec_smul, he, smul_comm]⟩

variable (G v β)

theorem same_iff_smul (a b : Dat G v β) :
    Same G v β x t hx Kf K' a b ↔ ∃ y : grp G β, y • pairOfDat G v β x t hx Kf K' a = pairOfDat G v β x t hx Kf K' b := by
  constructor
  · rintro ⟨y, k, c, hk1, hk2, hc, h1, h2⟩
    refine ⟨y, Prod.ext ?_ ?_⟩
    · change y • LeftCosets.mk _ _ a.1 = LeftCosets.mk _ _ b.1
      rw [LeftCosets.smul_mk, LeftCosets.mk_eq_mk, h1]
      change (((toAfF G β x t hx).prod (toP1 G β)) y * a.1)⁻¹ * (((toAfF G β x t hx).prod (toP1 G β)) y * a.1 * k) ∈ _
      rw [inv_mul_cancel_left]
      exact Subgroup.mem_prod.2 ⟨hk1, hk2⟩
    · change y • lineOf G v β a.2.1 _ = lineOf G v β b.2.1 _
      rw [smul_line_mk]
      change Projectivization.mk ℂ _ _ = Projectivization.mk ℂ _ _
      rw [Projectivization.mk_eq_mk_iff]
      refine ⟨(Units.mk0 c hc)⁻¹, ?_⟩
      rw [h2, Units.smul_def, smul_smul]
      simp [hc]
  · rintro ⟨y, hy⟩
    have h1 := congrArg Prod.fst hy
    have h2 := congrArg Prod.snd hy
    change y • LeftCosets.mk _ _ a.1 = LeftCosets.mk _ _ b.1 at h1
    change y • lineOf G v β a.2.1 _ = lineOf G v β b.2.1 _ at h2
    rw [LeftCosets.smul_mk, LeftCosets.mk_eq_mk] at h1
    rw [smul_line_mk] at h2
    change Projectivization.mk ℂ _ _ = Projectivization.mk ℂ _ _ at h2
    rw [Projectivization.mk_eq_mk_iff] at h2
    obtain ⟨u, hu⟩ := h2
    refine ⟨y, (((toAfF G β x t hx).prod (toP1 G β)) y * a.1)⁻¹ * b.1, ((u⁻¹ : ℂˣ) : ℂ),
      (Subgroup.mem_prod.1 h1).1, (Subgroup.mem_prod.1 h1).2, Units.ne_zero _, ?_, ?_⟩
    · exact (mul_inv_cancel_left _ _).symm
    · rw [← hu, Units.smul_def, smul_smul]
      simp

def ptsToOrbit : Pts G v β x t hx Kf K' → MulAction.orbitRel.Quotient (grp G β) (Ys G v β x t hx Kf K') :=
  Quot.lift (fun d => Quotient.mk (MulAction.orbitRel (grp G β) (Ys G v β x t hx Kf K')) (pairOfDat G v β x t hx Kf K' d))
    (fun a b h => by
      obtain ⟨y, hy⟩ := (same_iff_smul G v β x t hx Kf K' a b).1 h
      exact Quotient.sound ⟨y⁻¹, show y⁻¹ • _ = _ by rw [← hy, inv_smul_smul]⟩)

theorem ptsToOrbit_eq (q : Pts G v β x t hx Kf K') :
    ptsToOrbit G v β x t hx Kf K' q = Quotient.mk _ (pairOfDat G v β x t hx Kf K' (Quot.out q)) :=
  (congrArg (ptsToOrbit G v β x t hx Kf K') (Quot.out_eq q)).symm

theorem ptsToOrbit_injective : Function.Injective (ptsToOrbit G v β x t hx Kf K') := by
  intro q₁ q₂ h
  rw [ptsToOrbit_eq, ptsToOrbit_eq] at h
  obtain ⟨g, hg⟩ := Quotient.exact h
  rw [← Quot.out_eq q₁, ← Quot.out_eq q₂]
  exact (Quot.sound ((same_iff_smul G v β x t hx Kf K' _ _).2 ⟨g, hg⟩)).symm

theorem card_stab_eq (d : Dat G v β) :
    Nat.card (Stab G v β x t hx Kf K' d) =
      Nat.card (MulAction.stabilizer (grp G β) (pairOfDat G v β x t hx Kf K' d)) := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
  rw [MulAction.mem_stabilizer_iff, Prod.ext_iff]
  change _ ↔ y • LeftCosets.mk _ _ d.1 = LeftCosets.mk _ _ d.1 ∧
    y • lineOf G v β d.2.1 _ = lineOf G v β d.2.1 _
  rw [smul_line_eq_iff, ← MulAction.mem_stabilizer_iff, ← stab_eq_stabilizer]
  simp only [stab, Subgroup.mem_inf, Subgroup.mem_comap, LeftCosets.mem_map_conj, and_assoc]

theorem cxF_pairOfDat (wt : Polynomial G.F → ℂ) (f : G.GAf → ℂ) (hf : ∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g)
    (f' : Gr G 1 → ℂ) (hf' : ∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g) (d : Dat G v β) (y : grp G β) :
    cxF G v wt β x t hx Kf f K' f' (pairOfDat G v β x t hx Kf K' d) y =
      if FixL G v β y d.2.1 then
        f (d.1.1⁻¹ * toAfF G β x t hx y * d.1.1) * f' (d.1.2⁻¹ * toP1 G β y * d.1.2) *
          wt (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))
      else 0 := by
  obtain ⟨k, hk, e⟩ := LeftCosets.rep_mk (ι := (toAfF G β x t hx).prod (toP1 G β)) (K := Kf.prod K') d.1
  have hz := posV_ne_zero G v β d.2
  obtain ⟨u, hu⟩ : ∃ u : ℂˣ, u • d.2.1 = Projectivization.rep (lineOf G v β d.2.1 hz) :=
    (Projectivization.mk_eq_mk_iff ℂ _ _ (Projectivization.rep_nonzero _) hz).1
      (Projectivization.mk_rep (lineOf G v β d.2.1 hz))
  have hpos : 0 < (star (Projectivization.rep (lineOf G v β d.2.1 hz)) ⬝ᵥ
      (herm G v β *ᵥ Projectivization.rep (lineOf G v β d.2.1 hz))).re := by
    rw [← hu]
    have := (pos_iff_smul_toV p G v β 1 d.2.1 u u.ne_zero).1 d.2.2
    simpa [Units.smul_def] using this
  have hfix : FixL G v β y (Projectivization.rep (lineOf G v β d.2.1 hz)) ↔ FixL G v β y d.2.1 := by
    rw [← hu, Units.smul_def]
    exact fixL_smul_iff y _ _ u.ne_zero
  simp only [cxF, pairOfDat, hpos, hfix, true_and, e, Prod.fst_mul, Prod.snd_mul]
  split_ifs with hF
  · rw [Subgroup.mem_prod] at hk
    have e1 : (d.1.1 * k.1)⁻¹ * toAfF G β x t hx y * (d.1.1 * k.1) =
        k.1⁻¹ * (d.1.1⁻¹ * toAfF G β x t hx y * d.1.1) * k.1 := by group
    have e2 : (d.1.2 * k.2)⁻¹ * toP1 G β y * (d.1.2 * k.2) =
        k.2⁻¹ * (d.1.2⁻¹ * toP1 G β y * d.1.2) * k.2 := by group
    rw [e1, e2, hf _ hk.1, hf' _ hk.2]
  · rfl

end GlobalTheory.CxUnfold.OrbitSumGen

namespace GlobalTheory.CxUnfold.OrbitSumGen

end GlobalTheory.CxUnfold.OrbitSumGen
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.pairWeight_support_finite_of_finite_fixing : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ), (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g) → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), (∀ (h : G.GAf × Gr G 1) (z : Fin G.n → ℂ), 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re → Set.Finite {y : grp G β | FixL G v β y z ∧ f (h.1⁻¹ * toAfF G β x t hx y * h.1) * f' (h.2⁻¹ * toP1 G β y * h.2) ≠ 0}) → ∀ a : GlobalTheory.CxUnfold.Ys G v β x t hx Kf K', (Function.support (GlobalTheory.CxUnfold.cxF G v wt β x t hx Kf f K' f' a)).Finite := by
  first | (exact @GlobalTheory.CxUnfold.support_cxF_finite) | (exact GlobalTheory.CxUnfold.support_cxF_finite) | (intros; apply GlobalTheory.CxUnfold.support_cxF_finite <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CxUnfold

theorem cxF_smul_conj_gen : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F)
    (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ),
    (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ),
    (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g) → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t), ∀ (η : grp G β) (a : GlobalTheory.CxUnfold.Ys G v β x t hx Kf K') (y : grp G β),
    GlobalTheory.CxUnfold.cxF G v wt β x t hx Kf f K' f' (η • a) (η * y * η⁻¹) =
      GlobalTheory.CxUnfold.cxF G v wt β x t hx Kf f K' f' a y := by
  intro p _ G v wt Kf f hf K' f' hf' β x t hx η a y

  have ha1 : (η • a).1 = LeftCosets.mk ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K')
      (((toAfF G β x t hx).prod (toP1 G β)) η *
        LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1) := by
    show η • a.1 = _
    conv_lhs => rw [← LeftCosets.mk_rep a.1]
    rfl
  obtain ⟨k, hk, hrep⟩ := LeftCosets.rep_mk (ι := (toAfF G β x t hx).prod (toP1 G β))
    (K := Kf.prod K') (((toAfF G β x t hx).prod (toP1 G β)) η *
        LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1)
  rw [← ha1] at hrep
  rw [Subgroup.mem_prod] at hk
  have hF : f ((LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') (η • a).1).1⁻¹ *
        toAfF G β x t hx (η * y * η⁻¹) *
        (LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') (η • a).1).1) =
      f ((LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).1⁻¹ *
        toAfF G β x t hx y *
        (LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).1) := by
    rw [hrep, ← hf k.1 hk.1 ((LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).1⁻¹ *
        toAfF G β x t hx y *
        (LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).1)]
    congr 1
    simp only [Prod.fst_mul, MonoidHom.prod_apply, map_mul, map_inv]
    group
  have hF' : f' ((LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') (η • a).1).2⁻¹ *
        toP1 G β (η * y * η⁻¹) *
        (LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') (η • a).1).2) =
      f' ((LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).2⁻¹ *
        toP1 G β y *
        (LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).2) := by
    rw [hrep, ← hf' k.2 hk.2 ((LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).2⁻¹ *
        toP1 G β y *
        (LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).2)]
    congr 1
    simp only [Prod.snd_mul, MonoidHom.prod_apply, map_mul, map_inv]
    group

  have hM : minpoly G.F ((((η * y * η⁻¹ : grp G β) : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) =
      minpoly G.F ((((y : grp G β) : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) := by
    have e : ((((η * y * η⁻¹ : grp G β) : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) =
        (((η : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((((y : grp G β) : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) *
          ((((η : G.Cˣ × ℚˣ).1)⁻¹ : G.Cˣ) : G.C) := by
      simp [Units.val_mul]
    rw [e, minpoly_units_conj]

  obtain ⟨c, hc, hrepl⟩ := rep_smul G v β η a.2
  have hcond : (0 < (star (Projectivization.rep (((η • a).2 : PLv G v β) : Projectivization ℂ (Fin G.n → ℂ))) ⬝ᵥ
        (herm G v β *ᵥ Projectivization.rep (((η • a).2 : PLv G v β) : Projectivization ℂ (Fin G.n → ℂ)))).re ∧
      FixL G v β (η * y * η⁻¹)
        (Projectivization.rep (((η • a).2 : PLv G v β) : Projectivization ℂ (Fin G.n → ℂ)))) ↔
      (0 < (star (Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ))) ⬝ᵥ
        (herm G v β *ᵥ Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ)))).re ∧
      FixL G v β y (Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ)))) := by
    change (0 < (star (Projectivization.rep ((η • a.2 : PLv G v β) : Projectivization ℂ (Fin G.n → ℂ))) ⬝ᵥ
        (herm G v β *ᵥ Projectivization.rep ((η • a.2 : PLv G v β) : Projectivization ℂ (Fin G.n → ℂ)))).re ∧
      FixL G v β (η * y * η⁻¹)
        (Projectivization.rep ((η • a.2 : PLv G v β) : Projectivization ℂ (Fin G.n → ℂ)))) ↔ _
    rw [hrepl, fixL_smul_iff G v β _ _ c hc, ← fixL_conj_iff p G v β y η,
      ← pos_iff_smul_toV p G v β η _ c hc]
  unfold cxF
  by_cases hca : (0 < (star (Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ))) ⬝ᵥ
        (herm G v β *ᵥ Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ)))).re ∧
      FixL G v β y (Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ))))
  · rw [if_pos hca, if_pos (hcond.2 hca), hF, hF', hM]
  · rw [if_neg hca, if_neg (mt hcond.1 hca)]

end GlobalTheory.CxUnfold
end
end

section

open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate

theorem _root_.GlobalTheory.T.holomorphicDelOperatorAt_sum_smul_leibniz : ∀ {n : ℕ} {ι : Type} [Fintype ι] {v : ReciprocityTheory.L2DbarEstimates.V n} (g : ι → ReciprocityTheory.L2DbarEstimates.V n → ℂ) (Q : ι → ReciprocityTheory.L2DbarEstimates.V n → GlobalTheory.CxForm.Alt n), (∀ k, DifferentiableAt ℝ (g k) v) → (∀ k S, DifferentiableAt ℝ (fun w => (GlobalTheory.CxForm.bas n).repr (Q k w) S) v) → GlobalTheory.CxForm.delAt (fun w => ∑ k, g k w • Q k w) v = ∑ k, (GlobalTheory.CxForm.DelForm.dOne (g k) v * Q k v + g k v • GlobalTheory.CxForm.delAt (Q k) v) := by
  first | exact @GlobalTheory.CxForm.DelForm.delAt_sum_smul | exact GlobalTheory.CxForm.DelForm.delAt_sum_smul | (intros; apply GlobalTheory.CxForm.DelForm.delAt_sum_smul <;> assumption)
end

section

open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate

theorem _root_.GlobalTheory.T.holomorphicDifferentialOneForm_comp_holomorphic : ∀ {n : ℕ} {φ : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.L2DbarEstimates.V n} {c : ReciprocityTheory.L2DbarEstimates.V n → ℂ} {v : ReciprocityTheory.L2DbarEstimates.V n}, DifferentiableAt ℝ c (φ v) → DifferentiableAt ℂ φ v → GlobalTheory.CxForm.DelForm.dOne (fun w => c (φ w)) v = GlobalTheory.CxForm.pull (fderiv ℂ φ v) (GlobalTheory.CxForm.DelForm.dOne c (φ v)) := by
  first | exact @GlobalTheory.CxForm.DelForm.dOne_comp_holo | exact GlobalTheory.CxForm.DelForm.dOne_comp_holo | (intros; apply GlobalTheory.CxForm.DelForm.dOne_comp_holo <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.CtLevel

theorem blk_mul_dgM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E)
    (m k : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)),
    blk h w (k * m) X = dgM h w k * blk h w m X ∧
      blk h w (m * k) X = blk h w m (k.1.val * X * (k.2⁻¹).val) * dgM h w k := by
  intro E _ _ _ a b n h w m k X
  constructor
  · apply Units.ext
    rw [Units.val_mul, blk_val, blk_val, dgM_val, dgMat, reindex_apply, reindex_apply, reindex_apply,
      submatrix_mul_equiv, fromBlocks_multiply]
    simp [Prod.fst_mul, Prod.snd_mul, Units.val_mul, Matrix.mul_assoc]
  · apply Units.ext
    rw [Units.val_mul, blk_val, blk_val, dgM_val, dgMat, reindex_apply, reindex_apply, reindex_apply,
      submatrix_mul_equiv, fromBlocks_multiply]
    have hk : (k.2⁻¹).val * k.2.val = 1 := Units.inv_mul k.2
    simp [Prod.fst_mul, Prod.snd_mul, Units.val_mul, Matrix.mul_assoc, hk]

end GlobalTheory.BCT.CtLevel
end
