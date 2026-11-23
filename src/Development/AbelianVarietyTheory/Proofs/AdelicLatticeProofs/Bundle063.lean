module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle021
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle044
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle029
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle062
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle045
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle009
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle010
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle020
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle055
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle032
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle054
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle004
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.AlmostIntegral
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem mul_entry_mem_subring {ι : Type} [Fintype ι] {R : Type} [CommRing R]
    (S : Subring R) (k l : Matrix ι ι R) (hk : ∀ i j, k i j ∈ S) (hl : ∀ i j, l i j ∈ S) :
    ∀ i j, (k * l) i j ∈ S := by
  intro i j
  rw [Matrix.mul_apply]
  exact S.sum_mem fun a _ => S.mul_mem (hk _ _) (hl _ _)

theorem cf_of_ss : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), IsQGroup Γ → SS Γ → AdelicPair R R₀ → CF Γ R R₀ := by
  intro ι _ _ Γ R _ _ R₀ hΓ hss hA
  classical
  obtain ⟨m, d, t, hfix, hstab, hcl⟩ := GlobalTheory.T.exists_tensor_stabiliser_closed_SL_orbit ι Γ hΓ hss
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_ratPoly_eval_eq_tensorPowerSumRightAction ι m d t
  obtain ⟨-, hmul, hadj, hdet⟩ := GlobalTheory.T.ratZariskiClosurePoints_isGroup ι Γ hΓ.toIsPre R
  obtain ⟨hrat, hratR⟩ := GlobalTheory.T.rat_mem_ratZariskiClosurePoints ι Γ
  obtain ⟨D, hD, hDt⟩ := (adelicPair_elementary R R₀ hA).2.1 (TIdx ι d) (fun k => algebraMap ℚ R (t k))
  obtain ⟨Z, hZ⟩ := GlobalTheory.T.finite_integral_classes_closedOrbit ι m d t hcl D hD
  have hone : ∀ (S : Type) [CommRing S] (s : TIdx ι d → S), act d s 1 = s :=
    fun S _ s => ((tpow_act_algebra ι S).2 m d s).1
  have hact : ∀ (S : Type) [CommRing S] (s : TIdx ι d → S) (y z : Matrix ι ι S),
      act d s (y * z) = act d (act d s y) z :=
    fun S _ s => ((tpow_act_algebra ι S).2 m d s).2.1
  have hmap : ∀ (S : Type) [CommRing S] [Algebra ℚ S] (s : TIdx ι d → ℚ) (y : Matrix ι ι ℚ),
      act d (fun k => algebraMap ℚ S (s k)) (y.map (algebraMap ℚ S)) = fun k => algebraMap ℚ S (act d s y k) :=
    fun S _ _ s y => ((tpow_act_algebra ι ℚ).2 m d s).2.2.2.2.2 S (algebraMap ℚ S) y

  have hfixR : ∀ x ∈ pts Γ R, act d (fun k => algebraMap ℚ R (t k)) x = fun k => algebraMap ℚ R (t k) := by
    intro x hx
    funext k
    have hv : Φ k - MvPolynomial.C (t k) ∈ vanI Γ := by
      intro g hg
      have h1 := hΦ ℂ g k
      have h2 := congrFun (hfix g hg) k
      simp only [ev, map_sub, MvPolynomial.aeval_C] at h1 ⊢
      rw [h1, sub_eq_zero]
      exact h2
    have h3 := hx _ hv
    have h1 := hΦ R x k
    simp only [ev, map_sub, MvPolynomial.aeval_C] at h1 h3
    rw [← h1]
    exact sub_eq_zero.1 h3
  let P : (TIdx ι d → ℚ) → Matrix ι ι ℚ × Matrix ι ι R → Prop := fun z p =>
    p.1.det = 1 ∧ p.2.det = 1 ∧ (∀ i j, p.2 i j ∈ R₀) ∧ p.1.map (algebraMap ℚ R) * p.2 ∈ pts Γ R ∧
      act d t p.1 = z
  have key : ∀ x ∈ pts Γ R, ∃ z ∈ Z, ∃ p, P z p ∧ x = p.1.map (algebraMap ℚ R) * p.2 := by
    intro x hx
    obtain ⟨h, k, hh, hk, hkint, rfl⟩ := GlobalTheory.T.specialLinear_classNumber_one_adelic ι R R₀ hA x (hdet x hx)
    have hkk : k * k.adjugate = 1 := by rw [Matrix.mul_adjugate, hk, one_smul]
    have e1 : act d (fun k => algebraMap ℚ R (t k)) k.adjugate = fun k => algebraMap ℚ R (act d t h k) := by
      rw [← hmap]
      conv_lhs => rw [← hfixR _ hx, ← hact, Matrix.mul_assoc, hkk, Matrix.mul_one]
    have e2 : ∀ j, ∃ z : ℤ, (D : ℚ) * act d t h j = z := by
      intro j
      apply hA.int_of_mem
      have h1 := ((tpow_act_algebra ι R).2 m d ((D : R) • fun k => algebraMap ℚ R (t k))).2.2.2.1 R₀
        k.adjugate (fun k => hDt k) (adjugate_entry_mem_subring R₀ k hkint) j
      rw [((tpow_act_algebra ι R).2 m d (fun k => algebraMap ℚ R (t k))).2.2.2.2.1, e1] at h1
      rw [map_mul, map_natCast]
      exact h1
    obtain ⟨γ, hγ, hγZ⟩ := hZ h hh e2
    have hγγ : γ * γ.adjugate = 1 := by rw [Matrix.mul_adjugate, hγ, one_smul]
    have hγR : (γ.map (Int.cast : ℤ → ℚ)).map (algebraMap ℚ R) * γ.adjugate.map (Int.castRingHom R) = 1 := by
      have : (γ.map (Int.cast : ℤ → ℚ)).map (algebraMap ℚ R) = γ.map (Int.castRingHom R) := by
        ext i j; simp
      rw [this, ← Matrix.map_mul, hγγ, Matrix.map_one _ (map_zero _) (map_one _)]
    have e3 : (h * γ.map (Int.cast : ℤ → ℚ)).map (algebraMap ℚ R) * (γ.adjugate.map (Int.castRingHom R) * k)
        = h.map (algebraMap ℚ R) * k := by
      rw [Matrix.map_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ k, hγR, Matrix.one_mul]
    refine ⟨_, hγZ, (h * γ.map (Int.cast : ℤ → ℚ), γ.adjugate.map (Int.castRingHom R) * k),
      ⟨?_, ?_, ?_, ?_, rfl⟩, e3.symm⟩
    · have : (γ.map (Int.cast : ℤ → ℚ)).det = 1 := by
        have h1 := (Int.castRingHom ℚ).map_det γ
        rw [hγ, map_one] at h1
        exact h1.symm
      simp only [Matrix.det_mul, hh, this, one_mul]
    · have : (γ.adjugate.map (Int.castRingHom R)).det = 1 := by
        have h1 := (Int.castRingHom R).map_det γ.adjugate
        rw [Matrix.det_adjugate, hγ, one_pow, map_one] at h1
        exact h1.symm
      simp only [Matrix.det_mul, hk, this, one_mul]
    · exact mul_entry_mem_subring R₀ _ _ (fun i j => intCast_mem R₀ _) hkint
    · simp only
      rw [e3]; exact hx
  let c : (TIdx ι d → ℚ) → Matrix ι ι ℚ × Matrix ι ι R := fun z =>
    if hz : ∃ p, P z p then hz.choose else (1, 1)
  have hc : ∀ z, (∃ p, P z p) → P z (c z) := by
    intro z hz
    simp only [c, dif_pos hz]
    exact hz.choose_spec
  refine ⟨(Z.filter fun z => ∃ p, P z p).image fun z => (c z).1.map (algebraMap ℚ R) * (c z).2, ?_, ?_⟩
  · intro s hs
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hs
    exact (hc z (Finset.mem_filter.1 hz).2).2.2.2.1
  · intro x hx
    obtain ⟨z, hz, ⟨h, k⟩, hp, rfl⟩ := key x hx
    have hz' : z ∈ Z.filter fun z => ∃ p, P z p := Finset.mem_filter.2 ⟨hz, _, hp⟩
    have hq := hc z ⟨_, hp⟩
    have hs := Finset.mem_image_of_mem (fun z => (c z).1.map (algebraMap ℚ R) * (c z).2) hz'
    generalize (Z.filter fun z => ∃ p, P z p).image (fun z => (c z).1.map (algebraMap ℚ R) * (c z).2) = T at hs ⊢
    generalize c z = q at hq hs
    obtain ⟨h', k'⟩ := q
    obtain ⟨hh, hk, hkint, hxx, hhz⟩ := hp
    obtain ⟨hh', hk', hkint', hxx', hhz'⟩ := hq
    simp only at hh hk hkint hxx hhz hh' hk' hkint' hxx' hhz' hs ⊢
    have a1 : h' * h'.adjugate = 1 := by rw [Matrix.mul_adjugate, hh', one_smul]
    have a2 : h'.adjugate * h' = 1 := by rw [Matrix.adjugate_mul, hh', one_smul]
    have a3 : k' * k'.adjugate = 1 := by rw [Matrix.mul_adjugate, hk', one_smul]
    have g1 : act d t (h * h'.adjugate) = t := by
      rw [hact, hhz, ← hhz', ← hact, a1, hone]
    have g2 : h * h'.adjugate ∈ pts Γ ℚ := by
      apply hrat
      apply hstab
      · have h1 := (algebraMap ℚ ℂ).map_det (h * h'.adjugate)
        rw [Matrix.det_mul, Matrix.det_adjugate, hh, hh', one_pow, one_mul, map_one] at h1
        exact h1.symm
      · have h1 := hmap ℂ t (h * h'.adjugate)
        rw [g1] at h1
        exact h1
    have g3 := hratR R _ g2
    have e : h.map (algebraMap ℚ R) * k = (h * h'.adjugate).map (algebraMap ℚ R) *
        (h'.map (algebraMap ℚ R) * k') * (k'.adjugate * k) := by
      rw [← Matrix.mul_assoc _ _ k', ← Matrix.map_mul, Matrix.mul_assoc h, a2, Matrix.mul_one,
        Matrix.mul_assoc, ← Matrix.mul_assoc k', a3, Matrix.one_mul]
    refine ⟨_, g2, _, hs, k'.adjugate * k, ?_,
      mul_entry_mem_subring R₀ _ _ (adjugate_entry_mem_subring R₀ k' hkint') hkint, e⟩
    have g4 := hmul _ g3 _ hxx'
    have g5 := hmul _ (hadj _ g4) _ hxx
    rw [e, ← Matrix.mul_assoc, Matrix.adjugate_mul, hdet _ g4, one_smul, Matrix.one_mul] at g5
    exact g5

end GlobalTheory.ClassFin
end

section

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_unitary_correction_congruent_one_at_level : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (γ₀ : GL (Fin n) E) (N D : ℕ), IsUnE c G γ₀.1 → 0 < N → 0 < D → ∃ γ : GL (Fin n) E, IsUnE c G γ.1 ∧ CongAt L N D (γ * γ₀⁻¹).1 ∧ ∃ s : 𝓞 E, SplitOr c N s ∧ ∀ v ∈ L, s • (γ.1 *ᵥ v) ∈ L ∧ s • ((γ⁻¹).1 *ᵥ v) ∈ L := by
  first | exact @GlobalTheory.UnRep.Correct.exists_unitary_correction | exact GlobalTheory.UnRep.Correct.exists_unitary_correction | (intros; apply GlobalTheory.UnRep.Correct.exists_unitary_correction <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem relIndex_sup_zpowers_chooseT (p : ℕ) {G : Type} [CommGroup G] (Q : Subgroup G) (d : G)
    (hp : p.Prime) (hd : d ^ p ∈ Q) (hn : d ∉ Q) :
    Q.relIndex (Q ⊔ Subgroup.zpowers d) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Subgroup.relIndex_sup_left]
  have h := Subgroup.relIndex_ker (Subgroup.zpowers d) (QuotientGroup.mk' Q)
  rw [QuotientGroup.ker_mk', MonoidHom.map_zpowers, Nat.card_zpowers] at h
  rw [h]
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).2 hd
  · exact fun e => hn ((QuotientGroup.eq_one_iff _).1 e)

theorem mem_pows_sUnits_chooseT (p : ℕ) (hp : p ≠ 0) (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (x : Fˣ) (hx : x ∈ sUnits F S) (r : F)
    (hr : r ^ p = (x : F)) : x ∈ pows p (sUnits F S) := by
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact x.ne_zero (by rw [← hr, zero_pow hp])
  refine ⟨Units.mk0 r hr0, ?_, ?_⟩
  · rw [SetLike.mem_coe, mem_sUnits]
    intro v hv
    have h := (mem_sUnits F S x).1 hx v hv
    rw [← hr, map_pow] at h
    exact (pow_eq_one_iff_of_nonneg zero_le hp).1 h
  · ext
    simp [hr]

theorem exists_auxiliary_places_prime : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (ζ : F) (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → AdmP p F S → δ ∈ sUnits F S → (∀ r : F, r ^ p ≠ (δ : F)) → ∃ T : Finset (HeightOneSpectrum (𝓞 F)), Disjoint S T ∧ T.card + 1 = S.card + Fintype.card (InfinitePlace F) ∧ (∀ v ∈ T, ∃ r : v.adicCompletion F, r ^ p = algebraMap F (v.adicCompletion F) (δ : F)) ∧ ∀ v ∈ T, ∃ u ∈ sUnits F S, u ∉ powSub p (algebraMap F (v.adicCompletion F)) ∧ ∀ v' ∈ T, v' ≠ v → u ∈ powSub p (algebraMap F (v'.adicCompletion F)) := by
  intro p F _ _ _ ζ δ S hp hζ hS hδ hns
  classical
  have hQU : pows p (sUnits F S) ≤ sUnits F S := by
    rintro _ ⟨y, hy, rfl⟩
    exact (sUnits F S).pow_mem hy p
  have hdd : δ ^ p ∈ pows p (sUnits F S) := ⟨δ, hδ, rfl⟩
  have hdn : δ ∉ pows p (sUnits F S) := by
    rintro ⟨y, -, hy⟩
    exact hns (y : F) (by rw [← hy]; simp)
  have hHU : pows p (sUnits F S) ⊔ Subgroup.zpowers δ ≤ sUnits F S :=
    sup_le hQU ((Subgroup.zpowers_le).2 hδ)
  have hpos : 0 < Fintype.card (InfinitePlace F) := Fintype.card_pos
  obtain ⟨m, hm⟩ : ∃ m, m + 1 = S.card + Fintype.card (InfinitePlace F) :=
    ⟨S.card + Fintype.card (InfinitePlace F) - 1, by omega⟩
  have hidx : (pows p (sUnits F S) ⊔ Subgroup.zpowers δ).relIndex (sUnits F S) = p ^ m := by
    have h := Subgroup.relIndex_mul_relIndex _ _ _ le_sup_left hHU
    have h2 : (pows p (sUnits F S)).relIndex (sUnits F S) = _ :=
      (pTor_pIdx_sUnits p F ζ S hp hζ).2
    rw [relIndex_sup_zpowers_chooseT p _ _ hp hdd hdn, h2, ← hm, pow_succ'] at h
    exact Nat.eq_of_mul_eq_mul_left hp.pos h
  have hval : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : F),
      Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x := fun v x =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  have hpw : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ),
      x ^ p ∈ powSub p (algebraMap F (v.adicCompletion F)) := fun v x =>
    ⟨algebraMap F (v.adicCompletion F) x, by rw [Units.val_pow_eq_pow_val, map_pow]⟩
  obtain ⟨T, hT, hgood, hA⟩ := exists_indep_prime_index p Fˣ (HeightOneSpectrum (𝓞 F)) (sUnits F S)
    (pows p (sUnits F S) ⊔ Subgroup.zpowers δ)
    (fun v => powSub p (algebraMap F (v.adicCompletion F)))
    (fun v => v ∉ S ∧ ∃ r : v.adicCompletion F,
      r ^ p = algebraMap F (v.adicCompletion F) (δ : F)) m hp hidx
    (by
      rintro v ⟨-, hv⟩
      refine le_trans inf_le_right (sup_le ?_ ((Subgroup.zpowers_le).2 hv))
      rintro _ ⟨y, -, rfl⟩
      exact hpw v y)
    (fun v _ x _ => hpw v x)
    (by
      rintro v ⟨hv, -⟩ x hx hx' y hy
      obtain ⟨k, r, hr⟩ := GlobalTheory.T.exists_eq_pow_mul_pth_pow_adicCompletion_unit p F v (algebraMap F (v.adicCompletion F) x)
        (algebraMap F (v.adicCompletion F) y) hp (hS.2 v hv)
        (by rw [hval]; exact (mem_sUnits F S x).1 hx v hv)
        (by rw [hval]; exact (mem_sUnits F S y).1 hy v hv)
        (fun r hr => hx' ⟨r, hr⟩)
      refine ⟨k, r, ?_⟩
      have hx0 : algebraMap F (v.adicCompletion F) x ≠ 0 := by simp
      rw [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, map_div₀, map_pow, hr]
      field_simp)
    (by
      intro x hx hxH
      obtain ⟨v, h1, h2, h3⟩ := GlobalTheory.T.exists_place_pow_and_not_pow' p F ζ δ x S hp hζ δ.ne_zero x.ne_zero hns
        (fun k r h => hxH (by
          have h4 : x / δ ^ k ∈ pows p (sUnits F S) := by
            refine mem_pows_sUnits_chooseT p hp.ne_zero F S _
              ((sUnits F S).div_mem hx ((sUnits F S).pow_mem hδ k)) r ?_
            have hδ0 := δ.ne_zero
            rw [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, h]
            field_simp
          have h5 := Subgroup.mul_mem_sup h4 (Subgroup.pow_mem _ (Subgroup.mem_zpowers δ) k)
          rwa [div_mul_cancel] at h5))
      exact ⟨v, ⟨h1, h2⟩, fun ⟨r, hr⟩ => h3 r hr⟩)
  refine ⟨T, ?_, by rw [hT, hm], fun v hv => (hgood v hv).2, hA⟩
  rw [Finset.disjoint_right]
  exact fun v hv => (hgood v hv).1

end GlobalTheory.CNorm
end

section

namespace GlobalTheory.AdIdem

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct nonZeroDivisors

section

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_nat_mul_integral (y : E) :
    ∃ d : ℕ, 0 < d ∧ (d : E) * y ∈ Set.range (algebraMap (𝓞 E) E) := by
  have hy : IsAlgebraic ℤ y :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic y)
  obtain ⟨m, hm, h⟩ := hy.exists_integral_multiple
  refine ⟨(m * m).toNat, ?_, ?_⟩
  · have := mul_self_pos.2 hm
    omega
  · have h2 : (((m * m).toNat : ℕ) : E) = (m : E) * m := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (mul_self_nonneg m), Int.cast_mul]
    have h3 : IsIntegral ℤ ((m : E) * (m • y)) :=
      IsIntegral.mul (by simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := m)) h
    refine ⟨⟨_, h3⟩, ?_⟩
    rw [h2, mul_assoc, ← zsmul_eq_mul y m]
    rfl

omit [NumberField E] in
theorem mul_mem_hat {x y : RA F E} (hx : x ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)))
    (hy : y ∈ hat1 F (Set.range (algebraMap (𝓞 E) E))) :
    x * y ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)) := by
  refine mul_mem_adelicCompletionOfElementSet_of_mul_mem F ?_ hx hy
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  exact ⟨a * b, map_mul _ _ _⟩

theorem exists_eq_one_tmul_add (z : RA F E) :
    ∃ (x : E), ∃ h ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)),
      z = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x + h := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | tmul a y =>
    obtain ⟨d, hd, hy⟩ := exists_nat_mul_integral E y
    obtain ⟨x, b, hb, rfl⟩ := exists_eq_algebraMap_add_nsmul F d hd a
    refine ⟨x • y, b ⊗ₜ[F] ((d : E) * y), tmul_mem_adelicCompletion_of_integral F hb hy, ?_⟩
    rw [TensorProduct.add_tmul, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
      ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F,
      TensorProduct.smul_tmul]
  | add u v hu hv =>
    obtain ⟨x, h, hh, rfl⟩ := hu
    obtain ⟨x', h', hh', rfl⟩ := hv
    refine ⟨x + x', h + h', add_mem hh hh', ?_⟩
    rw [TensorProduct.tmul_add]
    abel

theorem mem_range_of_one_tmul_mem {x : E}
    (hx : (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x ∈ hat1 F (Set.range (algebraMap (𝓞 E) E))) :
    x ∈ Set.range (algebraMap (𝓞 E) E) := by
  have h : ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E) = Set.range (algebraMap (𝓞 E) E) := by
    ext y
    exact FractionalIdeal.mem_one_iff _
  rw [← h] at hx ⊢
  exact (one_tmul_mem_adelicCompletion_fractionalIdeal_iff F 1 x).1 hx

theorem mem_hat_of_idempotent (z : RA F E) (hz : z * z = z) :
    z ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)) := by
  obtain ⟨x, h, hh, hx⟩ := exists_eq_one_tmul_add F E z
  obtain ⟨N, hN, hNx⟩ := exists_nat_mul_integral E x
  have h1 : (1 : RA F E) ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)) :=
    one_tmul_mem_adelicCompletionOfElementSet F ⟨1, map_one _⟩
  have hc : ∀ y : E, (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] ((N : E) * y) =
      N • ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] y : RA F E) := by
    intro y
    rw [← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul F, TensorProduct.tmul_smul,
      Nat.cast_smul_eq_nsmul]
  have hNz : N • z ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)) := by
    rw [hx, nsmul_add, ← hc]
    exact add_mem (one_tmul_mem_adelicCompletionOfElementSet F hNx) (nsmul_mem hh N)
  have hpow : ∀ n : ℕ, ∃ a ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)),
      ∃ b ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)), (z - h) ^ n = a + z * b := by
    intro n
    induction n with
    | zero => exact ⟨1, h1, 0, zero_mem _, by simp⟩
    | succ n ih =>
      obtain ⟨a, ha, b, hb, e⟩ := ih
      refine ⟨-(a * h), neg_mem (mul_mem_hat F E ha hh), a + b - b * h,
        sub_mem (add_mem ha hb) (mul_mem_hat F E hb hh), ?_⟩
      rw [pow_succ, e]
      linear_combination b * hz
  have hzh : z - h = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x := by rw [hx]; abel
  have hint : ∀ n : ℕ, (N : E) * x ^ n ∈ Set.range (algebraMap (𝓞 E) E) := by
    intro n
    apply mem_range_of_one_tmul_mem F E
    obtain ⟨a, ha, b, hb, e⟩ := hpow n
    rw [hzh, Algebra.TensorProduct.tmul_pow, one_pow] at e
    rw [hc, e, nsmul_add, ← smul_mul_assoc]
    exact add_mem (nsmul_mem ha N) (mul_mem_hat F E hNz hb)
  have hai : IsAlmostIntegral (𝓞 E) x := by
    refine ⟨(N : 𝓞 E), mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.2 hN.ne'), fun n => ?_⟩
    rw [Algebra.smul_def, map_natCast]
    exact hint n
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hai.isIntegral
  rw [hx]
  exact add_mem (one_tmul_mem_adelicCompletionOfElementSet F ⟨r, hr⟩) hh

end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem idempotent_mem_intAE : ∀ (D : D7) (z : Af D.host.F ⊗[D.host.F] D.host.E), z * z = z → z ∈ intAE D := by
  intro D z hz
  have h : intAE D = GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)) := by
    unfold intAE GlobalTheory.AdLat.hat1
    congr 1
    ext z
    constructor
    · rintro ⟨a, ha, x, rfl⟩
      exact ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
    · rintro ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
      exact ⟨a, ha, x, rfl⟩
  rw [h]
  exact mem_hat_of_idempotent D.host.F D.host.E z hz

end

end GlobalTheory.AdIdem
end
