module

public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharacterTrivialNearOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Formalism.LocalRingCardinality.ConjSqrtMinusD
public import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle085
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle163
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JetSumTable
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle082
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle011
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomT.SplitK

theorem rat_int_of_isIntegral {E : Type} [Field E] [CharZero E] (r : ℚ) (h : IsIntegral ℤ (r : E)) :
    ∃ m : ℤ, (m : ℚ) = r := by
  have h1 : IsIntegral ℤ r :=
    (isIntegral_algHom_iff (algebraMap ℚ E).toIntAlgHom (algebraMap ℚ E).injective).1 (by simpa using h)
  simpa using IsIntegrallyClosed.isIntegral_iff.1 h1

theorem int_of_prime_mul_sq {d : ℕ} (hd : d.Prime) (c : ℚ) (k : ℤ) (h : (d : ℚ) * c ^ 2 = k) :
    ∃ n : ℤ, (n : ℚ) = c := by
  have h1 : IsIntegral ℤ (((d : ℚ) * c) ^ 2) := by
    have : ((d : ℚ) * c) ^ 2 = algebraMap ℤ ℚ (d * k) := by
      simp only [eq_intCast]; push_cast; rw [← h]; ring
    rw [this]; exact isIntegral_algebraMap
  obtain ⟨e, he⟩ := rat_int_of_isIntegral (E := ℚ) ((d : ℚ) * c)
    (by simpa using IsIntegral.of_pow two_pos h1)
  have h2 : e ^ 2 = d * k := by
    have : (e : ℚ) ^ 2 = d * k := by rw [he, ← h]; ring
    exact_mod_cast this
  obtain ⟨n, hn⟩ := (Nat.prime_iff_prime_int.1 hd).dvd_of_dvd_pow (n := 2) ⟨k, h2⟩
  refine ⟨n, ?_⟩
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne_zero
  apply mul_left_cancel₀ hd0
  rw [← he, hn]; push_cast; ring

theorem jacobi_of_eq {p : ℕ} (hp : p.Prime) (d m n : ℤ) (h : m ^ 2 + d * n ^ 2 = 4 * p)
    (hm : ¬ (p : ℤ) ∣ m) : jacobiSym (-d) p = 1 := by
  have hg : m.gcd p = 1 := by
    rw [Int.gcd_comm]
    exact Int.isCoprime_iff_gcd_eq_one.1 ((Nat.prime_iff_prime_int.1 hp).irreducible.coprime_iff_not_dvd.2 hm)
  have h1 : jacobiSym (-d * n ^ 2) p = 1 := by
    rw [← jacobiSym.sq_one' hg]
    apply jacobiSym.mod_left'
    exact (Int.emod_emod_of_dvd _ (dvd_refl _)).symm.trans
      ((Int.emod_emod_of_dvd _ (dvd_refl _)).trans (Int.modEq_iff_dvd.2 ⟨4, by linear_combination h⟩))
  rw [jacobiSym.mul_left, jacobiSym.pow_left] at h1
  rcases jacobiSym.trichotomy (-d) p with h2 | h2 | h2
  · rw [h2] at h1; simp at h1
  · exact h2
  · rw [h2] at h1; nlinarith [sq_nonneg (jacobiSym n p)]

theorem mem_K {D : D7} {X : Fields} (s : Seam D X) (hs : s.Ok) {x : X.E} (hx : x ∈ X.Kq) :
    s.iE x ∈ D.host.K := by
  have hall : ∀ τ τ' : D.what₂.Tau, TaylorLogMetric.embT D τ (s.iE x) = TaylorLogMetric.embT D τ' (s.iE x) := fun τ τ' => by
    have h1 := hs.1 (s.iT.symm τ) x
    have h2 := hs.1 (s.iT.symm τ') x
    rw [Equiv.apply_symm_apply] at h1 h2
    rw [← h1, ← h2, hx (s.iT.symm τ) (s.iT.symm τ')]
  let τ₀ : D.what₂.Tau := D.eTau.symm 1
  have h := GlobalTheory.InducedType.sum_eq_trace D (s.iE x)
  rw [← GlobalTheory.InducedType.restrict_K D τ₀, Finset.sum_congr rfl (fun τ _ => hall τ τ₀), Finset.sum_const,
    ← map_nsmul] at h
  have h2 := (TaylorLogMetric.embT D τ₀).injective h
  rw [nsmul_eq_mul] at h2
  have hc : (((Finset.univ : Finset D.what₂.Tau).card : ℕ) : D.host.E) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.2 ⟨τ₀, Finset.mem_univ _⟩).ne'
  rw [eq_div_of_mul_eq hc ((mul_comm _ _).trans h2)]
  exact div_mem (Subtype.property _) (natCast_mem _ _)

theorem splitk : ∀ (D : D7) (X : Fields) (s : Seam D X) (ϖ : 𝓞 X.E) (p : ℕ), s.Ok → (ϖ : X.E) ∈ X.Kq → (∃ κ : 𝓞 D.host.K, ((κ : D.host.K) : D.host.E) = s.iE (ϖ : X.E)) ∧ (p.Prime → p ≠ 2 → ϖ * X.conjO ϖ = (p : 𝓞 X.E) → IsCoprime ϖ (X.conjO ϖ) → jacobiSym (-(D.host.d : ℤ)) p = 1) := by
  intro D X s ϖ p hs hK
  have hmem := mem_K s hs hK
  refine ⟨?_, fun hp _ hN hco => ?_⟩
  · have h1 : IsIntegral ℤ (s.iE (ϖ : X.E)) :=
      IsIntegral.map (s.iE : X.E →+* D.host.E).toIntAlgHom ϖ.isIntegral_coe
    have h2 : IsIntegral ℤ (⟨_, hmem⟩ : D.host.K) :=
      (isIntegral_algHom_iff D.host.K.val.toRingHom.toIntAlgHom D.host.K.val.toRingHom.injective).1 h1
    exact ⟨⟨_, h2⟩, rfl⟩
  · obtain ⟨a, b, hab⟩ := GlobalTheory.QuadSubfield.exists_coords D hmem
    have hc : s.iE ((X.conjO ϖ : 𝓞 X.E) : X.E) = a - b * D.host.sqrtMinusD := by
      rw [← GlobalTheory.QuadSubfield.conj_coords, ← hab, ← hs.2]; rfl
    have hsum : ((ϖ + X.conjO ϖ : 𝓞 X.E) : X.E) = ((2 * a : ℚ) : X.E) := by
      apply s.iE.injective
      rw [map_ratCast]
      push_cast
      rw [map_add (f := _), hc, hab]; ring
    obtain ⟨m, hm⟩ := rat_int_of_isIntegral (E := X.E) (2 * a) (hsum ▸ (ϖ + X.conjO ϖ).isIntegral_coe)
    have hprod : a ^ 2 + D.host.d * b ^ 2 = p := by
      have h1 := congrArg (fun z : 𝓞 X.E => s.iE (z : X.E)) hN
      push_cast at h1
      rw [map_mul, hc, hab, map_natCast] at h1
      have h2 : (a : D.host.E) ^ 2 + D.host.d * (b : D.host.E) ^ 2 = p := by
        linear_combination h1 + (b : D.host.E) ^ 2 * D.host.sqrtMinusD_sq
      exact_mod_cast h2
    obtain ⟨n, hn⟩ := int_of_prime_mul_sq D.host.hyp.2.1 (2 * b) (4 * p - m ^ 2)
      (by push_cast; rw [hm]; linear_combination 4 * hprod)
    refine jacobi_of_eq hp _ m n ?_ ?_
    · have : (m : ℚ) ^ 2 + D.host.d * (n : ℚ) ^ 2 = 4 * p := by
        rw [hm, hn]; linear_combination 4 * hprod
      exact_mod_cast this
    · rintro ⟨t, ht⟩
      have h1 : ϖ + X.conjO ϖ = (p : 𝓞 X.E) * (t : 𝓞 X.E) := by
        apply RingOfIntegers.ext
        rw [hsum, ← hm, ht]
        simp
      rw [← hN] at h1
      have u1 : IsUnit ϖ := hco.isUnit_of_dvd' dvd_rfl ⟨X.conjO ϖ * t - 1, by linear_combination h1⟩
      have u2 : IsUnit (X.conjO ϖ) := u1.map _
      have u3 : IsUnit (algebraMap ℤ (𝓞 X.E) (p : ℤ)) := by
        simpa [hN] using u1.mul u2
      have := Algebra.IsIntegral.isLocalHom ℤ (𝓞 X.E)
      exact (Nat.prime_iff_prime_int.1 hp).not_unit (isUnit_of_map_unit _ _ u3)

end GlobalTheory.MomT.SplitK
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove.PeriodTwist

open GlobalTheory.ThetaMove.PeriodComp

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

theorem smul_mem_locP_perO (AA : Submodule (𝓞 E) E) (Q : HeightOneSpectrum (𝓞 E)) {N : Submodule (𝓞 E) (Sp E a)} (hN : N.FG)
    {N' M' : Submodule (𝓞 E) (Sp E b)} (k : E) (h : ∀ y ∈ localization₂ Q.asIdeal N', k • y ∈ localization₂ Q.asIdeal M')
    {x : HomE E a b} (hx : x ∈ localization₂ Q.asIdeal (perO AA N N')) : k • x ∈ localization₂ Q.asIdeal (perO AA N M') := by
  have key : ∀ z ∈ perO AA N N', k • z ∈ localization₂ Q.asIdeal (perO AA N M') := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨r, hr, x, hx, rfl⟩ := hz
      obtain ⟨s, hs, hsx⟩ := exists_common Q.asIdeal.primeCompl hN M' (k • x) fun y hy =>
        h _ (mem_localization_of_mem Q (hx _ hy))
      refine ⟨s, hs, ?_⟩
      rw [smul_comm k r, smul_comm s r]
      exact smul_mem_perO hr hsx
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ _ hy
  obtain ⟨s, hs, hx⟩ := hx
  rw [← localization_localization₂]
  exact ⟨s, hs, by rw [smul_comm]; exact key _ hx⟩

theorem twO_perO : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (a b : ℕ) (AA : Submodule (𝓞 E) E) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (c : ℕ) (e : HeightOneSpectrum (𝓞 E) → ℤ), N.FG → 0 < c → (∀ Q, -1 ≤ e Q ∧ e Q ≤ 1) → twist₂ (perO AA N N') c e = perO AA N (twist₂ N' c e) := by
  intro E _ _ _ a b AA N N' c e hN hc he
  have hk : ∀ Q, ((c : E) ^ e Q) ≠ 0 := fun Q => zpow_ne_zero _ (by exact_mod_cast hc.ne')
  apply le_antisymm
  · intro x hx
    refine mem_of_locP fun Q => ?_
    have h1 := (mem_localization_twist _ hc he Q x).1 (mem_localization_of_mem Q hx)
    have h2 := smul_mem_locP_perO AA Q hN (M' := twist₂ N' c e) ((c : E) ^ e Q) (fun y hy => by
      rw [mem_localization_twist _ hc he, inv_smul_smul₀ (hk Q)]; exact hy) h1
    rwa [smul_inv_smul₀ (hk Q)] at h2
  · intro x hx
    refine mem_of_locP fun Q => ?_
    rw [mem_localization_twist _ hc he]
    exact smul_mem_locP_perO AA Q hN _ (fun y hy => (mem_localization_twist _ hc he Q y).1 hy) (mem_localization_of_mem Q hx)

end GlobalTheory.ThetaMove.PeriodTwist
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

namespace GlobalTheory.RealSpaceCoord

theorem herm_eq_dot {P Q : ℕ} (x y : ActionCoordinates.Wsp P Q) :
    ActionCoordinates.herm y x = star x ⬝ᵥ (Formalism.UG.Jpq P Q *ᵥ y) := by
  simp [ActionCoordinates.herm, ActionCoordinates.sgn, Formalism.UG.Jpq, Fintype.sum_sum_type, dotProduct, fromBlocks_mulVec, neg_mulVec,
    mul_comm]

theorem form_eq {M P Q : ℕ} (A : Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ) (x y : Fin M → ℂ) :
    ∑ i, ∑ j, star (x i) * (Aᴴ * Formalism.UG.Jpq P Q * A) i j * y j = ActionCoordinates.herm (A *ᵥ y) (A *ᵥ x) := by
  rw [herm_eq_dot, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc, Pi.star_apply]

theorem exists_coord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (T : Type) [Fintype T] (τ : T → (E →+* ℂ)) (θ : T → (Ainf F ⊗[F] E →+* ℂ)), (Function.Bijective fun ρ => InfinitePlace.mk (τ ρ)) → (∀ ρ, IsInfEmb (τ ρ) (θ ρ)) → ∀ (M P Q : ℕ), P + Q = M → ∀ J : Matrix (Fin M) (Fin M) E, IsHermND σ J → ∀ A : T → Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ, (∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq P Q * A ρ = J.map (τ ρ)) → ∃ e : (Fin 1 → Fin M → Ainf F ⊗[F] E) ≃ₜ+ (T → ActionCoordinates.Wsp P Q), (∀ X ρ, e X ρ = A ρ *ᵥ fun i => θ ρ (X 0 i)) ∧ ∀ X Y ρ, θ ρ (hR (Ainf F) σ J (X 0) (Y 0)) = ActionCoordinates.herm (e Y ρ) (e X ρ) := by
  intro F E _ _ _ _ _ σ h T _ τ θ hτ hθ M P Q hM J hJ A hA
  obtain ⟨e0, he, hc, hc', hs⟩ := GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv F E σ T τ θ h hτ hθ
  let B : T → Matrix (Fin M) (Fin P ⊕ Fin Q) ℂ := fun ρ => (J.map (τ ρ))⁻¹ * ((A ρ)ᴴ * Formalism.UG.Jpq P Q)
  have hBA : ∀ ρ, B ρ * A ρ = 1 := fun ρ => by
    have hd : (J.map (τ ρ)).det = τ ρ J.det := ((τ ρ).map_det J).symm
    simp only [B]
    rw [Matrix.mul_assoc, hA, Matrix.nonsing_inv_mul]
    rw [hd]
    exact ((map_ne_zero (τ ρ)).2 hJ.2).isUnit
  have hAB : ∀ ρ, A ρ * B ρ = 1 := fun ρ =>
    (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [hM])).2 (hBA ρ)
  have he' : ∀ z ρ, θ ρ (e0.symm z) = z ρ := fun z ρ => by rw [← he, e0.apply_symm_apply]
  refine ⟨{ toFun := fun X ρ => A ρ *ᵥ fun i => θ ρ (X 0 i)
            invFun := fun z _ i => e0.symm fun ρ => (B ρ *ᵥ z ρ) i
            left_inv := fun X => ?_
            right_inv := fun z => ?_
            map_add' := fun X Y => ?_
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun _ _ => rfl, fun X Y ρ => ?_⟩
  · funext k i
    obtain rfl : k = 0 := Subsingleton.elim _ _
    simp only [mulVec_mulVec, hBA, one_mulVec]
    rw [RingEquiv.symm_apply_eq]
    funext ρ
    rw [he]
  · funext ρ
    simp only [he']
    rw [mulVec_mulVec, hAB, one_mulVec]
  · funext ρ
    refine Eq.trans ?_ (mulVec_add (A ρ) (fun i => θ ρ (X 0 i)) (fun i => θ ρ (Y 0 i)))
    congr 1
    funext i
    exact map_add (θ ρ) _ _
  · refine continuous_pi fun ρ => continuous_const.matrix_mulVec (continuous_pi fun i => ?_)
    simp only [← he]
    exact (continuous_apply ρ).comp (hc.comp ((continuous_apply i).comp (continuous_apply 0)))
  · exact continuous_pi fun _ => continuous_pi fun i => hc'.comp (continuous_pi fun ρ =>
      (continuous_apply i).comp (continuous_const.matrix_mulVec (continuous_apply ρ)))
  · refine Eq.trans ?_ (form_eq (A ρ) (fun i => θ ρ (X 0 i)) (fun i => θ ρ (Y 0 i)))
    rw [hA]

    simp only [hR, Formalism.UG.hform, map_sum, map_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [GlobalTheory.Mem.VolInfIso.infEmb_sigR σ (τ ρ) (θ ρ) h (hθ ρ)]
    congr 2
    exact (hθ ρ).1 _

end GlobalTheory.RealSpaceCoord
end
