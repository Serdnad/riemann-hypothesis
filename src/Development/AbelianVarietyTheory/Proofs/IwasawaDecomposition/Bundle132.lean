module

import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle055
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle004
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle227
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DedekindZetaEqSumRealEisenstein
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsBasisEmbedding
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle002
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ModularJExpansionAndPolynomialAndIsIntegral
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
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
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

namespace GlobalTheory.NatMulIntegralExists

open NumberField

theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ d : ℕ, 0 < d ∧ IsIntegral ℤ ((d : E) * a) := by
  have hz : IsAlgebraic ℤ a := IsFractionRing.isAlgebraic_iff ℤ ℚ E |>.mpr (.of_finite ℚ a)
  obtain ⟨y, hy, hint⟩ := hz.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
  rw [zsmul_eq_mul] at hint
  rcases Int.natAbs_eq y with h | h
  · have : ((y.natAbs : ℕ) : E) = (y : E) := by
      conv_rhs => rw [h]
      simp
    rw [this]; exact hint
  · have : ((y.natAbs : ℕ) : E) = -(y : E) := by
      conv_rhs => rw [h]
      simp
    rw [this, neg_mul]; exact hint.neg

theorem main : ∀ {E : Type} [inst : Field E] [NumberField E] {r : ℕ}
    (Λ : Submodule (NumberField.RingOfIntegers E) (Fin r → E)),
    Submodule.span E (↑Λ : Set (Fin r → E)) = ⊤ →
    ∀ (w : Fin r → E), ∃ (k : ℕ), (0 : ℕ) < k ∧ (↑k : E) • w ∈ Λ := by
  apply GlobalTheory.AlgDirMom.exists_nat_smul_mem <;> assumption

end GlobalTheory.NatMulIntegralExists
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric NumberField GlobalTheory.Mem.Per
open scoped nonZeroDivisors Pointwise UpperHalfPlane

namespace GlobalTheory.Mem.PerField

theorem ideal_eq_of_pow_eq {A : Type} [CommRing A] [IsDedekindDomain A] {I J : Ideal A} {n : ℕ} (hn : n ≠ 0)
    (h : I ^ n = J ^ n) : I = J := by
  apply le_antisymm
  · rw [← Ideal.dvd_iff_le, ← UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd hn, h]
  · rw [← Ideal.dvd_iff_le, ← UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd hn, h]

theorem exists_pow_eq_span {E : Type} [Field E] [NumberField E] (I : Ideal (𝓞 E)) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ β : 𝓞 E, I ^ n = Ideal.span {β} := by
  classical
  by_cases hI : I = ⊥
  · exact ⟨1, one_ne_zero, 0, by simp [hI]⟩
  have hI' : I ∈ (Ideal (𝓞 E))⁰ := mem_nonZeroDivisors_of_ne_zero hI
  refine ⟨Fintype.card (ClassGroup (𝓞 E)), Fintype.card_ne_zero, ?_⟩
  have h1 : ClassGroup.mk0 (⟨I, hI'⟩ ^ Fintype.card (ClassGroup (𝓞 E))) = 1 := by
    rw [map_pow, pow_card_eq_one]
  have h2 := (ClassGroup.mk0_eq_one_iff (pow_mem hI' (Fintype.card (ClassGroup (𝓞 E))))).1 h1
  exact ⟨_, (Ideal.span_singleton_generator _).symm⟩

theorem span_root {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] (f : E →+* L)
    {I : Ideal (𝓞 E)} {n : ℕ} (hn : n ≠ 0) {β : 𝓞 E} (h : I ^ n = Ideal.span {β}) {x : L}
    (hx : x ^ n = f β) :
    Submodule.span (𝓞 L) {x} = Submodule.span (𝓞 L) {y | ∃ c ∈ I, y = f (c : E)} := by
  have hi : IsIntegral ℤ x := by
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero hn) ?_
    rw [hx]
    exact (RingOfIntegers.isIntegral_coe β).map f.toIntAlgHom
  let x' : 𝓞 L := ⟨x, hi⟩
  let f' : 𝓞 E →+* 𝓞 L := RingOfIntegers.mapRingHom f
  have e : Ideal.span {x'} = I.map f' := by
    apply ideal_eq_of_pow_eq hn
    rw [← Ideal.map_pow, h, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_pow]
    congr 2
    exact RingOfIntegers.ext hx
  have e2 := congrArg (Submodule.map (Algebra.linearMap (𝓞 L) L)) e
  rw [Ideal.map, Ideal.span, Ideal.span, Submodule.map_span, Submodule.map_span, Set.image_singleton] at e2
  refine e2.trans ?_
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨c, hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨_, ⟨c, hc, rfl⟩, rfl⟩

variable {R : Ranks} (H : Host R)

theorem cmInverseHalfDifferent_mul_relativeDifferent :
    H.AA0 * (differentIdeal (𝓞 H.K) (𝓞 H.E) : FractionalIdeal (𝓞 H.E)⁰ H.E) =
      ((H.conj • H.𝔟 : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) := by
  have hd : differentIdeal (𝓞 H.K) (𝓞 H.E) ≠ ⊥ := differentIdeal_ne_bot
  have h1 : differentIdeal (𝓞 H.K) (𝓞 H.E) = H.𝔟 * (H.conj • H.𝔟) := H.𝔟_spec.1
  have hb : H.𝔟 ≠ ⊥ := by
    intro h0
    apply hd
    rw [h1, h0, Ideal.bot_mul]
  rw [h1, FractionalIdeal.coeIdeal_mul, Host.AA0, ← mul_assoc,
    inv_mul_cancel₀ (FractionalIdeal.coeIdeal_ne_zero.2 hb), one_mul]

theorem ellLat_eq {LL : Type} [Field LL] [NumberField LL] (embE : H.E →+* LL) (g : R.GG) :
    ellLat H embE g = Submodule.span (𝓞 LL)
      {y | ∃ c ∈ (H.conj • H.𝔟 : Ideal (𝓞 H.E)), y = (embE.comp (H.sigmaOf g : H.E →+* H.E)) (c : H.E)} := by
  apply le_antisymm
  · refine Submodule.span_mono ?_
    rintro _ ⟨a, ha, b, hb, rfl⟩
    have : a * (b : H.E) ∈ H.AA0 * (differentIdeal (𝓞 H.K) (𝓞 H.E) : FractionalIdeal (𝓞 H.E)⁰ H.E) :=
      FractionalIdeal.mul_mem_mul ha (FractionalIdeal.mem_coeIdeal_of_mem _ hb)
    rw [cmInverseHalfDifferent_mul_relativeDifferent] at this
    obtain ⟨c, hc, e⟩ := (FractionalIdeal.mem_coeIdeal _).1 this
    exact ⟨c, hc, by rw [← e]; rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨c, hc, rfl⟩
    have : (c : H.E) ∈ H.AA0 * (differentIdeal (𝓞 H.K) (𝓞 H.E) : FractionalIdeal (𝓞 H.E)⁰ H.E) := by
      rw [cmInverseHalfDifferent_mul_relativeDifferent]
      exact FractionalIdeal.mem_coeIdeal_of_mem _ hc
    refine FractionalIdeal.mul_induction_on
      (C := fun z => (embE.comp (H.sigmaOf g : H.E →+* H.E)) z ∈ ellLat H embE g) this ?_ ?_
    · intro a ha b hb
      obtain ⟨b', hb', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hb
      exact Submodule.subset_span ⟨a, ha, b', hb', rfl⟩
    · intro x y hx hy
      rw [map_add (f := _)]
      exact add_mem hx hy

theorem mem_baseLat (w : ℂ) : w ∈ baseLat H ↔ ∃ c ∈ H.ccK, w = H.φ₀ (((c : H.K) : H.E)) := by
  constructor
  · intro hw
    induction hw using AddSubgroup.closure_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, H.ccK.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨c', hc', rfl⟩ := hy
      exact ⟨c + c', H.ccK.add_mem hc hc', by simp⟩
    | neg x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨-c, H.ccK.neg_mem hc, by simp⟩
  · exact fun hw => AddSubgroup.subset_closure hw

theorem finrank_K : Module.finrank ℚ H.K = 2 :=
  Formalism.FrobeniusOrbits.SplitK.finrank_K H.hyp.2.1.pos (H.sqd_sq)

theorem discr_K : NumberField.discr H.K = -(H.d : ℤ) :=
  discr_eq_neg_of_sq_eq (finrank_K H) H.hyp.2.1.squarefree
    (by have := H.hyp.2.2.2.1; omega)
    (Formalism.FrobeniusOrbits.SplitK.bK_sq (H.sqd_sq))

theorem exists_periodPair_baseLat : ∃ L : PeriodPair, ∀ z, z ∈ baseLat H ↔ z ∈ L.lattice := by
  let σ : H.K →+* ℂ := H.φ₀.comp H.K.val.toRingHom
  let I : (Ideal (𝓞 H.K))⁰ := ⟨H.ccK, mem_nonZeroDivisors_of_ne_zero H.ccK_ne_bot⟩
  obtain ⟨L, hL⟩ := QuadraticZeta.exists_periodPair (finrank_K H) (discr_K H) σ
    (FractionalIdeal.mk0 H.K I)
  refine ⟨L, fun z => ?_⟩
  rw [mem_baseLat, ← SetLike.mem_coe, hL]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨(c : H.K), FractionalIdeal.mem_coeIdeal_of_mem _ hc, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, hc, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    exact ⟨c, hc, rfl⟩

theorem isIntegral_jLat : IsIntegral ℤ (jLat (baseLat H)) := by
  obtain ⟨L, hL⟩ := exists_periodPair_baseLat H
  have hd := GlobalTheory.LatticeInvariants.invariants_dictionary L _ hL
  obtain ⟨a, τ, ha, h⟩ := exists_lattice_eq_mul_tau L
  rw [jLat, TaylorLogMetric.discr, hd.1, hd.2.1, g₂_cube_div_eq_modularJ ha h]
  refine isIntegral_modularJ_of_ringOfIntegers (finrank_K H) (H.φ₀.comp H.K.val.toRingHom) fun α x hx ↦ ?_
  have key : ∀ y : ℂ, y ∈ Submodule.span ℤ {(τ : ℂ), 1} ↔ a * y ∈ L.lattice := fun y ↦ by
    rw [h, Submodule.mem_span_pair]
    simp [mul_right_inj' ha]
  rw [key, ← hL, mem_baseLat] at hx ⊢
  obtain ⟨c, hc, e⟩ := hx
  refine ⟨α * c, H.ccK.mul_mem_left α hc, ?_⟩
  rw [mul_left_comm, e]
  simp

theorem exists_fieldOK : ∀ (R : Ranks) (H : Host R) (M : IntermediateField ℚ ℂ), FiniteDimensional ℚ M → ∃ M' : IntermediateField ℚ ℂ, FiniteDimensional ℚ M' ∧ M ≤ M' ∧ ∀ (LL : Type) [Field LL] [NumberField LL] (emb : LL →+* ℂ) (embE : H.E →+* LL), emb.comp embE = H.φ₀ → (∀ x ∈ M', ∃ a, emb a = x) → FieldOK H emb embE := by
  intro R H M hM
  obtain ⟨n, hn, β, hβ⟩ := exists_pow_eq_span (H.conj • H.𝔟 : Ideal (𝓞 H.E))
  choose z hz using fun σ : H.E ≃ₐ[ℚ] H.E =>
    IsAlgClosed.exists_pow_nat_eq (H.φ₀ (σ (β : H.E))) (Nat.pos_of_ne_zero hn)
  let T : Set ℂ := insert (jLat (baseLat H)) (Set.range z)
  have : Finite T := (Set.finite_range z).insert _
  have hT : FiniteDimensional ℚ (IntermediateField.adjoin ℚ T) := by
    refine IntermediateField.finiteDimensional_adjoin fun x hx ↦ ?_
    rcases hx with rfl | ⟨σ, rfl⟩
    · exact (isIntegral_jLat H).tower_top
    · refine IsIntegral.of_pow (Nat.pos_of_ne_zero hn) ?_
      rw [hz]
      exact (Algebra.IsIntegral.isIntegral (R := ℚ) (σ (β : H.E))).map H.φ₀.toRatAlgHom
  refine ⟨M ⊔ IntermediateField.adjoin ℚ T, inferInstance, le_sup_left, ?_⟩
  intro LL _ _ emb embE he hM'
  have hT' : ∀ x ∈ T, ∃ a, emb a = x := fun x hx =>
    hM' x ((le_sup_right : _ ≤ M ⊔ _) (IntermediateField.subset_adjoin ℚ T hx))
  refine ⟨hT' _ (Set.mem_insert _ _), fun g => ?_⟩
  obtain ⟨x, hx⟩ := hT' _ (Set.mem_insert_of_mem _ ⟨H.sigmaOf g, rfl⟩)
  refine ⟨x, ?_⟩
  rw [IsGen, ellLat_eq]
  refine span_root _ hn hβ ?_
  apply emb.injective
  rw [map_pow, hx, hz, ← he]
  rfl

end GlobalTheory.Mem.PerField
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep Topology Matrix Filter

namespace GlobalTheory.CuspRep.LocSph

theorem exists_fixed_of_mem_iSup {G V U ι : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G U) (hσ : σ.IsIrreducible) (f : ι → U →ₗ[ℂ] V)
    (hf : ∀ i g u, f i (σ g u) = ρ g (f i u)) (K : Set G) (φ : V) (h0 : φ ≠ 0) (hK : ∀ k ∈ K, ρ k φ = φ)
    (hφ : φ ∈ ⨆ i, LinearMap.range (f i)) : ∃ v : U, v ≠ 0 ∧ ∀ k ∈ K, σ k v = v := by
  classical
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hφ
  have key : ∀ s : Finset ι, ∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → φ ∉ W →
      φ ∈ W ⊔ ⨆ i ∈ s, LinearMap.range (f i) → ∃ v : U, v ≠ 0 ∧ ∀ k ∈ K, σ k v = v := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro W _ h1 h2; exact absurd (by simpa using h2) h1
    | insert i s _ ih =>
      intro W hW h1 h2
      rw [Finset.iSup_insert, ← sup_assoc] at h2
      by_cases h3 : φ ∈ W ⊔ LinearMap.range (f i)
      · obtain ⟨x, hx, _, ⟨v, rfl⟩, e⟩ := Submodule.mem_sup.1 h3
        have hv : f i v ∉ W := fun h => h1 (e ▸ add_mem hx h)
        have hc : W.comap (f i) = ⊥ := by
          refine (((isIrreducible_iff σ).1 hσ).2 _ fun g u hu => ?_).resolve_right fun h => hv ?_
          · rw [Submodule.mem_comap, hf]; exact hW g _ hu
          · have : v ∈ W.comap (f i) := h ▸ Submodule.mem_top
            exact this
        refine ⟨v, fun h => hv (by rw [h, map_zero]; exact zero_mem _), fun k hk => ?_⟩
        have h4 : σ k v - v ∈ W.comap (f i) := by
          have h5 := hK k hk
          rw [← e, map_add (f := _)] at h5
          have h6 : f i (σ k v - v) = x - ρ k x := by
            rw [map_sub, hf]; linear_combination (norm := module) h5
          rw [Submodule.mem_comap, h6]
          exact sub_mem hx (hW k x hx)
        rw [hc, Submodule.mem_bot] at h4
        exact sub_eq_zero.1 h4
      · refine ih _ (fun g y hy => ?_) h3 h2
        obtain ⟨x, hx, _, ⟨v, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hy
        rw [map_add (f := _), ← hf]
        exact Submodule.add_mem_sup (hW g x hx) ⟨_, rfl⟩
  exact key s ⊥ (fun g x hx => by simp_all) (by simpa using h0) (by simpa using hs)

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem gl_ext {x y : GL (Fin a) (Af E)}
    (h : ∀ v, GeneralLinearGroup.map (pLoc E v) x = GeneralLinearGroup.map (pLoc E v) y) : x = y := by
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext _ fun v => ?_)
  exact congrArg (fun g : GL (Fin a) (v.adicCompletion E) => g.val i j) (h v)

theorem comm_locGL (w : HeightOneSpectrum (𝓞 E)) (k : GL (Fin a) (Af E))
    (hk : GeneralLinearGroup.map (pLoc E w) k = 1) (g : GL (Fin a) (w.adicCompletion E)) :
    k * locGL E a w g = locGL E a w g * k := by
  refine gl_ext fun v => ?_
  rw [map_mul, map_mul]
  by_cases h : v = w
  · subst h; rw [hk, one_mul, mul_one]
  · rw [pLoc_locGL_of_ne h, one_mul, mul_one]

theorem tendsto_sLoc (y : ∀ v : HeightOneSpectrum (𝓞 E), v.adicCompletion E)
    (hy : ∀ v, y v ∈ v.adicCompletionIntegers E) : Tendsto (fun v => sLoc E v (y v)) cofinite (𝓝 0) := by
  classical
  have h := (GlobalTheory.Mem.UnrAe.tendsto_finSingle y hy).sub
    (GlobalTheory.Mem.UnrAe.tendsto_finSingle (L := E) (fun _ => 0) fun _ => by simp)
  rw [sub_self] at h
  refine h.congr fun w => ?_
  refine FiniteAdeleRing.ext _ fun v => ?_
  change Function.update (fun v : HeightOneSpectrum (𝓞 E) => (1 : v.adicCompletion E)) w (y w) v -
      Function.update (fun v : HeightOneSpectrum (𝓞 E) => (1 : v.adicCompletion E)) w 0 v =
      (Pi.single w (y w) : ∀ v : HeightOneSpectrum (𝓞 E), v.adicCompletion E) v
  by_cases h : v = w
  · subst h; simp
  · simp [h]

theorem tendsto_corner (y : ∀ v : HeightOneSpectrum (𝓞 E), Matrix (Fin a) (Fin a) (v.adicCompletionIntegers E)) :
    Tendsto (fun v => corner (matN a (sLoc E v)) ((y v).map (v.adicCompletionIntegers E).subtype)) cofinite (𝓝 1) := by
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have h := ((tendsto_const_nhds (x := (1 : Matrix (Fin a) (Fin a) (Af E)) i j)).sub
    (tendsto_sLoc (E := E) (fun v => (1 : Matrix (Fin a) (Fin a) (v.adicCompletion E)) i j) fun v => by
      rw [Matrix.one_apply]; split_ifs; exacts [one_mem _, zero_mem _])).add
    (tendsto_sLoc (fun v => (y v i j : v.adicCompletion E)) fun v => (y v i j).2)
  rw [sub_zero, add_zero] at h
  exact h

theorem tendsto_locGL (y : ∀ v : HeightOneSpectrum (𝓞 E), GL (Fin a) (v.adicCompletionIntegers E)) :
    Tendsto (fun v => locGL E a v (GeneralLinearGroup.map (v.adicCompletionIntegers E).subtype (y v))) cofinite (𝓝 1) := by
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  exact (tendsto_corner fun v => (y v).val).prodMk_nhds
    ((MulOpposite.continuous_op.tendsto _).comp (tendsto_corner fun v => ((y v)⁻¹).val))

theorem eventually_mem {U : Set (GL (Fin a) (Af E))} (hU : U ∈ 𝓝 1) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∀ g : GL (Fin a) (w.adicCompletionIntegers E),
      locGL E a w (GeneralLinearGroup.map (w.adicCompletionIntegers E).subtype g) ∈ U := by
  have h : ∀ w : HeightOneSpectrum (𝓞 E), ∃ y : GL (Fin a) (w.adicCompletionIntegers E),
      locGL E a w (GeneralLinearGroup.map (w.adicCompletionIntegers E).subtype y) ∈ U →
      ∀ g : GL (Fin a) (w.adicCompletionIntegers E),
        locGL E a w (GeneralLinearGroup.map (w.adicCompletionIntegers E).subtype g) ∈ U := fun w => by
    by_contra hc
    push Not at hc
    obtain ⟨-, g, hg⟩ := hc 1
    exact hg (hc g).1
  choose y hy using h
  exact ((tendsto_locGL y).eventually_mem hU).mono fun w hw => hy w hw

variable [_root_.NumberField.IsTotallyComplex E]

def Maps (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) : Type :=
  {f : σ.V →ₗ[ℂ] Sm E a // (∀ v, f v ∈ π.V) ∧ ∀ g v, f (σ.ρ g v) = finRep E a (locGL E a w g) (f v)}

theorem iSup_range_eq (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E)))
    (h : π.IsLocComp w σ) : ⨆ f : Maps π w σ, LinearMap.range f.1 = π.V := by
  have comm : ∀ o : Op E a, (∀ g, act o * finRep E a (locGL E a w g) = finRep E a (locGL E a w g) * act o) →
      ∀ (f : Maps π w σ) v, act o (f.1 v) ∈ ⨆ f : Maps π w σ, LinearMap.range f.1 := fun o ho f v =>
    Submodule.mem_iSup_of_mem (⟨act o ∘ₗ f.1, fun v => π.stable o _ (f.2.1 v), fun g v => by
      rw [LinearMap.comp_apply, f.2.2]; exact LinearMap.congr_fun (ho g) _⟩ : Maps π w σ) ⟨v, rfl⟩
  refine (π.irred _ (iSup_le fun f => ?_) fun o φ hφ => ?_).resolve_left fun hb => ?_
  · rintro _ ⟨v, rfl⟩; exact f.2.1 v
  · have : (⨆ f : Maps π w σ, LinearMap.range f.1) ≤ (⨆ f : Maps π w σ, LinearMap.range f.1).comap (act o) := by
      refine iSup_le fun f => ?_
      rintro _ ⟨v, rfl⟩
      rw [Submodule.mem_comap]
      cases o with
      | fin k =>
        let g := GeneralLinearGroup.map (pLoc E w) k
        have h1 := comm (.fin (k * (locGL E a w g)⁻¹)) (fun g' => by
          change finRep E a _ * _ = _ * finRep E a _
          rw [← map_mul, ← map_mul, comm_locGL w _ (by rw [map_mul, map_inv, pLoc_locGL, mul_inv_cancel])]) f (σ.ρ g v)
        have h2 : act (.fin (k * (locGL E a w g)⁻¹)) (f.1 (σ.ρ g v)) = act (.fin k) (f.1 v) := by
          rw [f.2.2, act, act, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
        rwa [h2] at h1
      | cpt k =>
        refine comm (.cpt k) (fun g => ?_) f v
        have h2 := congrArg (rt E a) (infGL_comm (Unitary.toUnits k) (locGL E a w g))
        rw [map_mul, map_mul] at h2
        exact h2
      | lie X => exact comm (.lie X) (fun g => lie_rt_fin X (locGL E a w g)) f v
    exact this hφ
  · obtain ⟨f, h0, hf⟩ := h
    refine h0 (LinearMap.ext fun v => Subtype.ext ?_)
    have : (f v).1 ∈ ⨆ f : Maps π w σ, LinearMap.range f.1 :=
      Submodule.mem_iSup_of_mem (⟨π.V.subtype ∘ₗ f, fun v => (f v).2, fun g v => congrArg Subtype.val (hf g v)⟩ :
        Maps π w σ) ⟨v, rfl⟩
    rw [hb] at this
    exact this

theorem locComp_spherical : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a), ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), π.IsLocComp w σ → ∃ v : σ.V, v ≠ 0 ∧ ∀ g : GL (Fin a) (w.adicCompletionIntegers E), σ.ρ (Matrix.GeneralLinearGroup.map (w.adicCompletionIntegers E).subtype g) v = v := by
  intro E _ _ _ a π
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  filter_upwards [eventually_mem ((π.cusp φ hφ).1.level.mem_nhds (by simp))] with w hw σ hσ
  obtain ⟨v, h1, h2⟩ := exists_fixed_of_mem_iSup ((finRep E a).comp (locGL E a w)) σ.ρ σ.irred
    (fun f : Maps π w σ => f.1) (fun f => f.2.2)
    (Set.range (GeneralLinearGroup.map (w.adicCompletionIntegers E).subtype)) φ h0
    (by rintro _ ⟨g, rfl⟩; exact hw g) (by rw [iSup_range_eq π w σ hσ]; exact hφ)
  exact ⟨v, h1, fun g => h2 _ ⟨g, rfl⟩⟩

end GlobalTheory.CuspRep.LocSph
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep

namespace GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem commute_cap_of_commute_Eop (τ : E →+* ℂ) (u : ℂ) (z : Module.End ℂ (Sm E a))
    (h : ∀ i j, Commute (Eop τ i j) z) : Commute (cap τ u) z := by
  let S : Subalgebra ℂ (Module.End ℂ (Sm E a)) := Subalgebra.centralizer ℂ {z}
  have hS : ∀ x, x ∈ S ↔ Commute x z := fun x => by
    simp only [S, Subalgebra.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  have hE : ∀ i j, Eop τ i j ∈ S := fun i j => (hS _).2 (h i j)
  refine (hS _).1 ?_
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  refine S.add_mem ?_ (hE _ _)
  split_ifs
  · exact S.algebraMap_mem _
  · exact S.zero_mem

theorem commute_cap_Eop (τ τ' : E →+* ℂ) (u : ℂ) (i j : Fin a) : Commute (cap τ u) (Eop τ' i j) := by
  by_cases h : τ = τ'
  · subst h; exact cap_comm τ u i j
  · exact commute_cap_of_commute_Eop τ u _ fun k l => Eop_comm h k l i j

theorem lieS_atEmb_one (τ : E →+* ℂ) (i j : Fin a) :
    lieS E a i j (atEmb τ 1) = Eop τ i j + Eop (ComplexEmbedding.conjugate τ) i j := by
  have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by
    rw [atEmb_eq]; simp
  simp only [Eop, atEmb_conj, map_one, Complex.conj_I, e, map_neg]
  match_scalars <;> ring

theorem lieS_atEmb_I (τ : E →+* ℂ) (i j : Fin a) :
    lieS E a i j (atEmb τ Complex.I) = Complex.I • (Eop τ i j - Eop (ComplexEmbedding.conjugate τ) i j) := by
  have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by
    rw [atEmb_eq]; simp
  simp only [Eop, atEmb_conj, map_one, Complex.conj_I, e, map_neg]
  match_scalars <;> ring_nf <;> simp

theorem commute_cap_lieS (τ : E →+* ℂ) (u : ℂ) (i j : Fin a) (x : Cinf E) : Commute (cap τ u) (lieS E a i j x) := by
  classical
  have hx : x = ∑ w : InfinitePlace E, atEmb w.embedding (x w) := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    refine Finset.sum_congr rfl fun w _ => ?_
    unfold atEmb
    rw [InfinitePlace.mk_embedding, if_pos rfl]

  rw [hx, map_sum]
  refine Commute.sum_right _ _ _ fun w _ => ?_
  rw [atEmb_eq, map_add (f := _), map_smul, map_smul, lieS_atEmb_one, lieS_atEmb_I]
  exact (((commute_cap_Eop τ _ u i j).add_right (commute_cap_Eop τ _ u i j)).smul_right _).add_right
    ((((commute_cap_Eop τ _ u i j).sub_right (commute_cap_Eop τ _ u i j)).smul_right _).smul_right _)

theorem commute_cap_lie (τ : E →+* ℂ) (u : ℂ) (X : Lie E a) : Commute (cap τ u) (lie E a X) := by
  have hX : lie E a X = ∑ i, ∑ j, lieS E a i j (X i j) := by

    simp only [lieS_apply, ← map_sum]
    exact congrArg _ (Matrix.matrix_eq_sum_single (Matrix.of X))
  rw [hX]
  exact Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ => commute_cap_lieS τ u i j _

theorem commute_cap_finRep (τ : E →+* ℂ) (u : ℂ) (k : GL (Fin a) (Af E)) : Commute (cap τ u) (finRep E a k) := by
  have h : ∀ i j x, Commute (lieS E a i j x) (finRep E a k) := fun i j x => lie_rt_fin _ k
  exact commute_cap_of_commute_Eop τ u _ fun i j =>
    ((h i j _).sub_left ((h i j _).smul_left _)).smul_left _

end GlobalTheory.CuspRep
end
