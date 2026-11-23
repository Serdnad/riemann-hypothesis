module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle053
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUnitOfSumEqOne
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldIntegersInIntegrallyClosed
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.FarguesHodgeTate
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.HTL

theorem exists_retraction_mod : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Li : Type) [AddCommGroup Li] [Module K Li] (D : HTChart A K c p R N (Module.Dual K Li)) (ρ : 𝓞 E →+* Module.End K Li), (∀ (a : 𝓞 E) (w : Module.Dual K Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a)) → ∀ (σ : E →+* K) (m : ℕ), Module.Projective A (D.omHT σ) → (∀ y ∈ D.omHT σ, ∃ x : Fin N → A, ∃ y' ∈ D.omHT σ, y = D.q σ x + ((p : A) ^ m) • y') → ∃ Rr : (Fin N → K) →ₗ[K] Li, (∀ k, Rr (Pi.single k 1) ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom)) 1 (algebraMap A K).range) ∧ ∀ e ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom)) 1 (algebraMap A K).range, ∃ e' ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom)) 1 (algebraMap A K).range, Rr (fun l => D.h (Pi.single l 1) e) = e + ((p : K) ^ m) • e' := by
  intro A K _ _ _ _ _ _ _ E _ _ c hc p R N _ Li _ _ D ρ hact σ m hproj hsurj
  classical
  have hp : (p : K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hpm : ((p : K) ^ m) ≠ 0 := pow_ne_zero _ hp
  have hmemM : ∀ w ∈ D.om', eigProj D.ρΩ σ w ∈ D.omHT σ := fun w hw => ⟨w, hw, rfl⟩
  have hh : ∀ i : Fin N, D.h (Pi.single i 1) ∈ D.om' := fun i =>
    Submodule.mem_sup_left (Submodule.subset_span ⟨_, rfl⟩)
  let v : Fin N → D.omHT σ := fun i => ⟨eigProj D.ρΩ σ (D.h (Pi.single i 1)), hmemM _ (hh i)⟩
  let Q : (Fin N → A) →ₗ[A] D.omHT σ := Fintype.linearCombination A v
  have hQ : ∀ x, ((Q x : D.omHT σ) : Module.Dual K Li) = D.q σ x := by
    intro x
    simp [Q, Fintype.linearCombination_apply, HTChart.q, v]
  let P : Submodule A (D.omHT σ) := LinearMap.range (((p : A) ^ m) • (LinearMap.id : D.omHT σ →ₗ[A] D.omHT σ))
  have hsurjQ : Function.Surjective (P.mkQ ∘ₗ Q) := by
    intro y
    obtain ⟨z, rfl⟩ := P.mkQ_surjective y
    obtain ⟨x, y', hy', h⟩ := hsurj z z.2
    refine ⟨x, ?_⟩
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    refine ⟨-⟨y', hy'⟩, ?_⟩
    apply Subtype.ext
    simp [hQ, h]
  obtain ⟨r, hr⟩ := Module.projective_lifting_property (P.mkQ ∘ₗ Q) P.mkQ hsurjQ
  have hr' : ∀ z : D.omHT σ, ∃ z' : D.omHT σ, Q (r z) = z + ((p : A) ^ m) • z' := by
    intro z
    have := LinearMap.congr_fun hr z
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply] at this
    rw [Submodule.Quotient.eq] at this
    obtain ⟨z', hz'⟩ := this
    refine ⟨z', ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at hz'
    rw [hz']; abel
  have hvec := fun k => HTL.exists_vec D ρ hc hact σ ((LinearMap.proj k) ∘ₗ r)
  choose ev hev hevz using hvec
  let Rr : (Fin N → K) →ₗ[K] Li := Fintype.linearCombination K ev
  have hRr : ∀ x, Rr x = ∑ k, x k • ev k := fun x => by simp [Rr, Fintype.linearCombination_apply]
  have hzL : ∀ e ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom)) 1 (algebraMap A K).range,
      ∀ z : D.omHT σ, (z : Module.Dual K Li) e ∈ (algebraMap A K).range := by
    intro e he z
    obtain ⟨w, hw, hz⟩ := z.2
    have hz' : eigProj D.ρΩ σ w = z := hz
    rw [← hz', eigProj_apply D ρ hc hact σ he.1 w]
    simpa using he.2 w hw
  refine ⟨Rr, fun k => ?_, fun e he => ?_⟩
  · have h1 : Rr (Pi.single k 1) = ev k := by simp [hRr, Pi.single_apply]
    rw [h1]
    refine ⟨hev k, fun w hw => ?_⟩
    rw [one_mul, ← eigProj_apply D ρ hc hact σ (hev k) w]
    exact ⟨_, (hevz k ⟨_, hmemM w hw⟩).symm⟩
  · let x : Fin N → K := fun l => D.h (Pi.single l 1) e
    have hRx : Rr x ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom) := by
      rw [hRr]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hev k)
    have key : ∀ z : D.omHT σ, ∃ z' : D.omHT σ, (z : Module.Dual K Li) (Rr x) =
        (z : Module.Dual K Li) e + (p : K) ^ m * (z' : Module.Dual K Li) e := by
      intro z
      obtain ⟨z', hz'⟩ := hr' z
      refine ⟨z', ?_⟩
      have h1 : (z : Module.Dual K Li) (Rr x) = ∑ k, x k * algebraMap A K (r z k) := by

        rw [hRr, map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_smul, hevz k z]
        rfl
      have h2 : ((Q (r z) : D.omHT σ) : Module.Dual K Li) e = ∑ k, algebraMap A K (r z k) * x k := by
        rw [hQ, HTChart.q, LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [LinearMap.smul_apply, eigProj_apply D ρ hc hact σ he.1, Algebra.smul_def]
      have h3 : ((Q (r z) : D.omHT σ) : Module.Dual K Li) e =
          (z : Module.Dual K Li) e + (p : K) ^ m * (z' : Module.Dual K Li) e := by
        rw [hz']
        simp [Algebra.smul_def]
      rw [h1, ← h3, h2]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    have hsub := Submodule.sub_mem _ hRx he.1
    refine ⟨((p : K) ^ m)⁻¹ • (Rr x - e), ⟨Submodule.smul_mem _ _ hsub, fun w hw => ?_⟩, ?_⟩
    · rw [one_mul, ← eigProj_apply D ρ hc hact σ (Submodule.smul_mem _ _ hsub) w]
      obtain ⟨z', hz'⟩ := key ⟨_, hmemM w hw⟩
      have hval : eigProj D.ρΩ σ w (((p : K) ^ m)⁻¹ • (Rr x - e)) = (z' : Module.Dual K Li) e := by
        rw [map_smul, map_sub]
        have : eigProj D.ρΩ σ w (Rr x) = eigProj D.ρΩ σ w e + (p : K) ^ m * (z' : Module.Dual K Li) e := hz'
        rw [this, add_sub_cancel_left, smul_eq_mul, inv_mul_cancel_left₀ hpm]
      rw [hval]
      exact hzL e he z'
    · rw [smul_smul, mul_inv_cancel₀ hpm, one_smul]
      abel

end GlobalTheory.CompanionTheory.Ar.Flat.HTL
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

theorem kMinor_comp_perm {F : Type} [CommRing F] {n r : ℕ} (A : Matrix (Fin n) (Fin r) F) (k : ℕ)
    (hk : k ≤ r) (I : Fin k → Fin n) (σ : Equiv.Perm (Fin k)) :
    kMinor A k hk (I ∘ σ) = ((Equiv.Perm.sign σ : ℤ) : F) * kMinor A k hk I := by
  unfold kMinor
  have e : A.submatrix (I ∘ σ) (Fin.castLE hk) = (A.submatrix I (Fin.castLE hk)).submatrix σ id := by
    ext a b
    simp
  rw [e, Matrix.det_permute]

theorem normAt_comp_perm {F : Type} [Field F] (O : Subring F) {n r : ℕ} (Y : Matrix (Fin n) (Fin r) F)
    (k : ℕ) (hk : k ≤ r) (I : Fin k → Fin n) (σ : Equiv.Perm (Fin k)) (h : NormAt O Y k hk I) :
    NormAt O Y k hk (I ∘ σ) := by
  obtain ⟨h0, h1⟩ := h
  refine ⟨?_, fun J => ?_⟩
  · rw [kMinor_comp_perm]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · simpa [hs] using h0
    · simpa [hs] using h0
  · rw [kMinor_comp_perm]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · simpa [hs] using h1 J
    · simpa [hs, div_neg] using O.neg_mem (h1 J)

theorem exists_perm_castSucc {k : ℕ} (f : Fin k → Fin (k + 1)) (hf : Function.Injective f) :
    ∃ g : Equiv.Perm (Fin (k + 1)), ∀ a : Fin k, g a.castSucc = f a := by
  classical
  let e : {x // x ∈ Set.range (Fin.castSucc : Fin k → Fin (k + 1))} ≃ {x // x ∈ Set.range f} :=
    (Equiv.ofInjective _ (Fin.castSucc_injective k)).symm.trans (Equiv.ofInjective f hf)
  refine ⟨e.extendSubtype, fun a => ?_⟩
  have h := e.extendSubtype_apply_of_mem a.castSucc ⟨a, rfl⟩
  rw [h]
  have h2 : (Equiv.ofInjective _ (Fin.castSucc_injective k)).symm
      ⟨a.castSucc, ⟨a, rfl⟩⟩ = a := Equiv.ofInjective_symm_apply _ a
  simp only [e, Equiv.trans_apply]
  erw [h2]
  rfl

def castEmb {m n : ℕ} (h : m ≤ n) : Fin m ↪ Fin n := ⟨Fin.castLE h, Fin.castLE_injective h⟩

theorem exists_perm_restrict {m j r : ℕ} (hm : m ≤ j) (hj : j ≤ r) (hmr : m ≤ r)
    (g : Equiv.Perm (Fin m)) :
    ∃ σ : Equiv.Perm (Fin j), ∀ a : Fin j,
      g.viaFintypeEmbedding (castEmb hmr) (Fin.castLE hj a) = Fin.castLE hj (σ a) := by
  classical
  refine ⟨g.viaFintypeEmbedding (castEmb hm), fun a => ?_⟩
  by_cases ha : (a : ℕ) < m
  · have e1 : Fin.castLE hj a = castEmb hmr ⟨a, ha⟩ := by ext; simp [castEmb]
    have e2 : a = castEmb hm ⟨a, ha⟩ := by ext; simp [castEmb]
    rw [e1, Equiv.Perm.viaFintypeEmbedding_apply_image]
    conv_rhs => rw [e2, Equiv.Perm.viaFintypeEmbedding_apply_image]
    ext; simp [castEmb]
  · have n1 : Fin.castLE hj a ∉ Set.range (castEmb hmr) := by
      rintro ⟨b, hb⟩
      have := congrArg Fin.val hb
      have hb2 := b.2
      simp [castEmb] at this
      omega
    have n2 : a ∉ Set.range (castEmb hm) := by
      rintro ⟨b, hb⟩
      have := congrArg Fin.val hb
      have hb2 := b.2
      simp [castEmb] at this
      omega
    rw [Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ n1,
      Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ n2]

theorem exists_perm_top {F : Type} [Field F] (O : Subring F) {r : ℕ} (Y : Matrix (Fin r) (Fin r) F)
    (I : Fin r → Fin r) (h : NormAt O Y r le_rfl I) : ∃ w : Equiv.Perm (Fin r), ⇑w = I := by
  have hinj : Function.Injective I := by
    intro a b hab
    by_contra hne
    refine h.1 ?_
    unfold kMinor
    refine Matrix.det_zero_of_row_eq hne ?_
    ext c
    simp [hab]
  exact ⟨Equiv.ofBijective I (Finite.injective_iff_bijective.1 hinj), rfl⟩

theorem perm_step {F : Type} [Field F] (O : Subring F) {r : ℕ} (Y : Matrix (Fin r) (Fin r) F) (k : ℕ)
    (hk : k + 1 ≤ r) (w : Equiv.Perm (Fin r)) (f : Fin k → Fin (k + 1)) (hf : Function.Injective f)
    (hw : ∀ (j : ℕ) (hj : j ≤ r), k + 1 ≤ j → NormAt O Y j hj (w ∘ Fin.castLE hj))
    (hn : NormAt O Y k (Nat.le_of_succ_le hk) ((w ∘ Fin.castLE hk) ∘ f)) :
    ∃ w' : Equiv.Perm (Fin r), ∀ (j : ℕ) (hj : j ≤ r), k ≤ j → NormAt O Y j hj (w' ∘ Fin.castLE hj) := by
  classical
  obtain ⟨g, hg⟩ := exists_perm_castSucc f hf
  refine ⟨w * g.viaFintypeEmbedding (castEmb hk), fun j hj hkj => ?_⟩
  rcases Nat.eq_or_lt_of_le hkj with rfl | hlt
  · have e : (⇑(w * g.viaFintypeEmbedding (castEmb hk)) ∘ Fin.castLE hj) =
        (w ∘ Fin.castLE hk) ∘ f := by
      funext a
      have e1 : Fin.castLE hj a = castEmb hk a.castSucc := by ext; simp [castEmb]
      simp only [Function.comp_apply, Equiv.Perm.mul_apply]
      rw [e1, Equiv.Perm.viaFintypeEmbedding_apply_image, hg]
      rfl
    rw [e]
    exact hn
  · obtain ⟨σ, hσ⟩ := exists_perm_restrict (m := k + 1) (j := j) hlt hj hk g
    have e : (⇑(w * g.viaFintypeEmbedding (castEmb hk)) ∘ Fin.castLE hj) =
        (w ∘ Fin.castLE hj) ∘ σ := by
      funext a
      simp only [Function.comp_apply, Equiv.Perm.mul_apply]
      rw [hσ]
    rw [e]
    exact normAt_comp_perm O Y j hj _ σ (hw j hj hlt)

theorem exists_perm_normAt {F : Type} [Field F] (O : Subring F) {r : ℕ} (Y : Matrix (Fin r) (Fin r) F)
    (hex : ∀ (k : ℕ) (hk : k + 1 ≤ r) (I' : Fin (k + 1) → Fin r) (I : Fin k → Fin r),
      NormAt O Y (k + 1) hk I' → NormAt O Y k (Nat.le_of_succ_le hk) I →
        ∃ f : Fin k → Fin (k + 1), Function.Injective f ∧
          NormAt O Y k (Nat.le_of_succ_le hk) (I' ∘ f))
    (hall : ∀ (k : ℕ) (hk : k ≤ r), ∃ I : Fin k → Fin r, NormAt O Y k hk I) :
    ∃ w : Equiv.Perm (Fin r), ∀ (k : ℕ) (hk : k ≤ r), NormAt O Y k hk (w ∘ Fin.castLE hk) := by
  have key : ∀ d : ℕ, d ≤ r → ∃ w : Equiv.Perm (Fin r), ∀ (j : ℕ) (hj : j ≤ r), r - d ≤ j →
      NormAt O Y j hj (w ∘ Fin.castLE hj) := by
    intro d
    induction d with
    | zero =>
      intro _
      obtain ⟨I, hI⟩ := hall r le_rfl
      obtain ⟨w, hw⟩ := exists_perm_top O Y I hI
      refine ⟨w, fun j hj hrj => ?_⟩
      have hjr : j = r := le_antisymm hj (by simpa using hrj)
      subst hjr
      have e : (⇑w ∘ Fin.castLE hj) = I := by
        funext a
        simp [hw]
      rw [e]
      exact hI
    | succ d ih =>
      intro hd
      obtain ⟨w, hw⟩ := ih (by omega)
      obtain ⟨k, hkd⟩ : ∃ k, k + 1 = r - d := ⟨r - d - 1, by omega⟩
      have hk : k + 1 ≤ r := by omega
      obtain ⟨I, hI⟩ := hall k (Nat.le_of_succ_le hk)
      obtain ⟨f, hf, hn⟩ := hex k hk (w ∘ Fin.castLE hk) I (hw _ hk (by omega)) hI
      obtain ⟨w', hw'⟩ := perm_step O Y k hk w f hf (fun j hj h => hw j hj (by omega)) hn
      exact ⟨w', fun j hj h => hw' j hj (by omega)⟩
  obtain ⟨w, hw⟩ := key r le_rfl
  exact ⟨w, fun k hk => hw k hk (by omega)⟩

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

theorem exists_lu_of_leading_minors {F : Type} [Field F] {r : ℕ} (Y : Matrix (Fin r) (Fin r) F)
    (h : ∀ (k : ℕ) (hk : k ≤ r), kMinor Y k hk (Fin.castLE hk) ≠ 0) :
    ∃ C V : Matrix (Fin r) (Fin r) F, (∀ l k, k < l → C l k = 0) ∧ (∀ l k, l < k → V l k = 0) ∧
      (∀ l, V l l = 1) ∧ Y * C = V := by
  classical
  let B : ∀ k : Fin r, Matrix (Fin ((k : ℕ) + 1)) (Fin ((k : ℕ) + 1)) F := fun k =>
    Y.submatrix (Fin.castLE k.2) (Fin.castLE k.2)
  have hB : ∀ k, IsUnit (B k).det := fun k => isUnit_iff_ne_zero.2 (h _ k.2)
  let a : ∀ k : Fin r, Fin ((k : ℕ) + 1) → F := fun k =>
    (B k)⁻¹.mulVec (Pi.single (Fin.last _) 1)
  have ha : ∀ k, (B k).mulVec (a k) = Pi.single (Fin.last _) 1 := fun k => by
    simp only [a]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hB k), Matrix.one_mulVec]
  let C : Matrix (Fin r) (Fin r) F := fun l k =>
    if hlk : (l : ℕ) < (k : ℕ) + 1 then a k ⟨l, hlk⟩ else 0
  have hV : ∀ (k : Fin r) (l : Fin ((k : ℕ) + 1)),
      (Y * C) (Fin.castLE k.2 l) k = (Pi.single (Fin.last (k : ℕ)) (1 : F) :
        Fin ((k : ℕ) + 1) → F) l := by
    intro k l
    rw [← ha k]
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    symm
    refine Finset.sum_of_injOn (Fin.castLE k.2) (Fin.castLE_injective _).injOn
      (fun _ _ => Finset.mem_univ _) (fun j _ hj => ?_) (fun b _ => ?_)
    · have hjk : ¬ (j : ℕ) < (k : ℕ) + 1 := fun hlt =>
        hj ⟨⟨j, hlt⟩, by simp, by ext; simp⟩
      simp only [C, dif_neg hjk, mul_zero]
    · have hb : ((Fin.castLE k.2 b : Fin r) : ℕ) < (k : ℕ) + 1 := b.2
      simp only [C, dif_pos hb]
      rfl
  refine ⟨C, Y * C, fun l k hkl => ?_, fun l k hlk => ?_, fun l => ?_, rfl⟩
  · have hn : ¬ (l : ℕ) < (k : ℕ) + 1 := by
      have : (k : ℕ) < l := hkl
      omega
    simp only [C, dif_neg hn]
  · have hlt : (l : ℕ) < (k : ℕ) + 1 := by
      have : (l : ℕ) < k := hlk
      omega
    have h1 := hV k ⟨l, hlt⟩
    have e : Fin.castLE k.2 (⟨l, hlt⟩ : Fin ((k : ℕ) + 1)) = l := by ext; simp
    have hne : (⟨l, hlt⟩ : Fin ((k : ℕ) + 1)) ≠ Fin.last (k : ℕ) := by
      intro hh
      have h2 : (l : ℕ) = k := by simpa using Fin.ext_iff.1 hh
      have : (l : ℕ) < k := hlk
      omega
    rw [e, Pi.single_eq_of_ne hne] at h1
    exact h1
  · have h1 := hV l (Fin.last (l : ℕ))
    have e : Fin.castLE l.2 (Fin.last (l : ℕ)) = l := by ext; simp
    rw [e, Pi.single_eq_same] at h1
    exact h1

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
end
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

theorem det_mem_subring {F : Type} [CommRing F] (D : Subring F) {k : ℕ} (A : Matrix (Fin k) (Fin k) F)
    (hA : ∀ a b, A a b ∈ D) : A.det ∈ D := by
  rw [Matrix.det_apply']
  exact D.sum_mem fun σ _ => D.mul_mem (intCast_mem D _) (D.prod_mem fun a _ => hA _ _)

theorem mul_adjugate_apply_eq_kMinor {F : Type} [Field F] {n r : ℕ} (Y : Matrix (Fin n) (Fin r) F) (m : ℕ)
    (hm : m ≤ r) (J : Fin m → Fin n) (i : Fin n) (j : Fin m) :
    (Y.submatrix id (Fin.castLE hm) * (Y.submatrix J (Fin.castLE hm)).adjugate) i j =
      kMinor Y m hm (Function.update J j i) := by
  classical
  have h1 : (Y.submatrix id (Fin.castLE hm) * (Y.submatrix J (Fin.castLE hm)).adjugate) i j =
      Matrix.cramer (Y.submatrix J (Fin.castLE hm)).transpose (Y.submatrix id (Fin.castLE hm) i) j := by
    rw [Matrix.cramer_eq_adjugate_mulVec, ← Matrix.adjugate_transpose]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  rw [h1, Matrix.cramer_transpose_apply]
  unfold kMinor
  congr 1
  ext a b
  by_cases hab : a = j
  · subst hab
    simp
  · simp [Matrix.updateRow_ne hab, Function.update_of_ne hab]

theorem normAt_mul_inv_mem {F : Type} [Field F] (O : Subring F) {n r : ℕ} (Y : Matrix (Fin n) (Fin r) F)
    (m : ℕ) (hm : m ≤ r) (J : Fin m → Fin n) (hJ : NormAt O Y m hm J) (i : Fin n) (j : Fin m) :
    (Y.submatrix id (Fin.castLE hm) * (Y.submatrix J (Fin.castLE hm))⁻¹) i j ∈ O := by
  classical
  have e : (Y.submatrix id (Fin.castLE hm) * (Y.submatrix J (Fin.castLE hm))⁻¹) i j =
      kMinor Y m hm (Function.update J j i) / kMinor Y m hm J := by
    rw [Matrix.inv_def, Matrix.mul_smul, Matrix.smul_apply, mul_adjugate_apply_eq_kMinor,
      Ring.inverse_eq_inv', smul_eq_mul, div_eq_inv_mul]
    rfl
  rw [e]
  exact hJ.2 _

theorem normAt_exchange {F : Type} [Field F] (O : Subring F) [IsLocalRing O] {n r : ℕ}
    (Y : Matrix (Fin n) (Fin r) F) (k : ℕ) (hk : k + 1 ≤ r) (I' : Fin (k + 1) → Fin n) (I : Fin k → Fin n)
    (h' : NormAt O Y (k + 1) hk I') (h : NormAt O Y k (Nat.le_of_succ_le hk) I) :
    ∃ f : Fin k → Fin (k + 1), Function.Injective f ∧ NormAt O Y k (Nat.le_of_succ_le hk) (I' ∘ f) := by
  classical
  have hk0 : k ≤ r := Nat.le_of_succ_le hk
  have hM' : IsUnit (Y.submatrix I' (Fin.castLE hk)).det := isUnit_iff_ne_zero.2 h'.1
  have hM : IsUnit (Y.submatrix I (Fin.castLE hk0)).det := isUnit_iff_ne_zero.2 h.1
  obtain ⟨Z, hZdef⟩ : ∃ Z, Z = Y.submatrix id (Fin.castLE hk) * (Y.submatrix I' (Fin.castLE hk))⁻¹ := ⟨_, rfl⟩
  obtain ⟨Z', hZ'def⟩ : ∃ Z', Z' = Y.submatrix id (Fin.castLE hk0) * (Y.submatrix I (Fin.castLE hk0))⁻¹ :=
    ⟨_, rfl⟩
  have hZ : ∀ a b, Z a b ∈ O := fun a b => by
    rw [hZdef]; exact normAt_mul_inv_mem O Y _ hk I' h' a b
  have hZ' : ∀ a b, Z' a b ∈ O := fun a b => by
    rw [hZ'def]; exact normAt_mul_inv_mem O Y _ hk0 I h a b
  have e1 : Y.submatrix id (Fin.castLE hk) = Z * Y.submatrix I' (Fin.castLE hk) := by
    rw [hZdef, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hM', Matrix.mul_one]
  have hY0 : Y.submatrix id (Fin.castLE hk0) = Z * (Y.submatrix I' (Fin.castLE hk0)) := by
    ext a b
    have := congrFun (congrFun e1 a) (Fin.castSucc b)
    simpa [Matrix.mul_apply] using this
  have hD : ∀ {m : ℕ} (J : Fin m → Fin n), Z'.submatrix J id =
      Y.submatrix J (Fin.castLE hk0) * (Y.submatrix I (Fin.castLE hk0))⁻¹ := by
    intro m J
    rw [hZ'def]
    ext a b
    simp [Matrix.mul_apply]
  have hZZ : Z' = Z * Z'.submatrix I' id := by
    rw [hD, ← Matrix.mul_assoc, ← hY0, hZ'def]
  have hI : Z'.submatrix I id = 1 := by
    rw [hD, Matrix.mul_nonsing_inv _ hM]
  have hone : Z.submatrix I id * Z'.submatrix I' id = 1 := by
    rw [← hI]
    conv_rhs => rw [hZZ]
    ext a b
    simp [Matrix.mul_apply]
  have hsum := det_mul_expand (Z.submatrix I id) (Z'.submatrix I' id)
  rw [hone, Matrix.det_one] at hsum
  obtain ⟨f, -, hne, hinv⟩ := exists_unit_of_sum_eq_one O Finset.univ _
    (fun f _ => O.mul_mem (O.prod_mem fun a _ => hZ _ _) (det_mem_subring O _ fun a b => hZ' _ _)) hsum.symm
  have hc : (∏ a, (Z.submatrix I id) a (f a)) ≠ 0 := left_ne_zero_of_mul hne
  have hd : ((Z'.submatrix I' id).submatrix f id).det ≠ 0 := right_ne_zero_of_mul hne
  have hdet : ((Z'.submatrix I' id).submatrix f id).det =
      kMinor Y k hk0 (I' ∘ f) / kMinor Y k hk0 I := by
    have e2 : (Z'.submatrix I' id).submatrix f id = Z'.submatrix (I' ∘ f) id := by
      ext a b; simp
    rw [e2, hD, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', div_eq_mul_inv]
    rfl
  have hinj : Function.Injective f := by
    intro a b hab
    by_contra hne'
    exact hd (Matrix.det_zero_of_row_eq hne' (by ext c; simp [hab]))
  refine ⟨f, hinj, ?_, fun I'' => ?_⟩
  · intro h0
    apply hd
    rw [hdet, h0, zero_div]
  · have hP := h.1
    have hQ : kMinor Y k hk0 (I' ∘ f) ≠ 0 := by
      intro h0
      apply hd
      rw [hdet, h0, zero_div]
    have e : kMinor Y k hk0 I'' / kMinor Y k hk0 (I' ∘ f) =
        (kMinor Y k hk0 I'' / kMinor Y k hk0 I) * ((∏ a, (Z.submatrix I id) a (f a)) *
          ((∏ a, (Z.submatrix I id) a (f a)) * ((Z'.submatrix I' id).submatrix f id).det)⁻¹) := by
      rw [hdet]
      field_simp
    rw [e]
    exact O.mul_mem (h.2 I'') (O.mul_mem (O.prod_mem fun a _ => hZ _ _) hinv)

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
end
end

section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

theorem _root_.GlobalTheory.T.number_field_integers_in_integrally_closed : ∀ (A Ω : Type) [CommRing A] [IsDomain A] [Field Ω] [Algebra A Ω] [IsFractionRing A Ω] [IsIntegrallyClosed A] (E : Type) [Field E] [NumberField E] (σ : E →+* Ω) (a : 𝓞 E), σ (a : E) ∈ (algebraMap A Ω).range := by
  first | exact @GlobalTheory.CompanionTheory.Ar.IntEmb.ringOfIntegers_embedding_mem_range | exact GlobalTheory.CompanionTheory.Ar.IntEmb.ringOfIntegers_embedding_mem_range | (intros; apply GlobalTheory.CompanionTheory.Ar.IntEmb.ringOfIntegers_embedding_mem_range <;> assumption)
end
