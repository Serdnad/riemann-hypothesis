module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle126
public import Mathlib.RingTheory.Etale.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle129
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTemperateGrowthProdMkConst
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
public import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.Smooth.Fiber
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Localization.Integral

@[expose] public section

section

open IsLocalRing Polynomial

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TorsorFieldPoint


open IsLocalRing Polynomial in
open scoped TensorProduct in
theorem _root_.GlobalTheory.TorsorFieldPoint.formallyUnramified_of_isZTorsor (B D : Type) [CommRing B] [CommRing D]
    [Algebra B D] (q : ℕ) (hq : 0 < q) (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D))
    (h : _root_.GlobalTheory.KeyOriginCut.IsZTorsor B D q act) : Algebra.FormallyUnramified B D := by
  obtain ⟨-, -, hff, hbij⟩ := h
  haveI : NeZero q := ⟨hq.ne'⟩
  let g : D →ₐ[B] (Multiplicative (ZMod q) → D) :=
    Pi.algHom B (fun _ ↦ D) fun σ ↦ (act σ : D →ₐ[B] D)
  let F : D ⊗[B] D →ₐ[D] (Multiplicative (ZMod q) → D) :=
    Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId D _) g
  have hF : (F : D ⊗[B] D → _) = Algebra.TensorProduct.productMap
      (Pi.algHom B (fun _ ↦ D) fun _ ↦ AlgHom.id B D) g := by
    ext x : 1
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add x y hx hy => simp_all
  have hFb : Function.Bijective F := by rw [hF]; exact hbij
  haveI : Algebra.FormallyUnramified D (Multiplicative (ZMod q) → D) :=
    (Algebra.FormallyUnramified.pi_iff _).2 fun _ ↦ inferInstance
  haveI : Algebra.FormallyUnramified D (D ⊗[B] D) :=
    Algebra.FormallyUnramified.of_equiv (AlgEquiv.ofBijective F hFb).symm
  exact Algebra.FormallyUnramified.of_formallyUnramified_tensorProduct_of_faithfullyFlat D


open IsLocalRing Polynomial in
open scoped TensorProduct in
theorem _root_.GlobalTheory.TorsorFieldPoint.exists_point_finite_separable : ∀ (B K : Type) [CommRing B] [Field K]
    (f : B →+* K) (D : Type) [CommRing D] [Algebra B D]
    (q : ℕ), 0 < q → ∀ (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)),
    _root_.GlobalTheory.KeyOriginCut.IsZTorsor B D q act →
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : Algebra.IsSeparable K L)
      (σ : D →+* L), σ.comp (algebraMap B D) = (algebraMap K L).comp f := by
  intro B K _ _ f D _ _ q hq act h
  haveI := _root_.GlobalTheory.TorsorFieldPoint.formallyUnramified_of_isZTorsor B D q hq act h
  obtain ⟨hfin, -, hff, -⟩ := h
  letI : Algebra B K := f.toAlgebra
  haveI : Nontrivial (K ⊗[B] D) := Module.FaithfullyFlat.rTensor_nontrivial B D K
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[B] D)
  letI : Field (K ⊗[B] D ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite K (K ⊗[B] D ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K m).toLinearMap Ideal.Quotient.mk_surjective
  haveI : Algebra.FormallyUnramified K (K ⊗[B] D ⧸ m) :=
    Algebra.FormallyUnramified.of_surjective (Ideal.Quotient.mkₐ K m) Ideal.Quotient.mk_surjective
  refine ⟨K ⊗[B] D ⧸ m, inferInstance, inferInstance, inferInstance,
    Algebra.FormallyUnramified.isSeparable K _,
    (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeRight.toRingHom, ?_⟩
  ext b
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply, Ideal.Quotient.algebraMap_eq]
  rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  rfl

end GlobalTheory.TorsorFieldPoint
end
end

section

open IsLocalRing Polynomial

open scoped TensorProduct

namespace GlobalTheory.KeyOriginCut

theorem etale_of_isZTorsor (B D : Type) [CommRing B] [CommRing D] [Algebra B D] (q : ℕ)
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)) (h : IsZTorsor B D q act) :
    Algebra.Etale B D := by
  obtain ⟨hfin, hproj, hff, hbij⟩ := h
  set Φ := Algebra.TensorProduct.productMap
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id B D))
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom)) with hΦ
  have hmul : ∀ x : D ⊗[B] D, Algebra.TensorProduct.lmul' B x = Φ x 1 := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [hΦ, Algebra.TensorProduct.productMap_apply_tmul]
    | add x y hx hy => simp [map_add (f := _), hx, hy]
  have hidem : IsIdempotentElem (KaehlerDifferential.ideal B D) := by
    obtain ⟨e, he⟩ := hbij.2 (1 - Pi.single (1 : Multiplicative (ZMod q)) (1 : D))
    have heI : e ∈ KaehlerDifferential.ideal B D := by
      rw [KaehlerDifferential.ideal, RingHom.mem_ker]
      change Algebra.TensorProduct.lmul' B e = 0
      rw [hmul, he]; simp
    apply le_antisymm Ideal.mul_le_left
    intro x hx
    have hx0 : Φ x 1 = 0 := by
      rw [← hmul]
      exact (RingHom.mem_ker).1 hx
    have hxe : x = x * e := by
      apply hbij.1
      rw [map_mul, he]
      funext g
      by_cases hg : g = 1
      · subst hg; simp [hx0]
      · simp [Pi.single_apply, hg]
    rw [hxe]
    exact Ideal.mul_mem_mul hx heI
  haveI : Subsingleton Ω[D⁄B] := (Ideal.cotangent_subsingleton_iff _).2 hidem
  haveI : Algebra.FormallyUnramified B D := ⟨inferInstance⟩
  haveI : Module.Flat B D := inferInstance
  haveI : Module.FinitePresentation B D := Module.finitePresentation_of_projective B D
  haveI : Algebra.FinitePresentation B D :=
    (Module.FinitePresentation.iff_finitePresentation_of_finite B D).mp inferInstance
  exact Algebra.Etale.of_formallyUnramified_of_flat

end GlobalTheory.KeyOriginCut
end

section

open IsLocalRing

namespace GlobalTheory.AbhyankarLocal

open TensorProduct



theorem exists_kummer_element (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L]
    [IsScalarTower S K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ)
    (D : Type) [CommRing D] [Algebra S D]
    (ψ : D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial S)) :
    Irreducible π → 0 < e → ∀ [IsDomain D] [IsDiscreteValuationRing D]
    (Q : Ideal (integralClosure D (TensorProduct S D L))) [Q.IsMaximal] (m k : ℕ)
    (ϖ : Localization.AtPrime (Q.comap (GlobalTheory.AbhyankarLocal.toNorm S L D)))
    (u : (Localization.AtPrime (Q.comap (GlobalTheory.AbhyankarLocal.toNorm S L D)))ˣ), m * k = e →
    algebraMap S _ π = ϖ ^ m *
      (u : Localization.AtPrime (Q.comap (GlobalTheory.AbhyankarLocal.toNorm S L D))) →
    ∃ y : Localization.AtPrime Q, y ^ m = GlobalTheory.AbhyankarLocal.locHom Q u ∧
      (algebraMap D (Localization.AtPrime Q)
        (ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S)))) ^ k =
        GlobalTheory.AbhyankarLocal.locHom Q ϖ * y := by
  intro hπ he _ _ Q _ m k ϖ u hmk hrel
  generalize hU : (u : Localization.AtPrime (Q.comap (toNorm S L D))) = U at hrel ⊢
  have hm : m ≠ 0 := by rintro rfl; simp at hmk; omega
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  set t := ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S)) with ht_def
  have ht : t ^ e = algebraMap S D π := by
    have h0 := AdjoinRoot.eval₂_root (Polynomial.X ^ e - Polynomial.C π : Polynomial S)
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C] at h0
    have h1 : AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S) ^ e =
        algebraMap S (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial S)) π := by
      rw [AdjoinRoot.algebraMap_eq]; exact sub_eq_zero.mp h0
    have := congrArg ψ.symm h1
    rw [map_pow, AlgEquiv.commutes] at this
    exact this
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.mk'_surjective (Q.comap (toNorm S L D)).primeCompl ϖ
  obtain ⟨⟨a', s'⟩, hs'⟩ := IsLocalization.mk'_surjective (Q.comap (toNorm S L D)).primeCompl
    U
  simp only at hs hs'
  have hsA : ϖ * algebraMap _ (Localization.AtPrime (Q.comap (toNorm S L D))) (s : integralClosure S L) =
      algebraMap _ _ a := by rw [← hs]; exact IsLocalization.mk'_spec _ a s
  have hs'A : U *
      algebraMap _ (Localization.AtPrime (Q.comap (toNorm S L D))) (s' : integralClosure S L) =
      algebraMap _ _ a' := by rw [← hs']; exact IsLocalization.mk'_spec _ a' s'
  have hinj : Function.Injective (algebraMap (integralClosure S L)
      (Localization.AtPrime (Q.comap (toNorm S L D)))) :=
    IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors (Q.comap (toNorm S L D)))
  have hO : algebraMap S (integralClosure S L) π * (s : integralClosure S L) ^ (n + 1) *
      (s' : integralClosure S L) = a ^ (n + 1) * a' := by
    apply hinj
    rw [map_mul, map_mul, map_pow, map_mul, map_pow, ← IsScalarTower.algebraMap_apply, hrel,
      ← hsA, ← hs'A]
    ring
  have hL := congrArg (fun x : integralClosure S L => (x : L)) hO
  simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_algebraMap] at hL
  have hSL : Function.Injective (algebraMap S L) := by
    rw [IsScalarTower.algebraMap_eq S K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective S K)
  have hπL : algebraMap S L π ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap S L)]; exact fun h => hπ.ne_zero (hSL h)
  have hne : ∀ x : (Q.comap (toNorm S L D)).primeCompl, ((x : integralClosure S L) : L) ≠ 0 := by
    intro x hx
    apply x.2
    have : (x : integralClosure S L) = 0 := Subtype.ext hx
    rw [this]; exact Ideal.zero_mem _
  have haL : (a : L) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (Nat.succ_ne_zero n), zero_mul] at hL
    exact mul_ne_zero (mul_ne_zero hπL (pow_ne_zero _ (hne s))) (hne s') hL
  set w : TensorProduct S D L := (t ^ k) ⊗ₜ[S] (((s' : integralClosure S L) : L) *
    ((s : integralClosure S L) : L) / (a : L)) with hw
  have hwm : w ^ (n + 1) = ((toNorm S L D ((s' : integralClosure S L) ^ n * a') :
      integralClosure D (TensorProduct S D L)) : TensorProduct S D L) := by
    rw [toNorm_coe, hw, Algebra.TensorProduct.tmul_pow, ← pow_mul, mul_comm k, hmk, ht,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.smul_def]
    congr 1
    push_cast
    rw [div_pow, mul_div_assoc', div_eq_iff (pow_ne_zero _ haL)]
    linear_combination ((s' : integralClosure S L) : L) ^ n * hL
  have hwint : IsIntegral D w := IsIntegral.of_pow (Nat.succ_pos n)
    (by rw [hwm]; exact (toNorm S L D _).2)
  let b : integralClosure D (TensorProduct S D L) := ⟨w, hwint⟩
  have hbm : b ^ (n + 1) = toNorm S L D ((s' : integralClosure S L) ^ n * a') :=
    Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hwm)
  have hbrel : toNorm S L D a * b = toNorm S L D ((s : integralClosure S L) * s') *
      algebraMap D (integralClosure D (TensorProduct S D L)) (t ^ k) := by
    apply Subtype.ext
    rw [MulMemClass.coe_mul, MulMemClass.coe_mul, toNorm_coe, toNorm_coe, Subalgebra.coe_algebraMap,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    show ((1 : D) ⊗ₜ[S] (a : L)) * w = _
    rw [hw, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    congr 1
    push_cast
    rw [mul_comm (a : L), div_mul_cancel₀ _ haL]
    ring
  have hσ : toNorm S L D (s' : integralClosure S L) ∈ Q.primeCompl := s'.2
  have hσ2 : toNorm S L D (s : integralClosure S L) ∈ Q.primeCompl := s.2
  obtain ⟨y, hy⟩ : ∃ y : Localization.AtPrime Q,
      y * algebraMap _ (Localization.AtPrime Q) (toNorm S L D s') = algebraMap _ _ b :=
    ⟨_, IsLocalization.mk'_spec _ b (⟨_, hσ⟩ : Q.primeCompl)⟩
  have hu1 : IsUnit (algebraMap _ (Localization.AtPrime Q) (toNorm S L D s')) :=
    IsLocalization.map_units _ (⟨_, hσ⟩ : Q.primeCompl)
  have hu2 : IsUnit (algebraMap _ (Localization.AtPrime Q) (toNorm S L D s)) :=
    IsLocalization.map_units _ (⟨_, hσ2⟩ : Q.primeCompl)
  have hϖW : locHom Q ϖ * algebraMap _ (Localization.AtPrime Q) (toNorm S L D s) =
      algebraMap _ _ (toNorm S L D a) := by
    have := congrArg (locHom Q) hsA
    rw [map_mul, locHom_algebraMap Q (s : integralClosure S L), locHom_algebraMap Q a] at this
    exact this
  have huW : locHom Q U *
      algebraMap _ (Localization.AtPrime Q) (toNorm S L D s') =
      algebraMap _ _ (toNorm S L D a') := by
    have := congrArg (locHom Q) hs'A
    rw [map_mul, locHom_algebraMap Q (s' : integralClosure S L), locHom_algebraMap Q a'] at this
    exact this
  refine ⟨y, ?_, ?_⟩
  · rw [← (hu1.pow (n + 1)).mul_left_inj, ← mul_pow, hy, ← map_pow, hbm, pow_succ'
      (algebraMap _ (Localization.AtPrime Q) (toNorm S L D s')), ← mul_assoc, huW]
    simp only [map_mul, map_pow]
    ring
  · rw [← (hu1.mul hu2).mul_left_inj]
    calc _ = algebraMap _ (Localization.AtPrime Q) (toNorm S L D ((s : integralClosure S L) * s') *
          algebraMap D (integralClosure D (TensorProduct S D L)) (t ^ k)) := by
          simp only [map_mul, map_pow, ← IsScalarTower.algebraMap_apply]
          ring
      _ = algebraMap _ (Localization.AtPrime Q) (toNorm S L D a * b) := by rw [hbrel]
      _ = (locHom Q ϖ * algebraMap _ (Localization.AtPrime Q) (toNorm S L D s)) *
          (y *
            algebraMap _ (Localization.AtPrime Q) (toNorm S L D s')) := by
          rw [hϖW, hy, map_mul]
      _ = _ := by ring

end GlobalTheory.AbhyankarLocal
end

section

open IsLocalRing

namespace GlobalTheory.AbhyankarLocal


theorem exists_frac_closure : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D] (ψ : D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial S)), Irreducible π → 0 < e → ∀ [IsDomain D] [IsDiscreteValuationRing D] (Q : Ideal (integralClosure D (TensorProduct S D L))) [Q.IsMaximal] (w : Localization.AtPrime Q), ∃ x z : Localization.AtPrime Q, x ∈ Subring.closure (Set.range (GlobalTheory.AbhyankarLocal.locHom Q) ∪ {algebraMap D (Localization.AtPrime Q) (ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S)))}) ∧ z ∈ Subring.closure (Set.range (GlobalTheory.AbhyankarLocal.locHom Q) ∪ {algebraMap D (Localization.AtPrime Q) (ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S)))}) ∧ z ∈ nonZeroDivisors (Localization.AtPrime Q) ∧ z * w = x := by
  intro S K L _ _ _ _ _ _ _ _ _ _ _ _ π e D _ _ ψ _ _ _ _ Q _ w

  have hS : ∀ r : S, algebraMap D (Localization.AtPrime Q) (algebraMap S D r) =
      locHom Q (algebraMap _ _ (algebraMap S (integralClosure S L) r)) := by
    intro r
    rw [locHom_algebraMap, IsScalarTower.algebraMap_apply D (integralClosure D (TensorProduct S D L))
      (Localization.AtPrime Q)]
    congr 1
    apply Subtype.ext
    simp only [toNorm_coe, Subalgebra.coe_algebraMap, Algebra.TensorProduct.algebraMap_apply]
    rw [Algebra.algebraMap_eq_smul_one r, Algebra.algebraMap_eq_smul_one r]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    rw [TensorProduct.smul_tmul]
  have hD : ∀ d : D, algebraMap D (Localization.AtPrime Q) d ∈ Subring.closure (Set.range (GlobalTheory.AbhyankarLocal.locHom Q) ∪ {algebraMap D (Localization.AtPrime Q) (ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S)))}) := by
    intro d
    rw [← ψ.symm_apply_apply d]
    generalize ψ d = a
    have hd : a ∈ Algebra.adjoin S ({AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S)} : Set _) := by
      rw [AdjoinRoot.adjoinRoot_eq_top]; trivial
    induction hd using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Subring.subset_closure (Or.inr rfl)
    | algebraMap r =>
      rw [AlgEquiv.commutes, hS]
      exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)
    | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _)]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul, map_mul]; exact mul_mem hx hy

  have hT : ∀ u : TensorProduct S D (integralClosure S L), ∃ b : integralClosure D (TensorProduct S D L),
      (b : TensorProduct S D L) = Algebra.TensorProduct.map (AlgHom.id S D) (integralClosure S L).val u ∧
      algebraMap _ (Localization.AtPrime Q) b ∈ Subring.closure (Set.range (GlobalTheory.AbhyankarLocal.locHom Q) ∪ {algebraMap D (Localization.AtPrime Q) (ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S)))}) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp, by simp⟩
    | tmul d o =>
      refine ⟨algebraMap D _ d * toNorm S L D o, ?_, ?_⟩
      · simp [toNorm_coe, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
      · rw [map_mul, ← IsScalarTower.algebraMap_apply, ← locHom_algebraMap]
        exact mul_mem (hD d) (Subring.subset_closure (Or.inl ⟨_, rfl⟩))
    | add u v hu hv =>
      obtain ⟨b1, h1, m1⟩ := hu
      obtain ⟨b2, h2, m2⟩ := hv
      exact ⟨b1 + b2, by simp [h1, h2], by rw [(algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)).map_add]; exact add_mem m1 m2⟩
  have hI : ∀ y : TensorProduct S D L, ∃ σ : S, σ ≠ 0 ∧ ∃ u : TensorProduct S D (integralClosure S L),
      Algebra.TensorProduct.map (AlgHom.id S D) (integralClosure S L).val u = σ • y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
    | tmul d l =>
      have hl : IsAlgebraic S l := (IsFractionRing.isAlgebraic_iff S K L).2 (Algebra.IsAlgebraic.isAlgebraic l)
      obtain ⟨σ, hσ, hint⟩ := hl.exists_integral_multiple
      exact ⟨σ, hσ, d ⊗ₜ ⟨σ • l, hint⟩, by simp [TensorProduct.tmul_smul]⟩
    | add y1 y2 h1 h2 =>
      obtain ⟨σ1, n1, u1, e1⟩ := h1
      obtain ⟨σ2, n2, u2, e2⟩ := h2
      refine ⟨σ1 * σ2, mul_ne_zero n1 n2, σ2 • u1 + σ1 • u2, ?_⟩
      rw [map_add (f := _), map_smul, map_smul, e1, e2, smul_add, smul_smul, smul_smul, mul_comm σ1 σ2]
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl w
  obtain ⟨σ1, n1, u1, e1⟩ := hI (b : TensorProduct S D L)
  obtain ⟨σ2, n2, u2, e2⟩ := hI ((s : integralClosure D (TensorProduct S D L)) : TensorProduct S D L)
  obtain ⟨bb, hbb, mb⟩ := hT (σ2 • u1)
  obtain ⟨ss, hss, ms⟩ := hT (σ1 • u2)
  set a : integralClosure D (TensorProduct S D L) := algebraMap D _ (algebraMap S D (σ1 * σ2)) with ha
  have hcoe : ∀ y : integralClosure D (TensorProduct S D L), ((a * y : integralClosure D (TensorProduct S D L)) : TensorProduct S D L) = (σ1 * σ2) • (y : TensorProduct S D L) := by
    intro y
    rw [ha, Subalgebra.coe_mul, Subalgebra.coe_algebraMap, ← IsScalarTower.algebraMap_apply, Algebra.smul_def]
  have hbb' : bb = a * b := by
    apply Subtype.ext
    rw [hcoe, hbb, map_smul, e1, smul_smul, mul_comm σ2 σ1]
  have hss' : ss = a * s := by
    apply Subtype.ext
    rw [hcoe, hss, map_smul, e2, smul_smul]
  have hL : algebraMap S L (σ1 * σ2) ≠ 0 := by
    intro h
    rw [IsScalarTower.algebraMap_apply S K L, map_eq_zero, IsFractionRing.to_map_eq_zero_iff] at h
    exact mul_ne_zero n1 n2 h
  have hU : IsUnit (algebraMap S (TensorProduct S D L) (σ1 * σ2)) := by
    rw [← (Algebra.TensorProduct.includeRight (R := S) (A := D) (B := L)).commutes]
    exact (IsUnit.mk0 _ hL).map _
  have haN : a ∈ nonZeroDivisors (integralClosure D (TensorProduct S D L)) := by
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    have := congrArg Subtype.val hy
    rw [mul_comm, hcoe, Algebra.smul_def, ZeroMemClass.coe_zero] at this
    exact Subtype.ext (by simpa using (hU.mul_right_eq_zero).1 this)
  refine ⟨algebraMap _ _ bb, algebraMap _ _ ss, mb, ms, ?_, ?_⟩
  · rw [hss', map_mul]
    have h1 : algebraMap _ (Localization.AtPrime Q) a ∈ nonZeroDivisors (Localization.AtPrime Q) :=
      IsLocalization.map_nonZeroDivisors_le Q.primeCompl (Localization.AtPrime Q)
        (Submonoid.mem_map_of_mem (algebraMap _ (Localization.AtPrime Q)) haN)
    exact mul_mem h1 (IsLocalization.map_units (Localization.AtPrime Q) s).mem_nonZeroDivisors
  · rw [hss', hbb', map_mul, map_mul, mul_assoc, IsLocalization.mk'_spec']

end GlobalTheory.AbhyankarLocal
end

section

open scoped SchwartzMap ContDiff
open GlobalTheory.SchwartzFstOp

namespace GlobalTheory.SchwartzFstOp

theorem norm_iteratedFDeriv_sliceCLM_le {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V'] (f : 𝓢(V × V', ℂ)) (x' : V') (n : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ n (sliceCLM x' f) x‖ ≤ ‖iteratedFDeriv ℝ n f (x, x')‖ := by
  have e : (⇑(sliceCLM x' f) : V → ℂ) =
      (fun q => f (q + ((0 : V), x'))) ∘ (ContinuousLinearMap.inl ℝ V V') := by
    funext y; simp
  have hc : ContDiff ℝ n (fun q : V × V' => f (q + ((0 : V), x'))) :=
    ((f.smooth ⊤).comp (contDiff_id.add contDiff_const)).of_le (by exact_mod_cast le_top)
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right _ hc _ le_rfl, iteratedFDeriv_comp_add_right]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have h1 : ∏ _i : Fin n, ‖ContinuousLinearMap.inl ℝ V V'‖ ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => ContinuousLinearMap.norm_inl_le_one ℝ V V')
  have h2 : (ContinuousLinearMap.inl ℝ V V') x + ((0 : V), x') = (x, x') := by simp
  rw [h2]
  exact (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)).trans (le_of_eq (mul_one _))

theorem norm_pow_mul_seminorm_sliceCLM_le {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V'] (f : 𝓢(V × V', ℂ)) (x' : V') (j k n : ℕ) :
    ‖x'‖ ^ k * SchwartzMap.seminorm ℂ j n (sliceCLM x' f) ≤ SchwartzMap.seminorm ℂ (j + k) n f := by
  set M := SchwartzMap.seminorm ℂ (j + k) n f
  have hM : 0 ≤ M := apply_nonneg _ _
  have hpt : ∀ x : V, ‖x'‖ ^ k * (‖x‖ ^ j * ‖iteratedFDeriv ℝ n (sliceCLM x' f) x‖) ≤ M := by
    intro x
    have hw : ‖x'‖ ^ k * ‖x‖ ^ j ≤ ‖(x, x')‖ ^ (j + k) := by
      rw [pow_add, mul_comm]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (norm_fst_le (x, x')) _)
        (pow_le_pow_left₀ (norm_nonneg _) (norm_snd_le (x, x')) _) (by positivity) (by positivity)
    calc ‖x'‖ ^ k * (‖x‖ ^ j * ‖iteratedFDeriv ℝ n (sliceCLM x' f) x‖)
        = (‖x'‖ ^ k * ‖x‖ ^ j) * ‖iteratedFDeriv ℝ n (sliceCLM x' f) x‖ := by ring
      _ ≤ ‖(x, x')‖ ^ (j + k) * ‖iteratedFDeriv ℝ n f (x, x')‖ :=
          mul_le_mul hw (norm_iteratedFDeriv_sliceCLM_le f x' n x) (norm_nonneg _) (by positivity)
      _ ≤ M := SchwartzMap.le_seminorm ℂ (j + k) n f (x, x')
  rcases eq_or_lt_of_le (pow_nonneg (norm_nonneg x') k : (0 : ℝ) ≤ ‖x'‖ ^ k) with h0 | hpos
  · rw [← h0, zero_mul]; exact hM
  · rw [mul_comm, ← le_div_iff₀ hpos]
    refine SchwartzMap.seminorm_le_bound ℂ j n _ (div_nonneg hM hpos.le) (fun x => ?_)
    rw [le_div_iff₀ hpos, mul_comm]
    exact hpt x

end GlobalTheory.SchwartzFstOp
end

end

section

@[expose] public section

open scoped SchwartzMap ContDiff
open GlobalTheory.SchwartzFstOp

theorem _root_.GlobalTheory.T.schwartz_slice_seminorm_le : ∀ {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V'] [NormedSpace ℝ V'] (f : 𝓢(V × V', ℂ)) (x' : V') (j k n : ℕ), ‖x'‖ ^ k * SchwartzMap.seminorm ℂ j n (sliceCLM x' f) ≤ SchwartzMap.seminorm ℂ (j + k) n f := by
  first | exact @GlobalTheory.SchwartzFstOp.norm_pow_mul_seminorm_sliceCLM_le | exact GlobalTheory.SchwartzFstOp.norm_pow_mul_seminorm_sliceCLM_le | (intros; apply GlobalTheory.SchwartzFstOp.norm_pow_mul_seminorm_sliceCLM_le <;> assumption)

end
end
