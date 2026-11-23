module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle415
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle266
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AevalSurjectiveOfSpanCotangent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle277
public import Mathlib.Algebra.Azumaya.Defs
public import Mathlib.Algebra.Central.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle170
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOrderTensorPadicIsAzumayaAlmostAll
import GroundTheory.Brauer.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle280
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle284
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle419
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle310
public import Mathlib.FieldTheory.IsSepClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisLocallyConstantTupleRingTensorPowerUnivers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle327
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle339
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle420
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle421
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOneTraceOpenFiniteAdeleRing
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.zmodTorsor_baseChange_transport_point : ∀ (A A₁ R R₁ : Type) [CommRing A] [CommRing A₁] [IsDomain A₁] [CommRing R] [Algebra A R]
    [CommRing R₁] [Algebra A₁ R₁] (j : A →+* A₁) (γ : R →+* R₁) (ρ : R →+* A) (ρ₁ : R₁ →+* A₁)
    (β : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib A₁ R₁),
    β.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) = (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp γ →
    ρ₁.comp (algebraMap A₁ R₁) = RingHom.id A₁ →
    ρ₁.comp γ = j.comp ρ →
    ∀ (q : ℕ), 0 < q → ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A R) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A R] DA)),
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A R) DA q actA →
    ∃ (DA₁ : Type) (_ : CommRing DA₁) (_ : Algebra (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA₁)
      (actA₁ : Multiplicative (ZMod q) →* (DA₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib A₁ R₁] DA₁)) (h : DA →+* DA₁),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA₁ q actA₁ ∧
      h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A R) DA) = (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA₁).comp β ∧
      ∀ σ : DA →+* FractionRing A₁,
        (σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A R) DA)).comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) =
          (algebraMap A₁ (FractionRing A₁)).comp (j.comp ρ) →
        ∃ σ₁ : DA₁ →+* FractionRing A₁,
          (σ₁.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA₁)).comp (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)) =
            (algebraMap A₁ (FractionRing A₁)).comp ρ₁ := by
  first | (exact @GlobalTheory.KeyOriginCut.torsor_baseChange_point) | (exact GlobalTheory.KeyOriginCut.torsor_baseChange_point) | (intros; apply GlobalTheory.KeyOriginCut.torsor_baseChange_point  <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.FrobKerDim

theorem finrank_quot_frobKerIdeal_le : ∀ (q : ℕ) (K H : Type) [Field K] [CommRing H] [Bialgebra K H]
    [Module.Finite K H], 0 < q →
    Module.finrank K (H ⧸ frobKerIdeal q K H) ≤ q ^ Module.finrank K (Cot K H) := by
  intro q K H _ _ _ _ hq
  classical
  set J := frobKerIdeal q K H with hJ
  set ε := Bialgebra.counitAlgHom K H with hε
  set mk := Ideal.Quotient.mkₐ K J with hmk
  have hJI : ∀ a ∈ J, ε a = 0 := fun a ha => frobKerIdeal_le_augIdeal hq.ne' K H ha
  set εQ : (H ⧸ J) →ₐ[K] K := Ideal.Quotient.liftₐ J ε hJI with hεQ
  have hεQmk : ∀ a, εQ (mk a) = ε a := fun a => rfl
  have hmks : Function.Surjective mk := Ideal.Quotient.mkₐ_surjective K J
  haveI hfinQ : Module.Finite K (H ⧸ J) := Module.Finite.of_surjective mk.toLinearMap hmks
  haveI : IsNoetherianRing (H ⧸ J) := isNoetherian_of_tower K inferInstance

  have hkerQ : ∀ z ∈ RingHom.ker εQ, ∃ a ∈ RingHom.ker ε, mk a = z := by
    intro z hz
    obtain ⟨a, rfl⟩ := hmks z
    refine ⟨a, ?_, rfl⟩
    rw [RingHom.mem_ker] at hz ⊢
    rw [← hεQmk]; exact hz
  have hpowQ : ∀ z ∈ RingHom.ker εQ, z ^ q = 0 := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := hkerQ z hz
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_frobKerIdeal ha)
  have hnil : IsNilpotent (RingHom.ker εQ) := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    intro f hf
    exact ⟨q, hpowQ f hf⟩

  haveI : Module.Finite K (AugCot ε) := Module.Finite.of_surjective _ (AugCot.d_surjective ε)
  set d := Module.finrank K (AugCot ε) with hd
  let b := Module.finBasis K (AugCot ε)
  choose x hx using fun i => (RingHom.ker ε).toCotangent_surjective (b i)
  have hsum : ∀ l : Fin d → K, AugCot.d ε (∑ i, l i • (x i : H)) = ∑ i, l i • b i := by
    intro l

    simp [map_sum, hx]
  have hmem : ∀ l : Fin d → K, (∑ i, l i • (x i : H)) ∈ RingHom.ker ε := by
    intro l
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (x i).2
  have hspanH : ∀ a ∈ RingHom.ker ε, ∃ l : Fin d → K, a - ∑ i, l i • (x i : H) ∈ RingHom.ker ε ^ 2 := by
    intro a ha
    refine ⟨b.repr (AugCot.d ε a), ?_⟩
    have h1 : AugCot.d ε (a - ∑ i, b.repr (AugCot.d ε a) i • (x i : H)) = 0 := by
      rw [map_sub, hsum, b.sum_repr, sub_self]
    rwa [AugCot.d_of_mem _ (sub_mem ha (hmem _)), Ideal.toCotangent_eq_zero] at h1
  let y : Fin d → H ⧸ J := fun i => mk (x i)
  have hy : ∀ i, y i ∈ RingHom.ker εQ := fun i => by
    rw [RingHom.mem_ker, hεQmk]; exact (x i).2
  have hmapI : Ideal.map mk (RingHom.ker ε) ≤ RingHom.ker εQ := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker]
    exact ha
  have hspan : ∀ z ∈ RingHom.ker εQ, ∃ l : Fin d → K, z - ∑ i, l i • y i ∈ RingHom.ker εQ ^ 2 := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := hkerQ z hz
    obtain ⟨l, hl⟩ := hspanH a ha
    refine ⟨l, ?_⟩
    have h1 : mk (a - ∑ i, l i • (x i : H)) ∈ Ideal.map mk (RingHom.ker ε ^ 2) :=
      Ideal.mem_map_of_mem _ hl
    rw [Ideal.map_pow] at h1
    have h2 := Ideal.pow_right_mono hmapI 2 h1

    simpa [y, map_sub, map_sum, map_smul] using h2
  have hsurj := GlobalTheory.HeightOneHopf.aeval_surjective_of_span_cotangent εQ hnil y hy hspan
  have hyq : ∀ i, y i ^ q = 0 := fun i => hpowQ _ (hy i)

  let mon : (Fin d → Fin q) → H ⧸ J := fun e => ∏ i, y i ^ (e i : ℕ)
  have htop : Submodule.span K (Set.range mon) = ⊤ := by
    have hall : ∀ P : MvPolynomial (Fin d) K, MvPolynomial.aeval y P ∈ Submodule.span K (Set.range mon) := by
      intro P
      induction P using MvPolynomial.induction_on' with
      | monomial u a =>
        rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _),
          ← Algebra.smul_def]
        refine Submodule.smul_mem _ _ ?_
        by_cases h : ∀ i, u i < q
        · exact Submodule.subset_span ⟨fun i => ⟨u i, h i⟩, rfl⟩
        · push_neg at h
          obtain ⟨i, hi⟩ := h
          have h0 : y i ^ u i = 0 := pow_eq_zero_of_le hi (hyq i)
          rw [Finset.prod_eq_zero (i := i) (Finset.mem_univ i) h0]
          exact Submodule.zero_mem _
      | add P Q hP hQ => rw [map_add (f := _)]; exact Submodule.add_mem _ hP hQ
    refine eq_top_iff.2 fun z _ => ?_
    obtain ⟨P, rfl⟩ := hsurj z
    exact hall P
  have h1 := finrank_range_le_card (R := K) (b := mon)
  rw [Set.finrank, htop, finrank_top] at h1
  simpa [Fintype.card_fun, Fintype.card_fin] using h1

end GlobalTheory.FrobKerDim
end
end

section

open scoped TensorProduct
open GlobalTheory.LKInvGood
open GlobalTheory.LocAzumaya Module in

theorem _root_.GlobalTheory.T.localOrderTensorPadic_isAzumaya_almost_all : ∀ (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] [Algebra ℚ B]
    [IsScalarTower ℚ F B] [Algebra.IsCentral F B] [IsSimpleRing B] [FiniteDimensional F B]
    (Λ : Subring B) (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ),
    Module.Finite ℤ Λ → (∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ Λ) →
    ∃ N : ℕ, 0 < N ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ N →
      letI := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ;
      IsAzumaya (cenOrder ℓ F) (locOrder ℓ Λ) := by
  intro F B _ _ _ _ _ _ _ _ _ Λ hΛ hfin hspan
  classical
  have hlocalBasis : ∀ (ι : Type) [Fintype ι] (e : Module.Basis ι F B), (∀ i, e i ∈ Λ) →
      ∃ D : ℕ, 0 < D ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ D →
        letI := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ;
        ∃ f : Module.Basis ι (cenOrder ℓ F) (locOrder ℓ Λ),
          (∀ i, (f i : ℚ_[ℓ] ⊗[ℚ] B) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e i) ∧
          ∀ (y : locOrder ℓ Λ) (b : B), (y : ℚ_[ℓ] ⊗[ℚ] B) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b →
            ∀ k, ((f.repr y k : cenOrder ℓ F) : ℚ_[ℓ] ⊗[ℚ] F) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e.repr b k := by
    intro ι _ e he
    obtain ⟨D, hD, hDint⟩ := exists_den_coords F B Λ hfin ι e
    refine ⟨D, hD, fun ℓ _ hℓ => ?_⟩
    let _ := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ
    have hco : ∀ x ∈ Λ, ∀ k, (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e.repr x k ∈ cenOrder ℓ F :=
      fun x hx k => GlobalTheory.SepModel.tmul_mem_cenOrder ℓ hℓ (hDint x hx k)
    have hv : ∀ i, (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e i ∈ locOrder ℓ Λ := fun i => Algebra.subset_adjoin ⟨_, he i, rfl⟩
    let v : ι → locOrder ℓ Λ := fun i => ⟨_, hv i⟩
    have hsmul : ∀ (c : cenOrder ℓ F) (y : locOrder ℓ Λ),
        ((c • y : locOrder ℓ Λ) : ℚ_[ℓ] ⊗[ℚ] B) = cenMap ℓ F B c * y := fun c y => rfl
    have hsum : ∀ c : ι → cenOrder ℓ F, ((∑ i, c i • v i : locOrder ℓ Λ) : ℚ_[ℓ] ⊗[ℚ] B) =
        ∑ i, cenMap ℓ F B (c i) * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e i) := by
      intro c
      rw [AddSubmonoidClass.coe_finsetSum]
      simp only [hsmul, v]
    have hcoef : ∀ (c : ι → cenOrder ℓ F) (b : B),
        ((∑ i, c i • v i : locOrder ℓ Λ) : ℚ_[ℓ] ⊗[ℚ] B) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b →
        ∀ k, ((c k : cenOrder ℓ F) : ℚ_[ℓ] ⊗[ℚ] F) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e.repr b k := by
      intro c b h k
      obtain ⟨π, hπ1, hπ2⟩ := exists_coordProj ℓ F B e k
      have h' := congrArg π h

      rw [hsum, map_sum, hπ1] at h'
      simp only [hπ2, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h'
      exact h'
    have hli : LinearIndependent (cenOrder ℓ F) v := by
      rw [Fintype.linearIndependent_iff]
      intro c hc k
      have h0 : ((∑ i, c i • v i : locOrder ℓ Λ) : ℚ_[ℓ] ⊗[ℚ] B) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (0 : B) := by
        rw [hc, TensorProduct.tmul_zero]; rfl
      have := hcoef c 0 h0 k
      apply Subtype.ext
      simpa using this
    have hsp : ⊤ ≤ Submodule.span (cenOrder ℓ F) (Set.range v) := by
      rintro y -
      obtain ⟨c, hc, hy⟩ := exists_coords_of_mem_locOrder ℓ F B Λ ι e he hco y y.2
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨fun i => ⟨c i, hc i⟩, Subtype.ext ?_⟩
      rw [hsum, hy]
    let f := Basis.mk hli hsp
    have hfv : ∀ i, f i = v i := fun i => Basis.mk_apply hli hsp i
    refine ⟨f, fun i => by rw [hfv], fun y b hy k => ?_⟩
    apply hcoef (fun i => f.repr y i) b _ k
    have hs := f.sum_repr y
    simp only [hfv] at hs
    rw [hs, hy]
  obtain ⟨e, he⟩ := exists_basis_mem (F := F) Λ hspan
  have hδ : IsUnit (structMat e).det :=
    (bijective_iff_isUnit_det e).1 (GroundTheory.Brauer.mulLeftRight_bijective F B)
  obtain ⟨m, hm, hmint⟩ := GlobalTheory.SepModel.exists_nat_integral ({((structMat e).det)⁻¹} : Finset F)
  obtain ⟨D, hD, hbasis⟩ := hlocalBasis _ e he
  refine ⟨D * m, by positivity, fun ℓ _ hℓ => ?_⟩
  let _ := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ
  obtain ⟨f, hf1, hf2⟩ := hbasis ℓ (fun h => hℓ (Dvd.dvd.mul_right h _))
  have hinv : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((structMat e).det)⁻¹ ∈ cenOrder ℓ F :=
    GlobalTheory.SepModel.tmul_mem_cenOrder ℓ (fun h => hℓ (Dvd.dvd.mul_left h _))
      (hmint _ (Finset.mem_singleton_self _))
  have hent : (cenOrder ℓ F).val.toRingHom.mapMatrix (structMat f) =
      (Algebra.TensorProduct.includeRight (R := ℚ) (A := ℚ_[ℓ]) (B := F)).toRingHom.mapMatrix
        (structMat e) := by
    ext ⟨k, l⟩ ⟨i, j⟩
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Subalgebra.coe_val, Algebra.TensorProduct.includeRight_apply, structMat_apply]
    apply hf2
    simp only [Subalgebra.coe_mul, hf1, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  have hdet : (((structMat f).det : cenOrder ℓ F) : ℚ_[ℓ] ⊗[ℚ] F) =
      (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (structMat e).det := by
    have h1 := RingHom.map_det (cenOrder ℓ F).val.toRingHom (structMat f)
    have h2 := RingHom.map_det
      (Algebra.TensorProduct.includeRight (R := ℚ) (A := ℚ_[ℓ]) (B := F)).toRingHom (structMat e)
    rw [hent, ← h2] at h1
    simpa using h1
  have hunit : IsUnit (structMat f).det := by
    refine isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext ?_⟩
    rw [Subalgebra.coe_mul, hdet, Subalgebra.coe_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      mul_inv_cancel₀ hδ.ne_zero, Algebra.TensorProduct.one_def]
  have : Nontrivial B := inferInstance
  have : FaithfulSMul (cenOrder ℓ F) (locOrder ℓ Λ) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    have h : cenMap ℓ F B a = cenMap ℓ F B b :=
      congrArg (fun x : locOrder ℓ Λ => (x : ℚ_[ℓ] ⊗[ℚ] B)) hab
    exact Subtype.ext (cenMap_injective ℓ F B h)
  have := Module.Projective.of_basis f
  have := Module.Finite.of_basis f
  exact ⟨(bijective_iff_isUnit_det f).2 hunit⟩
end

section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.exists_specialisation_to_strictlyHenselian : ∀ (R S O : Type) [CommRing R] [CommRing S] [IsLocalRing S] [CommRing O]
    [HenselianLocalRing O] [IsSepClosed (IsLocalRing.ResidueField O)] [Algebra R S] [Algebra R O]
    (Q y : Ideal R) [Q.IsPrime] [y.IsPrime], Q ≤ y →
    (IsLocalRing.maximalIdeal S).comap (algebraMap R S) = y →
    (IsLocalRing.maximalIdeal O).comap (algebraMap R O) = Q →
    Module.Flat R S → GlobalTheory.LocAcyc.LocPiecesEtale R S → Nonempty (S →ₐ[R] O) := by
  first | exact @GlobalTheory.Specialise.specialisation_exists | exact GlobalTheory.Specialise.specialisation_exists | (intros; apply GlobalTheory.Specialise.specialisation_exists <;> assumption)
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.HeckeTwo.TermHol


open Classical in
theorem wirtWord_eq_sum (F : Type) [Field F] [NumberField F] (b ν : F) (hb : b ≠ 0) (hJ : (∀ (n : ℝ) (k : ℕ) (y : ℝ), y ≠ 0 →
    (∀ σ ∈ halfPlane, HasDerivAt (iteratedDeriv k (hTrans σ n)) (iteratedDeriv (k + 1) (hTrans σ n) y) y) ∧
    DifferentiableOn ℂ (fun σ => iteratedDeriv k (hTrans σ n) y) halfPlane))
    (w : List (Emb F × Bool)) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℂ) (qf : ι → Emb F → ℕ), ∀ σ ∈ halfPlane, ∀ z ∈ upperHalf F,
      wirtWord w (fun z : Emb F → ℂ => fTerm σ z b ν) z = ∑ i, c i * termQ σ b ν (qf i) z := by
  have hU := GlobalTheory.HeckeTwo.GoodAdd.upperHalf_isOpen F
  induction w with
  | nil =>
    refine ⟨Unit, inferInstance, fun _ => 1, fun _ => 0, fun σ _ z _ => ?_⟩
    simp [wirtWord_nil, termQ_zero]
  | cons x ws ih =>
    obtain ⟨ι, _, c, qf, h⟩ := ih
    obtain ⟨τ₀, bar⟩ := x
    refine ⟨ι ⊕ ι, inferInstance,
      Sum.elim (fun i => c i * (2 * (Real.pi : ℂ) * I * ((τ₀ ν * τ₀ b : ℝ) : ℂ)) / 2)
        (fun i => (if bar then I else -I) * c i * ((τ₀ b : ℝ) : ℂ) / 2),
      Sum.elim qf (fun i => qf i + Pi.single τ₀ 1), fun σ hσ z hz => ?_⟩
    rw [wirtWord_cons]
    rw [GlobalTheory.HeckeTwo.GoodAdd.wirt_congr hU (g := fun z => ∑ i, c i * termQ σ b ν (qf i) z)
      (fun z hz => h σ hσ z hz) _ _ hz]
    have hd := fun i => GlobalTheory.T.heckeYDerivativeTerm_hasFDeriv_upperHalfPlane F b ν hb hJ σ hσ (qf i) z hz τ₀
    have hF : HasFDerivAt (fun z => ∑ i, c i * termQ σ b ν (qf i) z)
        (∑ i, c i • fderiv ℝ (termQ σ b ν (qf i)) z) z :=
      HasFDerivAt.fun_sum fun i _ => ((hd i).1.hasFDerivAt.const_mul (c i))
    simp only [wirt, hF.fderiv, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, (hd _).2.1, (hd _).2.2, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

end GlobalTheory.HeckeTwo.TermHol


open GlobalTheory.HeckeTwo.TermHol in
theorem GlobalTheory.HeckeTwo.fTerm_wirtWord_differentiableOn : ∀ (F : Type) [Field F] [NumberField F] (b ν : F), b ≠ 0 → ∀ w : List (Emb F × Bool), ∀ z ∈ upperHalf F,
  DifferentiableOn ℂ (fun σ => wirtWord w (fun z : Emb F → ℂ => fTerm σ z b ν) z) halfPlane := by
  intro F _ _ b ν hb w z hz
  have hJ := GlobalTheory.T.iteratedDeriv_heckePhiTransform_hasDerivAt_holo GlobalTheory.T.heckeHankelTransformAB_hasDerivAt_y GlobalTheory.T.heckeHankelTransformAB_differentiableOn_sigma
  obtain ⟨ι, _, c, qf, h⟩ := wirtWord_eq_sum F b ν hb hJ w
  refine DifferentiableOn.congr ?_ (fun σ hσ => h σ hσ z hz)
  refine DifferentiableOn.fun_sum fun i _ => DifferentiableOn.const_mul ?_ _
  unfold termQ
  refine DifferentiableOn.fun_finsetProd fun τ _ => DifferentiableOn.const_mul ?_ _
  have hy : (τ b : ℝ) * (z τ).im ≠ 0 :=
    mul_ne_zero ((map_ne_zero τ).2 hb) (hz τ).ne'
  exact (hJ (τ ν) (qf i τ) _ hy).2
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.galoisLocallyConstantTupleRing_tensorPower_universal : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (k : ℕ) (B : Type) [CommRing B] (g : Fin (k + 1) → (Ω →+* B)) (c : K →+* B), (∀ i, (g i).comp (algebraMap K Ω) = c) → ∃! u : GlobalTheory.EtC.GalSec.LCRing K Ω k →+* B, u.comp (GlobalTheory.EtC.GalSec.baseHom K Ω k) = c ∧ ∀ i, u.comp (GlobalTheory.EtC.GalSec.legHom K Ω k i) = g i := by
  first | (exact @GlobalTheory.EtC.GalSec.Tens.lcRing_universal) | (exact GlobalTheory.EtC.GalSec.Tens.lcRing_universal) | (intros; apply GlobalTheory.EtC.GalSec.Tens.lcRing_universal  <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

theorem _root_.GlobalTheory.T.affineHilbertIdealSheafOfQuotient_ideal_top : ∀ (A B C : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C] (J : Ideal (C ⊗[A] B)), (GlobalTheory.HilbAff.xI A B C J).ideal ⟨⊤, isAffineOpen_top _⟩ = J.map (GlobalTheory.HilbAff.psi A B C) := by
  first | (exact @GlobalTheory.HilbAff.xI_ideal_top) | (exact GlobalTheory.HilbAff.xI_ideal_top) | (intros; apply GlobalTheory.HilbAff.xI_ideal_top  <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

theorem _root_.GlobalTheory.T.sectionTensorPullbackRingHom_bijective : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (U : T.affineOpens), Function.Bijective (GlobalTheory.HilbAff.theta A B g U) := by
  first | (exact @GlobalTheory.HilbAff.theta_bijective) | (exact GlobalTheory.HilbAff.theta_bijective) | (intros; apply GlobalTheory.HilbAff.theta_bijective  <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology

theorem _root_.GlobalTheory.T.quaternion_normOne_re_open_near_of_isUnit : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (a b : R), SqOpen R → ∀ g : ℍ[R, a, b], nrm g = 1 → IsUnit (1 - g.re ^ 2) → ∀ W : Set ℍ[R, a, b], W ∈ 𝓝 g → ∃ O : Set R, IsOpen O ∧ g.re ∈ O ∧ ∀ t ∈ O, ∃ u ∈ W, nrm u = 1 ∧ u.re = t := by
  first | exact @GlobalTheory.traceOpen_near_of_isUnit | exact GlobalTheory.traceOpen_near_of_isUnit | (intros; apply GlobalTheory.traceOpen_near_of_isUnit <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology

theorem _root_.GlobalTheory.T.quaternionNormOneTraceOpen_pi : ∀ (ι : Type) [Fintype ι] (R : ι → Type) [∀ i, CommRing (R i)] [∀ i, TopologicalSpace (R i)] (a b : ∀ i, R i), (∀ i, TraceOpen (R i) (a i) (b i)) → TraceOpen (∀ i, R i) a b := by
  first | exact @GlobalTheory.QSA.traceOpen_pi | exact GlobalTheory.QSA.traceOpen_pi | (intros; apply GlobalTheory.QSA.traceOpen_pi <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology

theorem _root_.GlobalTheory.T.quaternionNormOneTraceOpen_prod : ∀ (R₁ R₂ : Type) [CommRing R₁] [TopologicalSpace R₁] [CommRing R₂] [TopologicalSpace R₂] (a₁ b₁ : R₁) (a₂ b₂ : R₂), TraceOpen R₁ a₁ b₁ → TraceOpen R₂ a₂ b₂ → TraceOpen (R₁ × R₂) (a₁, a₂) (b₁, b₂) := by
  first | exact @GlobalTheory.QSA.traceOpen_prod | exact GlobalTheory.QSA.traceOpen_prod | (intros; apply GlobalTheory.QSA.traceOpen_prod <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology

theorem _root_.GlobalTheory.T.quaternionNormOneTraceOpen_finiteAdeleRing : ∀ (F : Type) [Field F] [NumberField F] (a b : F), (∀ v : HeightOneSpectrum (𝓞 F), TraceOpen (v.adicCompletion F) (algebraMap F (v.adicCompletion F) a) (algebraMap F (v.adicCompletion F) b)) → (∀ᶠ v in (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 F))), ∀ t ∈ v.adicCompletionIntegers F, ∃ u : ℍ[v.adicCompletion F, algebraMap F (v.adicCompletion F) a, algebraMap F (v.adicCompletion F) b], nrm u = 1 ∧ u.re = t ∧ u.imI ∈ v.adicCompletionIntegers F ∧ u.imJ ∈ v.adicCompletionIntegers F ∧ u.imK ∈ v.adicCompletionIntegers F) → TraceOpen (FiniteAdeleRing (𝓞 F) F) (algebraMap F (FiniteAdeleRing (𝓞 F) F) a) (algebraMap F (FiniteAdeleRing (𝓞 F) F) b) := by
  first | exact @GlobalTheory.QSA.FinAdele.traceOpen_finiteAdele | exact GlobalTheory.QSA.FinAdele.traceOpen_finiteAdele | (intros; apply GlobalTheory.QSA.FinAdele.traceOpen_finiteAdele <;> assumption)
end
