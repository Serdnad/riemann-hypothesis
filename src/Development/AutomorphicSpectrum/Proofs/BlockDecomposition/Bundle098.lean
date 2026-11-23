module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle001
public import Mathlib.RingTheory.WittVector.Teichmuller
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormLaws
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle086
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExteriorPowerSplit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle024
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle018
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.ColMatMulGlEmbMat
public import Mathlib.Topology.Instances.Matrix
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle077
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceGroupOfBlockDet
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviDecompOfBlockDet
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviQuotientOfBlockDet
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.Descend
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle078
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.GapAbsOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle079
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
public import Mathlib.NumberTheory.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Perfectoid.FontaineTheta
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
import Mathlib.RingTheory.DividedPowers.Basic
public import Mathlib.RingTheory.Perfection
import Mathlib.Topology.Sheaves.Presheaf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle050

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.PerfectWittMaps

theorem isAdicComplete_of_pow_eq_zero (p : ℕ) {B : Type} [CommRing B] {n : ℕ} (hn : (p : B) ^ n = 0) :
    IsAdicComplete (Ideal.span {(p : B)}) B := by
  have hI : (Ideal.span {(p : B)}) ^ n = ⊥ := by
    rw [Ideal.span_singleton_pow, hn]; simp
  have hz0 : ∀ x y : B, x ≡ y [SMOD ((Ideal.span {(p : B)}) ^ n • ⊤ : Submodule B B)] → x = y := by
    intro x y h
    rw [hI] at h
    simpa [SModEq.bot] using h
  refine { haus' := fun x h => hz0 _ _ (h n), prec' := fun f h => ⟨f n, fun m => ?_⟩ }
  rcases le_total m n with hmn | hmn
  · exact h hmn
  · rw [hz0 _ _ (h hmn)]

theorem exists_pow_pow_eq (p : ℕ) {A : Type} [CommRing A] (h : Function.Bijective fun x : A => x ^ p)
    (k : ℕ) (a : A) : ∃ b : A, b ^ p ^ k = a := by
  induction k generalizing a with
  | zero => exact ⟨a, by simp⟩
  | succ k ih =>
    obtain ⟨c, hc⟩ := h.2 a
    obtain ⟨b, hb⟩ := ih c
    refine ⟨b, ?_⟩
    rw [pow_succ, pow_mul, hb]
    exact hc

theorem exists_lift (p : ℕ) [Fact p.Prime] {A B : Type} [CommRing A] [CommRing B] [CharP A p]
    [PerfectRing A p] [Fact ¬IsUnit (p : B)] [IsAdicComplete (Ideal.span {(p : B)}) B] (J : Ideal B)
    (hpJ : (p : B) ∈ J) (hJ : ∀ x ∈ J, x ^ p ∈ Ideal.span {(p : B)}) (g : A →+* B ⧸ J) :
    ∃ f : WittVector p A →+* B, ∀ a, Ideal.Quotient.mk J (f (WittVector.teichmuller p a)) = g a := by
  let φ : B ⧸ J →+* ModP B p := Ideal.Quotient.lift J
    ((frobenius (ModP B p) p).comp (Ideal.Quotient.mk _)) (by
      intro x hx
      rw [RingHom.comp_apply, frobenius_def, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact hJ x hx)
  let σ : A →+* A := ((frobeniusEquiv A p).symm : A ≃+* A)
  let g₁ : A →+* ModP B p := φ.comp (g.comp σ)
  let G : A →+* PreTilt B p := Perfection.lift p A (ModP B p) g₁
  have hle : Ideal.span {(p : B)} ≤ J := (Ideal.span_singleton_le_iff_mem _).2 hpJ
  let res : ModP B p →+* B ⧸ J := Ideal.Quotient.factor hle
  have hres : ∀ u : B, Ideal.Quotient.mk J u = res (Ideal.Quotient.mk _ u) := fun u => rfl
  have hφ : ∀ y : B ⧸ J, res (φ y) = y ^ p := by
    intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    have : φ (Ideal.Quotient.mk J b) = Ideal.Quotient.mk _ (b ^ p) := by
      simp [φ, frobenius_def]
    rw [this, ← hres, map_pow]
  refine ⟨(WittVector.fontaineTheta B p).comp (WittVector.map G), fun a => ?_⟩
  have h1 : (WittVector.fontaineTheta B p).comp (WittVector.map G) (WittVector.teichmuller p a)
      = (G a).untilt := by
    rw [RingHom.comp_apply, WittVector.map_teichmuller, WittVector.fontaineTheta_teichmuller]
  have h3 : PreTilt.coeff 0 (G a) = g₁ a := rfl
  rw [h1, hres, PreTilt.mk_untilt_eq_coeff_zero, h3]
  change res (φ (g (σ a))) = g a
  rw [hφ, ← map_pow]
  congr 1
  exact frobeniusEquiv_symm_pow_p A p a

theorem lift_unique (p : ℕ) [Fact p.Prime] {A B : Type} [CommRing A] [CommRing B] [CharP A p]
    [PerfectRing A p] [Fact ¬IsUnit (p : B)] (J : Ideal B) (n : ℕ) (hbij : Function.Bijective fun x : A => x ^ p)
    (hn : (p : B) ^ n = 0) (hJ : ∀ x ∈ J, x ^ p ∈ Ideal.span {(p : B)})
    (f f' : WittVector p A →+* B)
    (h : ∀ a, Ideal.Quotient.mk J (f (WittVector.teichmuller p a)) =
      Ideal.Quotient.mk J (f' (WittVector.teichmuller p a))) : f = f' := by
  refine WittVector.eq_of_apply_teichmuller_eq f f' ⟨n, hn⟩ fun a => ?_
  obtain ⟨b, rfl⟩ := exists_pow_pow_eq p hbij (n + 1) a
  rw [map_pow, map_pow, map_pow]
  set u := f (WittVector.teichmuller p b)
  set v := f' (WittVector.teichmuller p b)
  have huv : u - v ∈ J := Ideal.Quotient.eq.1 (h b)
  have h1 : (p : B) ∣ u ^ p - v ^ p := by
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_pow,
      ← sub_pow_char, ← map_sub, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact hJ _ huv
  have h2 := dvd_sub_pow_of_dvd_sub h1 n
  have h0 : (p : B) ^ (n + 1) = 0 := by rw [pow_succ, hn, zero_mul]
  rw [h0, zero_dvd_iff, sub_eq_zero, ← pow_mul, ← pow_mul, ← pow_succ'] at h2
  exact h2

theorem wittVector_lift : ∀ (p : ℕ) [Fact p.Prime] {A B : Type} [CommRing A] [CommRing B] (J : Ideal B) (n : ℕ), D.Pf p A → (p : B) ^ n = 0 → (p : B) ∈ J → (∀ x ∈ J, x ^ p ∈ Ideal.span {(p : B)}) → ∀ g : A →+* B ⧸ J, (∃ f : WittVector p A →+* B, ∀ a, Ideal.Quotient.mk J (f (WittVector.teichmuller p a)) = g a) ∧ ∀ f f' : WittVector p A →+* B, (∀ a, Ideal.Quotient.mk J (f (WittVector.teichmuller p a)) = Ideal.Quotient.mk J (f' (WittVector.teichmuller p a))) → f = f' := by
  intro p _ A B _ _ J n hA hn hpJ hJ g
  by_cases hB : Subsingleton B
  · have hQ : Subsingleton (B ⧸ J) := (Ideal.Quotient.mk_surjective (I := J)).subsingleton
    refine ⟨⟨{ toFun := fun _ => 0, map_one' := Subsingleton.elim _ _, map_mul' := fun _ _ => Subsingleton.elim _ _,
               map_zero' := rfl, map_add' := fun _ _ => Subsingleton.elim _ _ }, fun a => Subsingleton.elim _ _⟩,
      fun f f' _ => RingHom.ext fun x => Subsingleton.elim _ _⟩
  · rw [not_subsingleton_iff_nontrivial] at hB
    have hu : ¬IsUnit (p : B) := IsNilpotent.not_isUnit ⟨n, hn⟩
    haveI : Fact ¬IsUnit (p : B) := ⟨hu⟩
    haveI := isAdicComplete_of_pow_eq_zero p hn
    have hAn : Nontrivial A := by
      by_contra hA'
      rw [not_nontrivial_iff_subsingleton] at hA'
      have h1 : (1 : B) ∈ J := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_one, ← map_one g, Subsingleton.elim (1 : A) 0, map_zero]
      have h2 := hJ 1 h1
      rw [one_pow, Ideal.mem_span_singleton] at h2
      exact hu (isUnit_of_dvd_one h2)
    haveI : CharP A p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hA.char
    haveI : PerfectRing A p := ⟨hA.bij⟩
    exact ⟨exists_lift p J hpJ hJ g, fun f f' h => lift_unique p J n hA.bij hn hJ f f' h⟩

end GlobalTheory.CompanionTheory.PerfectWittMaps
end

section

open TensorProduct CrystallineSemistableComparison.Onto

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.OmKun

theorem piCongrRight_single {K ι : Type} [CommRing K] [DecidableEq ι] {X Y : ι → Type}
    [∀ i, AddCommGroup (X i)] [∀ i, Module K (X i)] [∀ i, AddCommGroup (Y i)] [∀ i, Module K (Y i)]
    (f : ∀ i, X i ≃ₗ[K] Y i) (a : ι) (x : X a) :
    LinearEquiv.piCongrRight f (Pi.single a x) = Pi.single a (f a x) := by
  funext b
  by_cases h : b = a
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem omKun_pushout (K A B R : Type) [CommRing K] [CommRing A] [CommRing B] [CommRing R]
    [Algebra K A] [Algebra K B] [Algebra K R] [Algebra A R] [Algebra B R]
    [IsScalarTower K A R] [IsScalarTower K B R] [Algebra.IsPushout K A B R] (c : ℕ) :
    ∃ e : (∀ a : Fin (c + 1), TensorProduct K (Om K A a) (Om K B (c - a))) ≃ₗ[K] Om K R c,
      ∀ (a : Fin (c + 1)) (g₀ : A) (g : Fin a → A) (h₀ : B) (h : Fin (c - a) → B),
        e (Pi.single a (form K g₀ g ⊗ₜ form K h₀ h)) = form K (algebraMap A R g₀ * algebraMap B R h₀)
          (Fin.append (fun k => algebraMap A R (g k)) (fun k => algebraMap B R (h k)) ∘
            Fin.cast (by have := a.2; omega)) := by
  obtain ⟨r, π, h1, h2, h3, h4, h5⟩ := GlobalTheory.CompanionTheory.KaehlerPushout.kaehler_pushout_split K A B R
  obtain ⟨E, hE⟩ := GlobalTheory.CompanionTheory.TopExtSplit.exteriorPower_split R _ _ _ _ _ r π h1 h2 h3 h4 h5 c
  choose bA hbA using fun a : ℕ => GlobalTheory.CompanionTheory.ExteriorBase.exists_baseChange_equiv A R (Ω[A⁄K]) a
  choose bB hbB using fun a : ℕ => GlobalTheory.CompanionTheory.ExteriorBase.exists_baseChange_equiv B R (Ω[B⁄K]) a
  choose t ht using fun a : Fin (c + 1) => GlobalTheory.CompanionTheory.TensorPushout.tensor_equiv_baseChange_tensor K A B R (Om K A a) (Om K B (c - a))
  refine ⟨LinearEquiv.piCongrRight (fun a => t a ≪≫ₗ
    (TensorProduct.congr (bA a) (bB (c - a))).restrictScalars K) ≪≫ₗ E.restrictScalars K, ?_⟩
  intro a g₀ g h₀ h
  have hA : bA a ((1 : R) ⊗ₜ[A] form K g₀ g) = algebraMap A R g₀ •
      exteriorPower.ιMulti R a (fun k => (1 : R) ⊗ₜ[A] KaehlerDifferential.D K A (g k)) := by
    unfold form
    rw [← TensorProduct.smul_tmul, hbA, Algebra.smul_def, mul_one]
  have hB : bB (c - a) ((1 : R) ⊗ₜ[B] form K h₀ h) = algebraMap B R h₀ •
      exteriorPower.ιMulti R (c - a) (fun k => (1 : R) ⊗ₜ[B] KaehlerDifferential.D K B (h k)) := by
    unfold form
    rw [← TensorProduct.smul_tmul, hbB, Algebra.smul_def, mul_one]
  have hmain : (TensorProduct.congr (bA a) (bB (c - a))) (((1 : R) ⊗ₜ[A] form K g₀ g) ⊗ₜ[R]
      ((1 : R) ⊗ₜ[B] form K h₀ h)) = (algebraMap A R g₀ * algebraMap B R h₀) •
        (exteriorPower.ιMulti R a (fun k => (1 : R) ⊗ₜ[A] KaehlerDifferential.D K A (g k)) ⊗ₜ[R]
        exteriorPower.ιMulti R (c - a) (fun k => (1 : R) ⊗ₜ[B] KaehlerDifferential.D K B (h k))) := by
    rw [TensorProduct.congr_tmul, hA, hB, TensorProduct.smul_tmul_smul]
  simp only [LinearEquiv.trans_apply, piCongrRight_single, LinearEquiv.restrictScalars_apply, ht,
    hmain, Pi.single_smul, map_smul, hE]
  unfold form
  congr 2
  funext k
  simp only [Function.comp_apply, KaehlerDifferential.mapBaseChange_tmul, one_smul]
  generalize Fin.cast _ k = j
  induction j using Fin.addCases with
  | left j => simp [KaehlerDifferential.mapBaseChange_tmul]
  | right j => simp [KaehlerDifferential.mapBaseChange_tmul]

theorem omKun : CrystallineSemistableComparison.Onto.OmKun := by
  intro K A B _ _ _ _ _ c
  let _ : Algebra B (A ⊗[K] B) := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower K B (A ⊗[K] B) := Algebra.TensorProduct.right_isScalarTower
  obtain ⟨e, he⟩ := omKun_pushout K A B (A ⊗[K] B) c
  refine ⟨e, fun a g₀ g h₀ h => ?_⟩
  rw [he]
  congr 1
  change g₀ ⊗ₜ[K] (1 : B) * (1 : A) ⊗ₜ[K] h₀ = _
  simp [Algebra.TensorProduct.tmul_mul_tmul]

end GlobalTheory.CompanionTheory.OmKun
end

section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir

namespace GlobalTheory.CompanionTheory.BZPhiPhi

variable (k : Type) [Field k]

def rowQ (n : ℕ) (g : Mir k (n + 1)) : Fin (n + 1) → k :=
  fun j => ((g : GL (Fin (n + 2)) k) : Matrix (Fin (n + 2)) (Fin (n + 2)) k) (Fin.castSucc (Fin.last n)) (Fin.castSucc j)

def unipM (n : ℕ) : Multiplicative (Fin (n + 1) → k) →* Mir k (n + 1) :=
  (unip k (n + 1)).codRestrict (Mir k (n + 1)) (fun v => MirU_le_Mir k (n + 1) ⟨v, rfl⟩)

theorem unipM_val (n : ℕ) (v : Multiplicative (Fin (n + 1) → k)) :
    ((unipM k n v : Mir k (n + 1)) : GL (Fin (n + 2)) k) = unip k (n + 1) v := rfl

theorem unipM_mem_MirUin (n : ℕ) (v : Multiplicative (Fin (n + 1) → k)) : unipM k n v ∈ MirUin k (n + 1) := by
  rw [GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU]
  exact ⟨v, rfl⟩

end GlobalTheory.CompanionTheory.BZPhiPhi

namespace GlobalTheory.CompanionTheory.BZPhiPhi

variable (k : Type) [Field k]

theorem rowQ_one (n : ℕ) : rowQ k n 1 = Pi.single (Fin.last n) 1 := by
  funext j
  by_cases h : j = Fin.last n
  · subst h
    simp [GlobalTheory.CompanionTheory.BZPhiPhi.rowQ]
  · simp [GlobalTheory.CompanionTheory.BZPhiPhi.rowQ, Matrix.one_apply, Pi.single_apply, h, Ne.symm h]

end GlobalTheory.CompanionTheory.BZPhiPhi

namespace GlobalTheory.CompanionTheory.BZPhiPhi

section Top

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_matMir (n : ℕ) :
    Continuous fun g : Mir k (n + 1) => ((g : GL (Fin (n + 2)) k) : Matrix (Fin (n + 2)) (Fin (n + 2)) k) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_rowQ (n : ℕ) : Continuous (rowQ k n) :=
  continuous_pi fun j => (continuous_apply _).comp ((continuous_apply _).comp (continuous_matMir n))

theorem continuous_unipM (n : ℕ) :
    Continuous fun v : Fin (n + 1) → k => unipM k n (Multiplicative.ofAdd v) := by
  have hcol : Continuous fun v : Fin (n + 1) → k => GlobalTheory.BZMir.colMat k (n + 1) v := by
    refine continuous_matrix fun i j => ?_
    unfold GlobalTheory.BZMir.colMat
    by_cases hj : j = Fin.last (n + 1)
    · simp only [if_pos hj]
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
      · simp only [Fin.lastCases_castSucc]
        exact continuous_apply i
      · simp only [Fin.lastCases_last]
        exact continuous_const
    · simp only [if_neg hj]
      exact continuous_const
  have hval : Continuous fun v : Fin (n + 1) → k =>
      (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) k) + GlobalTheory.BZMir.colMat k (n + 1) v :=
    continuous_const.add hcol
  have hinv : Continuous fun v : Fin (n + 1) → k =>
      (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) k) - GlobalTheory.BZMir.colMat k (n + 1) v :=
    continuous_const.sub hcol
  have hGL : Continuous fun v : Fin (n + 1) → k =>
      GlobalTheory.BZMir.unip k (n + 1) (Multiplicative.ofAdd v) :=
    Units.continuous_iff.2 ⟨hval, hinv⟩
  exact hGL.subtype_mk _

end Top

end GlobalTheory.CompanionTheory.BZPhiPhi

end
end

section


theorem _root_.GlobalTheory.T.unipotent_convergence_of_parabolic : PositivityTheory.RgEis.ParLaw → PositivityTheory.RgEis.ConvU := by
  first | exact @GlobalTheory.CompanionTheory.RgEis.UnitaryConv.convU_of_parLaw | exact GlobalTheory.CompanionTheory.RgEis.UnitaryConv.convU_of_parLaw | (intros; apply GlobalTheory.CompanionTheory.RgEis.UnitaryConv.convU_of_parLaw <;> assumption)
end

section


theorem _root_.GlobalTheory.T.convergence_group_of_block_det : PositivityTheory.RgEis.BdetLaw → PositivityTheory.RgEis.ExtLaw → PositivityTheory.RgEis.ConvGrOf := by
  first | exact @GlobalTheory.CompanionTheory.Plucker.convGrOf | exact GlobalTheory.CompanionTheory.Plucker.convGrOf | (intros; apply GlobalTheory.CompanionTheory.Plucker.convGrOf <;> assumption)
end

section


theorem _root_.GlobalTheory.T.levi_decomp_of_block_det : PositivityTheory.RgEis.BdetLaw → PositivityTheory.RgEis.ExtLaw → PositivityTheory.RgEis.GrpTop → PositivityTheory.RgEis.LeviS := by
  first | exact @GlobalTheory.CompanionTheory.RgEisLevi.leviS | exact GlobalTheory.CompanionTheory.RgEisLevi.leviS | (intros; apply GlobalTheory.CompanionTheory.RgEisLevi.leviS <;> assumption)
end

section


theorem _root_.GlobalTheory.T.levi_quotient_of_block_det : PositivityTheory.RgEis.BdetLaw → PositivityTheory.RgEis.ExtLaw → PositivityTheory.RgEis.GrpTop → PositivityTheory.RgEis.LeviQ := by
  first | exact @GlobalTheory.CompanionTheory.RgEisLeviQUnit.leviQ | exact GlobalTheory.CompanionTheory.RgEisLeviQUnit.leviQ | (intros; apply GlobalTheory.CompanionTheory.RgEisLeviQUnit.leviQ <;> assumption)
end

section


theorem _root_.GlobalTheory.T.eisenstein_scaling_law : PositivityTheory.RgEis.Scale := by
  first | exact @GlobalTheory.CompanionTheory.RgEisScale.scale | exact GlobalTheory.CompanionTheory.RgEisScale.scale | (intros; apply GlobalTheory.CompanionTheory.RgEisScale.scale <;> assumption)
end

section


theorem _root_.GlobalTheory.T.twist_of_section_law : PositivityTheory.RgEis.SecLaw → PositivityTheory.RgEis.Twist := by
  first | exact @GlobalTheory.CompanionTheory.RgEisTwist.twist | exact GlobalTheory.CompanionTheory.RgEisTwist.twist | (intros; apply GlobalTheory.CompanionTheory.RgEisTwist.twist <;> assumption)
end

section


theorem _root_.GlobalTheory.T.transfer_of_section_and_wall_laws : PositivityTheory.RgEis.SecLaw → PositivityTheory.RgEis.WallLaw → PositivityTheory.RgEis.Transfer := by
  first | exact @GlobalTheory.CompanionTheory.RgTransfer.transfer | exact GlobalTheory.CompanionTheory.RgTransfer.transfer | (intros; apply GlobalTheory.CompanionTheory.RgTransfer.transfer <;> assumption)
end

section

open Finset Matrix PositivityTheory.RgHe.Frame

namespace GlobalTheory.CompanionTheory.RgHeFrame

theorem pfOrth : ∀ {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ),
    Function.Injective (Sum.elim d d') → ∀ i k, i ≠ k →
      1 - ∑ j, pfR d d' j / ((d i - d' j) * (d k - d' j)) = 0 := by
  intro m d d' hinj i k hik
  have hi := GlobalTheory.T.partial_fraction_diagonal_identity d d' hinj i
  have hk := GlobalTheory.T.partial_fraction_diagonal_identity d d' hinj k
  have hne : d i - d k ≠ 0 := sub_ne_zero.mpr fun h => hik (Sum.inl.inj (@hinj (Sum.inl i) (Sum.inl k) h))
  have hij : ∀ j, d i - d' j ≠ 0 := fun j => sub_ne_zero.mpr fun h =>
    Sum.inl_ne_inr (@hinj (Sum.inl i) (Sum.inr j) h)
  have hkj : ∀ j, d k - d' j ≠ 0 := fun j => sub_ne_zero.mpr fun h =>
    Sum.inl_ne_inr (@hinj (Sum.inl k) (Sum.inr j) h)
  have hdiff : ∑ j, pfR d d' j / (d i - d' j) - ∑ j, pfR d d' j / (d k - d' j) =
      -(d i - d k) * ∑ j, pfR d d' j / ((d i - d' j) * (d k - d' j)) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp [hij j, hkj j]
    ring
  have key : (d i - d k) * (1 - ∑ j, pfR d d' j / ((d i - d' j) * (d k - d' j))) = 0 := by
    linear_combination hi - hk - hdiff
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h hne
  · exact h

end GlobalTheory.CompanionTheory.RgHeFrame
end

section

open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit

theorem _root_.GlobalTheory.T.card_functionals_vanishing_subspace : ∀ (k : Type) [Field k] [Fintype k] (n j : ℕ) (M : Submodule k (Fin (n + 1) → k)), e0 k n ∉ M →
  Module.finrank k M + (j + 1) = n + 1 →
  (Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ e0 k n = 1 ∧ ∀ x ∈ M, a ⬝ᵥ x = 0)).card = Fintype.card k ^ j := by
  first | exact @GlobalTheory.CompanionTheory.GapOpCount.card_forms_vanishing_missing_line | exact GlobalTheory.CompanionTheory.GapOpCount.card_forms_vanishing_missing_line | (intros; apply GlobalTheory.CompanionTheory.GapOpCount.card_forms_vanishing_missing_line <;> assumption)
end
