module

public import Formalism.LocalRingCardinality.Bundle001
public import Formalism.LocalRingCardinality.DataKernels
public import Formalism.SatakeDualWeyl.Bundle001
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace Formalism.BasicNotions

open NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

section Defs

variable {F E : Type} [Field F] [CommRing E] [Algebra F E]

@[reducible] def tensTopL (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] :
    TopologicalSpace (E ⊗[F] R) :=
  letI : Algebra R (E ⊗[F] R) := Algebra.TensorProduct.rightAlgebra
  moduleTopology R (E ⊗[F] R)

end Defs

def IsProGrp {G : Type} [Group G] [TopologicalSpace G] (g : ℕ) (Uw : Subgroup G) : Prop :=
  IsCompact (Uw : Set G) ∧ ∀ N : Subgroup Uw, IsOpen (N : Set Uw) → N.Normal → ∃ m : ℕ, N.index = g ^ m

section Iw

variable (F : Type) [Field F] [NumberField F] (k : ℕ)

def upperUni (A : Type) [CommRing A] : Set (GL (Fin k) A) :=
  {x | ∀ i j : Fin k, (j < i → (x : Matrix (Fin k) (Fin k) A) i j = 0) ∧
    (x : Matrix (Fin k) (Fin k) A) i i = 1}

def iwU (v : HeightOneSpectrum (𝓞 F)) : Subgroup (GL (Fin k) (v.adicCompletion F)) :=
  congPre (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F))
    (Subgroup.closure (upperUni k _))

end Iw

namespace Spaces

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E] (sp : Spaces R F E)

theorem rank0 : (sp.X 0).rank = R.k := by
  simpa [Ranks.N] using sp.X_rank 0 (Nat.zero_le _)

def gram0 : Matrix (Fin R.k) (Fin R.k) E :=
  (sp.X 0).gram.reindex (finCongr sp.rank0) (finCongr sp.rank0)

def crd0 : (sp.X 0).V ≃ₗ[E] (Fin R.k → E) :=
  (sp.X 0).frame.equivFun.trans (LinearEquiv.funCongrLeft E E (finCongr sp.rank0).symm)

def crdLat0 (L : Submodule (𝓞 E) (sp.X 0).V) : Submodule (𝓞 E) (Fin R.k → E) :=
  L.map ((sp.crd0 : (sp.X 0).V →ₗ[E] (Fin R.k → E)).restrictScalars (𝓞 E))

private theorem hT_eq_hform_gram_reindex_frame (S : HSpace E) {n : ℕ} (h : S.rank = n) (x y : S.V) :
    S.hT x y = hform (starRingEnd E) (S.gram.reindex (finCongr h) (finCongr h))
      ((S.frame.equivFun.trans (LinearEquiv.funCongrLeft E E (finCongr h).symm)) x)
      ((S.frame.equivFun.trans (LinearEquiv.funCongrLeft E E (finCongr h).symm)) y) := by
  subst h
  simp [hform, HSpace.gram]
  conv_lhs => rw [← S.frame.sum_repr x, ← S.frame.sum_repr y]

  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
  smul_eq_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hermitianForm_base_coordinates (x y : (sp.X 0).V) :
    (sp.X 0).hT x y = hform (sp.cm.sig : E →+* E) sp.gram0 (sp.crd0 x) (sp.crd0 y) := by
  exact hT_eq_hform_gram_reindex_frame (sp.X 0) sp.rank0 x y

theorem baseGram_isHermitian : IsHerm (sp.cm.sig : E →+* E) sp.gram0 := by
  unfold IsHerm cT
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply, gram0, Matrix.reindex_apply,
    Matrix.submatrix_apply, HSpace.gram]
  exact (sp.X 0).herm.eq _ _

end Spaces

abbrev intV {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) : Subring (E ⊗[F] v.adicCompletion F) :=
  tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring

def dualSet {E : Type} [Field E] [NumberField E] {n : Type} [Fintype n] (σ : E →+* E)
    (J : Matrix n n E) (L : Submodule (𝓞 E) (n → E)) : Set (n → E) :=
  {y | ∀ x ∈ L, hform σ J x y ∈ (algebraMap (𝓞 E) E).range}

structure ColLevel (R : Ranks) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] (sp : Spaces R F E) (gp : Fin 2 → ℕ)
    {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc) (A : ColumnsAtT R C)
    (clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V) where

  Lb : Submodule (𝓞 E) (Fin R.k → E)
  Lb_fin : Module.Finite (𝓞 E) Lb
  Lb_span : Submodule.span E (Lb : Set (Fin R.k → E)) = ⊤

  Lb_int : ∀ x ∈ Lb, x ∈ dualSet (sp.cm.sig : E →+* E) sp.gram0 Lb

  Lb_dual : ∀ y ∈ dualSet (sp.cm.sig : E →+* E) sp.gram0 Lb, (A.T : E) • y ∈ Lb

  Lb_index : Lb.toAddSubgroup.relIndex
    (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) sp.gram0 Lb)).toAddSubgroup = A.T ^ (2 * R.f)

  Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin R.k) (E ⊗[F] v.adicCompletion F))
  Uloc_le : ∀ v, Uloc v ≤ UPts sp.cm.sig sp.gram0 (v.adicCompletion F)

  Uloc_lev : ∀ v, Uloc v ≤ levelVL sp.cm.sig sp.gram0 v Lb

  Uloc_hyp : ∀ v : HeightOneSpectrum (𝓞 F), ((gp 0 : 𝓞 F) ∉ v.asIdeal) →
    ((gp 1 : 𝓞 F) ∉ v.asIdeal) → ((A.T : 𝓞 F) ∉ v.asIdeal) →
    Uloc v = levelVL sp.cm.sig sp.gram0 v Lb

  splitG : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
    E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F
  splitG_sig : ∀ i v h x, splitG i v h (sigR sp.cm.sig (v.adicCompletion F) x) =
    swapR _ (splitG i v h x)

  frG : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
    GL (Fin R.k) (v.adicCompletion F)

  Uloc_g : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal), ∀ x ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F),
    x ∈ Uloc v ↔ (frG i v h)⁻¹ * bc ((RingHom.fst _ _).comp (splitG i v h).toRingHom) x * frG i v h ∈
      iwU F R.k v

  fM : ∀ v : HeightOneSpectrum (𝓞 F), (A.T : 𝓞 F) ∈ v.asIdeal → Type
  [fM_acg : ∀ v h, AddCommGroup (fM v h)]
  [fM_mod : ∀ v h, Module (intV E v) (fM v h)]
  fT : ∀ v h, latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) sp.gram0 Lb)) →ₗ[intV E v] fM v h
  fT_ne : ∀ v h, fT v h ≠ 0
  fT_T : ∀ v h x, fT v h ((A.T : intV E v) • x) = 0

  fM_card : ∀ v h, Nat.card (fM v h) = A.T

  fT_L : ∀ v h x, x.1 ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb → fT v h x = 0

  UlocAlt : ∀ v h, Uloc v = levelVL sp.cm.sig sp.gram0 v Lb ⊓ stabFun _ (fT v h)

  U : Subgroup (GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
  U_eq : ∀ x, x ∈ U ↔ x ∈ UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F) ∧
    ∀ v, bc (prV (E := E) v) x ∈ Uloc v

  U_compact : letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    IsCompact (U : Set (GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
  U_open : letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    IsOpen {x : UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F) | (x : GL _ _) ∈ U}

  w1 : HeightOneSpectrum (𝓞 F)
  reflection_mem_Glev_castSucc : (gp 0 : 𝓞 F) ∈ w1.asIdeal

  y : C.cls 0 → UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)
  y_bij : Function.Bijective (fun c : C.cls 0 =>
    (Quotient.mk'' (y c) : ClassSet
      ((ratPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)).subgroupOf
        (UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)))
      (U.subgroupOf (UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)))))

  y_lat : ∀ c (x : Fin R.k → E ⊗[F] FiniteAdeleRing (𝓞 F) F),
    x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (sp.crdLat0 (clsLat 0 c)) ↔
    ((((y c : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))⁻¹ : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
      Matrix (Fin R.k) (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ x ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Lb

  stabI : ∀ c : C.cls 0, C.stab 0 c →* UJ (sp.cm.sig : E →+* E) sp.gram0
  stabI_inj : ∀ c, Function.Injective (stabI c)

  stabI_range : ∀ c (γ : GL (Fin R.k) E) (hγ : γ ∈ UJ (sp.cm.sig : E →+* E) sp.gram0),
    (⟨γ, hγ⟩ : UJ (sp.cm.sig : E →+* E) sp.gram0) ∈ (stabI c).range ↔
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ ∈
        U.map (MulAut.conj (y c : GL (Fin R.k) _)).toMonoidHom

  stabI_lat : ∀ c (γ : C.stab 0 c) (x : Fin R.k → E),
    x ∈ sp.crdLat0 (clsLat 0 c) ↔
      (((stabI c γ : GL (Fin R.k) E) : Matrix (Fin R.k) (Fin R.k) E) *ᵥ x) ∈ sp.crdLat0 (clsLat 0 c)

attribute [instance] ColLevel.fM_acg ColLevel.fM_mod

namespace ColLevel

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

def ProG (L : ColLevel R F E sp gp C A clsLat) : Prop :=
  ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
    letI := tensTopL (F := F) (E := E) (v.adicCompletion F)
    IsProGrp (gp i) (L.Uloc v)

end ColLevel

end Formalism.BasicNotions

end
end

section

open NumberField Formalism.FrobeniusOrbits Formalism.HC

namespace Formalism.BasicNotions

section cls

variable {φ : Frame} (H : HostRaw φ) {p : ℕ}

theorem primeClass_eq_ramified_iff : primeClass H p = .ram2 ↔ p ∈ H.small := by
  unfold primeClass
  split_ifs <;> simp_all

private theorem ne_q_and_ne_d_of_mem_small (hp : p ∈ H.small) : p ≠ H.q ∧ p ≠ H.d := by
  rw [HostRaw.small, Nat.mem_primeFactors] at hp
  obtain ⟨hpp, hdvd, -⟩ := hp
  have hc := H.QS_coprime
  constructor
  · intro heq
    rw [heq] at hdvd hpp
    have h1 : H.q ∣ Nat.gcd H.QS (H.q * H.d) := Nat.dvd_gcd hdvd (dvd_mul_right _ _)
    rw [hc.gcd_eq_one] at h1
    exact hpp.one_lt.ne' (Nat.dvd_one.mp h1)
  · intro heq
    rw [heq] at hdvd hpp
    have h1 : H.d ∣ Nat.gcd H.QS (H.q * H.d) := Nat.dvd_gcd hdvd (dvd_mul_left _ _)
    rw [hc.gcd_eq_one] at h1
    exact hpp.one_lt.ne' (Nat.dvd_one.mp h1)

theorem primeClass_eq_ramQ_iff : primeClass H p = .ramQ ↔ p = H.q := by
  have hs : p ∈ H.small → p ≠ H.q := fun h => (ne_q_and_ne_d_of_mem_small H h).1
  unfold primeClass
  split_ifs <;> simp_all

private theorem q_ne_d' : H.q ≠ H.d := by
  have hh := H.hyp
  unfold HostHyp at hh
  obtain ⟨-, -, h1, h2, -⟩ := hh
  omega

theorem primeClass_eq_ramD_iff : primeClass H p = .ramD ↔ p = H.d := by
  have hs : p ∈ H.small → p ≠ H.d := fun h => (ne_q_and_ne_d_of_mem_small H h).2
  have hqd := q_ne_d' H
  unfold primeClass
  split_ifs <;> simp_all

theorem primeClass_eq_splitK_iff : primeClass H p = .splitK ↔
    p ∉ H.small ∧ p ≠ H.q ∧ p ≠ H.d ∧ jacobiSym (-(H.d : ℤ)) p = 1 := by
  unfold primeClass
  split_ifs <;> simp_all

theorem primeClass_eq_signal_iff : primeClass H p = .signal ↔
    p ∉ H.small ∧ p ≠ H.q ∧ p ≠ H.d ∧ jacobiSym (-(H.d : ℤ)) p ≠ 1 ∧ H.psAt p = 1 := by
  unfold primeClass
  split_ifs <;> simp_all

theorem primeClass_eq_inert_iff : primeClass H p = .inertClass ↔
    p ∉ H.small ∧ p ≠ H.q ∧ p ≠ H.d ∧ jacobiSym (-(H.d : ℤ)) p ≠ 1 ∧ H.psAt p ≠ 1 := by
  unfold primeClass
  split_ifs <;> simp_all

theorem primeClass_two : primeClass H 2 = .ram2 := by
  apply (primeClass_eq_ramified_iff H).2
  rw [HostRaw.small, Nat.mem_primeFactors]
  exact ⟨Nat.prime_two, dvd_trans (dvd_pow_self 2 (by omega)) H.tower_dvd, H.QS_pos.ne'⟩
theorem primeClass_q : primeClass H H.q = .ramQ := (primeClass_eq_ramQ_iff H).2 rfl
theorem primeClass_d : primeClass H H.d = .ramD := (primeClass_eq_ramD_iff H).2 rfl

theorem dvd_condN_iff_primeClass (hp : p.Prime) : p ∣ H.condN ↔
    primeClass H p = .ram2 ∨ primeClass H p = .ramQ ∨ primeClass H p = .ramD := by
  have hh := H.hyp
  unfold HostHyp at hh
  obtain ⟨hq, hd, -, -, -⟩ := hh
  have hQS := H.QS_pos.ne'
  show p ∣ H.QS * H.q * H.d ↔ _
  rw [primeClass_eq_ramified_iff, primeClass_eq_ramQ_iff, primeClass_eq_ramD_iff, hp.dvd_mul, hp.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hp hq, Nat.prime_dvd_prime_iff_eq hp hd, HostRaw.small, Nat.mem_primeFactors]
  tauto

theorem not_dvd_condN_iff_primeClass (hp : p.Prime) : ¬ p ∣ H.condN ↔
    primeClass H p = .splitK ∨ primeClass H p = .signal ∨ primeClass H p = .inertClass := by
  rw [dvd_condN_iff_primeClass H hp]
  unfold primeClass
  split_ifs <;> simp

variable {H}

theorem not_dvd_of_splitK (hp : p.Prime) (h : primeClass H p = .splitK) : ¬ p ∣ H.condN := (not_dvd_condN_iff_primeClass H hp).2 (Or.inl h)

theorem not_dvd_of_signal (hp : p.Prime) (h : primeClass H p = .signal) : ¬ p ∣ H.condN := (not_dvd_condN_iff_primeClass H hp).2 (Or.inr (Or.inl h))

theorem not_dvd_conductor_of_inert (hp : p.Prime) (h : primeClass H p = .inertClass) : ¬ p ∣ H.condN := (not_dvd_condN_iff_primeClass H hp).2 (Or.inr (Or.inr h))

theorem jacobi_d_eq_one_or (hp : p.Prime) (hd : p ≠ H.d) :
    jacobiSym (-(H.d : ℤ)) p = 1 ∨ jacobiSym (-(H.d : ℤ)) p = -1 := by
  have hh := H.hyp
  unfold HostHyp at hh
  obtain ⟨-, hdp, -, -, -⟩ := hh
  apply jacobiSym.eq_one_or_neg_one
  show Nat.gcd (-(H.d : ℤ)).natAbs (p : ℤ).natAbs = 1
  simpa using (Nat.coprime_primes hdp hp).2 (Ne.symm hd)

private theorem not_dvd_condN_iff' (hp : p.Prime) :
    ¬ p ∣ H.condN ↔ p ∉ H.small ∧ p ≠ H.q ∧ p ≠ H.d := by
  rw [dvd_condN_iff_primeClass H hp, primeClass_eq_ramified_iff, primeClass_eq_ramQ_iff,
    primeClass_eq_ramD_iff]
  tauto

theorem primeClass_eq_splitK_iff' (hp : p.Prime) : primeClass H p = .splitK ↔
    ¬ p ∣ H.condN ∧ jacobiSym (-(H.d : ℤ)) p = 1 := by
  rw [primeClass_eq_splitK_iff, not_dvd_condN_iff' hp]
  tauto

theorem primeClass_eq_signal_iff' (hp : p.Prime) : primeClass H p = .signal ↔
    ¬ p ∣ H.condN ∧ jacobiSym (-(H.d : ℤ)) p = -1 ∧ H.psAt p = 1 := by
  rw [primeClass_eq_signal_iff, not_dvd_condN_iff' hp]
  have key : p ≠ H.d → (jacobiSym (-(H.d : ℤ)) p ≠ 1 ↔ jacobiSym (-(H.d : ℤ)) p = -1) := fun hd => by
    rcases jacobi_d_eq_one_or hp hd with h | h <;> simp [h]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨h1, h2, h3⟩, (key h3).1 h4, h5⟩
  · rintro ⟨⟨h1, h2, h3⟩, h4, h5⟩
    exact ⟨h1, h2, h3, (key h3).2 h4, h5⟩

private theorem psAt_eq_one_or_neg_one (hp : p.Prime) (h : ¬ p ∣ H.condN) :
    H.psAt p = 1 ∨ H.psAt p = -1 := by
  have hc : Nat.Coprime p H.condN := (Nat.Prime.coprime_iff_not_dvd hp).2 h
  unfold HostRaw.psAt
  rw [dite_eq_left hc]
  rcases Int.units_eq_one_or ((H.art (ZMod.unitOfCoprime p hc)).1.1) with h1 | h1 <;> simp [h1]

theorem primeClass_eq_inert_iff_symbols (hp : p.Prime) : primeClass H p = .inertClass ↔
    ¬ p ∣ H.condN ∧ jacobiSym (-(H.d : ℤ)) p = -1 ∧ H.psAt p = -1 := by
  rw [primeClass_eq_inert_iff, not_dvd_condN_iff' hp]
  have key : p ≠ H.d → (jacobiSym (-(H.d : ℤ)) p ≠ 1 ↔ jacobiSym (-(H.d : ℤ)) p = -1) := fun hd => by
    rcases jacobi_d_eq_one_or hp hd with h | h <;> simp [h]
  have key2 : p ∉ H.small → p ≠ H.q → p ≠ H.d → (H.psAt p ≠ 1 ↔ H.psAt p = -1) := fun h1 h2 h3 => by
    rcases psAt_eq_one_or_neg_one (H := H) hp ((not_dvd_condN_iff' (H := H) hp).2 ⟨h1, h2, h3⟩) with h | h <;> simp [h]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨h1, h2, h3⟩, (key h3).1 h4, (key2 h1 h2 h3).1 h5⟩
  · rintro ⟨⟨h1, h2, h3⟩, h4, h5⟩
    exact ⟨h1, h2, h3, (key h3).2 h4, (key2 h1 h2 h3).2 h5⟩

end cls

namespace Ranks

variable (R : Ranks)

theorem n_eq_ord : R.n = R.ord := rfl
theorem f_eq_ord : R.f = 2 * R.ord := rfl
theorem n_pos' : 0 < R.n := by
  show 0 < R.ord
  have h1 := R.m_le_f
  have h2 := R.two_le_m
  omega
theorem two_pow_le_n : 2 ^ R.e ≤ R.n := Nat.le_of_dvd R.n_pos' R.toFrame.two_pow_dvd_ord

end Ranks

namespace Host

variable {R : Ranks} (H : Host R)

include H in
theorem four_le_two_pow : 4 ≤ 2 ^ R.e := by
  have h := H.two_le_e
  calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ R.e := Nat.pow_le_pow_right (by norm_num) h

include H in
theorem four_le_n' : 4 ≤ R.n := le_trans (four_le_two_pow H) R.two_pow_le_n



theorem finrank_E' : Module.finrank ℚ H.E = 2 * R.f := by
  rw [H.der.finrank_E]
  show 4 * R.ord = 2 * (2 * R.ord)
  ring

end Host

end Formalism.BasicNotions
end
