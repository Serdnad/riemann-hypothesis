module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle044
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle330
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle099
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle333
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.CanonicalSurjection

noncomputable section

namespace GlobalTheory.Mem.WeightBideterminants

open MvPolynomial

private theorem prod_eval_mem_span_prod_of_mem_span {L : Type} [Field L] {ι : Type} [Fintype ι] {X : Type}
    (A : ι → Set (X → L)) (s : Finset ι) :
    ∀ h : ι → X → L, (∀ τ ∈ s, h τ ∈ Submodule.span L (A τ)) → (∀ τ ∉ s, h τ ∈ A τ) →
      (fun y : ι → X => ∏ τ, h τ (y τ)) ∈
        Submodule.span L {F | ∃ g : ι → X → L, (∀ τ, g τ ∈ A τ) ∧ F = fun y => ∏ τ, g τ (y τ)} := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro h _ h2
    exact Submodule.subset_span ⟨h, fun τ => h2 τ (by simp), rfl⟩
  | insert a s ha ih =>
    intro h h1 h2

    have hsplit : ∀ x : X → L, (fun y : ι → X => ∏ τ, Function.update h a x τ (y τ)) =
        fun y => x (y a) * ∏ τ ∈ Finset.univ.erase a, h τ (y τ) := by
      intro x
      funext y
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a)]
      congr 1
      · simp
      · apply Finset.prod_congr rfl
        intro τ hτ
        rw [Function.update_apply, if_neg (Finset.ne_of_mem_erase hτ)]

    have key : ∀ x ∈ Submodule.span L (A a), (fun y : ι → X => ∏ τ, Function.update h a x τ (y τ)) ∈
        Submodule.span L {F | ∃ g : ι → X → L, (∀ τ, g τ ∈ A τ) ∧ F = fun y => ∏ τ, g τ (y τ)} := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        apply ih
        · intro τ hτ
          have hne : τ ≠ a := fun e => ha (e ▸ hτ)
          rw [Function.update_apply, if_neg hne]
          exact h1 τ (Finset.mem_insert_of_mem hτ)
        · intro τ hτ
          by_cases e : τ = a
          · subst e
            simpa using hx
          · rw [Function.update_apply, if_neg e]
            exact h2 τ (by simp [e, hτ])
      | zero =>
        rw [hsplit]
        convert Submodule.zero_mem _ using 1
        funext y
        simp
      | add x x' _ _ hx hx' =>
        rw [hsplit] at hx hx' ⊢
        convert Submodule.add_mem _ hx hx' using 1
        funext y
        simp [add_mul]
      | smul c x _ hx =>
        rw [hsplit] at hx ⊢
        convert Submodule.smul_mem _ c hx using 1
        funext y
        simp [mul_assoc]
    simpa using key (h a) (h1 a (Finset.mem_insert_self a s))

theorem prod_mem_span_prod {L : Type} [Field L] {ι : Type} [Fintype ι] {X : Type} (A : ι → Set (X → L))
    (h : ι → X → L) (hh : ∀ τ, h τ ∈ Submodule.span L (A τ)) :
    (fun y : ι → X => ∏ τ, h τ (y τ)) ∈
      Submodule.span L {F | ∃ g : ι → X → L, (∀ τ, g τ ∈ A τ) ∧ F = fun y => ∏ τ, g τ (y τ)} :=
  prod_eval_mem_span_prod_of_mem_span A Finset.univ h (fun τ _ => hh τ) (fun τ hτ => absurd (Finset.mem_univ τ) hτ)

theorem eval_rowAct {L : Type} [Field L] {N : ℕ} (g Y : Matrix (Fin N) (Fin N) L)
    (f : MvPolynomial (Fin N × Fin N) L) :
    eval (fun v : Fin N × Fin N => Y v.1 v.2) (Formalism.GradedWeylDivisibility.rowAct L g f) =
      eval (fun v : Fin N × Fin N => (g * Y) v.1 v.2) f := by
  unfold Formalism.GradedWeylDivisibility.rowAct
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp]
    simp [Matrix.mul_apply]

def evFn (L : Type) [Field L] (N : ℕ) :
    MvPolynomial (Fin N × Fin N) L →ₗ[L] (Matrix (Fin N) (Fin N) L → L) :=
  LinearMap.pi fun Y => (aeval fun v : Fin N × Fin N => Y v.1 v.2).toLinearMap

theorem evFn_apply (L : Type) [Field L] (N : ℕ) (P : MvPolynomial (Fin N × Fin N) L) (Y : Matrix (Fin N) (Fin N) L) :
    evFn L N P Y = eval (fun v : Fin N × Fin N => Y v.1 v.2) P := by
  simp [evFn]

theorem evFn_mem_span (L : Type) [Field L] (N : ℕ) (ν : Fin N → ℕ) (P : MvPolynomial (Fin N × Fin N) L)
    (hP : P ∈ Formalism.GradedWeylDivisibility.dualWeyl L N N ν) : evFn L N P ∈ Submodule.span L (bideterminantFunctionsOfShape L N ν) := by

  obtain ⟨b, hb, hbm⟩ := Formalism.GradedWeylDivisibility.sSBasis L N N ν
  have hP' : P ∈ Submodule.span L (Set.range b) := by
    rw [hb.2.1]
    exact hP
  have h1 : evFn L N P ∈ (Submodule.span L (Set.range b)).map (evFn L N) := Submodule.mem_map_of_mem hP'
  rw [Submodule.map_span] at h1
  refine Submodule.span_mono ?_ h1
  rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
  obtain ⟨-, -, Kc, sz, hsz, I, hs, hI, hbI⟩ := hbm m
  refine ⟨Kc, sz, hsz, I, hs, hI, ?_⟩
  funext Y
  rw [evFn_apply, hbI]

theorem weightPolynomial_mem_span_bideterminantProducts : ∀ (K L : Type) [Field K] [Field L] [Infinite K] (φ : K →+* L) (ι : Type) [Fintype ι] (N : ℕ)
    (ν : ι → Fin N → ℕ) (M : ι → Matrix (Fin N) (Fin N) L), ∀ Q ∈ WtPol K ν,
    (fun y : ι → Matrix (Fin N) (Fin N) L =>
      MvPolynomial.eval (fun k : ι × Fin N × Fin N => (M k.1 * y k.1) k.2.1 k.2.2) (MvPolynomial.map φ Q)) ∈
    Submodule.span L {F | ∃ g : ι → Matrix (Fin N) (Fin N) L → L, (∀ τ, g τ ∈ bideterminantFunctionsOfShape L N (ν τ)) ∧
      F = fun y => ∏ τ, g τ (y τ)} := by
  intro K L _ _ _ φ ι _ N ν M Q hQ

  have hT := Formalism.L2.Ker.wtPol_le_tensor (K := K) ν hQ
  clear hQ
  induction hT using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx

    have hfun : (fun y : ι → Matrix (Fin N) (Fin N) L =>
        MvPolynomial.eval (fun k : ι × Fin N × Fin N => (M k.1 * y k.1) k.2.1 k.2.2)
          (MvPolynomial.map φ (∏ s, Formalism.GradedWeylDivisibility.blockEmb K s (F s)))) =
        fun y => ∏ τ, evFn L N (Formalism.GradedWeylDivisibility.rowAct L (M τ) (MvPolynomial.map φ (F τ))) (y τ) := by
      funext y
      simp only [map_prod, Formalism.GradedWeylDivisibility.blockEmb, MvPolynomial.map_rename, MvPolynomial.eval_rename, evFn_apply,
        eval_rowAct, Function.comp_def]
    rw [hfun]
    apply prod_mem_span_prod
    intro τ
    apply evFn_mem_span
    exact Formalism.GradedWeylDivisibility.dualWeylRowStable L N N (ν τ) (M τ) _ (Formalism.GradedWeylDivisibility.dualWeylMap K L φ N N (ν τ) (F τ) (hF τ))
  | zero =>
    convert Submodule.zero_mem _ using 1
    funext y
    simp
  | add x x' _ _ hx hx' =>
    convert Submodule.add_mem _ hx hx' using 1
    funext y
    simp
  | smul c x _ hx =>
    convert Submodule.smul_mem _ (φ c) hx using 1
    funext y
    simp [MvPolynomial.smul_eq_C_mul]

end GlobalTheory.Mem.WeightBideterminants
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.GroupLoc.Crt

theorem mem_sup_prod_smul {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] (T N : Submodule R M)
    (I : ι → Ideal R) (hI : ∀ i j, i ≠ j → IsCoprime (I i) (I j)) {y : M} (hy : y ∈ N) (s : Finset ι)
    (h : ∀ i ∈ s, y ∈ T ⊔ I i • N) : y ∈ T ⊔ (∏ i ∈ s, I i) • N := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Submodule.mem_sup_right hy
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    have h1 := h i (Finset.mem_insert_self _ _)
    have h2 := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    have hc : IsCoprime (I i) (∏ j ∈ s, I j) :=
      IsCoprime.prod_right fun j hj => hI i j (fun e => hi (e ▸ hj))
    obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 hc
    have key : ∀ (A B : Ideal R) (c : R), c ∈ A → y ∈ T ⊔ B • N → c • y ∈ T ⊔ (A * B) • N := by
      intro A B c hc hy
      obtain ⟨t, ht, z, hz, rfl⟩ := Submodule.mem_sup.1 hy
      rw [smul_add]
      refine Submodule.add_mem_sup (T.smul_mem c ht) ?_
      rw [Submodule.mul_smul]
      exact Submodule.smul_mem_smul hc hz
    have e : y = a • y + b • y := by rw [← add_smul, hab, one_smul]
    rw [e]
    refine Submodule.add_mem _ (key _ _ a ha h2) ?_
    rw [mul_comm]
    exact key _ _ b hb h1

theorem mem_sup_smul_mono {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {T N : Submodule R M}
    {I J : Ideal R} (h : I ≤ J) {y : M} (hy : y ∈ T ⊔ I • N) : y ∈ T ⊔ J • N :=
  (sup_le_sup_left (Submodule.smul_mono_left h) T : T ⊔ I • N ≤ T ⊔ J • N) hy

theorem prod_le_span {O : Type*} [CommRing O] [IsDedekindDomain O] {g : O} (hg : g ≠ 0)
    (hsq : ∀ w : HeightOneSpectrum O, g ∉ w.asIdeal ^ 2) (s : Finset (HeightOneSpectrum O))
    (hs : ∀ w : HeightOneSpectrum O, g ∈ w.asIdeal → w ∈ s) :
    ∏ w ∈ s, w.asIdeal ≤ Ideal.span {g} := by
  have h0 : (Ideal.span {g} : Ideal O) ≠ ⊥ := fun e => hg (Ideal.span_singleton_eq_bot.1 e)
  have hsf : Squarefree (Ideal.span {g} : Ideal O) := by
    refine (squarefree_iff_no_irreducibles (x := (Ideal.span {g} : Ideal O)) h0).2 ?_
    intro x hx hd
    have hp : Prime x := UniqueFactorizationMonoid.irreducible_iff_prime.1 hx
    refine hsq ⟨x, Ideal.isPrime_of_prime hp, hp.ne_zero⟩ ?_
    rw [Ideal.dvd_span_singleton, ← pow_two] at hd
    exact hd
  have hrad : (Ideal.span {g}).radical ≤ Ideal.span {g} := by
    rintro x ⟨n, hn⟩
    rw [← Ideal.dvd_span_singleton] at hn ⊢
    rw [← Ideal.span_singleton_pow] at hn
    exact hsf.isRadical n _ hn
  refine le_trans ?_ hrad
  rw [Ideal.radical_eq_sInf]
  refine le_sInf ?_
  rintro P ⟨hP1, hP2⟩
  have hP0 : P ≠ ⊥ := fun e => h0 (le_bot_iff.1 (hP1.trans e.le))
  have hm := hs ⟨P, hP2, hP0⟩ ((Ideal.span_singleton_le_iff_mem _).1 hP1)
  have hle : ∏ w ∈ s, w.asIdeal ≤ (⟨P, hP2, hP0⟩ : HeightOneSpectrum O).asIdeal :=
    (Ideal.prod_le_inf (s := s) (f := fun w : HeightOneSpectrum O => w.asIdeal)).trans (Finset.inf_le hm)
  exact hle

variable {D : D7}

theorem g_not_mem_sq (w : HeightOneSpectrum (𝓞 D.host.E)) :
    ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal ^ 2 := by
  intro hm
  have hc : IsCoprime ((D.host.g 0 : ℕ) : 𝓞 D.host.E) ((D.host.g 1 : ℕ) : 𝓞 D.host.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)
  have key : ∀ k (b : 𝓞 D.host.E), IsCoprime ((D.host.g k : ℕ) : 𝓞 D.host.E) b →
      ((D.host.g k : ℕ) : 𝓞 D.host.E) * b ∈ w.asIdeal ^ 2 → ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
    rintro k b ⟨u, v, huv⟩ h hk
    refine (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) w hk).2.1 ?_
    have e : ((D.host.g k : ℕ) : 𝓞 D.host.E) =
        u * ((D.host.g k : ℕ) : 𝓞 D.host.E) ^ 2 + v * (((D.host.g k : ℕ) : 𝓞 D.host.E) * b) := by
      linear_combination (-((D.host.g k : ℕ) : 𝓞 D.host.E)) * huv
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hk 2)) (Ideal.mul_mem_left _ _ h)
  rw [Nat.cast_mul] at hm
  rcases w.isPrime.mem_or_mem (Ideal.pow_le_self two_ne_zero hm) with h | h
  · exact key 0 _ hc hm h
  · exact key 1 _ hc.symm (mul_comm (G := 𝓞 D.host.E) _ _ ▸ hm) h

def toInt (I : Formalism.MainNotions.S.AutInst) : 𝓞 I.E →+* Formalism.MainNotions.S.IntAf I.F I.E :=
  ((Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)).comp (algebraMap (𝓞 I.E) I.E)).codRestrict _ fun t =>
    Subring.subset_closure (Or.inl ⟨⟨algebraMap (𝓞 I.E) I.E t, ⟨t, rfl⟩⟩, rfl⟩)

theorem toInt_smul (I : Formalism.MainNotions.S.AutInst) (a : 𝓞 I.E) (y : Fin I.n → I.E) :
    toInt I a • incl I y = incl I ((a : I.E) • y) := by
  funext i
  show Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (a : I.E) * Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (y i) =
    Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) ((a : I.E) * y i)
  rw [map_mul]

def hostInt (X : HidaSetting D) : 𝓞 D.host.E →+* Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E :=
  (toInt X.B.I).comp (RingOfIntegers.mapRingEquiv X.ιE.symm).toRingHom

theorem wLf_eq (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    wLf X w = (w.asIdeal.map (hostInt X)) • X.B.I.Lf := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    show incl X.B.I x ∈ (w.asIdeal.map (hostInt X)) • X.B.I.Lf
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, ⟨b, hb, hab⟩, y, hy, rfl⟩ := hz
      rw [← toInt_smul]
      have : toInt X.B.I a = hostInt X b := by
        refine congrArg (toInt X.B.I) (RingOfIntegers.ext ?_)
        show (a : X.B.I.E) = X.ιE.symm (b : D.host.E)
        rw [← hab, RingEquiv.symm_apply_apply]
      rw [this]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hb) (Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩)
    | zero =>
      have : incl X.B.I 0 = 0 := funext fun i => map_zero _
      rw [this]; exact zero_mem _
    | add x y _ _ hx hy =>
      have : incl X.B.I (x + y) = incl X.B.I x + incl X.B.I y := funext fun i => map_add _ _ _
      rw [this]; exact add_mem hx hy
    | smul a x _ hx =>
      have : incl X.B.I (a • x) = toInt X.B.I a • incl X.B.I x := (toInt_smul _ a x).symm
      rw [this]; exact Submodule.smul_mem _ _ hx
  · unfold Ideal.map
    rw [show X.B.I.Lf = Submodule.span _ (Set.range fun x : X.B.I.L => incl X.B.I x) from rfl]
    rw [Submodule.span_smul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨b, hb, rfl⟩, _, ⟨⟨y, hy⟩, rfl⟩, rfl⟩
    show toInt X.B.I (RingOfIntegers.mapRingEquiv X.ιE.symm b) • incl X.B.I y ∈ wLf X w
    rw [toInt_smul]
    refine Submodule.subset_span ⟨⟨_, Submodule.subset_span ⟨_, ⟨b, hb, ?_⟩, y, hy, rfl⟩⟩, rfl⟩
    exact X.ιE.apply_symm_apply _

theorem mL_eq (X : HidaSetting D) (m : ℕ) :
    mL X.B.I m = ((Ideal.span {(m : 𝓞 D.host.E)}).map (hostInt X)) • X.B.I.Lf := by
  rw [Ideal.map_span, Set.image_singleton, map_natCast]
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    exact Submodule.smul_mem_smul (r := (m : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E)) (Ideal.mem_span_singleton_self _) hx
  · refine Submodule.smul_le.2 fun r hr x hx => ?_
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [mul_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, hx, rfl⟩)

theorem inMod_iff_forall_modW : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (S : Set (VA X.B.I)), S ⊆ X.B.I.Lf → ∀ y ∈ X.B.I.Lf, (InMod X.B.I X.B.g S y ↔ ∀ w : HeightOneSpectrum (𝓞 D.host.E), ((X.B.g : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal → GlobalTheory.Mem.GroupLoc.ModW X w S y) := by
  intro D X _ _ S _ y hy
  unfold InMod ModW
  simp only [mL_eq, wLf_eq]
  constructor
  · intro h w hw
    exact mem_sup_smul_mono (Ideal.map_mono ((Ideal.span_singleton_le_iff_mem _).2 hw)) h
  · intro h
    have hg : ((X.B.g : ℕ) : 𝓞 D.host.E) ≠ 0 := by
      rw [X.g_eq]
      exact Nat.cast_ne_zero.2 (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
    have hfin : {w : HeightOneSpectrum (𝓞 D.host.E) | ((X.B.g : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal}.Finite := by
      have := Ideal.finite_factors (I := Ideal.span {((X.B.g : ℕ) : 𝓞 D.host.E)}) (by simpa using hg)
      simpa only [Ideal.dvd_span_singleton] using this
    have h1 := mem_sup_prod_smul _ _ (fun w : HeightOneSpectrum (𝓞 D.host.E) => w.asIdeal.map (hostInt X))
      (fun i j hij => by
        rw [Ideal.isCoprime_iff_sup_eq, ← Ideal.map_sup,
          i.isMaximal.coprime_of_ne j.isMaximal (fun e => hij (HeightOneSpectrum.ext e)), Ideal.map_top])
      hy hfin.toFinset (fun w hw => h w (hfin.mem_toFinset.1 hw))
    refine mem_sup_smul_mono ?_ h1
    have h2 := prod_le_span hg (fun w => by rw [X.g_eq]; exact g_not_mem_sq w) hfin.toFinset
      (fun w hw => hfin.mem_toFinset.2 hw)
    refine le_trans (le_of_eq ?_) (Ideal.map_mono h2)
    exact (map_prod (Ideal.mapHom (hostInt X)) _ _).symm

end GlobalTheory.Mem.GroupLoc.Crt

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymChar.Resid

open GlobalTheory.Mem.SymFrame

variable {D : D7}

theorem rank_eq (D : D7) : D.R.r = D.R.k + 2 * D.R.rS + 1 := by
  unfold Ranks.r Ranks.rS
  obtain ⟨t, ht⟩ := D.R.m_even
  have := D.R.two_le_m
  omega

def posE (D : D7) (a : Fin D.R.rS) : Fin D.R.r := ⟨a.1, by have := rank_eq D; omega⟩

def posB (D : D7) (i : Fin D.R.k) : Fin D.R.r := ⟨D.R.rS + i.1, by have := rank_eq D; omega⟩

def posN (D : D7) (a : Fin D.R.rS) : Fin D.R.r :=
  ⟨if a.1 + 1 < D.R.rS then a.1 + 1 else D.R.rS + D.R.k, by have := rank_eq D; split_ifs <;> omega⟩

theorem symVec_posN (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (a : Fin D.R.rS) :
    symVec X w (posN D a) = nxt X.e0 X.z0 a := by
  unfold symVec GlobalTheory.SeeConjRead.flagV posN nxt
  by_cases h : a.1 + 1 < D.R.rS
  · simp [h]
  · have h2 : ¬ (D.R.rS + D.R.k < D.R.rS) := by omega
    simp [h]

theorem symVec_posB (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : EwAt X w) (i : Fin D.R.k) :
    symVec X w (posB D i) = X.bw i := by
  unfold symVec GlobalTheory.SeeConjRead.flagV posB epsW
  have h1 : ¬ (D.R.rS + i.1 < D.R.rS) := by omega
  have h2 : D.R.rS + i.1 < D.R.rS + D.R.k := by omega
  simp [h1, h2, hw]

theorem dual_row (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) {g : ℕ} {u : Fin D.R.r → VA X.B.I}
    {x : X.B.I.Gf} {N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod g)} (hN : IsMatIn X w u x N)
    {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) (i₀ : Fin D.R.r)
    (hd : ∀ j, hA X.B.I y (u j) - (if j = i₀ then 1 else 0) ∈ wInt X w) (i : Fin D.R.r) :
    hA X.B.I y (X.B.I.fmat x *ᵥ u i) - (((N i₀ i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈
      wInt X w := by
  have h := hA_isMatIn X w hN hy i
  have hs : (∑ j, (((N j i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) *
      (hA X.B.I y (u j) - (if j = i₀ then 1 else 0))) ∈ wInt X w := by
    refine Submodule.sum_mem _ fun j _ => ?_
    exact (wInt X w).smul_mem
      (⟨_, natCast_mem _ (N j i).val⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) (hd j)
  have e : (∑ j, (((N j i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) *
      (hA X.B.I y (u j) - (if j = i₀ then 1 else 0))) =
      (∑ j, (((N j i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * hA X.B.I y (u j)) -
        (((N i₀ i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) := by
    simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  rw [e] at hs
  have := add_mem h hs
  convert this using 1
  abel

theorem natCast_g_mem (X : HidaSetting D) {w : HeightOneSpectrum (𝓞 D.host.E)} (k : Fin 2)
    (hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) :
    ((D.host.g k : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w := by
  refine Submodule.subset_span ⟨(D.host.g k : 𝓞 X.B.I.E), ⟨_, hg, ?_⟩, ?_⟩
  · simp
  · simp

theorem one_sub_ew_mem (X : HidaSetting D) {w : HeightOneSpectrum (𝓞 D.host.E)} (k : Fin 2)
    (hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) (hw : EwAt X w) : 1 - X.ew ∈ wInt X w := by
  have hz : X.z0 ∈ X.B.I.Lf := X.vectorsInLattice.2.1
  have h1 := hA_mem_wInt X w hz (hw X.z0 hz)
  rw [hA_smul_right'] at h1
  have h2 := wInt_of_zmod X k hg X.formsAtZero.1
  have hint : 1 - X.ew ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E := sub_mem (one_mem _) X.ew_int
  have h3 : (1 - X.ew) * (hA X.B.I X.z0 X.z0 + 1) ∈ wInt X w :=
    (wInt X w).smul_mem (⟨_, hint⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) h2
  have := sub_mem h3 h1
  convert this using 1
  ring

end GlobalTheory.Mem.SymChar.Resid
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.standardAdelicCharacter_localComponent_ne_one : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ v, ∃ y, psiV D.host.F ψ v y ≠ 1 := by
  first | exact @GlobalTheory.StdCharLocal.psiV_ne_one | exact GlobalTheory.StdCharLocal.psiV_ne_one | (intros; apply GlobalTheory.StdCharLocal.psiV_ne_one <;> assumption)
end
