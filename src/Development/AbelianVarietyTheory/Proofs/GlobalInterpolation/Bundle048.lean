module

public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
public import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Formalism.LocalToGlobal.HermitianForms.Bundle002
public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle001
public import Formalism.SatakeDualWeyl.Bundle001
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle004
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Nat.Totient
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ArithmeticLargeSieveOneResidueClassPerPrime
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle003
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.L2.Col

namespace GlobalTheory.SplitUnram

variable {E : Type} [Field E] [NumberField E]

theorem absNorm_span_invol (s : 𝓞 E →+* 𝓞 E) (hs : ∀ x, s (s x) = x) (a : 𝓞 E) :
    Ideal.absNorm (Ideal.span {s a}) = Ideal.absNorm (Ideal.span {a}) := by
  let e : 𝓞 E ≃+* 𝓞 E := RingEquiv.ofRingHom s s (RingHom.ext hs) (RingHom.ext hs)
  let e' : 𝓞 E ≃ₐ[ℤ] 𝓞 E := AlgEquiv.ofRingEquiv (f := e) (fun n => by simp)
  rw [Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton]
  exact congrArg Int.natAbs (Algebra.norm_eq_of_algEquiv e' a)

theorem natCast_notMem_sq : ∀ (E : Type) [Field E] [NumberField E] (s : 𝓞 E →+* 𝓞 E) (a : 𝓞 E) (p : ℕ),
    (∀ x, s (s x) = x) → p.Prime → a * s a = (p : 𝓞 E) → IsCoprime a (s a) →
    2 * (divs a).card = Module.finrank ℚ E → (∀ P ∈ divs a, Ideal.absNorm P.asIdeal = p) →
    ∀ P ∈ divs a, ((p : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 := by
  intro E _ _ s a p hs hp ha hcop hcard hN P hP hmem
  classical
  have hp0 : (p : 𝓞 E) ≠ 0 := by exact_mod_cast hp.ne_zero
  have ha0 : a ≠ 0 := left_ne_zero_of_mul (ha ▸ hp0)
  have hnorm : Ideal.absNorm (Ideal.span {a}) = p ^ (divs a).card := by
    have h1 : Ideal.absNorm (Ideal.span {a}) ^ 2 = (p ^ (divs a).card) ^ 2 := by
      rw [← pow_mul, mul_comm, hcard, ← RingOfIntegers.rank, ← Ideal.absNorm_span_natCast, ← ha,
        ← Ideal.span_singleton_mul_span_singleton, map_mul, absNorm_span_invol s hs, sq]
    exact Nat.pow_left_injective two_ne_zero h1
  have haP : a ∈ P.asIdeal := (mem_divs ha0 P).1 hP
  have ha2 : a ∈ P.asIdeal ^ 2 := by
    obtain ⟨u, v, huv⟩ := hcop
    have h1 : a = u * a ^ 2 + v * (p : 𝓞 E) := by
      rw [← ha]
      linear_combination (-a) * huv
    rw [h1]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow haP 2)) (Ideal.mul_mem_left _ _ hmem)
  have hd1 : P.asIdeal ^ 2 ∣ Ideal.span {a} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact ha2
  have hd2 : ∏ Q ∈ (divs a).erase P, Q.asIdeal ∣ Ideal.span {a} := by
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro P _ Q _ hPQ
      exact (HeightOneSpectrum.isCoprime_of_ne P Q hPQ)
    · intro Q hQ
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact (mem_divs ha0 Q).1 (Finset.mem_of_mem_erase hQ)
  have hc : IsCoprime (P.asIdeal ^ 2) (∏ Q ∈ (divs a).erase P, Q.asIdeal) := by
    refine IsCoprime.pow_left (IsCoprime.prod_right fun Q hQ => ?_)
    exact HeightOneSpectrum.isCoprime_of_ne P Q (Finset.ne_of_mem_erase hQ).symm
  have hd := map_dvd Ideal.absNorm (hc.mul_dvd hd1 hd2)
  rw [hnorm, map_mul, map_pow, map_prod, hN P hP,
    Finset.prod_congr rfl (fun Q hQ => hN Q (Finset.mem_of_mem_erase hQ)), Finset.prod_const, ← pow_add,
    Nat.pow_dvd_pow_iff_le_right hp.one_lt] at hd
  have h3 := Finset.card_erase_add_one hP
  omega

end GlobalTheory.SplitUnram
end

section

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory

theorem gLevH_chi_pow_eq_one_and_mem_range : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (gp : Fin 2 → ℕ) (G : GLoc F E σ gp) (H : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin n) (kv F v))) (lam : ∀ a v h, H a v h →* ℂˣ) (_ : GLevH S G H lam) (K : Type) [Field K] (s : K →+* ℂ) (N : ℕ), (∀ i, (gp i).Prime) → (∀ a v h M, ((lam a v h M : ℂˣ) : ℂ) ^ N = 1 ∧ ∃ r : K, s r = ((lam a v h M : ℂˣ) : ℂ)) → ∀ x : S.U, ((S.chi x : ℂˣ) : ℂ) ^ N = 1 ∧ ∃ r : K, s r = ((S.chi x : ℂˣ) : ℂ) := by
  intro F E _ _ _ _ _ σ n J T f bad S gp G H lam L K _ s N _ hl x
  have hmul : ∀ a b : ℂ, (a ^ N = 1 ∧ ∃ r : K, s r = a) → (b ^ N = 1 ∧ ∃ r : K, s r = b) →
      ((a * b) ^ N = 1 ∧ ∃ r : K, s r = a * b) := by
    rintro a b ⟨ha, r, hr⟩ ⟨hb, r', hr'⟩
    exact ⟨by rw [mul_pow, ha, hb, one_mul], r * r', by rw [map_mul, hr, hr']⟩
  have hone : (1 : ℂ) ^ N = 1 ∧ ∃ r : K, s r = 1 := ⟨one_pow N, 1, map_one s⟩
  rw [L.chi_eq x]
  refine Finset.prod_induction _ (fun z : ℂ => z ^ N = 1 ∧ ∃ r : K, s r = z) hmul hone ?_
  intro a _
  refine finprod_induction (fun z : ℂ => z ^ N = 1 ∧ ∃ r : K, s r = z) hone hmul ?_
  intro v
  refine finprod_induction (fun z : ℂ => z ^ N = 1 ∧ ∃ r : K, s r = z) hone hmul ?_
  intro h
  obtain ⟨h1, r, hr⟩ := hl a v h (L.red a v h x)
  exact ⟨by rw [inv_pow, h1, inv_one], r⁻¹, by rw [map_inv₀, hr]⟩

end GlobalTheory
end

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory

theorem goodLift_pow_smul_mem : ∀ (g : ℕ) (S : JMB.Setup g) (p : ℕ) [Fact p.Prime] (lam : JMB.Qbar →+* ℂ_[p]) (N₀ n : ℕ), S.Ok →
    ∀ y ∈ AddSubgroup.closure {y : Fin g → ℂ | ∃ κ ∈ JMB.OK S.d,
      ‖JMB.lamA lam ((starRingEnd ℂ) κ)‖ ≤ (p : ℝ) ^ (-(2 * n : ℤ)) ∧
      ∃ x ∈ S.La, y = (κ * (N₀ : ℂ) / (p : ℂ) ^ n) • x}, ((p : ℂ) ^ n) • y ∈ S.La := by
  intro g S p _ lam N₀ n hS y hy
  have hw : ∀ x ∈ S.La, JMB.w0 S.d • x ∈ S.La := hS.2.2.2.2.2.1
  have hzs : ∀ (z : ℤ) (x : Fin g → ℂ), x ∈ S.La → ((z : ℂ)) • x ∈ S.La := by
    intro z x hx
    rw [Int.cast_smul_eq_zsmul ℂ z x]
    exact S.La.smul_mem z hx
  have hp : ((p : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨κ, ⟨u, v, hκ⟩, _, x, hx, rfl⟩ := hy
    rw [smul_smul, mul_div_cancel₀ _ hp, hκ]
    have : ((u : ℂ) + (v : ℂ) * JMB.w0 S.d) * (N₀ : ℂ) = ((u * N₀ : ℤ) : ℂ) + ((v * N₀ : ℤ) : ℂ) * JMB.w0 S.d := by
      push_cast; ring
    rw [this, add_smul, mul_smul]
    exact S.La.add_mem (hzs _ _ hx) (hzs _ _ (hw x hx))
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact S.La.add_mem ha hb
  | neg a _ ha => rw [smul_neg]; exact S.La.neg_mem ha

end GlobalTheory
end

section

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.MainNotions.StandardLattice
open scoped TensorProduct

namespace GlobalTheory.LatticeStabLocal

section Gen
variable {F E : Type} [Field F] [Field E] [NumberField E] [Algebra F E] {n : Type}
  {R : Type} [CommRing R] [Algebra F R] (T : Subring R) (N : Submodule (𝓞 E) (n → E))
  {k : ℕ} (s : Fin k → N)

def IsComb (u : n → E ⊗[F] R) : Prop :=
  ∃ a : Fin k → R, (∀ j, a j ∈ T) ∧ ∀ i, u i = ∑ j, (s j : n → E) i ⊗ₜ[F] a j

variable {T N s}

theorem isComb_zero : IsComb (F := F) T N s 0 :=
  ⟨0, fun _ => zero_mem _, fun i => by simp⟩

theorem IsComb.add {y z : n → E ⊗[F] R} (hy : IsComb T N s y) (hz : IsComb T N s z) :
    IsComb T N s (y + z) := by
  obtain ⟨a, ha, ea⟩ := hy
  obtain ⟨b, hb, eb⟩ := hz
  exact ⟨a + b, fun j => add_mem (ha j) (hb j), fun i => by
    simp only [Pi.add_apply, ea, eb, TensorProduct.tmul_add, Finset.sum_add_distrib]⟩

theorem IsComb.neg {y : n → E ⊗[F] R} (hy : IsComb T N s y) : IsComb T N s (-y) := by
  obtain ⟨a, ha, ea⟩ := hy
  exact ⟨-a, fun j => neg_mem (ha j), fun i => by
    simp only [Pi.neg_apply, ea, TensorProduct.tmul_neg, Finset.sum_neg_distrib]⟩

theorem isComb_tmul (hs : Submodule.span ℤ (Set.range s) = ⊤) {w : n → E} (hw : w ∈ N) {a : R}
    (ha : a ∈ T) : IsComb (F := F) T N s (fun i => w i ⊗ₜ[F] a) := by
  have : (⟨w, hw⟩ : N) ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨m, hm⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 this
  have e : w = ∑ j, m j • (s j : n → E) := by simpa using (congrArg Subtype.val hm).symm
  refine ⟨fun j => m j • a, fun j => zsmul_mem ha _, fun i => ?_⟩
  rw [e]
  simp only [Finset.sum_apply, Pi.smul_apply, TensorProduct.sum_tmul]
  exact Finset.sum_congr rfl fun j _ => TensorProduct.smul_tmul _ _ _

theorem IsComb.smul (hs : Submodule.span ℤ (Set.range s) = ⊤) {t : E ⊗[F] R}
    (ht : t ∈ tensInt (F := F) R (intOE E) T) :
    ∀ {y : n → E ⊗[F] R}, IsComb T N s y → IsComb T N s (t • y) := by
  refine Subring.closure_induction
    (p := fun t _ => ∀ {y : n → E ⊗[F] R}, IsComb T N s y → IsComb T N s (t • y))
    ?_ ?_ ?_ ?_ ?_ ?_ ht
  · rintro x (⟨⟨e, ⟨e', rfl⟩⟩, rfl⟩ | ⟨⟨b, hb⟩, rfl⟩) y ⟨a, ha, ea⟩
    · have : ((algebraMap (𝓞 E) E e' ⊗ₜ[F] (1 : R)) • y : n → E ⊗[F] R) =
          ∑ j, fun i => (e' • (s j : n → E)) i ⊗ₜ[F] a j := by
        funext i
        rw [Pi.smul_apply, ea, smul_eq_mul, Finset.mul_sum, Finset.sum_apply]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Pi.smul_apply, Algebra.smul_def]
      change IsComb T N s ((algebraMap (𝓞 E) E e' ⊗ₜ[F] (1 : R)) • y)
      rw [this]
      exact Finset.sum_induction _ (IsComb T N s) (fun _ _ hx hy => hx.add hy) isComb_zero
        fun j _ => isComb_tmul hs (N.smul_mem e' (s j).2) (ha j)
    · refine ⟨fun j => b * a j, fun j => mul_mem hb (ha j), fun i => ?_⟩
      change ((1 : E) ⊗ₜ[F] b) * y i = _
      rw [ea, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  · intro y _; rw [zero_smul]; exact isComb_zero
  · intro y hy; rwa [one_smul]
  · intro a b _ _ ha hb y hy; rw [add_smul]; exact (ha hy).add (hb hy)
  · intro a _ ha y hy; rw [neg_smul]; exact (ha hy).neg
  · intro a b _ _ ha hb y hy; rw [mul_smul]; exact ha (hb hy)

theorem mem_latS_iff_isComb (hs : Submodule.span ℤ (Set.range s) = ⊤) (u : n → E ⊗[F] R) :
    u ∈ latS R (tensInt (F := F) R (intOE E) T) N ↔ IsComb T N s u := by
  constructor
  · intro hu
    unfold latS at hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      exact isComb_tmul hs hw (one_mem T)
    | zero => exact isComb_zero
    | add x y _ _ hx hy => exact hx.add hy
    | smul t x _ hx => exact IsComb.smul hs t.2 hx
  · rintro ⟨a, ha, ea⟩
    have e : u = ∑ j, (⟨(1 : E) ⊗ₜ[F] a j, Subring.subset_closure (Or.inr ⟨⟨a j, ha j⟩, rfl⟩)⟩ :
        tensInt (F := F) R (intOE E) T) • fun i => inclE (F := F) R ((s j : n → E) i) := by
      funext i
      rw [ea, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      change _ = ((1 : E) ⊗ₜ[F] a j) * ((s j : n → E) i ⊗ₜ[F] (1 : R))
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [e]
    exact sum_mem fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨s j, (s j).2, rfl⟩)

end Gen

section Adelic
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : Type}
  (N : Submodule (𝓞 E) (n → E))

theorem mem_latS_adele_iff [Module.Finite (𝓞 E) N] (u : n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    u ∈ latS (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) N ↔
      ∀ v : HeightOneSpectrum (𝓞 F), (fun i => prV (E := E) v (u i)) ∈
        latS (v.adicCompletion F) (tensInt (F := F) (v.adicCompletion F) (intOE E)
          (v.adicCompletionIntegers F).toSubring) N := by
  have : Module.Finite ℤ N := Module.Finite.trans (𝓞 E) N
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := N)
  simp only [mem_latS_iff_isComb hs]
  constructor
  · rintro ⟨a, ha, ea⟩ v
    refine ⟨fun j => a j v, fun j => ha j v, fun i => ?_⟩

    simp only [ea, map_sum]
    rfl
  · intro h
    choose a ha ea using h
    let A : Fin k → FiniteAdeleRing (𝓞 F) F :=
      fun j => ⟨fun v => a v j, Filter.Eventually.of_forall fun v => ha v j⟩
    refine ⟨A, fun j v => ha v j, fun i => ?_⟩
    rw [← sub_eq_zero]
    refine Formalism.UG.P.afsplit_inj _ fun v => ?_

    rw [map_sub, sub_eq_zero, map_sum]
    exact ea v i

theorem prV_mulVec [Fintype n] (v : HeightOneSpectrum (𝓞 F))
    (M : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (u : n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    (fun i => prV (E := E) v ((M *ᵥ u) i)) =
      M.map (prV (E := E) v) *ᵥ fun i => prV (E := E) v (u i) := by
  funext i
  exact RingHom.map_mulVec _ M u i

theorem mem_stabGL_adele_iff [Fintype n] [DecidableEq n] [Module.Finite (𝓞 E) N]
    (g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
    g ∈ stabGL (latS (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) N) ↔
      ∀ v : HeightOneSpectrum (𝓞 F), bc (prV (E := E) v) g ∈
        stabGL (latS (v.adicCompletion F) (tensInt (F := F) (v.adicCompletion F) (intOE E)
          (v.adicCompletionIntegers F).toSubring) N) := by
  constructor
  · intro hg v x
    have key := hg fun i => Formalism.UG.P.afsplitIE v (x i)
    rw [mem_latS_adele_iff, mem_latS_adele_iff] at key
    simp only [prV_mulVec] at key
    have h0 : ∀ w, w ≠ v → (fun i => prV (E := E) w (Formalism.UG.P.afsplitIE v (x i))) = 0 :=
      fun w hw => funext fun i => Formalism.UG.P.afsplit_prV_IE_ne v w hw _
    have h1 : (fun i => prV (E := E) v (Formalism.UG.P.afsplitIE v (x i))) = x :=
      funext fun i => Formalism.UG.P.afsplit_prV_IE v _
    rw [Formalism.UG.P.afsplit_coe_bc_prV]
    constructor
    · intro hx
      have := key.1 (fun w => by
        by_cases hw : w = v
        · subst hw; rw [h1]; exact hx
        · rw [h0 w hw]; exact zero_mem _) v
      rwa [h1] at this
    · intro hx
      have := key.2 (fun w => by
        by_cases hw : w = v
        · subst hw; rw [h1]; exact hx
        · rw [h0 w hw, Matrix.mulVec_zero]; exact zero_mem _) v
      rwa [h1] at this
  · intro h u
    rw [mem_latS_adele_iff, mem_latS_adele_iff]
    refine forall_congr' fun v => ?_
    rw [prV_mulVec]
    exact h v _

end Adelic

theorem mem_levelAfL_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (N : Submodule (𝓞 E) (Fin n → E)), Module.Finite (𝓞 E) N → ∀ g, g ∈ levelAfL σ J N ↔ g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) ∧ ∀ v : HeightOneSpectrum (𝓞 F), bc (prV (E := E) v) g ∈ levelVL σ J v N := by
  intro F E _ _ _ _ _ σ n J N hN g
  constructor
  · intro hg
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hg
    exact ⟨h1, fun v => Subgroup.mem_inf.2 ⟨Formalism.UG.P.afsplit_bc_mem σ J v g h1,
      (mem_stabGL_adele_iff N g).1 h2 v⟩⟩
  · rintro ⟨h1, h2⟩
    exact Subgroup.mem_inf.2 ⟨h1, (mem_stabGL_adele_iff N g).2 fun v => (Subgroup.mem_inf.1 (h2 v)).2⟩

end GlobalTheory.LatticeStabLocal
end

section

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.MainNotions.StandardLattice
open scoped TensorProduct

namespace GlobalTheory

theorem stabGL_iff_conj_stdLat {A : Type} [CommRing A] (S : Subring A) {n : Type} [Fintype n]
    [DecidableEq n] (b : GL n A) (Λ : Submodule S (n → A))
    (hΛ : ∀ x, x ∈ Λ ↔ ∀ i, ((b⁻¹).1 *ᵥ x) i ∈ S) (g : GL n A) :
    g ∈ stabGL Λ ↔ b⁻¹ * g * b ∈ stabGL (stdLat (n := n) (A := A) S) := by
  have key : ∀ x : n → A, x ∈ Λ ↔ (b⁻¹).1 *ᵥ x ∈ stdLat (n := n) (A := A) S := fun x => by
    rw [hΛ, Formalism.UG.P.afsplit_mem_stdLat]
  constructor
  · intro hg y
    have h := hg (b.1 *ᵥ y)
    rw [key, key] at h
    simpa only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Units.val_mul,
      Matrix.mul_assoc] using h
  · intro hg x
    have h := hg ((b⁻¹).1 *ᵥ x)
    rw [key, key]
    simpa only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.mul_one, Units.val_mul,
      Matrix.mul_assoc] using h

theorem conj_mem_UJ_one {A : Type} [CommRing A] (τ : A →+* A) {n : Type} [Fintype n]
    [DecidableEq n] (J : Matrix n n A) (b : GL n A) (hb : cT τ b.1 * J * b.1 = 1)
    (g : GL n A) (hg : g ∈ UJ τ J) : b⁻¹ * g * b ∈ UJ τ (1 : Matrix n n A) := by
  have hg' : cT τ g.1 * J * g.1 = J := hg
  have cm : ∀ M N : Matrix n n A, cT τ (M * N) = cT τ N * cT τ M := fun M N => by
    simp only [cT, Matrix.map_mul, Matrix.transpose_mul]
  have c1 : cT τ (1 : Matrix n n A) = 1 := by
    simp only [cT, Matrix.map_one _ (map_zero τ) (map_one τ), Matrix.transpose_one]
  have hJ : cT τ (b⁻¹).1 * (b⁻¹).1 = J := by
    calc cT τ (b⁻¹).1 * (b⁻¹).1 = cT τ (b⁻¹).1 * (cT τ b.1 * J * b.1) * (b⁻¹).1 := by
          rw [hb, Matrix.mul_one]
      _ = cT τ (b.1 * (b⁻¹).1) * J * (b.1 * (b⁻¹).1) := by
          rw [cm]; simp only [Matrix.mul_assoc]
      _ = J := by rw [Units.mul_inv, c1, Matrix.one_mul, Matrix.mul_one]
  change cT τ (b⁻¹ * g * b).1 * 1 * (b⁻¹ * g * b).1 = 1
  calc cT τ (b⁻¹ * g * b).1 * 1 * (b⁻¹ * g * b).1
      = cT τ b.1 * (cT τ g.1 * (cT τ (b⁻¹).1 * (b⁻¹).1) * g.1) * b.1 := by
        simp only [Units.val_mul, cm, Matrix.mul_one, Matrix.mul_assoc]
    _ = 1 := by rw [hJ, hg', hb]

theorem split_stabGL_iff_mem_range :
    ∀ (A K : Type) [CommRing A] [Field K] (O : ValuationSubring K) (S : Subring A) (τ : A →+* A) (φ : A ≃+* K × K), (∀ x, φ (τ x) = swapR K (φ x)) → (∀ x, x ∈ S ↔ (φ x).1 ∈ O ∧ (φ x).2 ∈ O) → ∀ (n : Type) [Fintype n] [DecidableEq n] (J : Matrix n n A) (b : GL n A) (Λ : Submodule S (n → A)), cT τ b.1 * J * b.1 = 1 → (∀ x, x ∈ Λ ↔ ∀ i, ((b⁻¹).1 *ᵥ x) i ∈ S) → ∀ g ∈ UJ τ J, g ∈ stabGL Λ ↔ (bc ((RingHom.fst K K).comp φ.toRingHom) b)⁻¹ * bc ((RingHom.fst K K).comp φ.toRingHom) g * bc ((RingHom.fst K K).comp φ.toRingHom) b ∈ (bc (n := n) (algebraMap O K)).range := by
  intro A K _ _ O S τ φ hτ hS n _ _ J b Λ hb hΛ g hg
  have hU := conj_mem_UJ_one τ J b hb g hg
  rw [stabGL_iff_conj_stdLat S b Λ hΛ g, ← map_inv, ← map_mul, ← map_mul]
  generalize b⁻¹ * g * b = h at hU
  have hinj : Function.Injective (algebraMap O K) := Subtype.val_injective
  have hOr : ∀ x : K, x ∈ Set.range (algebraMap O K) ↔ x ∈ O :=
    fun x => ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩
  rw [Formalism.UG.P.afsplit_stab_iff, Formalism.UG.P.levelvsplit_mem_range_iff _ hinj, ← map_inv,
    Formalism.UG.P.levelvsplit_coe_bc, Formalism.UG.P.levelvsplit_coe_bc]
  simp only [hOr, hS]
  have main : ∀ k : GL n A, k ∈ UJ τ (1 : Matrix n n A) → ∀ i j,
      (φ (k.1 i j)).2 = (φ ((k⁻¹).1 j i)).1 := by
    intro k hk i j
    have rel := Formalism.UG.P.levelvsplit_unitary τ φ hτ _ k hk
    rw [Matrix.map_one _ (map_zero _) (map_one _)] at rel
    have hk1 : k.1.map ((RingHom.fst K K).comp φ.toRingHom) *
        (k⁻¹).1.map ((RingHom.fst K K).comp φ.toRingHom) = 1 := by
      rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    have s := Formalism.UG.P.levelvsplit_solve 1 1 _ _ _ (Matrix.mul_one _) hk1 rel
    rw [Matrix.one_mul, Matrix.mul_one] at s
    exact congrFun (congrFun s i) j
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j => (h1 i j).1, fun i j => (h2 i j).1⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j => ⟨h1 i j, ?_⟩, fun i j => ⟨h2 i j, ?_⟩⟩
    · rw [main h hU]; exact h2 j i
    · rw [main h⁻¹ (inv_mem hU), inv_inv]; exact h1 j i

end GlobalTheory
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

namespace GlobalTheory

theorem isFibreFamily_map_homeomorph : ∀ (V V' X X' : Type) [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace V'] [MeasurableSpace V'] [BorelSpace V'] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace X'] [MeasurableSpace X'] [BorelSpace X'] (e : V ≃ₜ V') (r : X ≃ₜ X') (μ : Measure V) (ν : Measure X) (f : V → X) (f' : V' → X') (B : Set X) (fib : X → Measure V), (∀ v, f' (e v) = r (f v)) → IsFibreFamily μ f id Set.univ ν B fib → IsFibreFamily (μ.map e) f' id Set.univ (ν.map r) (r '' B) fun b => (fib (r.symm b)).map e := by
  intro V V' X X' _ _ _ _ _ _ _ _ _ _ _ _ e r μ ν f f' B fib hf h
  obtain ⟨h1, h2, h3⟩ := h
  have he : MeasurableEmbedding e := e.measurableEmbedding
  have hr : MeasurableEmbedding r := r.measurableEmbedding
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hφ hc _ => ?_⟩
  · rw [he.map_apply]
    convert h1 (r.symm b) using 2
    ext v
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.inter_univ, Set.mem_singleton_iff, id, hf]
    exact not_congr r.eq_symm_apply.symm
  · have := h2 (fun v => φ (e v)) (hφ.comp he.measurable)
    rw [Measure.restrict_univ] at this ⊢
    rw [he.lintegral_map, hr.lintegral_map, this]
    refine lintegral_congr fun b => ?_
    rw [he.lintegral_map, r.symm_apply_apply]
  · obtain ⟨h4, h5⟩ := h3 (φ ∘ e) (hφ.comp e.continuous) (hc.comp_homeomorph e) (Set.subset_univ _)
    refine ⟨?_, ?_⟩
    · rintro _ ⟨b, hb, rfl⟩
      rw [he.integrable_map_iff, r.symm_apply_apply]
      exact h4 b hb
    · have h6 := h5.comp (s := r '' B) r.symm.continuous.continuousOn (by
        rintro _ ⟨b, hb, rfl⟩
        rw [r.symm_apply_apply]
        exact hb)
      refine h6.congr fun b _ => ?_
      simp only [Function.comp]
      rw [he.integral_map]

end GlobalTheory
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.arithmeticLargeSieve_one_residue_class_per_prime : ∀ (M N Q q : ℕ) (S : Finset ℕ), 1 ≤ Q → 1 ≤ q → S ⊆ Finset.Ioc M (M + N) → (∀ p : ℕ, p.Prime → p ≤ Q → ¬ p ∣ q → ∃ c : ℕ, ∀ n ∈ S, ¬ n ≡ c [MOD p]) → (S.card : ℝ) * ((q.totient : ℝ) / q * Real.log Q) ≤ (Q : ℝ) ^ 2 + 2 * Real.pi * N := by
  first | exact @GlobalTheory.arithmetic_large_sieve_one_class | exact GlobalTheory.arithmetic_large_sieve_one_class | (intros; apply GlobalTheory.arithmetic_large_sieve_one_class <;> assumption)
end
