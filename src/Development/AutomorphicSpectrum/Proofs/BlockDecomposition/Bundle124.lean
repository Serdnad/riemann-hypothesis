module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle084
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle082
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle113
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle101
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle112
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle107
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle043
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.SchCut
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle111
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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

@[expose] public section

section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DualCover

variable {E : Type} [Field E] [NumberField E]

def kcSub {m : ℕ} (c : Matrix (Fin m) (Fin m) E) : Submodule (𝓞 E) (Fin m → 𝓞 E) where
  carrier := (Kc c : Set (Fin m → 𝓞 E))
  add_mem' := fun hx hy => (Kc c).add_mem hx hy
  zero_mem' := (Kc c).zero_mem
  smul_mem' := by
    intro r y hy i
    obtain ⟨o, ho⟩ := hy i
    refine ⟨r * o, ?_⟩
    have h : (fun j => algebraMap (𝓞 E) E ((r • y) j)) =
        (algebraMap (𝓞 E) E r) • fun j => algebraMap (𝓞 E) E (y j) := by
      funext j
      simp
    rw [h, Matrix.mulVec_smul, Pi.smul_apply, ← ho, map_mul, smul_eq_mul]

def pair {m : ℕ} (w : Fin m → E) : (Fin m → 𝓞 E) →ₗ[𝓞 E] E where
  toFun y := ∑ j, w j * (y j : E)
  map_add' := by
    intro y z
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro r y
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change w j * ((r * y j : 𝓞 E) : E) = r • (w j * (y j : E))
    rw [Algebra.smul_def]
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul]
    ring

def bMod {m : ℕ} (c : Matrix (Fin m) (Fin m) E) (w : Fin m → E) : Submodule (𝓞 E) E :=
  1 ⊔ (kcSub c).map (pair w)

theorem bMod_fg {m : ℕ} (c : Matrix (Fin m) (Fin m) E) (w : Fin m → E) : (bMod c w).FG := by
  refine Submodule.FG.sup ?_ (Submodule.FG.map _ (IsNoetherian.noetherian _))
  rw [Submodule.one_eq_span]
  exact Submodule.fg_span_singleton _

variable {F : Type} [Field F] [Algebra F E]

theorem sO_mem_tor (σ : E →ₐ[F] E) (hinv : ∀ x, σ (σ x) = x)
    (hsO : ∀ o : 𝓞 E, ((sO σ o : 𝓞 E) : E) = σ (o : E)) {m : ℕ}
    (c : Matrix (Fin m) (Fin m) E) (hc : ∀ a b, σ (c b a) = c a b) (u : Fin m → E) (a : 𝓞 E)
    (ha : ∀ y ∈ Kc c, (a : E) * ∑ j, σ (u j) * (y j : E) ∈ (1 : Submodule (𝓞 E) E)) :
    sO σ a ∈ tor c u := by
  have hmem : (sO σ a) • u ∈ lam c := by
    refine GlobalTheory.T.mem_lattice_of_dual_pairing E m (lam c) (GlobalTheory.T.lam_is_lattice E m c) _ ?_
    intro a' hL

    have hstd : ∀ j, (Pi.single j (1 : E) : Fin m → E) ∈ intVec E m := by
      intro j i
      by_cases h : i = j
      · subst h
        exact ⟨1, by simp⟩
      · exact ⟨0, by simp [Pi.single_apply, h]⟩
    have hent : ∀ j, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = a' j := by
      intro j
      have h1 := hL _ (Submodule.mem_sup_left (hstd j) : _ ∈ lam c)
      rw [Submodule.mem_one] at h1
      obtain ⟨o, ho⟩ := h1
      exact ⟨o, by rw [ho]; simp⟩
    choose o ho using hent
    have hcol : ∀ i, ∃ p : 𝓞 E, algebraMap (𝓞 E) E p = ∑ j, a' j * c j i := by
      intro i
      have hx : c *ᵥ (Pi.single i (1 : E) : Fin m → E) ∈ lam c :=
        Submodule.mem_sup_right (Submodule.mem_map_of_mem (f := c.mulVecLin.restrictScalars (𝓞 E)) (hstd i))
      have h1 := hL _ hx
      rw [Submodule.mem_one] at h1
      obtain ⟨p, hp⟩ := h1
      refine ⟨p, ?_⟩
      rw [hp]
      simp [dotProduct, Matrix.mulVec_single_one, Matrix.col_apply]
    have hy : (fun j => sO σ (o j)) ∈ Kc c := by
      intro i
      obtain ⟨p, hp⟩ := hcol i
      refine ⟨sO σ p, ?_⟩
      have e1 : algebraMap (𝓞 E) E (sO σ p) = σ (algebraMap (𝓞 E) E p) := hsO p

      rw [e1, hp, map_sum]
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun j _ => ?_
      have e2 : algebraMap (𝓞 E) E (sO σ (o j)) = σ (a' j) := by
        rw [← ho j]; exact hsO (o j)
      rw [e2, map_mul, hc i j, mul_comm]
    have h2 := ha _ hy
    rw [Submodule.mem_one] at h2 ⊢
    obtain ⟨q, hq⟩ := h2
    refine ⟨sO σ q, ?_⟩
    have e1 : algebraMap (𝓞 E) E (sO σ q) = σ (algebraMap (𝓞 E) E q) := hsO q

    rw [e1, hq, map_mul, map_sum]
    simp only [dotProduct, Finset.mul_sum, Pi.smul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e3 : ((sO σ (o j) : 𝓞 E) : E) = σ (a' j) := by
      rw [hsO, ← ho j]
    simp only [e3, map_mul, hinv, Algebra.smul_def]
    have e4 : algebraMap (𝓞 E) E (sO σ a) = σ (a : E) := hsO a
    rw [e4]
    ring
  rw [tor, Ideal.mem_torsionOf_iff, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact hmem

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DualCover


open GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DualCover in
theorem GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.dual_cover : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (m : ℕ) (c : Matrix (Fin m) (Fin m) E), (∀ a b, σ (c b a) = c a b) → ∀ (u : Fin m → E) (b : E), (∀ t ∈ tor c u, σ (t : E) * b ∈ (1 : Submodule (𝓞 E) E)) → ∃ y : Fin m → 𝓞 E, y ∈ Kc c ∧ b - ∑ j, σ (u j) * (y j : E) ∈ (1 : Submodule (𝓞 E) E) := by
  open GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DualCover in
  intro F E _ _ _ _ _ σ hcm m c hc u b hb
  obtain ⟨hinv, -, hsO, -⟩ := GlobalTheory.T.cm_conjugation_properties F E σ hcm
  set w : Fin m → E := fun j => σ (u j) with hw
  let B : FractionalIdeal (nonZeroDivisors (𝓞 E)) E :=
    ⟨bMod c w, FractionalIdeal.isFractional_of_fg (bMod_fg c w)⟩
  have hB1 : (1 : E) ∈ B := by
    change (1 : E) ∈ bMod c w
    exact Submodule.mem_sup_left (Submodule.one_le.mp le_rfl)
  have hB0 : B ≠ 0 := by
    intro h
    rw [h, FractionalIdeal.mem_zero_iff] at hB1
    exact one_ne_zero hB1
  have hBi : B⁻¹ ≠ 0 := inv_ne_zero hB0
  have hbB : b ∈ B := by
    have hbi : b ∈ (B⁻¹)⁻¹ := by
      rw [FractionalIdeal.mem_inv_iff hBi]
      intro x hx
      rw [FractionalIdeal.mem_inv_iff hB0] at hx
      have hx1 := hx 1 hB1
      rw [mul_one, FractionalIdeal.mem_one_iff] at hx1
      obtain ⟨a, rfl⟩ := hx1
      have ht : sO σ a ∈ tor c u := by
        refine sO_mem_tor σ hinv hsO c hc u a ?_
        intro y hy
        have hyB : ∑ j, σ (u j) * (y j : E) ∈ B := by
          change _ ∈ bMod c w
          exact Submodule.mem_sup_right (Submodule.mem_map_of_mem (f := pair w) (show y ∈ kcSub c from hy))
        have := hx _ hyB
        rw [FractionalIdeal.mem_one_iff] at this
        obtain ⟨q, hq⟩ := this
        rw [Submodule.mem_one]
        exact ⟨q, hq⟩
      have h := hb _ ht
      rw [hsO, hinv] at h
      rw [Submodule.mem_one] at h
      obtain ⟨q, hq⟩ := h
      rw [FractionalIdeal.mem_one_iff]
      refine ⟨q, ?_⟩
      rw [mul_comm]
      exact hq
    rwa [inv_inv] at hbi
  have hbB' : b ∈ bMod c w := hbB
  obtain ⟨p, hp, z, hz, hpz⟩ := Submodule.mem_sup.mp hbB'
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hz
  refine ⟨y, hy, ?_⟩
  have : b - ∑ j, σ (u j) * (y j : E) = p := by
    rw [← hpz]
    change p + ∑ j, σ (u j) * (y j : E) - _ = p
    ring
  rw [this]
  exact hp
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical

theorem _root_.GlobalTheory.T.euler_product_convergence_bound : CountBd → ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ (K : Set (Ainf F)), IsCompact K → ∀ N : ℕ, 0 < N → ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (C : ℝ) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ), 0 ≤ C → (∀ v, v ∉ S → (∀ s ∈ v.adicCompletionIntegers F, s ≠ 0 → |g v s - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ)) ∧ ∀ s : Fv F v, Valued.v s = 1 → |g v s - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) → ∀ δ : ℝ, 0 < δ → ∀ D : Finset (HeightOneSpectrum (𝓞 F)), Disjoint D S → ∀ B : Finset F, (∀ x ∈ B, x ≠ 0 ∧ x ∈ IntOut S ∧ (∃ y : 𝓞 F, (y : F) = (N : F) * x) ∧ θ δ * algebraMap F (Ainf F) x ∈ K) → δ ^ Module.finrank ℚ F * ∑ x ∈ B, ∏ v ∈ D, |g v (algebraMap F (Fv F v) x) - 1| ≤ C' * ∏ v ∈ D, (2 * C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) := by
  first | exact @GlobalTheory.CompanionTheory.Mass.SumDev.sum_bounded_prod | exact GlobalTheory.CompanionTheory.Mass.SumDev.sum_bounded_prod | (intros; apply GlobalTheory.CompanionTheory.Mass.SumDev.sum_bounded_prod <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier ValuativeRel
open scoped Topology

namespace GlobalTheory.CompanionTheory.MirFourier

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem polyBall_mono (n : ℕ) {s₁ s₂ : kˣ} (h : valuation k (s₁ : k) ≤ valuation k (s₂ : k)) :
    polyBall n s₁ ≤ polyBall n s₂ :=
  fun x hx i => show valuation k (x.toAdd i) ≤ valuation k (s₂ : k) from
    le_trans (show valuation k (x.toAdd i) ≤ valuation k (s₁ : k) from hx i) h

theorem exists_mem_polyBall {n : ℕ} (x : Multiplicative (Fin n → k)) :
    ∃ s : kˣ, x ∈ polyBall n s := by
  obtain ⟨M, hM⟩ := Finite.exists_le (fun i : Fin n => valuation k (x.toAdd i))
  obtain ⟨y, hy⟩ := valuation_surjective (max M 1)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact absurd (hy.symm ▸ le_max_right M 1 : (1 : ValueGroupWithZero k) ≤ 0) (by simp)
  refine ⟨Units.mk0 y hy0, fun i => ?_⟩
  show valuation k (x.toAdd i) ≤ valuation k y
  rw [hy]
  exact le_trans (hM i) (le_max_left _ _)

theorem twKer_polyBall_mono (ψ : AddChar k Circle) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Multiplicative (Fin n → k)) V) (a : Fin n → k) {s₁ s₂ : kˣ}
    (h : valuation k (s₁ : k) ≤ valuation k (s₂ : k)) :
    twKer ρ (polyBall n s₁) (resChr ψ a (polyBall n s₁)) ≤
      twKer ρ (polyBall n s₂) (resChr ψ a (polyBall n s₂)) := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨⟨x, hx⟩, v, rfl⟩
  exact Submodule.subset_span ⟨⟨x, polyBall_mono n h hx⟩, v, rfl⟩

theorem exists_mem_twKer_polyBall (ψ : AddChar k Circle) {n : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ (Multiplicative (Fin n → k)) V) (a : Fin n → k) (v : V)
    (hv : v ∈ twKer ρ ⊤ (resChr ψ a ⊤)) :
    ∃ s : kˣ, v ∈ twKer ρ (polyBall n s) (resChr ψ a (polyBall n s)) := by
  unfold twKer at hv
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨⟨x, -⟩, u, rfl⟩ := hw
    obtain ⟨s, hs⟩ := exists_mem_polyBall x
    exact ⟨s, Submodule.subset_span ⟨⟨x, hs⟩, u, rfl⟩⟩
  | zero => exact ⟨1, Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨s₁, h₁⟩ := hx
    obtain ⟨s₂, h₂⟩ := hy
    rcases le_total (valuation k (s₁ : k)) (valuation k (s₂ : k)) with h | h
    · exact ⟨s₂, Submodule.add_mem _ (twKer_polyBall_mono ψ ρ a h h₁) h₂⟩
    · exact ⟨s₁, Submodule.add_mem _ h₁ (twKer_polyBall_mono ψ ρ a h h₂)⟩
  | smul c x _ hx =>
    obtain ⟨s, hs⟩ := hx
    exact ⟨s, Submodule.smul_mem _ c hs⟩

end GlobalTheory.CompanionTheory.MirFourier
end

section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier ValuativeRel
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.MirFourier

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem coe_polyBall_eq (n : ℕ) (t : kˣ) :
    (polyBall (k := k) n t : Set (Multiplicative (Fin n → k))) =
      Multiplicative.ofAdd '' FourierPi.box (Fin n) t := by
  ext x
  constructor
  · intro hx
    exact ⟨x.toAdd, fun i _ => hx i, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact fun i => hy i trivial

theorem isCompact_polyBall (n : ℕ) (t : kˣ) :
    IsCompact (polyBall (k := k) n t : Set (Multiplicative (Fin n → k))) := by
  rw [coe_polyBall_eq]
  exact (FourierPi.isCompact_box t).image (continuous_ofAdd)

theorem isOpen_polyBall (n : ℕ) (t : kˣ) :
    IsOpen (polyBall (k := k) n t : Set (Multiplicative (Fin n → k))) := by
  have h : (polyBall (k := k) n t : Set (Multiplicative (Fin n → k))) =
      Multiplicative.toAdd ⁻¹' FourierPi.box (Fin n) t := by
    ext x
    exact ⟨fun hx i _ => hx i, fun hx i => hx i trivial⟩
  rw [h]
  exact (FourierPi.isOpen_box t).preimage continuous_toAdd

theorem dotProduct_mem_cball {n : ℕ} {a b c : kˣ} (h : valuation k (a : k) * valuation k (b : k) ≤ valuation k (c : k))
    {u x : Fin n → k} (hu : ∀ i, u i ∈ cball a) (hx : ∀ i, x i ∈ cball b) : u ⬝ᵥ x ∈ cball c := by
  refine Finset.sum_induction _ (· ∈ cball c) (fun _ _ => add_mem_cball) (by simp [cball]) fun i _ => ?_
  show valuation k (u i * x i) ≤ valuation k (c : k)
  rw [map_mul]
  exact (mul_le_mul' (hu i) (hx i)).trans h

theorem exists_reps_sum_eq_zero :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), Continuous ψ → ∀ (n : ℕ) (t s : kˣ),
      ∃ R : Finset (Fin n → k), R.Nonempty ∧ (∀ a ∈ R, Multiplicative.ofAdd a ∈ polyBall n t) ∧
        ∀ x : polyBall (k := k) n s, (x : Multiplicative (Fin n → k)) ∉ ann ψ n t →
          ∑ a ∈ R, (((resChr ψ a (polyBall n s) x)⁻¹ : ℂˣ) : ℂ) = 0 := by
  intro k _ _ _ _ ψ hψ n t s
  classical
  obtain ⟨c, hc⟩ := exists_cball_addChar_eq_one ψ hψ
  obtain ⟨t', ht1, ht2⟩ : ∃ t' : kˣ, valuation k (t' : k) ≤ valuation k (t : k) ∧
      valuation k (t' : k) ≤ valuation k ((c * s⁻¹ : kˣ) : k) := by
    rcases le_total (valuation k (t : k)) (valuation k ((c * s⁻¹ : kˣ) : k)) with h | h
    · exact ⟨t, le_rfl, h⟩
    · exact ⟨c * s⁻¹, h, le_rfl⟩
  have hts : valuation k (t' : k) * valuation k (s : k) ≤ valuation k (c : k) := by
    have hs0 : valuation k (s : k) ≠ 0 := by simp
    calc valuation k (t' : k) * valuation k (s : k)
        ≤ valuation k ((c * s⁻¹ : kˣ) : k) * valuation k (s : k) := mul_le_mul_left ht2 _
      _ = valuation k (c : k) := by
        rw [← map_mul]
        simp
  let H : Subgroup (Multiplicative (Fin n → k)) := polyBall n t
  let N : Subgroup H := (polyBall n t').subgroupOf H
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp (isCompact_polyBall n t)
  have hNopen : IsOpen (N : Set H) := (isOpen_polyBall n t').preimage continuous_subtype_val
  haveI : Finite (H ⧸ N) := Subgroup.quotient_finite_of_isOpen _ hNopen
  letI : Fintype (H ⧸ N) := Fintype.ofFinite _
  haveI : N.Normal := ⟨fun a ha b => by
    rw [mul_comm b a, mul_inv_cancel_right]; exact ha⟩
  let rep : H ⧸ N → Fin n → k := fun q => ((q.out : H) : Multiplicative (Fin n → k)).toAdd
  have hinj : Function.Injective rep := fun p q h =>
    Quotient.out_injective (Subtype.ext (Multiplicative.toAdd.injective h))
  refine ⟨Finset.univ.image rep, ?_, ?_, ?_⟩
  · exact ⟨rep 1, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  · intro a ha
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 ha
    exact (q.out : H).2
  · intro x hx
    rw [Finset.sum_image (fun a _ b _ h => hinj h)]
    obtain ⟨l₀, hl₀, hne⟩ : ∃ a ∈ polyBall (k := k) n t, ψ (a.toAdd ⬝ᵥ (x : Multiplicative (Fin n → k)).toAdd) ≠ 1 := by
      by_contra h
      push Not at h
      exact hx h
    let y : H → Circle := fun b => (ψ ((b : Multiplicative (Fin n → k)).toAdd ⬝ᵥ (x : Multiplicative (Fin n → k)).toAdd))⁻¹
    let f : H → ℂ := fun b => (y b : ℂ)
    have hmul : ∀ b b' : H, f (b * b') = f b * f b' := by
      intro b b'
      simp only [f, y, ← Circle.coe_mul]
      congr 1
      rw [Subgroup.coe_mul, toAdd_mul, add_dotProduct, AddChar.map_add_eq_mul, mul_inv]
    have hN : ∀ b, ∀ u ∈ N, f (b * u) = f b := by
      intro b u hu
      have h1 : ψ ((u : Multiplicative (Fin n → k)).toAdd ⬝ᵥ (x : Multiplicative (Fin n → k)).toAdd) = 1 :=
        hc _ (dotProduct_mem_cball hts (Subgroup.mem_subgroupOf.1 hu) x.2)
      have h2 : f u = 1 := by simp [f, y, h1]
      rw [hmul, h2, mul_one]
    let l : H := ⟨l₀, hl₀⟩
    have hl : f l ≠ 1 := by
      intro h
      apply hne
      have h3 : y l = 1 := Circle.ext (by simpa [f] using h)
      simpa [y, l] using h3
    have hsum := GlobalTheory.CompanionTheory.TwistedAverage.sum_out_mul_right N f hN l
    simp only [hmul] at hsum
    rw [← Finset.sum_mul] at hsum
    have hS : ∑ q : H ⧸ N, f q.out = 0 := by
      have h4 : (∑ q : H ⧸ N, f q.out) * (f l - 1) = 0 := by
        rw [mul_sub, hsum, mul_one, sub_self]
      exact (mul_eq_zero.1 h4).resolve_right (sub_ne_zero.2 hl)
    rw [← hS]
    refine Finset.sum_congr rfl fun q _ => ?_
    show (((Circle.toUnits (ψ (rep q ⬝ᵥ (x : Multiplicative (Fin n → k)).toAdd)))⁻¹ : ℂˣ) : ℂ) = f q.out
    simp [f, y, rep]

end GlobalTheory.CompanionTheory.MirFourier

end
end

section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier ValuativeRel
open scoped Topology

namespace GlobalTheory.CompanionTheory.MirFourier

theorem ann_subset_of_mem_nhds {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (hψ : ψ ≠ 1) (n : ℕ)
    {S : Set (Multiplicative (Fin n → k))} (hS : S ∈ 𝓝 (1 : Multiplicative (Fin n → k))) :
    ∃ t : kˣ, (ann ψ n t : Set (Multiplicative (Fin n → k))) ⊆ S := by
  obtain ⟨y, hy⟩ : ∃ y, ψ y ≠ 1 := by
    by_contra h
    push Not at h
    exact hψ (by ext a; simp [h a])
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hy (AddChar.map_zero_eq_one ψ)
  have hS' : {v : Fin n → k | Multiplicative.ofAdd v ∈ S} ∈ 𝓝 (0 : Fin n → k) := hS
  obtain ⟨s, hs⟩ := FourierPi.exists_box_subset hS'
  refine ⟨Units.mk0 y hy0 * s⁻¹, fun x hx => ?_⟩
  have hbox : x.toAdd ∈ FourierPi.box (Fin n) s := by
    intro i _
    show valuation k (x.toAdd i) ≤ valuation k (s : k)
    by_contra hlt
    have hlt' : valuation k (s : k) < valuation k (x.toAdd i) := not_le.mp hlt
    have hxi : x.toAdd i ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hlt'
      exact not_lt_zero hlt'
    have hmem : Multiplicative.ofAdd (Pi.single i (y / x.toAdd i) : Fin n → k) ∈ polyBall n
        (Units.mk0 y hy0 * s⁻¹) := by
      intro j
      by_cases hj : j = i
      · subst hj
        show valuation k ((Pi.single j (y / x.toAdd j) : Fin n → k) j) ≤
          valuation k ((Units.mk0 y hy0 * s⁻¹ : kˣ) : k)
        have hs0 : 0 < valuation k (s : k) :=
          zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr s.ne_zero)
        rw [Pi.single_eq_same, map_div₀, Units.val_mul, map_mul, Units.val_mk0,
          Units.val_inv_eq_inv_val, map_inv₀, div_eq_mul_inv]
        exact mul_le_mul_right ((inv_le_inv₀ (hs0.trans hlt') hs0).mpr hlt'.le) _
      · simp [Pi.single_eq_of_ne hj, cball]
    have h1 := hx _ hmem
    rw [toAdd_ofAdd, single_dotProduct, div_mul_cancel₀ _ hxi] at h1
    exact hy h1
  exact hs hbox

end GlobalTheory.CompanionTheory.MirFourier

end
end

section

noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.finite_part_open : PositivityTheory.PfSWUS.SchInf.FinOpen := by
  first | exact @GlobalTheory.CompanionTheory.SW.FinOpenGram.finOpen | exact GlobalTheory.CompanionTheory.SW.FinOpenGram.finOpen | (intros; apply GlobalTheory.CompanionTheory.SW.FinOpenGram.finOpen <;> assumption)
end
end
