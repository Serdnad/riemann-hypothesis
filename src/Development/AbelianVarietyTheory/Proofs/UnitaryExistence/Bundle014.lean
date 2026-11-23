module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle001
import Mathlib.Algebra.Module.StablyFree.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.FourierProjections.Bundle001
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.SpGenStatement
import ReciprocityTheory.ThetaQuasiPeriods.PeriodLattice
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LevelHalf


open NumberField Matrix in
open scoped nonZeroDivisors in
theorem _root_.GlobalTheory.LevelHalf.trivial_mod_of_trivial_on_half :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H)
      (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (gam : D.La ≃ₗ[𝓞 E] D.La), (∀ a b, D.EF (gam a) (gam b) = D.EF a b) →
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
        ∃ e, gam a = a + l.M • e) → ∀ a, ∃ e, gam a = a + l.M • e := by
  intro E _ _ _ H D l gam hiso hhalf x
  cases D with
  | mk La _ _ EF _ hbij hbar _ _ _ _ => ?_
  obtain ⟨M, _, _, Mb, _, _, hsup, _, _⟩ := l
  dsimp only at *
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp
    (hsup ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ Mb ⊔ Mb.map (H.bar : 𝓞 E →+* 𝓞 E))
  set y := gam x - x with hy
  obtain ⟨e₁, he₁⟩ := hhalf (j • x) (Submodule.smul_mem_smul hj Submodule.mem_top)
  have hjy : j • y = M • e₁ := by
    rw [hy, smul_sub, ← LinearEquiv.map_smul, he₁]
    abel
  have hdiv : ∀ z, (M : ℤ) ∣ EF (i • y) z := by
    intro z
    rw [hbar]
    have hmem : H.bar i ∈ Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      simpa using Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hi
    obtain ⟨e₂, he₂⟩ := hhalf (H.bar i • z) (Submodule.smul_mem_smul hmem Submodule.mem_top)
    refine ⟨-EF (gam x) e₂, ?_⟩
    rw [hy, map_sub, LinearMap.sub_apply, ← hiso x (H.bar i • z), he₂, map_add (f := _), map_nsmul,
      nsmul_eq_mul]
    ring
  let ψ : La →ₗ[ℤ] ℤ :=
    { toFun := fun z => EF (i • y) z / M
      map_add' := fun a b => by
        simp only [map_add (f := _)]
        exact Int.add_ediv_of_dvd_left (hdiv a)
      map_smul' := fun c a => by
        simp only [map_zsmul, smul_eq_mul, eq_intCast, Int.cast_id]
        exact Int.mul_ediv_assoc _ (hdiv a) }
  obtain ⟨w, hw⟩ := hbij.2 ψ
  have hiy : i • y = M • w := by
    apply hbij.1
    ext z
    rw [map_nsmul, LinearMap.smul_apply, hw]
    simp [ψ, nsmul_eq_mul, Int.mul_ediv_cancel' (hdiv z)]
  refine ⟨e₁ + w, ?_⟩
  calc gam x = x + y := by rw [hy]; abel
    _ = x + M • (e₁ + w) := by
      rw [smul_add, ← hjy, ← hiy, add_comm (j • y), ← add_smul, hij, one_smul]

end GlobalTheory.LevelHalf
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory.SatDual

theorem exists_int_extension {L V : Type} [AddCommGroup L] [AddCommGroup V] [Module.Finite ℤ L]
    [Module.IsTorsionFree ℤ V] (q : L →ₗ[ℤ] V) (f : L →ₗ[ℤ] ℚ)
    (hf : ∀ x, q x = 0 → ∃ n : ℤ, f x = n) :
    ∃ g : L →ₗ[ℤ] ℤ, ∀ x, q x = 0 → (g x : ℚ) = f x := by
  haveI : Module.Finite ℤ (LinearMap.range q) := inferInstance
  haveI : Module.Free ℤ (LinearMap.range q) := Module.free_of_finite_type_torsion_free'
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property q.rangeRestrict LinearMap.id
    q.surjective_rangeRestrict
  let p : L →ₗ[ℤ] L := LinearMap.id - σ ∘ₗ q.rangeRestrict
  have hp : ∀ x, q (p x) = 0 := by
    intro x
    have h := congrArg Subtype.val (LinearMap.congr_fun hσ (q.rangeRestrict x))
    simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.codRestrict_apply] at h
    simp only [p, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub]
    exact sub_eq_zero.2 h.symm
  have hp' : ∀ x, q x = 0 → p x = x := by
    intro x hx
    have : q.rangeRestrict x = 0 := Subtype.ext hx
    simp [p, this]
  choose n hn using fun x => hf (p x) (hp x)
  refine ⟨AddMonoidHom.toIntLinearMap (AddMonoidHom.mk' n ?_), ?_⟩
  · intro a b
    have : ((n (a + b) : ℤ) : ℚ) = ((n a + n b : ℤ) : ℚ) := by
      push_cast
      rw [← hn, ← hn, ← hn, map_add (f := _), map_add (f := _)]
    exact_mod_cast this
  · intro x hx
    change ((n x : ℤ) : ℚ) = f x
    rw [← hn, hp' x hx]

variable {E : Type} [Field E] [NumberField E]

theorem exists_int_smul_mem {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] (Λ : Submodule (𝓞 E) V) (v : V)
    (hv : v ∈ Submodule.span E (Λ : Set V)) : ∃ N : ℤ, N ≠ 0 ∧ (N : E) • v ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.IntMulMem.exists_int_mul_mem
  | exact _root_.GlobalTheory.IntMulMem.exists_int_mul_mem
  | (apply _root_.GlobalTheory.IntMulMem.exists_int_mul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntMulMem.exists_int_mul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntMulMem.exists_int_mul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntMulMem.exists_int_mul_mem ..)

variable [IsCMField E]

theorem herm_smul_snd {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) (a : E) :
    FD.herm G x (a • y) = FD.herm G x y * FD.cc a := by
  simp only [FD.herm, FD.cc, Pi.smul_apply, smul_eq_mul, map_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem pairing_pseudoBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (s : ℕ) (e : Fin s → (Fin r → E)) (c : Fin s → FractionalIdeal (𝓞 E)⁰ E), FD.cc ξ = -ξ → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y))) → LinearIndependent E e → (∀ a : Fin s → E, (∑ b, a b • e b) ∈ LinearMap.range φ ↔ ∀ b, a b ∈ c b) → ∀ y : Fin s → E, (∃ x, ∀ b, ξ * FD.herm Gm (φ x) (e b) = y b) ↔ ∀ b, ∀ a ∈ c b, ∃ n : ℤ, Algebra.trace ℚ E (y b * FD.cc a) = n := by
  intro E _ _ _ H D r ξ Gm φ s e c _ hφ he hc y
  obtain ⟨hinj, hspan, -, -, hEF⟩ := hφ
  have hsingle : ∀ (b : Fin s) (a : E), ∑ b', (Pi.single b a : Fin s → E) b' • e b' = a • e b := by
    intro b a
    rw [Finset.sum_eq_single b]
    · simp
    · intro b' _ hb'
      simp [Pi.single_eq_of_ne hb']
    · simp
  have hmem : ∀ (b : Fin s) (a : E), a • e b ∈ LinearMap.range φ ↔ a ∈ c b := by
    intro b a
    rw [← hsingle, hc]
    constructor
    · intro h
      simpa using h b
    · intro h b'
      by_cases hb : b' = b
      · subst hb
        simpa using h
      · rw [Pi.single_eq_of_ne hb]
        exact FractionalIdeal.zero_mem _
  constructor
  · rintro ⟨x, hx⟩ b a ha
    obtain ⟨z, hz⟩ := (hmem b a).2 ha
    refine ⟨D.EF x z, ?_⟩
    rw [hEF, hz, herm_smul_snd, ← _root_.mul_assoc, hx]
  · intro hy
    haveI := D.fin
    haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
    let j : (Fin s → E) →ₗ[E] (Fin r → E) := Fintype.linearCombination E e
    have hj : LinearMap.ker j = ⊥ :=
      LinearMap.ker_eq_bot.2 he.fintypeLinearCombination_injective
    obtain ⟨π, hπ⟩ := j.exists_leftInverse_of_injective hj
    have hπ' : ∀ a, π (j a) = a := fun a => LinearMap.congr_fun hπ a
    let q : D.La →ₗ[ℤ] (Fin r → E) := AddMonoidHom.toIntLinearMap
      (AddMonoidHom.mk' (fun x => φ x - j (π (φ x))) (by
        intro a b
        simp only [map_add (f := _)]
        abel))
    let f : D.La →ₗ[ℤ] ℚ := AddMonoidHom.toIntLinearMap
      (AddMonoidHom.mk' (fun x => ∑ b, Algebra.trace ℚ E (y b * FD.cc (π (φ x) b))) (by
        intro a b
        simp only [map_add (f := _), Pi.add_apply, FD.cc, mul_add, Finset.sum_add_distrib]))
    have hq : ∀ x, q x = φ x - j (π (φ x)) := fun _ => rfl
    have hf : ∀ x, f x = ∑ b, Algebra.trace ℚ E (y b * FD.cc (π (φ x) b)) := fun _ => rfl
    obtain ⟨g, hg⟩ := exists_int_extension q f (by
      intro x hx
      rw [hq, sub_eq_zero] at hx
      have h1 : ∀ b, π (φ x) b ∈ c b := (hc _).1 ⟨x, hx⟩
      choose n hn using fun b => hy b _ (h1 b)
      refine ⟨∑ b, n b, ?_⟩
      rw [hf]
      push_cast
      exact Finset.sum_congr rfl fun b _ => hn b)
    obtain ⟨x, hx⟩ := D.unimod.2 g
    refine ⟨x, fun b => ?_⟩
    have key : ∀ a ∈ c b,
        Algebra.trace ℚ E ((ξ * FD.herm Gm (φ x) (e b) - y b) * FD.cc a) = 0 := by
      intro a ha
      obtain ⟨z, hz⟩ := (hmem b a).2 ha
      have hz' : φ z = j (Pi.single b a) := by
        rw [hz, ← hsingle]
        rfl
      have h1 := hg z (by rw [hq, hz', hπ', sub_self])
      rw [← hx, hEF, hz, herm_smul_snd, hf, hz', hπ', Finset.sum_eq_single b] at h1
      · rw [sub_mul, map_sub, _root_.mul_assoc, h1]
        simp
      · intro b' _ hb'
        simp [Pi.single_eq_of_ne hb', FD.cc]
      · simp
    rw [← sub_eq_zero]
    refine (traceForm_nondegenerate ℚ E).1 _ fun t => ?_
    obtain ⟨N, hN, hNt⟩ := exists_int_smul_mem (E := E) (LinearMap.range φ) (FD.cc t • e b)
      (by rw [LinearMap.coe_range, hspan]; trivial)
    rw [smul_smul, hmem] at hNt
    have h2 := key _ hNt
    have h3 : FD.cc ((N : E) * FD.cc t) = (N : ℚ) • t := by
      simp [FD.cc, Algebra.smul_def]
    rw [h3, mul_smul_comm, map_smul, smul_eq_zero] at h2
    rcases h2 with h2 | h2
    · exact absurd (by exact_mod_cast h2) hN
    · rw [Algebra.traceForm_apply]
      exact h2

end GlobalTheory.SatDual
end

section

namespace GlobalTheory.UpperHalfImaginaryForm

open ReciprocityTheory.ChartRestriction.G.I2

noncomputable section

variable {ι : Type} [Fintype ι]

def imForm : EuclideanSpace ℂ ι →ₗ[ℝ] EuclideanSpace ℂ ι →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => (Hf x y).im)
    (fun x y z => by simp [Hf, add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Hf, PiLp.smul_apply, Complex.real_smul, mul_assoc, ← Finset.mul_sum, smul_eq_mul]
      simp)
    (fun x y z => by simp [Hf, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Hf, PiLp.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal,
        mul_left_comm _ (c : ℂ), ← Finset.mul_sum, smul_eq_mul]
      simp)

theorem imForm_apply (x y : EuclideanSpace ℂ ι) : imForm x y = (Hf x y).im := rfl

theorem imForm_swap (x y : EuclideanSpace ℂ ι) : imForm y x = -imForm x y := by
  have h : Hf y x = starRingEnd ℂ (Hf x y) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Hf, map_sum, mul_comm]
  rw [imForm_apply, imForm_apply, h, Complex.conj_im]

variable {n : ℕ}

def upper (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℂ ι)) :
    EuclideanSpace ℂ ι →ₗ[ℝ] EuclideanSpace ℂ ι →ₗ[ℝ] ℝ :=
  b.constr ℝ fun i => b.constr ℝ fun j => if i < j then imForm (b i) (b j) else 0

theorem upper_basis (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℂ ι)) (i j : Fin n) :
    upper b (b i) (b j) = if i < j then imForm (b i) (b j) else 0 := by
  simp only [upper, b.constr_basis]

theorem upper_sub (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℂ ι)) (x y : EuclideanSpace ℂ ι) :
    imForm x y = upper b x y - upper b y x := by
  have key : imForm = upper b - (upper b).flip := by
    refine b.ext fun i => b.ext fun j => ?_
    simp only [LinearMap.sub_apply, LinearMap.flip_apply, upper_basis]
    rcases lt_trichotomy i j with h | h | h
    · simp [h, lt_asymm h]
    · subst h
      have := imForm_swap (b i) (b i)
      simp only [lt_irrefl, if_false, sub_zero]
      linarith
    · have := imForm_swap (b j) (b i)
      simp only [h, lt_asymm h, if_true, if_false, zero_sub]
      linarith
  rw [key]
  simp only [LinearMap.sub_apply, LinearMap.flip_apply]

theorem upper_int (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℂ ι))
    (hint : ∀ x y : EuclideanSpace ℂ ι, x ∈ lat b → y ∈ lat b → ∃ k : ℤ, (Hf x y).im = k)
    {x y : EuclideanSpace ℂ ι} (hx : x ∈ lat b) (hy : y ∈ lat b) :
    ∃ k : ℤ, upper b x y = k := by
  have base : ∀ i j, ∃ k : ℤ, upper b (b i) (b j) = k := by
    intro i j
    rw [upper_basis]
    split_ifs
    · rw [imForm_apply]
      exact hint _ _ (Submodule.subset_span ⟨i, rfl⟩) (Submodule.subset_span ⟨j, rfl⟩)
    · exact ⟨0, by simp⟩
  have hrow : ∀ i, ∃ k : ℤ, upper b (b i) y = k := by
    intro i
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      exact base i j
    | zero => exact ⟨0, by simp⟩
    | add z w _ _ hz hw =>
      obtain ⟨k₁, h₁⟩ := hz
      obtain ⟨k₂, h₂⟩ := hw
      exact ⟨k₁ + k₂, by simp [map_add (f := _), h₁, h₂]⟩
    | smul n z _ hz =>
      obtain ⟨k₁, h₁⟩ := hz
      exact ⟨n * k₁, by simp [map_zsmul, h₁, zsmul_eq_mul]⟩
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨i, rfl⟩ := hz
    exact hrow i
  | zero => exact ⟨0, by simp⟩
  | add z w _ _ hz hw =>
    obtain ⟨k₁, h₁⟩ := hz
    obtain ⟨k₂, h₂⟩ := hw
    exact ⟨k₁ + k₂, by simp [map_add (f := _), LinearMap.add_apply, h₁, h₂]⟩
  | smul n z _ hz =>
    obtain ⟨k₁, h₁⟩ := hz
    exact ⟨n * k₁, by simp [map_zsmul, LinearMap.smul_apply, h₁, zsmul_eq_mul]⟩

theorem exists_coc {ι : Type} [Fintype ι]
    (b : Module.Basis (Fin (2 * Fintype.card ι)) ℝ (EuclideanSpace ℂ ι))
    (hint : ∀ x y : EuclideanSpace ℂ ι, x ∈ lat b → y ∈ lat b → ∃ k : ℤ, (Hf x y).im = k)
    (hperf : ∀ φ : lat b →+ ℤ, ∃ x ∈ lat b, ∀ y : lat b,
      (φ y : ℝ) = (Hf x (y : EuclideanSpace ℂ ι)).im) :
    ∃ Y : GT ι, Y.b = b ∧ FPw.Coc Y 1 := by
  refine ⟨⟨b, hint, hperf, fun x => Complex.exp (((Real.pi * upper b x x : ℝ) : ℂ) * Complex.I),
    fun x _ => Complex.norm_exp_ofReal_mul_I _⟩, rfl, ?_⟩
  intro γ hγ γ' hγ'
  obtain ⟨k, hk⟩ := upper_int b hint hγ hγ'
  have him : (Hf γ γ').im = upper b γ γ' - upper b γ' γ := by
    rw [← imForm_apply]
    exact upper_sub b γ γ'
  have hadd : upper b (γ + γ') (γ + γ') =
      upper b γ γ + upper b γ γ' + upper b γ' γ + upper b γ' γ' := by
    simp only [map_add (f := _), LinearMap.add_apply]
    ring
  dsimp only
  rw [← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨k, ?_⟩
  rw [hadd, him, hk]
  push_cast
  ring

end

end GlobalTheory.UpperHalfImaginaryForm
end
