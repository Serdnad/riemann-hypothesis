module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.MemPowSmul
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem ac_mul {G R : Type} [TopologicalSpace G] [CommRing R] {I : Ideal R} {f h : G → R}
    (hf : AdicCont I f) (hh : AdicCont I h) : AdicCont I fun g => f g * h g := fun N => by
  simp only [map_mul]; exact (hf N).mul (hh N)

private theorem ac_const {G R : Type} [TopologicalSpace G] [CommRing R] {I : Ideal R} (c : R) :
    AdicCont I fun _ : G => c := fun _ => IsLocallyConstant.const _

private theorem ac_sum {G R ι : Type} [TopologicalSpace G] [CommRing R] {I : Ideal R} (s : Finset ι)
    {f : ι → G → R} (hf : ∀ i, AdicCont I (f i)) : AdicCont I fun g => ∑ i ∈ s, f i g := by
  classical
  intro N

  simp only [map_sum]
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact IsLocallyConstant.const 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a N).add ih

private theorem mat_lc {G A R : Type} [TopologicalSpace G] [CommRing A] [CommRing R] [Algebra A R]
    {n : ℕ} (t : A) (f : G → Matrix (Fin n) (Fin n) R)
    (hf : ∀ i j, AdicCont (Ideal.span {algebraMap A R t}) fun g => f g i j) (N : ℕ) :
    IsLocallyConstant fun g =>
      (Ideal.span {t} ^ N • (⊤ : Submodule A (Matrix (Fin n) (Fin n) R))).mkQ (f g) := by
  classical
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hx : ∀ᶠ y in nhds x, ∀ i j, Ideal.Quotient.mk (Ideal.span {algebraMap A R t} ^ N) (f y i j)
      = Ideal.Quotient.mk (Ideal.span {algebraMap A R t} ^ N) (f x i j) :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (hf i j N).eventually_eq x
  filter_upwards [hx] with y hy
  have hc : ∀ i j, ∃ c : R, c * algebraMap A R t ^ N = f y i j - f x i j := by
    intro i j
    have h := Ideal.Quotient.eq.1 (hy i j)
    rwa [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h
  choose c hc using hc
  simp only [Submodule.mkQ_apply]
  rw [Submodule.Quotient.eq]
  have hm : f y - f x = t ^ N • Matrix.of c := by
    ext i j
    simp [Algebra.smul_def, ← hc i j, mul_comm]
  rw [hm, Ideal.span_singleton_pow]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top

theorem UpperTheory.V.Pa.Det.matFg :
    ∀ (l : ℕ) [Fact l.Prime] {K G R : Type} [Field K] [Finite K] [CharP K l] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] [CommRing R] [Algebra (PowerSeries K) R] [Module.Free (PowerSeries K) R] [Module.Finite (PowerSeries K) R] {n : ℕ} (χ : G →* R) (r : G →* Matrix (Fin n) (Fin n) R) (Z : Submodule (PowerSeries K) (G → Matrix (Fin n) (Fin n) R)), PhiCond G l → AdicCont (Ideal.span {algebraMap (PowerSeries K) R PowerSeries.X}) χ → (∀ i j, AdicCont (Ideal.span {algebraMap (PowerSeries K) R PowerSeries.X}) fun g => r g i j) → (∀ z ∈ Z, (∀ i j, AdicCont (Ideal.span {algebraMap (PowerSeries K) R PowerSeries.X}) fun g => z g i j) ∧ TwCoc χ r Set.univ z) → Z.FG := by
  intro l _ K G R _ _ _ _ _ _ _ _ _ _ _ _ n χ r Z hφ hχ hr hZ
  let ρ : G →* Module.End (PowerSeries K) (Matrix (Fin n) (Fin n) R) :=
    { toFun := fun g =>
        { toFun := fun m => χ g • (r g * m * r g⁻¹)
          map_add' := by intro a b; simp [Matrix.mul_add, Matrix.add_mul]
          map_smul' := by
            intro c m
            simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]
            exact smul_comm _ _ _ }
      map_one' := by ext m : 1; simp
      map_mul' := by
        intro g h
        ext m : 1
        simp [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc, mul_comm] }
  have hinv : ∀ i j, AdicCont (Ideal.span {algebraMap (PowerSeries K) R PowerSeries.X}) fun g => r g⁻¹ i j :=
    fun i j N => (hr i j N).comp_continuous continuous_inv
  refine Det.z1Fg l ρ Z hφ ?_ ?_
  · intro N m
    refine mat_lc PowerSeries.X (fun g => χ g • (r g * m * r g⁻¹)) ?_ N
    intro i j
    have e : (fun g => (χ g • (r g * m * r g⁻¹)) i j)
        = fun g => χ g * ∑ q, (∑ k, r g i k * m k q) * r g⁻¹ q j := by
      funext g
      simp [Matrix.mul_apply]
    rw [e]
    exact ac_mul hχ (ac_sum _ fun q => ac_mul (ac_sum _ fun k => ac_mul (hr i k) (ac_const _)) (hinv q j))
  · intro z hz
    obtain ⟨hzc, hzt⟩ := hZ z hz
    exact ⟨fun N => mat_lc PowerSeries.X z hzc N, fun g h => hzt g trivial h trivial⟩
end

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem mem_ev_iff_apply_eq_zero_off_diagonal_blocks {A R : Type} [CommRing A] [CommRing R] [Algebra A R] (n a : ℕ)
    (Z : Matrix (Fin n) (Fin n) R) :
    Z ∈ Ev A R n a ↔ ∀ i j : Fin n, ¬((i : ℕ) < a ↔ (j : ℕ) < a) → Z i j = 0 := by
  constructor
  · intro h i j hij
    exact (Submodule.mem_bot A).1 ((h i j).2 hij)
  · intro h i j
    exact ⟨fun _ => Submodule.mem_top, fun hij => by rw [h i j hij]; exact Submodule.zero_mem _⟩

theorem UpperTheory.V.Pa.Det.detFr :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n), l ≠ 2 → (∃ g : F.G₀, PadicInt.toZMod ((F.ε g : ℤ_[l]ˣ) : ℤ_[l]) ≠ 1) → ∃ D : DetFr (FractionRing x.A) F.G₀ n, D.a = x.a ∧ D.G' = F.G' ∧ (∀ g, D.r g = x.ρX (FractionRing x.A) g) ∧ D.σ = F.conj ∧ ∀ g : F.G₀, D.χF g = algebraMap x.A (FractionRing x.A) (algebraMap ℤ_[l] x.A (F.ε g : ℤ_[l])) := by
  intro l _ F n x hl hg
  obtain ⟨g₀, hg₀⟩ := hg
  have hev : ∀ g : F.G₀, (mat x.ρ g).map (algebraMap x.A (FractionRing x.A)) ∈
      Ev (FractionRing x.A) (FractionRing x.A) n x.a := by
    intro g
    rw [mem_ev_iff_apply_eq_zero_off_diagonal_blocks]
    intro i j hij
    have h0 := (mem_ev_iff_apply_eq_zero_off_diagonal_blocks _ _ _).1 (x.blk g) i j hij
    rw [Matrix.map_apply, h0, map_zero]
  have hmap : ∀ M ∈ Submodule.span x.A ((mat x.ρ) '' (F.G' : Set F.G₀)),
      M.map (algebraMap x.A (FractionRing x.A)) ∈ Submodule.span (FractionRing x.A)
        ((fun g : F.G₀ => (mat x.ρ g).map (algebraMap x.A (FractionRing x.A))) '' (F.G' : Set F.G₀)) := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem M hM =>
      obtain ⟨g, hg, rfl⟩ := hM
      exact Submodule.subset_span ⟨g, hg, rfl⟩
    | zero =>
      have h0 : (0 : Matrix (Fin n) (Fin n) x.A).map (algebraMap x.A (FractionRing x.A)) = 0 := by
        ext i j
        simp
      rw [h0]
      exact Submodule.zero_mem _
    | add M N _ _ hM hN =>
      have h0 : (M + N).map (algebraMap x.A (FractionRing x.A)) =
          M.map (algebraMap x.A (FractionRing x.A)) + N.map (algebraMap x.A (FractionRing x.A)) := by
        ext i j
        simp
      rw [h0]
      exact Submodule.add_mem _ hM hN
    | smul c M _ hM =>
      have h0 : (c • M).map (algebraMap x.A (FractionRing x.A)) =
          algebraMap x.A (FractionRing x.A) c • M.map (algebraMap x.A (FractionRing x.A)) := by
        ext i j
        simp
      rw [h0]
      exact Submodule.smul_mem _ _ hM
  have hsingle : ∀ i j : Fin n, ((i : ℕ) < x.a ↔ (j : ℕ) < x.a) →
      Matrix.single i j (1 : FractionRing x.A) ∈ Submodule.span (FractionRing x.A)
        ((fun g : F.G₀ => (mat x.ρ g).map (algebraMap x.A (FractionRing x.A))) '' (F.G' : Set F.G₀)) := by
    intro i j hij
    have hZ : Matrix.single i j (1 : x.A) ∈ Ev x.A x.A n x.a := by
      rw [mem_ev_iff_apply_eq_zero_off_diagonal_blocks]
      intro k m hkm
      rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      exact hkm hij
    obtain ⟨s, hs⟩ := x.span _ hZ
    have key := hmap _ hs
    have h1 : ((PowerSeries.X : x.A) ^ s • Matrix.single i j (1 : x.A)).map
        (algebraMap x.A (FractionRing x.A)) =
        algebraMap x.A (FractionRing x.A) ((PowerSeries.X : x.A) ^ s) • Matrix.single i j (1 : FractionRing x.A) := by
      ext k m
      simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
      split_ifs <;> simp
    rw [h1] at key
    have hne : algebraMap x.A (FractionRing x.A) ((PowerSeries.X : x.A) ^ s) ≠ 0 := by
      intro h
      apply pow_ne_zero s (PowerSeries.X_ne_zero (R := x.K))
      apply IsFractionRing.injective x.A (FractionRing x.A)
      rw [h, map_zero]
    have h2 := Submodule.smul_mem _ (algebraMap x.A (FractionRing x.A) ((PowerSeries.X : x.A) ^ s))⁻¹ key
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h2
  have hspan : Submodule.span (FractionRing x.A)
      ((fun g : F.G₀ => (mat x.ρ g).map (algebraMap x.A (FractionRing x.A))) '' (F.G' : Set F.G₀)) =
      Ev (FractionRing x.A) (FractionRing x.A) n x.a := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨g, -, rfl⟩
      exact hev g
    · intro Z hZ
      rw [Matrix.matrix_eq_sum_single Z]
      refine Submodule.sum_mem _ (fun i _ => Submodule.sum_mem _ (fun j _ => ?_))
      by_cases hij : ((i : ℕ) < x.a ↔ (j : ℕ) < x.a)
      · have h3 : Matrix.single i j (Z i j) = Z i j • Matrix.single i j (1 : FractionRing x.A) := by
          rw [Matrix.smul_single, smul_eq_mul, mul_one]
        rw [h3]
        exact Submodule.smul_mem _ _ (hsingle i j hij)
      · rw [(mem_ev_iff_apply_eq_zero_off_diagonal_blocks _ _ _).1 hZ i j hij, Matrix.single_zero]
        exact Submodule.zero_mem _
  have h2 : IsUnit (2 : ℤ_[l]) := by
    by_contra h
    have hm : (2 : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := (IsLocalRing.mem_maximalIdeal _).2 h
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker] at hm
    have h4 : ((2 : ℕ) : ZMod l) = 0 := by
      rw [Nat.cast_ofNat, ← hm, map_ofNat]
    have h5 : l ∣ 2 := (ZMod.natCast_eq_zero_iff 2 l).1 h4
    exact hl ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 h5)
  have hc : ∀ g : F.G₀, F.ε ((F.conj g : F.G₀) : F.Γ) = F.ε (g : F.Γ) := by
    intro g
    show F.ε (F.c * (g : F.Γ) * F.c⁻¹) = F.ε (g : F.Γ)
    rw [map_mul, map_mul, map_inv, mul_comm (F.ε F.c), mul_inv_cancel_right]
  refine ⟨DetFr.mk ?_ x.a x.a_pos x.a_le F.G' ?_ (F.eps x.A (FractionRing x.A)) ?_ g₀ ?_
    ((algebraMap x.A (FractionRing x.A)).mapMatrix.toMonoidHom.comp (mat x.ρ)) hspan hev F.conj ?_ ?_
    (fun g => Units.map (algebraMap x.A (FractionRing x.A)).toMonoidHom
      ((F.eps ℤ_[l] x.A g) ^ (1 - (n : ℤ)))) ?_, rfl, rfl, fun g => rfl, rfl, fun g => rfl⟩
  · have h6 := (h2.map ((algebraMap x.A (FractionRing x.A)).comp (algebraMap ℤ_[l] x.A))).ne_zero
    rw [RingHom.comp_apply, map_ofNat, map_ofNat] at h6
    exact h6
  · intro g h
    rw [GFrame.G', MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one,
      mul_inv_eq_iff_eq_mul, mul_comm]
  · intro g hg
    rw [GFrame.G', MonoidHom.mem_ker] at hg
    show Units.map _ ((F.ε.comp F.η.ker.subtype) g) = 1
    rw [hg, map_one]
  · intro h
    apply hg₀
    have h7 := congrArg Units.val h
    change algebraMap x.A (FractionRing x.A) (algebraMap ℤ_[l] x.A ((F.ε g₀ : ℤ_[l]ˣ) : ℤ_[l])) = 1 at h7
    have h8 : ((F.ε g₀ : ℤ_[l]ˣ) : ℤ_[l]) - 1 ∈
        RingHom.ker ((algebraMap x.A (FractionRing x.A)).comp (algebraMap ℤ_[l] x.A)) := by
      rw [RingHom.mem_ker, map_sub, RingHom.comp_apply, h7, map_one, sub_self]
    have h9 := IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _) h8
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at h9
    exact h9
  · intro g
    apply Subtype.ext
    show F.c * (F.c * (g : F.Γ) * F.c⁻¹) * F.c⁻¹ = (g : F.Γ)
    calc F.c * (F.c * (g : F.Γ) * F.c⁻¹) * F.c⁻¹ = (F.c * F.c) * (g : F.Γ) * (F.c * F.c)⁻¹ := by group
      _ = (g : F.Γ) := by rw [F.c_sq]; group
  · intro g
    show Units.map _ ((F.ε.comp F.η.ker.subtype) (F.conj g)) = Units.map _ ((F.ε.comp F.η.ker.subtype) g)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
    exact congrArg _ (hc g)
  · intro g
    show ((mat x.ρ g).map (algebraMap x.A (FractionRing x.A)))ᵀ *
        (mat x.ρ (F.conj g)).map (algebraMap x.A (FractionRing x.A)) =
        (algebraMap x.A (FractionRing x.A) ((F.eps ℤ_[l] x.A g ^ (1 - (n : ℤ)) : x.Aˣ) : x.A)) • 1
    have h0 := x.form g
    rw [Units.val_one, Matrix.mul_one] at h0
    rw [← Matrix.transpose_map, ← Matrix.map_mul, h0]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
end
