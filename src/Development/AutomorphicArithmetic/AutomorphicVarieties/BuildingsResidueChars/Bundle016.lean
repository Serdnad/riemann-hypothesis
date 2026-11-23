module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalFiniteness.HasUnivOfStep
public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.FixedPointCriteria.Cond
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.CintIdx
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import ReciprocityTheory.GaloisValuations.GlobalA
public import Mathlib.LinearAlgebra.Basis.Bilinear

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

private theorem trace_conj_gl3 {k : Type} [Field k] (g x : GL (Fin 3) k) :
    ((g * x * g⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).trace = (x : Matrix (Fin 3) (Fin 3) k).trace := by
  rw [Units.val_mul, Matrix.trace_mul_comm, ← Units.val_mul, ← mul_assoc, inv_mul_cancel, one_mul]

private theorem place_over_rational_prime (K : Type) [Field K] [NumberField K] (p : ℕ) (w : HeightOneSpectrum (𝓞 K))
    (hw : (p : 𝓞 K) ∈ w.asIdeal) : ∃ v : HeightOneSpectrum (𝓞 ℚ), (p : 𝓞 ℚ) ∈ v.asIdeal := by
  refine ⟨w.under (𝓞 ℚ), ?_⟩
  change (p : 𝓞 ℚ) ∈ w.asIdeal.comap (algebraMap (𝓞 ℚ) (𝓞 K))
  rw [Ideal.mem_comap, map_natCast]
  exact hw
end

section

attribute [local instance 100] LieRing.ofAssociativeRing

open UpperTheory.V.Af.CuspFin in
theorem UpperTheory.map_center_envelopingProductGL_mem_capelliAlgebra :
    ∀ (𝔤 : Type) [LieRing 𝔤] [LieAlgebra ℝ 𝔤] (ι : Type) [Fintype ι] (n : ℕ) (b : Module.Basis (ι × Fin n × Fin n) ℝ 𝔤), (∀ v i j k l, ⁅b (v, i, j), b (v, k, l)⁆ = (if j = k then b (v, i, l) else 0) - (if l = i then b (v, k, j) else 0)) → (∀ v v', v ≠ v' → ∀ i j k l, ⁅b (v, i, j), b (v', k, l)⁆ = 0) → ∀ (A : Type) [Ring A] [Algebra ℂ A] [Algebra ℝ A] [IsScalarTower ℝ ℂ A] (ψ : UniversalEnvelopingAlgebra ℝ 𝔤 →ₐ[ℝ] A), ∀ z ∈ Subalgebra.center ℝ (UniversalEnvelopingAlgebra ℝ 𝔤), ψ z ∈ UpperTheory.V.Af.CuspFin.capAlg fun v i j => ψ (UniversalEnvelopingAlgebra.ι ℝ (b (v, i, j))) := by
  intro 𝔤 _ _ ι _ n b h1 h2 A _ _ _ _ ψ z hz
  obtain ⟨T, _, _, E, hE⟩ := hasUniv_of_sum (UpperTheory.glRelations_hasUniversalProperty n) (UpperTheory.capelliAlgebra_map_of_glRelations n) ι
  letI : Algebra ℝ T := Algebra.compHom T (algebraMap ℝ ℂ)
  haveI : IsScalarTower ℝ ℂ T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let l : 𝔤 →ₗ[ℝ] T := b.constr ℝ fun p => E p.1 p.2.1 p.2.2
  have hl : ∀ v i j, l (b (v, i, j)) = E v i j := fun v i j => b.constr_basis ℝ _ _
  have hlie : ∀ x y, l ⁅x, y⁆ = l x * l y - l y * l x := by
    have key : (LieModule.toEnd ℝ 𝔤 𝔤 : 𝔤 →ₗ[ℝ] 𝔤 →ₗ[ℝ] 𝔤).compr₂ l =
        (LinearMap.mul ℝ T).compl₁₂ l l - ((LinearMap.mul ℝ T).compl₁₂ l l).flip := by
      refine LinearMap.ext_basis b b ?_
      rintro ⟨v, i, j⟩ ⟨v', k, m⟩
      change l ⁅b (v, i, j), b (v', k, m)⁆ =
        l (b (v, i, j)) * l (b (v', k, m)) - l (b (v', k, m)) * l (b (v, i, j))
      rw [hl, hl]
      by_cases hv : v = v'
      · subst hv
        rw [h1, hE.rel.1 v i j k m, map_sub]
        congr 1 <;> split_ifs <;> simp [hl]
      · rw [h2 v v' hv, map_zero, (hE.rel.2 v v' hv i j k m).eq, sub_self]
    intro x y
    exact LinearMap.congr_fun₂ key x y
  let L : 𝔤 →ₗ⁅ℝ⁆ T := { l with map_lie' := fun {x y} => hlie x y }
  let f : UniversalEnvelopingAlgebra ℝ 𝔤 →ₐ[ℝ] T := UniversalEnvelopingAlgebra.lift ℝ L
  have hf : ∀ v i j, f (UniversalEnvelopingAlgebra.ι ℝ (b (v, i, j))) = E v i j := fun v i j => by
    rw [← hl]
    exact UniversalEnvelopingAlgebra.lift_ι_apply ℝ L _
  have hcen : f z ∈ Subalgebra.center ℂ T := by
    rw [Subalgebra.mem_center_iff]
    intro t
    have ht : t ∈ Algebra.adjoin ℂ {z | ∃ v i j, z = E v i j} := hE.gen ▸ Algebra.mem_top
    refine (Algebra.commute_of_mem_adjoin_of_forall_mem_commute ht ?_).symm.eq
    rintro _ ⟨v, i, j, rfl⟩
    rw [← hf, Commute, SemiconjBy, ← map_mul, ← map_mul, Subalgebra.mem_center_iff.1 hz]
  have hbr : ∀ x y : 𝔤,
      ψ (UniversalEnvelopingAlgebra.ι ℝ x) * ψ (UniversalEnvelopingAlgebra.ι ℝ y) -
        ψ (UniversalEnvelopingAlgebra.ι ℝ y) * ψ (UniversalEnvelopingAlgebra.ι ℝ x) =
      ψ (UniversalEnvelopingAlgebra.ι ℝ ⁅x, y⁆) := fun x y => by
    rw [LieHom.map_lie, Ring.lie_def, map_sub, map_mul, map_mul]
  have hrel : MultiRel fun v i j => ψ (UniversalEnvelopingAlgebra.ι ℝ (b (v, i, j))) := by
    refine ⟨fun v i j k m => ?_, fun v v' hv i j k m => ?_⟩
    · rw [hbr, h1, map_sub, map_sub]
      congr 1 <;> split_ifs <;> simp
    · rw [Commute, SemiconjBy, ← sub_eq_zero, hbr, h2 v v' hv, map_zero, map_zero]
  obtain ⟨ρ, hρ⟩ := hE.univ A _ hrel
  have hcomp : (ρ.restrictScalars ℝ).comp f = ψ := by
    apply UniversalEnvelopingAlgebra.hom_ext
    refine LieHom.ext fun x => LinearMap.congr_fun (f := LieHom.toLinearMap _)
      (g := LieHom.toLinearMap _) (b.ext ?_) x
    rintro ⟨v, i, j⟩
    change ρ (f (UniversalEnvelopingAlgebra.ι ℝ (b (v, i, j)))) =
      ψ (UniversalEnvelopingAlgebra.ι ℝ (b (v, i, j)))
    rw [hf, hρ]
  have hψ : ψ z = ρ (f z) := by rw [← hcomp]; rfl
  rw [hψ]
  have hle : capAlg E ≤ (capAlg fun v i j =>
      ψ (UniversalEnvelopingAlgebra.ι ℝ (b (v, i, j)))).comap ρ := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨v, u, rfl⟩
    refine Algebra.subset_adjoin ⟨v, u, ?_⟩
    refine (map_qdet ρ _ _).trans ?_
    simp only [hρ]
  exact hle (hE.centre hcen)
end

section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PK

section

variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {τ : K}

private theorem yy_val (π : O) (m : ℕ) (x : Etau K τ) :
    yy π m x = algebraMap O (Etau K τ) (π ^ m) * x := by
  rw [yy, algebraMap_etau (O := O), Algebra.smul_def]

private theorem mem_ord {y w : Etau K τ} :
    w ∈ Ord O y ↔ ∃ a b : O, w = algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * y := by
  change w ∈ (Submodule.span O {1, y} : Submodule O (Etau K τ)) ↔ _
  rw [Submodule.mem_span_pair]
  simp only [Algebra.smul_def, mul_one, eq_comm]

private theorem one_mem_ord (y : Etau K τ) : (1 : Etau K τ) ∈ Ord O y :=
  mem_ord.2 ⟨1, 0, by simp⟩

private theorem ord_mul {y : Etau K τ} {c : O} (hy : y * y = algebraMap O (Etau K τ) c)
    {v w : Etau K τ} (hv : v ∈ Ord O y) (hw : w ∈ Ord O y) : v * w ∈ Ord O y := by
  obtain ⟨a, b, rfl⟩ := mem_ord.1 hv
  obtain ⟨p, q, rfl⟩ := mem_ord.1 hw
  refine mem_ord.2 ⟨a * p + b * q * c, a * q + b * p, ?_⟩
  simp only [map_add (f := _), map_mul]
  linear_combination (algebraMap O (Etau K τ) b * algebraMap O (Etau K τ) q) * hy

private theorem ord_mono (π : O) (m : ℕ) (x : Etau K τ) :
    Ord O (yy π (m + 1) x) ⊆ Ord O (yy π m x) := by
  intro w hw
  obtain ⟨a, b, rfl⟩ := mem_ord.1 hw
  refine mem_ord.2 ⟨a, b * π, ?_⟩
  simp only [yy_val, pow_succ, map_mul]
  ring

private theorem yy_sq {π e : O} {x : Etau K τ} (h : x * x = algebraMap O (Etau K τ) e) (m : ℕ) :
    yy π m x * yy π m x = algebraMap O (Etau K τ) (π ^ m * π ^ m * e) := by
  simp only [yy_val, map_mul]
  linear_combination (algebraMap O (Etau K τ) (π ^ m) * algebraMap O (Etau K τ) (π ^ m)) * h

private theorem unit_mem {y : Etau K τ} {u : (Etau K τ)ˣ} (hu : u ∈ Hu O y) :
    (u : Etau K τ) ∈ Ord O y ∧ ((u⁻¹ : (Etau K τ)ˣ) : Etau K τ) ∈ Ord O y := by
  have h : PS.ml u (Ord O y) = Ord O y := hu
  refine ⟨h.subset ⟨1, one_mem_ord y, mul_one _⟩, ?_⟩
  have := PS.mem_ml.1 (h.symm.subset (one_mem_ord (O := O) y))
  rwa [mul_one] at this

private theorem hu_of_mem {y : Etau K τ} {c : O} (hy : y * y = algebraMap O (Etau K τ) c)
    {u : (Etau K τ)ˣ} (h1 : (u : Etau K τ) ∈ Ord O y)
    (h2 : ((u⁻¹ : (Etau K τ)ˣ) : Etau K τ) ∈ Ord O y) : u ∈ Hu O y := by
  change PS.ml u (Ord O y) = Ord O y
  ext w
  rw [PS.mem_ml]
  refine ⟨fun hw => ?_, fun hw => ord_mul hy h2 hw⟩
  have := ord_mul hy h1 hw
  rwa [Units.mul_inv_cancel_left] at this

private theorem ord_int {y w : Etau K τ} (hy : IsIntegral O y) (hw : w ∈ Ord O y) :
    IsIntegral O w := by
  obtain ⟨a, b, rfl⟩ := mem_ord.1 hw
  exact isIntegral_algebraMap.add (isIntegral_algebraMap.mul hy)

end

theorem UpperTheory.stabilizer_order_level_antitone_le_units :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → ∀ (π : O) (n : ℕ) (e : Oˣ) (h : O) (x : Etau K τ), Cond π n e h x → ∀ m : ℕ, Hu O (yy π (m + 1) x) ≤ Hu O (yy π m x) ∧ Hu O (yy π m x) ≤ Gu O τ := by
  intro O K _ _ _ _ _ Δ τ _ _ π n e h x c m
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · obtain ⟨h1, h2⟩ := unit_mem hu
    exact hu_of_mem (yy_sq c.sq m) (ord_mono π m x h1) (ord_mono π m x h2)
  · obtain ⟨h1, h2⟩ := unit_mem hu
    have hi : IsIntegral O (yy π m x) := by
      rw [yy_val]
      exact isIntegral_algebraMap.mul c.gen.int
    exact ⟨ord_int hi h1, ord_int hi h2⟩
end

section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PK

theorem UpperTheory.exists_discriminant_normal_form :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → τ ∈ (algebraMap O K).range → ∀ (s : O) (ε : Oˣ), τ ^ 2 - 4 = algebraMap O K (ε * s ^ 2) → ∃ (π : O) (n : ℕ) (e : Oˣ) (h : O) (x : Etau K τ), Cond π n e h x ∧ Ideal.span {s} = Ideal.span {π ^ n} := by
  intro O K _ _ _ _ _ Δ τ hL hτ hτr s ε hs
  haveI := hL.frac
  have inj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  obtain ⟨t, rfl⟩ := hτr
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hτ
    rw [hs]
    simp
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, μ, hμ⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hϖ
  have h2K : algebraMap O K (((hL.two.unit)⁻¹ : Oˣ) : O) * 2 = 1 := by
    have h1 : (((hL.two.unit)⁻¹ : Oˣ) : O) * 2 = 1 := hL.two.val_inv_mul
    have h3 := congrArg (algebraMap O K) h1
    rw [map_mul, map_one, map_ofNat] at h3
    exact h3
  have two_ne : (2 : K) ≠ 0 := by
    intro h
    rw [h, mul_zero] at h2K
    exact zero_ne_one h2K
  have hI : algebraMap O K (((hL.two.unit)⁻¹ : Oˣ) : O) = 2⁻¹ := by
    field_simp
    exact h2K
  have hP : algebraMap O K (ϖ ^ n) ≠ 0 := by
    rw [map_ne_zero_iff _ inj]
    exact pow_ne_zero _ hϖ.ne_zero
  have hrel : algebraMap O K t ^ 2 - 4
      = algebraMap O K ε * algebraMap O K μ ^ 2 * algebraMap O K (ϖ ^ n) ^ 2 := by
    rw [hs, hμ]
    simp only [map_mul, map_pow]
    ring
  set T := algebraMap O K t with hT
  set P := algebraMap O K (ϖ ^ n) with hPdef
  let x : Etau K T := ⟨-T / 2 / P, 1 / P⟩
  have hxre : x.re = -T / 2 / P := rfl
  have hxim : x.im = 1 / P := rfl
  have htr : trace x = 0 := by
    rw [trace_def, hxre, hxim]
    field_simp
    ring
  refine ⟨ϖ, n, ε * μ * μ * (hL.two.unit)⁻¹ * (hL.two.unit)⁻¹, t * (((hL.two.unit)⁻¹ : Oˣ) : O), x,
    ⟨hϖ, ⟨?_, ?_, ?_⟩, htr, ?_, ?_⟩, ?_⟩
  · rw [htr]
    exact ⟨0, map_zero _⟩
  · refine ⟨-((ε * μ * μ * (hL.two.unit)⁻¹ * (hL.two.unit)⁻¹ : Oˣ) : O), ?_⟩
    rw [norm_def, hxre, hxim]
    simp only [map_neg, Units.val_mul, map_mul, hI]
    field_simp
    linear_combination hrel
  · refine ⟨ε * μ * μ, ?_⟩
    rw [hxim, hrel]
    simp only [Units.val_mul, map_mul]
    field_simp
  · apply QuadraticAlgebra.ext
    · rw [algebraMap_etau, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.re_mul, hxre, hxim]
      simp only [Units.val_mul, map_mul, hI]
      field_simp
      linear_combination hrel
    · rw [algebraMap_etau, QuadraticAlgebra.algebraMap_im, QuadraticAlgebra.im_mul, hxre, hxim]
      field_simp
      ring
  · apply QuadraticAlgebra.ext
    · show (0 : K) = (algebraMap O (Etau K T) (t * (((hL.two.unit)⁻¹ : Oˣ) : O))).re + (yy ϖ n x).re
      rw [algebraMap_etau, QuadraticAlgebra.algebraMap_re]
      simp only [yy, QuadraticAlgebra.re_smul, smul_eq_mul, map_mul, hI, hxre]
      rw [← hT, ← hPdef]
      field_simp
      ring
    · show (1 : K) = (algebraMap O (Etau K T) (t * (((hL.two.unit)⁻¹ : Oˣ) : O))).im + (yy ϖ n x).im
      rw [algebraMap_etau, QuadraticAlgebra.algebraMap_im]
      simp only [yy, QuadraticAlgebra.im_smul, smul_eq_mul, hxim]
      rw [← hPdef]
      field_simp
      ring
  · rw [Ideal.span_singleton_eq_span_singleton, hμ]
    exact associated_unit_mul_left _ _ μ.isUnit
end

section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PK

theorem UpperTheory.exists_unit_smul_order_of_mem_gs :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → ∀ (π : O) (n : ℕ) (e : Oˣ) (h : O) (x : Etau K τ), Cond π n e h x → ∀ (t : Kˣ) (S : Set (Etau K τ)), S ∈ PS.Gs O τ t 1 → ∃ (m : ℕ) (r : Kˣ) (u : (Etau K τ)ˣ), u ∈ Gu O τ ∧ S = PS.ml (PS.sc τ r * u) (Ord O (yy π m x)) := by
  intro O K _ _ _ _ _ Δ τ hL hτ π n e h x hC t S hS
  obtain ⟨hfix, c, hc, hgen⟩ := hS
  rw [one_mul] at hgen
  obtain ⟨r, u, hu1, hu2, hcu⟩ := hC.gen.cint hL hc
  obtain ⟨s0, hs0⟩ := hfix.fg
  subst hs0
  set N : Submodule O (Etau K τ) := Submodule.span O (s0 : Set (Etau K τ)) with hN
  have hcS : (c : Etau K τ) ∈ N := hgen.1
  have hint : ∀ w ∈ N, ∃ a b : O, ((c⁻¹ : (Etau K τ)ˣ) : Etau K τ) * w
      = algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * x :=
    fun w hw => (hC.gen.int_iff hL _).1 (hgen.2 w hw)
  let B : Ideal O :=
    { carrier := {b | ∃ a : O,
        (c : Etau K τ) * (algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * x) ∈ N}
      add_mem' := by
        rintro b1 b2 ⟨a1, h1⟩ ⟨a2, h2⟩
        refine ⟨a1 + a2, ?_⟩
        have key : (c : Etau K τ) * (algebraMap O (Etau K τ) (a1 + a2) + algebraMap O (Etau K τ) (b1 + b2) * x)
            = (c : Etau K τ) * (algebraMap O (Etau K τ) a1 + algebraMap O (Etau K τ) b1 * x)
              + (c : Etau K τ) * (algebraMap O (Etau K τ) a2 + algebraMap O (Etau K τ) b2 * x) := by
          simp only [map_add (f := _)]
          ring
        rw [key]
        exact N.add_mem h1 h2
      zero_mem' := by
        refine ⟨0, ?_⟩
        simp only [map_zero, zero_mul, add_zero, mul_zero]
        exact N.zero_mem
      smul_mem' := by
        rintro k b ⟨a, hab⟩
        refine ⟨k * a, ?_⟩
        have key : (c : Etau K τ) * (algebraMap O (Etau K τ) (k * a) + algebraMap O (Etau K τ) (k • b) * x)
            = k • ((c : Etau K τ) * (algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * x)) := by
          rw [smul_eq_mul, Algebra.smul_def, map_mul, map_mul]
          ring
        rw [key]
        exact N.smul_mem k hab }
  have hB : B ≠ ⊥ := by
    have hωc : ω * (c : Etau K τ) ∈ N := hfix.stab _ hcS
    obtain ⟨a, b, hab⟩ := hint _ hωc
    have hω : (ω : Etau K τ) = algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * x := by
      rw [← hab, mul_left_comm, Units.inv_mul, mul_one]
    have hb : b ∈ B := ⟨a, by rw [← hω, mul_comm]; exact hωc⟩
    intro hbot
    rw [hbot] at hb
    have hb0 : b = 0 := (Submodule.mem_bot O).1 hb
    rw [hb0, map_zero, zero_mul, add_zero] at hω
    have him := congrArg QuadraticAlgebra.im hω
    rw [algebraMap_etau, QuadraticAlgebra.algebraMap_im] at him
    exact one_ne_zero him
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hB hC.irr
  have hyy : yy π m x = algebraMap O (Etau K τ) (π ^ m) * x := by
    rw [yy, Algebra.smul_def, algebraMap_etau (O := O) (π ^ m)]
  have hpm : π ^ m ∈ B := by
    rw [hm]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨a0, ha0⟩ := hpm
  refine ⟨m, r, u, ⟨hu1, hu2⟩, ?_⟩
  rw [← hcu]
  ext w
  rw [PS.mem_ml]
  show w ∈ N ↔ _ ∈ Submodule.span O {1, yy π m x}
  rw [Submodule.mem_span_pair]
  constructor
  · intro hw
    obtain ⟨a, b, hab⟩ := hint w hw
    have hbB : b ∈ B := ⟨a, by rw [← hab, ← mul_assoc, Units.mul_inv, one_mul]; exact hw⟩
    rw [hm, Ideal.mem_span_singleton'] at hbB
    obtain ⟨k, rfl⟩ := hbB
    refine ⟨a, k, ?_⟩
    rw [hab, hyy, Algebra.smul_def, Algebra.smul_def, map_mul]
    ring
  · rintro ⟨a, k, hak⟩
    have hw : w = (c : Etau K τ) * (a • 1 + k • yy π m x) := by
      rw [hak, ← mul_assoc, Units.mul_inv, one_mul]
    rw [hw, mul_add, hyy]
    apply N.add_mem
    · rw [mul_smul_comm, mul_one]
      exact N.smul_mem a hcS
    · rw [mul_smul_comm]
      apply N.smul_mem
      have key : (c : Etau K τ) * (algebraMap O (Etau K τ) (π ^ m) * x)
          = (c : Etau K τ) * (algebraMap O (Etau K τ) a0 + algebraMap O (Etau K τ) (π ^ m) * x)
            - a0 • (c : Etau K τ) := by
        rw [Algebra.smul_def]
        ring
      rw [key]
      exact N.sub_mem ha0 (N.smul_mem a0 hcS)
end

section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PK

theorem UpperTheory.isSquare_sq_sub_four_iff_isSquare_unit :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → ∀ (π : O) (n : ℕ) (e : Oˣ) (h : O) (x : Etau K τ), Cond π n e h x → (IsSquare (τ ^ 2 - 4) ↔ IsSquare (e : O)) := by
  intro O K _ _ _ _ _ Δ τ L hD π n e h x hc
  haveI := L.frac
  have E : (ω - algebraMap O (Etau K τ) h) * (ω - algebraMap O (Etau K τ) h) = algebraMap O (Etau K τ) (π ^ n * π ^ n * e) := by
    rw [hc.om, add_sub_cancel_left]
    simp only [yy, smul_mul_smul_comm, hc.sq]
    simp only [algebraMap_etau (O := O), Algebra.smul_def, map_mul]
  have Er := congrArg QuadraticAlgebra.re E
  have Ei := congrArg QuadraticAlgebra.im E
  simp [algebraMap_etau] at Er Ei
  have hτ : τ = 2 * algebraMap O K h := by linear_combination Ei
  have key : τ ^ 2 - 4 = (2 * algebraMap O K π ^ n) ^ 2 * algebraMap O K (e : O) := by
    rw [hτ]
    linear_combination 4 * Er
  constructor
  · rintro ⟨r, hr⟩
    have hq : 2 * algebraMap O K π ^ n ≠ 0 := by
      intro h0
      apply hD
      rw [key, h0]
      ring
    have hsq : (r / (2 * algebraMap O K π ^ n)) ^ 2 = algebraMap O K (e : O) := by
      rw [div_pow, sq r, ← hr, key]
      exact mul_div_cancel_left₀ _ (pow_ne_zero 2 hq)
    obtain ⟨b, hb⟩ := sq_int L _ _ hsq
    refine ⟨b, IsFractionRing.injective O K ?_⟩
    rw [map_mul, hb, ← hsq]
    ring
  · rintro ⟨b, hb⟩
    refine ⟨2 * algebraMap O K π ^ n * algebraMap O K b, ?_⟩
    rw [key, hb, map_mul]
    ring
end

section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PK

theorem UpperTheory.relIndex_stabilizer_order_level_zero :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → ∀ (π : O) (n : ℕ) (e : Oˣ) (h : O) (x : Etau K τ), Cond π n e h x → (Hu O (yy π 0 x)).relIndex (Gu O τ) = 1 := by
  intro O K _ _ _ _ _ Δ τ L hD π n e h x hc
  have hy : yy π 0 x = x := by simp [yy]
  have hO : PK.Ord O (yy π 0 x) = (PK.Mx O τ : Set (Etau K τ)) := by
    rw [hy, Gen1.span L hc.gen]
    rfl
  rw [Subgroup.relIndex_eq_one]
  intro u hu
  show PS.ml u (PK.Ord O (yy π 0 x)) = PK.Ord O (yy π 0 x)
  rw [hO]
  exact ml_Mx hu.1 hu.2
end
