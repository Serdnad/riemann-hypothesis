module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle557
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle733
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle573
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle780
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle602
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle601
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle652
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle757
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle634
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle588
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle781
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle759
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle106
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle082
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle761
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle745
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle783
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle775
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle748
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle776
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle782
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection

@[expose] public section

section

noncomputable section

namespace GlobalTheory.RefPair

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField
  IsDedekindDomain GlobalTheory.NPin GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def HasThetaAt (D : D7) {μt : D.what₂.Tup} {j : ℕ} (Mr : MtReal D μt j) {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r}
    (X : RowMod D rep j) (μ η : HChar D.host.E) : Prop :=
  ∃ (Ω : Type) (_ : AddCommGroup Ω) (_ : Module ℂ Ω) (ω : GAf D.host.E D.R.nV × GAf D.host.E D.R.r →* Module.End ℂ Ω)
    (Λ : Ω →ₗ[ℂ] ↥(NG.AFall D.host.E D.R.nV Mr.wt.ρ) →ₗ[ℂ] ↥X.C →ₗ⋆[ℂ] ℂ) (φ₀ : Ω),
    (∀ h g φ (F F' : ↥(NG.AFall D.host.E D.R.nV Mr.wt.ρ)) (y y' : ↥X.C),
      (F' : GAf D.host.E D.R.nV → Mr.wt.W) = NG.rt D.host.E D.R.nV h F → (y' : X.A) = X.ρ g y →
      Λ (ω (h, g) φ) F' y' = Λ φ F y) ∧
    (∀ x y (F : ↥(NG.AFall D.host.E D.R.nV Mr.wt.ρ)), (F : GAf D.host.E D.R.nV → Mr.wt.W) = Mr.real x →
      inner ℂ y (D.what₂.thetaP μt j x) = Λ φ₀ F ⟨X.φ y, X.φ_mem y⟩) ∧
    ∀ (s : SplitPlace D.host.E) μw ηw, IsComp μ s.w μw → IsComp η s.w ηw →
      φ₀ ∈ ⨆ (ι : SB (Matrix (Fin D.R.nV) (Fin D.R.r) (s.w.adicCompletion D.host.E)) →ₗ[ℂ] Ω)
        (_ : IsLinAt ω s μw ηw ι), LinearMap.range ι

end GlobalTheory.RefPair

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim

theorem exists_beta_limit : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ), F.IsDR → ∃ B : Matrix (Fin d) (Fin d) (Per.BdRp l), ∀ m : ℕ, ∃ (k : ℕ) (β : Matrix (Fin d) (Fin d) bk.S), F.IsBeta m k β ∧ ∀ i j, aDp l (bk.ev (β i j)) - (l : Per.BdRp l) ^ k * B i j ∈ Per.FilP l m := by
  intro l _ K bk N d ρ F hF
  choose k β hβ using hF
  have mono : ∀ {m n : ℕ}, m ≤ n → ∀ {k' : ℕ} {β' : Matrix (Fin d) (Fin d) bk.S}, F.IsBeta n k' β' → F.IsBeta m k' β' :=
    fun h _ _ hb => ⟨hb.1, fun g i j => (pow_dvd_pow _ h).trans (hb.2 g i j)⟩
  obtain ⟨ζ, e, h0, -, h1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : e.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps e := ⟨he, fun hh => h1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  obtain ⟨hfil, -, hcomp, -⟩ := GlobalTheory.MemLoc.filtration_eq_xi_pow l e hE
  obtain ⟨v, hv⟩ := (isUnit_l_BdRp l).exists_left_inv
  have hvk : ∀ a : ℕ, v ^ a * (l : Per.BdRp l) ^ a = 1 := fun a => by rw [← mul_pow, hv, one_pow]
  set X : ℕ → Fin d → Fin d → Per.BdRp l := fun n i j => aDp l (bk.ev (β n i j)) with hX
  set x : ℕ → Fin d → Fin d → Per.BdRp l := fun n i j => v ^ k n * X n i j with hx
  have cauchy : ∀ m n, m ≤ n → ∀ i j, x n i j - x m i j ∈ Per.FilP l m := by
    intro m n hmn i j
    have h := GlobalTheory.T.breuilKisin_beta_unique_mod_E_pow l K bk m N d ρ F (k m) (k n) (β m) (β n) (hβ m) (mono hmn (hβ n)) i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h
    have h2 : bk.ev bk.E ^ m ∣ bk.ev ((l : bk.S) ^ k n * β m i j - (l : bk.S) ^ k m * β n i j) := by
      rw [← map_pow]; exact map_dvd bk.ev h
    have h3 := ((GlobalTheory.T.eisensteinImage_pow_ideal_ainf_properties l K bk m).2.2.1 _).2 h2
    simp only [map_sub, map_mul, map_pow, map_natCast] at h3
    have h4 := Ideal.mul_mem_left (Per.FilP l m) (-(v ^ k n * v ^ k m)) h3
    convert h4 using 1
    simp only [hx, hX]
    linear_combination (v ^ k m * aDp l (bk.ev (β m i j))) * hvk (k n) - (v ^ k n * aDp l (bk.ev (β n i j))) * hvk (k m)
  have hmem : ∀ (n : ℕ) (y : Per.BdRp l), y ∈ (Ideal.span {aDp l (xi e)} ^ n • ⊤ : Submodule (Per.BdRp l) (Per.BdRp l)) ↔
      y ∈ Per.FilP l n := by
    intro n y
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton, hfil]
  have lim : ∀ i j, ∃ L : Per.BdRp l, ∀ n, x n i j - L ∈ Per.FilP l n := by
    intro i j
    obtain ⟨L, hL⟩ := hcomp.toIsPrecomplete.prec (f := fun n => x n i j) (fun {m n} hmn => by
      rw [SModEq.sub_mem, hmem, ← neg_sub]
      exact (Per.FilP l m).neg_mem (cauchy m n hmn i j))
    exact ⟨L, fun n => (hmem n _).1 (SModEq.sub_mem.1 (hL n))⟩
  choose B hB using lim
  refine ⟨Matrix.of B, fun m => ⟨k m, β m, hβ m, fun i j => ?_⟩⟩
  have h := Ideal.mul_mem_left (Per.FilP l m) ((l : Per.BdRp l) ^ k m) (hB i j m)
  convert h using 1
  simp only [Matrix.of_apply, hx, hX]
  linear_combination (-(aDp l (bk.ev (β m i j)))) * hvk (k m)

end GlobalTheory.BKLim
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem map_ne_top_of_isLoc_ff {l : ℕ} {R : Type} [CommRing R] {B L C : Obj l R} (s : B.A) (h : Hom B L)
    (hL : IsLoc s h) (e : Hom L C) (he : (qmap e 1).FaithfullyFlat) (𝔪 : Ideal B.A) (hm : 𝔪.IsMaximal)
    (hs : s ∉ 𝔪) : 𝔪.map (e.comp h).f ≠ ⊤ := by
  have hJ : adI B ^ 1 ≤ 𝔪 := by
    rw [pow_one]
    haveI := B.complete
    exact le_trans (IsAdicComplete.le_jacobson_bot (adI B)) fun x hx => Ideal.mem_sInf.1 hx ⟨bot_le, hm⟩
  haveI : 𝔪.IsPrime := hm.isPrime
  have hp : (𝔪.map (Ideal.Quotient.mk (adI B ^ 1))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hs' : Ideal.Quotient.mk (adI B ^ 1) s ∉ 𝔪.map (Ideal.Quotient.mk (adI B ^ 1)) := by
    rwa [Ideal.mem_quotient_iff_mem hJ]
  letI := (qmap h 1).toAlgebra
  haveI := hL.away 1
  have h1 : ((𝔪.map (Ideal.Quotient.mk (adI B ^ 1))).map (qmap h 1)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (Ideal.Quotient.mk (adI B ^ 1) s))
      (L.A ⧸ adI L ^ 1) _ hp ((Ideal.disjoint_powers_iff_notMem_of_isPrime _).2 hs')
  have h2 : ((𝔪.map (Ideal.Quotient.mk (adI B ^ 1))).map (qmap h 1)).map (qmap e 1) ≠ ⊤ := by
    intro htop
    apply h1.ne_top
    letI := (qmap e 1).toAlgebra
    haveI : Module.FaithfullyFlat (L.A ⧸ adI L ^ 1) (C.A ⧸ adI C ^ 1) := he
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := C.A ⧸ adI C ^ 1)
      ((𝔪.map (Ideal.Quotient.mk (adI B ^ 1))).map (qmap h 1))]
    change Ideal.comap (qmap e 1) (Ideal.map (qmap e 1) _) = ⊤
    rw [htop, Ideal.comap_top]
  intro htop
  apply h2
  rw [Ideal.map_map, Ideal.map_map]
  have : ((qmap e 1).comp (qmap h 1)).comp (Ideal.Quotient.mk (adI B ^ 1)) =
      (Ideal.Quotient.mk (adI C ^ 1)).comp (e.comp h).f := RingHom.ext fun _ => rfl
  rw [this, ← Ideal.map_map, htop, Ideal.map_top]

end GlobalTheory.BSP

namespace GlobalTheory.BSP

theorem map_ne_top_of_comp {l : ℕ} {R : Type} [CommRing R] {B Q C : Obj l R} (c : Hom B Q) (π : Hom Q C)
    (a : Hom B C) (hc : π.comp c = a) (𝔪 : Ideal B.A) (ha : 𝔪.map a.f ≠ ⊤) : 𝔪.map c.f ≠ ⊤ := by
  subst hc
  intro htop
  apply ha
  change Ideal.map (π.f.comp c.f) 𝔪 = ⊤
  rw [← Ideal.map_map, htop, Ideal.map_top]

theorem exists_cover_receiving_bk : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)),
    ∃ (C : Obj l ↥(OL K)) (h : Hom B C), Nonempty (Hom bk.prism C) ∧ Cover h := by
  intro l _ K bk B
  obtain ⟨n, s, t, hspan, hst⟩ := GlobalTheory.T.invertible_ideal_principal_on_zariski_cover B.A B.I B.inv
  have hga : ∀ i, GenAway B (s i) (t i) := fun i => ⟨(hst i).1, fun x hx => by
    obtain ⟨c, hc⟩ := (hst i).2 x hx
    exact ⟨1, by rw [pow_one, hc]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)⟩⟩
  choose L h hL hLI using fun i => GlobalTheory.T.exists_isPrismLocalizationAway_of_generated l (↥(OL K)) B (s i) (t i) (hga i)
  have hfr : ∀ i, ∃ p, IsFrame bk (L i) ((h i).f (t i)) p := fun i => by
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective ((L i).str (bk.str.symm (Ideal.Quotient.mk _ X)))
    exact ⟨p, hLI i, hp⟩
  choose p hp using hfr
  have En : ∀ i, Env bk (L i) ((h i).f (t i)) (p i) := fun i => (GlobalTheory.T.nonempty_breuilKisinPrismCoproduct l K bk (L i) _ _ (hp i)).some
  obtain ⟨Q, π, hbij, -, huniv⟩ := GlobalTheory.T.exists_finite_product_oriented_boundedPrisms l (↥(OL K)) n (fun i => (En i).Q) fun i => ⟨_, (En i).I_eq⟩
  obtain ⟨c, hc⟩ := huniv B fun i => (En i).inl.comp (h i)
  obtain ⟨g, -⟩ := huniv bk.prism fun i => (En i).inr
  refine ⟨Q, c, ⟨g⟩, ?_⟩
  have hcov : ∀ i, Cover (En i).inl := fun i => GlobalTheory.T.isPrismCover_breuilKisinCoproduct_inl l K bk (L i) _ _ (hp i) (En i)
  have hstab : ∀ i, Stable ((π i).comp c) := fun i => by
    rw [hc i]
    exact GlobalTheory.T.isStablePrismHom_comp l _ B (L i) (En i).Q (h i) (En i).inl
      (GlobalTheory.T.isStablePrismHom_of_localizationAway l _ B (L i) (s i) (h i) ⟨t i, (hga i).1, (hga i).2⟩ (hL i)) (hcov i).stable
  refine GlobalTheory.T.isPrismCover_of_stable_maximal_map_ne_top l _ B Q c (GlobalTheory.T.isStablePrismHom_of_finite_product_components l _ n _ (fun i => ⟨_, (En i).I_eq⟩) Q π hbij B c hstab) ?_
  intro 𝔪 hm
  obtain ⟨i, hi⟩ : ∃ i, s i ∉ 𝔪 := by
    by_contra hall
    push_neg at hall
    exact hm.ne_top (eq_top_iff.2 (hspan ▸ Ideal.span_le.2 (Set.range_subset_iff.2 hall)))
  exact map_ne_top_of_comp c (π i) _ (hc i) 𝔪
    (map_ne_top_of_isLoc_ff (s i) (h i) (hL i) (En i).inl ((hcov i).ff 1) 𝔪 hm hi)

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.RealMatrix

section Alg

variable {R R' : Type} [CommRing R] [CommRing R'] {n : Type} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
theorem map_smul_hom (f : R →+* R') (c : R) (M : Matrix n n R) : (c • M).map f = f c • M.map f := by
  ext i j
  simp

theorem frobenius_matrix_equation_inverse_scaling (F : R →+* R) (e t v : R) (hv : v * t = 1) (ht : F t = e * t) (a N : ℕ) (Y A : Matrix n n R)
    (h : e ^ a • Y.map F = Y * A) : e ^ (a + N) • (v ^ N • Y).map F = (v ^ N • Y) * A := by
  have h1 : F v * (e * t) = 1 := by rw [← ht, ← map_mul, hv, map_one]
  have h2 : e * F v = v := by linear_combination v * h1 - (e * F v) * hv
  have h3 : e ^ (a + N) * F v ^ N = v ^ N * e ^ a := by
    rw [pow_add, mul_assoc, ← mul_pow, h2, mul_comm]
  rw [map_smul_hom, map_pow, smul_smul, h3, ← smul_smul, h, Matrix.smul_mul]

theorem galois_matrix_equation_inverse_scaling (G : R →+* R) (t v : R) (hv : v * t = 1) (N : ℕ) (P Y ε : Matrix n n R)
    (h : t ^ N • (P * Y.map G) = G t ^ N • (Y * ε)) : P * (v ^ N • Y).map G = (v ^ N • Y) * ε := by
  have h1 : G v * G t = 1 := by rw [← map_mul, hv, map_one]
  have h2 := congrArg (fun M => (v ^ N * G v ^ N) • M) h
  have h3 : v ^ N * G v ^ N * t ^ N = G v ^ N := by
    rw [mul_right_comm, ← mul_pow, hv, one_pow, one_mul]
  have h4 : v ^ N * G v ^ N * G t ^ N = v ^ N := by
    rw [mul_assoc, ← mul_pow, h1, one_pow, mul_one]
  simp only [smul_smul, h3, h4] at h2
  rw [map_smul_hom, map_pow, Matrix.mul_smul, h2, Matrix.smul_mul]

theorem descend (f : R →+* R') (hf : Function.Injective f) (x y : R) (N : ℕ) (M Y ε : Matrix n n R)
    (h : f x ^ N • M.map f = f y ^ N • (Y.map f * ε.map f)) : x ^ N • M = y ^ N • (Y * ε) := by
  apply Matrix.map_injective hf
  simp only []
  rw [map_smul_hom, map_smul_hom, map_pow, map_pow, Matrix.map_mul, h]

theorem push (f : R →+* R') (x y : R) (N : ℕ) (P Q Y ε : Matrix n n R) (h : x ^ N • (P * Q) = y ^ N • (Y * ε)) :
    f x ^ N • (P.map f * Q.map f) = f y ^ N • (Y.map f * ε.map f) := by
  rw [← Matrix.map_mul, ← Matrix.map_mul, ← map_pow, ← map_pow, ← map_smul_hom, ← map_smul_hom, h]

end Alg

theorem exists_mreal : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ S : Strat bk d, S.a = ht.a + s.N → S.A = ht.A → (∀ g : ↥(GK K), ht.Rel (B := ainfObj K) (BK.hf bk.ι X) bk.ι ((ainfHom K g).comp bk.ι) ((S.ε bk.ι ((ainfHom K g).comp bk.ι)).map bk.iA)) → ∃ T : Matrix (Fin d) (Fin d) (WCb l), MReal S ρ T := by
  intro l _ K bk d ρ τ s ht hτ S ha hA hrel
  obtain ⟨u, hu⟩ := (GlobalTheory.T.breuilKisin_period_isUnit_and_ainf_saturated l K bk τ hτ).1
  have hv : (↑u⁻¹ : WCb l) * inclW l τ = 1 := by rw [← hu, Units.inv_mul]
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have hinj : Function.Injective bk.iA := (GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk (Ainf l) bk.ev ι tb).1
  refine ⟨(↑u⁻¹ : WCb l) ^ s.N • ht.Y.map (inclW l), ?_, ?_, ?_⟩
  · rw [Algebra.smul_def]
    exact (((Units.isUnit _).pow _).map _).mul ht.unit
  · rw [ha, hA]
    refine frobenius_matrix_equation_inverse_scaling (frobW l : WCb l →+* WCb l) (bk.evW bk.E) (inclW l τ) _ hv ?_ _ _ _ _ ?_
    · change frobW l (inclW l τ) = inclW l (bk.ev bk.E) * inclW l τ
      rw [frobW_inclW, hτ.1, map_mul]
    · have h := congrArg (fun M => M.map (inclW l)) ht.φ
      try beta_reduce at h
      rw [map_smul_hom, map_pow, Matrix.map_mul] at h
      refine Eq.trans ?_ h
      congr 1
      ext1 i j
      exact frobW_inclW _
  · intro g
    have h0 := descend bk.iA hinj _ _ _ _ _ _ (GlobalTheory.T.rel_galois_comparison_matrix l K bk d ρ τ s ht hτ g _ (hrel g))
    have h := push (inclW l) _ _ _ _ _ _ _ h0
    rw [← galW_inclW] at h
    refine galois_matrix_equation_inverse_scaling (galW l (g : GQ l) : WCb l →+* WCb l) (inclW l τ) _ hv _ _ _ _ ?_
    refine Eq.trans ?_ h
    congr 2
    · ext1 i j
      exact ((inclWA l).commutes _).symm
    · ext1 i j
      exact galW_inclW _ _

end GlobalTheory.BSP.RealMatrix
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem pow_dvd_map_of_smul_eq {A D W : Type} [CommRing A] [CommRing D] [CommRing W] {n : Type} [Fintype n]
    [DecidableEq n] (i : A →+* D) (hi : Function.Injective i) (j : A →+* W) (t t' : A) (N l k : ℕ)
    (M Y y : Matrix n n A) (ε : Matrix n n D) (h : i t ^ N • M.map i = i t' ^ N • (Y.map i * ε))
    (hy : y.map i = (l : D) ^ k • ε) (ht : IsUnit (j t')) (hY : IsUnit (Y.map j)) (a b : n) :
    (l : W) ^ k ∣ j (y a b) := by
  have h1 : ((l : A) ^ k * t ^ N) • M = t' ^ N • (Y * y) := by
    apply Matrix.map_injective hi
    change (((l : A) ^ k * t ^ N) • M).map i = (t' ^ N • (Y * y)).map i
    have e1 : (((l : A) ^ k * t ^ N) • M).map i = (l : D) ^ k • (i t ^ N • M.map i) := by
      ext p q; simp [mul_assoc]
    have e2 : (t' ^ N • (Y * y)).map i = i t' ^ N • (Y.map i * y.map i) := by
      rw [← Matrix.map_mul]; ext p q; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow]
    rw [e1, e2, h, hy, Matrix.mul_smul, smul_comm]
  have h2 : (l : W) ^ k • (j t ^ N • M.map j) = j t' ^ N • (Y.map j * y.map j) := by
    have e := congrArg (fun Z : Matrix n n A => Z.map j) h1
    rw [← Matrix.map_mul]
    ext p q
    have := congrFun (congrFun e p) q
    simpa only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, map_natCast, mul_assoc]
      using this
  obtain ⟨u, hu⟩ := hY
  obtain ⟨v, hv⟩ := ht.pow N
  have h3 : y.map j = (l : W) ^ k • ((↑v⁻¹ : W) • ((↑u⁻¹ : Matrix n n W) * (j t ^ N • M.map j))) := by
    rw [smul_comm, ← Matrix.mul_smul, h2, ← hu, ← hv, Matrix.mul_smul, ← mul_assoc, Units.inv_mul, one_mul,
      smul_smul, Units.inv_mul, one_smul]
  exact ⟨_, congrFun (congrFun h3 a) b⟩

theorem pow_dvd_of_rel_gal : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → (∀ g, IsUnit (ρ g)) → ∀ (g : ↥(GK K)) (ε : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)), ht.Rel (B := ainfObj K) (BK.hf bk.ι X) bk.ι ((ainfHom K g).comp bk.ι) ε → ∀ (k : ℕ) (y : Matrix (Fin d) (Fin d) (Ainf l)), y.map bk.iA = ((l : ℕ) : bk.DA bk.ρ₀) ^ k • ε → ∀ i j, ((l : ℕ) : Ainf l) ^ k ∣ y i j := by
  intro l _ K bk d ρ τ s ht hτ _ g ε hε k y hy i j
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  obtain ⟨-, hu, hsat⟩ := GlobalTheory.T.breuilKisin_period_isUnit_and_ainf_saturated l K bk τ hτ
  exact hsat k _ (pow_dvd_map_of_smul_eq bk.iA (GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk (Ainf l) bk.ev ι tb).1 (inclW l) τ _ s.N l k
    _ ht.Y y ε (GlobalTheory.T.rel_galois_comparison_matrix l K bk d ρ τ s ht hτ g ε hε) hy (hu g) ht.unit i j)

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.EquivKisin



theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N N' d d' : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') (ℤ_[l])) (F : Pre bk N d ρ) (F' : Pre bk N' d' ρ') (f : Matrix (Fin d') (Fin d) (ℤ_[l])), (∀ g, f * ρ g = ρ' g * f) → ∃ Y : Matrix (Fin d') (Fin d) (bk.S), F'.T * Y.map bk.evW = zW f * F.T := by
  intro l _ K bk τ hτ N N' d d' ρ ρ' F F' f hf
  obtain ⟨u, hu⟩ := F'.unit
  have cancel : ∀ M M' : Matrix (Fin d') (Fin d) (WCb l), F'.T * M = F'.T * M' → M = M' := by
    intro M M' h
    have h2 := congrArg (fun Z => (↑u⁻¹ : Matrix (Fin d') (Fin d') (WCb l)) * Z) h
    simp only [← hu, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at h2
    exact h2
  have hzmul : ∀ {m n o : Type} [Fintype n] (A : Matrix m n ℤ_[l]) (B : Matrix n o ℤ_[l]),
      zW (A * B) = zW A * zW B := fun A B => Matrix.map_mul
  set Xm : Matrix (Fin d') (Fin d) (WCb l) := (↑u⁻¹ : Matrix (Fin d') (Fin d') (WCb l)) * (zW f * F.T) with hXm
  have hX : F'.T * Xm = zW f * F.T := by
    rw [hXm, ← hu, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

  have hfix : ∀ g : ↥(GK K), bk.FixFlat g → Xm.map (galW l (g : GQ l)) = Xm := by
    intro g hg
    let G : WCb l →+* WCb l := (galW l (g : GQ l)).toRingEquiv.toRingHom
    have hzG : ∀ {m n : Type} (M : Matrix m n ℤ_[l]), (zW M).map G = zW M :=
      fun M => Matrix.ext fun i j => (galW l (g : GQ l)).commutes _
    have a1 : zW (ρ' g) * F'.T.map G = F'.T := F'.fix g hg
    have a2 : zW (ρ g) * F.T.map G = F.T := F.fix g hg
    change Xm.map G = Xm
    apply cancel
    have h1 := congrArg (fun M => M.map G) hX
    simp only [Matrix.map_mul, hzG] at h1
    calc F'.T * Xm.map G = zW (ρ' g) * (F'.T.map G * Xm.map G) := by
          rw [← Matrix.mul_assoc, a1]
      _ = zW (ρ' g * f) * F.T.map G := by rw [h1, hzmul, Matrix.mul_assoc]
      _ = zW f * (zW (ρ g) * F.T.map G) := by rw [← hf g, hzmul, Matrix.mul_assoc]
      _ = F'.T * Xm := by rw [a2, hX]

  have hφ : bk.evW bk.E ^ N • (F'.A.map bk.evW * Xm.map (frobW l)) =
      bk.evW bk.E ^ N' • (Xm * F.A.map bk.evW) := by
    let Fr : WCb l →+* WCb l := (frobW l).toRingHom
    have hzF : ∀ {m n : Type} (M : Matrix m n ℤ_[l]), (zW M).map Fr = zW M :=
      fun M => Matrix.ext fun i j => (frobW l).commutes _
    have b1 : bk.evW bk.E ^ N • F.T.map Fr = F.T * F.A.map bk.evW := F.φ
    have b2 : bk.evW bk.E ^ N' • F'.T.map Fr = F'.T * F'.A.map bk.evW := F'.φ
    change bk.evW bk.E ^ N • (F'.A.map bk.evW * Xm.map Fr) = bk.evW bk.E ^ N' • (Xm * F.A.map bk.evW)
    apply cancel
    have h1 := congrArg (fun M => M.map Fr) hX
    simp only [Matrix.map_mul, hzF] at h1
    rw [Matrix.mul_smul, Matrix.mul_smul, ← Matrix.mul_assoc, ← b2, Matrix.smul_mul, h1, smul_smul,
      ← Matrix.mul_assoc, hX, Matrix.mul_assoc, ← b1, Matrix.mul_smul, smul_smul, mul_comm]

  have hOE : ∀ i j, Xm i j ∈ bk.OE := by
    obtain ⟨w, hw, hew⟩ := (GlobalTheory.T.integral_elements_unit_factorization l K bk).2.2.1 bk.E (GlobalTheory.BSP.EquivOE.not_dvd_E bk)
    have hA : F.A.map bk.evW * F.A'.map bk.evW =
        bk.evW bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (WCb l)) := by
      rw [← Matrix.map_mul, F.A_mul]
      ext i j
      by_cases h : i = j <;> simp [h, Matrix.one_apply]
    have h1 : Xm = (w ^ (N' + 2 * N) * bk.evW bk.E ^ N) •
        (F'.A.map bk.evW * Xm.map (frobW l) * F.A'.map bk.evW) := by
      rw [mul_smul, ← Matrix.smul_mul, hφ, Matrix.smul_mul, Matrix.mul_assoc, hA, Matrix.mul_smul, Matrix.mul_one,
        smul_smul, smul_smul, mul_assoc, ← pow_add, ← mul_pow, mul_comm w, hew, one_pow, one_smul]
    intro i j
    refine GlobalTheory.T.mem_OE_of_invariant_frobenius_solution l K bk (Fin d' × Fin d) (fun p => Xm p.1 p.2)
      (fun p q => w ^ (N' + 2 * N) * bk.evW bk.E ^ N * bk.evW (F'.A q.1 p.1) * bk.evW (F.A' p.2 q.2))
      (fun p q => ?_) (fun q => ?_) (fun g h q => ?_) (i, j)
    · exact bk.OE.mul_mem (bk.OE.mul_mem (bk.OE.mul_mem (bk.OE.pow_mem hw _)
        (bk.OE.pow_mem (GlobalTheory.BSP.EquivOE.evW_mem bk _) _)) (GlobalTheory.BSP.EquivOE.evW_mem bk _))
        (GlobalTheory.BSP.EquivOE.evW_mem bk _)
    · have h2 := congrFun (congrFun h1 q.1) q.2
      rw [h2, Fintype.sum_prod_type_right]
      simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => by ring
    · exact congrFun (congrFun (hfix g h) q.1) q.2

  obtain ⟨Y₁, Y₁', hY₁, hY₁'⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N' d' ρ' F'
  obtain ⟨Y₂, Y₂', hY₂, hY₂'⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N d ρ F
  set t : WCb l := inclW l τ with ht
  have hinv : t ^ N' • Y₁'.map (inclW l) = t ^ N' • (t ^ N' • (↑u⁻¹ : Matrix (Fin d') (Fin d') (WCb l))) := by
    have e1 := congrArg (fun M => M.map (inclW l)) hY₁'
    simp only [Matrix.map_mul, hY₁] at e1
    have e2 : (τ ^ (2 * N') • (1 : Matrix (Fin d') (Fin d') (Ainf l))).map (inclW l) =
        (t ^ N' * t ^ N') • (1 : Matrix (Fin d') (Fin d') (WCb l)) := by
      ext i j
      by_cases h : i = j <;> simp [h, Matrix.one_apply, ht, ← pow_add, two_mul]
    rw [e2, Matrix.smul_mul, ← hu] at e1
    have e3 := congrArg (fun Z => (↑u⁻¹ : Matrix (Fin d') (Fin d') (WCb l)) * Z) e1
    simp only [Matrix.mul_smul, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_one] at e3
    rw [e3, smul_smul]
  have hzf : (f.map (algebraMap ℤ_[l] (Ainf l))).map (inclW l) = zW f := by
    exact Matrix.ext fun i j => (inclWA l).commutes (f i j)
  let x : Matrix (Fin d') (Fin d) (Ainf l) := τ ^ N' • (Y₁' * f.map (algebraMap ℤ_[l] (Ainf l)) * Y₂)
  have hx : x.map (inclW l) = inclW l τ ^ (2 * N' + N) • Xm := by
    have : x.map (inclW l) = t ^ N' • (Y₁'.map (inclW l) * zW f * (t ^ N • F.T)) := by
      have e : x.map (inclW l) = t ^ N' • ((Y₁' * f.map (algebraMap ℤ_[l] (Ainf l)) * Y₂).map (inclW l)) :=
        Matrix.ext fun i j => by simp only [x, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, ht]
      rw [e, Matrix.map_mul, Matrix.map_mul, hzf, hY₂]
    rw [this, ← Matrix.smul_mul, ← Matrix.smul_mul, hinv, hXm]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
    rw [← ht]
    congr 1
    ring
  obtain ⟨Y, hY⟩ := GlobalTheory.T.exists_powerSeries_lift_of_period_pow_smul_integral_matrix l K bk τ hτ d d' (2 * N' + N) Xm x hOE hx
  exact ⟨Y, by rw [hY, hX]⟩

end GlobalTheory.BKLim.EquivKisin

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.semistable_disc_coefficient_recurrence : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ), ∀ (ι : Type) (TB : TopBasis bk.ev bk.J ι) (j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → ∀ (cD : ι → (bk.DA bk.ρ₀ →+ bk.DS bk.ρ₀)), (∀ i a, cD i (bk.iA a) = toDisc l (X : bk.S) bk.ρ₀ (TB.c i a)) → (∀ i x y, cD i (j x * y) = x * cD i y) → (∀ y, HasSum (fun i => j (cD i y) * bk.iA (TB.b i)) y) → (∀ i y, ‖cD i y‖ ≤ ‖y‖) → ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → ∀ (i₁ : ι) (a b : Fin d), HasSum (fun i => Φ ((s.W * (s.W'.map (cD i)).map j) a b) * bk.iS (TB.c i₁ (WittVector.frobenius (TB.b i)))) (bk.iS bk.E ^ (2 * s.N) * (s.W * (s.W'.map (cD i₁)).map j) a b) := by
  first | exact @GlobalTheory.BSP.wseed_coeff_recurrence | exact GlobalTheory.BSP.wseed_coeff_recurrence | (intros; apply GlobalTheory.BSP.wseed_coeff_recurrence <;> assumption)
end
