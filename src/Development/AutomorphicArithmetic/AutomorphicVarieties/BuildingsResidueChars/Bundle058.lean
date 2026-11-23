module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle053
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle716
import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle043
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle008
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
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Polynomial

private theorem slopeHi_spec {L : Type} [Field L] {d : ℕ} (G : Matrix (Fin d) (Fin d) L) (hG : IsUnit G.det) {a : L}
    (ha : a ∈ spectrum L G) : a ≠ 0 ∧ a⁻¹ ∈ spectrum L (G⁻¹).transpose := by
  rw [spectrum.mem_iff] at ha
  have h0 : a ≠ 0 := by
    rintro rfl
    apply ha
    rw [map_zero, zero_sub]
    exact ((Matrix.isUnit_iff_isUnit_det _).2 hG).neg
  refine ⟨h0, spectrum.mem_iff.2 fun hu => ha ?_⟩
  have e : (algebraMap L (Matrix (Fin d) (Fin d) L) a⁻¹ - (G⁻¹).transpose).transpose * ((-a) • G) =
      algebraMap L (Matrix (Fin d) (Fin d) L) a - G := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Matrix.transpose_sub,
      Matrix.transpose_smul, Matrix.transpose_one, Matrix.transpose_transpose, Matrix.mul_smul, Matrix.sub_mul,
      Matrix.smul_mul, Matrix.one_mul, Matrix.nonsing_inv_mul _ hG, smul_sub, smul_smul, neg_mul,
      mul_inv_cancel₀ h0, neg_smul, neg_smul, one_smul]
    abel
  rw [← e]
  refine ((Matrix.isUnit_transpose _).2 hu).mul ?_
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_smul]
  exact ((IsUnit.mk0 _ (neg_ne_zero.2 h0)).pow _).mul hG

private theorem slopeHi_inv {R S : Type} [Field R] [CommRing S] [Nontrivial S] (j : R →+* S) (ψ : S →+* S)
    {d : ℕ} (M M' : Matrix (Fin d) (Fin d) S) (F : Matrix (Fin d) (Fin d) R) (hMM : M * M' = 1)
    (h : M.map ψ = M * F.map j) :
    IsUnit F.det ∧ M'.transpose.map ψ = M'.transpose * (F⁻¹).transpose.map j := by
  have hMM' : M' * M = 1 := mul_eq_one_comm.1 hMM
  have e1 : M'.map ψ * M.map ψ = 1 := by
    rw [← Matrix.map_mul, hMM', Matrix.map_one _ (map_zero _) (map_one _)]
  have hF : IsUnit F.det := by
    refine IsUnit.mk0 _ fun h0 => ?_
    have := congrArg Matrix.det e1
    have h1 : (F.map j).det = 0 := by
      have h2 := RingHom.map_det j F
      rw [h0, map_zero] at h2
      exact h2.symm
    rw [h, Matrix.det_mul, Matrix.det_mul, h1, mul_zero, mul_zero, Matrix.det_one] at this
    exact zero_ne_one this
  refine ⟨hF, ?_⟩
  rw [Matrix.transpose_map, Matrix.transpose_map, ← Matrix.transpose_mul]
  congr 1
  have e2 : F.map j * (F⁻¹).map j = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hF, Matrix.map_one _ (map_zero _) (map_one _)]
  calc M'.map ψ = M'.map ψ * (M * (F.map j * (F⁻¹).map j) * M') := by
        rw [e2, Matrix.mul_one, hMM, Matrix.mul_one]
    _ = _ := by
        rw [← Matrix.mul_assoc M, ← h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, Matrix.one_mul]

theorem UpperTheory.filtration_inverse_frobenius_matrix :
    ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (f : ℕ), 0 < f → (∀ x : ↥(K0 K), (((PP l).PD K).σ)^[f] x = x) → ∀ {d : ℕ} (M M' : Matrix (Fin d) (Fin d) (Bcr l)) (A F : Matrix (Fin d) (Fin d) ↥(K0 K)), M * M' = 1 → IsUnit A.det → M.map (PP l).φB = M * A.map (algebraMap ↥(K0 K) (Bcr l)) → M.map (((PP l).φB)^[f]) = M * F.map (algebraMap ↥(K0 K) (Bcr l)) → ∀ b : ℤ, (∀ i j, (PP l).ιB (M' i j) ∈ ((PP l).PD (botExt l)).Fil (-b)) → ∀ β ∈ spectrum (Om l) (F.map (algebraMap ↥(K0 K) (Om l))), ‖((l : Om l) ^ f) ^ b * β⁻¹‖ ≤ 1 := by
  intro l _ K f hf hσ d M M' A F hMM _ hA hF b hb β hβ
  haveI : Nontrivial (Bcr l) := ⟨⟨1, 0, fun h => ((PP l).PD K).not_mem_filtration_two (by
    rw [← mul_one ((PP l).PD K).t, h, mul_zero, map_zero]; exact Submodule.zero_mem _)⟩⟩
  have hc : ((PP l).φB)^[f] = ⇑((PP l).φB ^ f) := (AlgHom.coe_pow _ _).symm
  obtain ⟨hA1, hA2⟩ := slopeHi_inv (algebraMap ↥(K0 K) (Bcr l)) ((PP l).φB : Bcr l →+* Bcr l) M M' A hMM hA
  obtain ⟨hF1, hF2⟩ := slopeHi_inv (algebraMap ↥(K0 K) (Bcr l)) (((PP l).φB ^ f : Bcr l →ₐ[ℚ_[l]] Bcr l) : Bcr l →+* Bcr l)
    M M' F hMM (by rw [hc] at hF; exact hF)
  have hu : IsUnit (F.map (algebraMap ↥(K0 K) (Om l))).det := by
    have := hF1.map (algebraMap ↥(K0 K) (Om l))
    rw [RingHom.map_det] at this
    exact this
  obtain ⟨-, ha'⟩ := slopeHi_spec _ hu hβ
  have e : (F.map (algebraMap ↥(K0 K) (Om l)))⁻¹ = (F⁻¹).map (algebraMap ↥(K0 K) (Om l)) := by
    apply Matrix.inv_eq_right_inv
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hF1, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [e, ← Matrix.transpose_map] at ha'
  have h := UpperTheory.filtration_entries_of_frobenius_matrix K f hf hσ M'.transpose M.transpose (A⁻¹).transpose (F⁻¹).transpose
    (by rw [← Matrix.transpose_mul, hMM, Matrix.transpose_one])
    (by rw [Matrix.det_transpose]; exact Matrix.isUnit_nonsing_inv_det _ hA1)
    hA2 (by rw [hc]; exact hF2) (-b) (fun i j => hb j i) β⁻¹ ha'
  rwa [neg_neg] at h
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
open scoped Pointwise

private theorem td_move {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A B : ValuationSubring Ω}
    (g : G F Ω) (hg : ∀ x, g x ∈ A ↔ x ∈ B) {w : HeightOneSpectrum (𝓞 F)} (hw : IsPlaceOver A w) :
    IsPlaceOver B w := by
  intro x
  rw [← hw x, valuation_lt_one_iff', valuation_lt_one_iff']
  have hy : g (algebraMap F Ω x) = algebraMap F Ω x := g.commutes _
  have hyi : g (algebraMap F Ω x)⁻¹ = (algebraMap F Ω x)⁻¹ := by rw [map_inv₀, hy]
  rw [← hg (algebraMap F Ω x), hy, ← hg (algebraMap F Ω x)⁻¹, hyi]

private theorem td_count (l : ℕ) [hl : Fact l.Prime] (F : Type) [Field F] [NumberField F] [IsGalois ℚ F] {V : Type}
    (pl : V → HeightOneSpectrum (𝓞 F)) (hi : Function.Injective pl) (hm : ∀ v, ((l : ℕ) : 𝓞 F) ∈ (pl v).asIdeal)
    (hs : ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∃ v, pl v = w) (v : V) :
    locDeg (pl v) * Nat.card V = Module.finrank ℚ F := by
  classical
  let p : Ideal ℤ := Ideal.span {((l : ℕ) : ℤ)}
  have hpp : p.IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hl.out.ne_zero)).2 (Nat.prime_iff_prime_int.1 hl.out)
  haveI hpmax : p.IsMaximal :=
    hpp.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hl.out.ne_zero)
  have hlo : ∀ P : Ideal (𝓞 F), P.IsPrime → ((l : ℕ) : 𝓞 F) ∈ P → P.LiesOver p := by
    intro P hP hlP
    constructor
    apply hpmax.eq_of_le (Ideal.comap_ne_top _ hP.ne_top)
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show algebraMap ℤ (𝓞 F) ((l : ℕ) : ℤ) ∈ P
    rwa [map_natCast]
  let f : V → p.primesOver (𝓞 F) := fun u =>
    ⟨(pl u).asIdeal, (pl u).isPrime, hlo _ (pl u).isPrime (hm u)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      apply hi
      exact HeightOneSpectrum.ext (congrArg Subtype.val h)
    · rintro ⟨P, hP, hPl⟩
      have hlP : ((l : ℕ) : 𝓞 F) ∈ P := by
        have hm' : ((l : ℕ) : ℤ) ∈ p := Ideal.subset_span (Set.mem_singleton _)
        rw [hPl.over] at hm'
        have hm'' := Ideal.mem_comap.1 hm'
        rwa [map_natCast] at hm''
      have hne : P ≠ ⊥ := by
        intro h
        rw [h, Ideal.mem_bot] at hlP
        exact hl.out.ne_zero (by exact_mod_cast hlP)
      obtain ⟨u, hu⟩ := hs ⟨P, hP, hne⟩ hlP
      exact ⟨u, Subtype.ext (congrArg HeightOneSpectrum.asIdeal hu)⟩
  have key : (p.primesOver (𝓞 F)).ncard = Nat.card V := by
    rw [← Nat.card_coe_set_eq]
    exact (Nat.card_eq_of_bijective f hf).symm
  have hG := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p (𝓞 F) (F ≃ₐ[ℚ] F)
  haveI := hlo _ (pl v).isPrime (hm v)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p (pl v).asIdeal (F ≃ₐ[ℚ] F),
    Ideal.inertiaDegIn_eq_inertiaDeg p (pl v).asIdeal (F ≃ₐ[ℚ] F), key,
    IsGalois.card_aut_eq_finrank] at hG
  rw [← hG, mul_comm]
  rfl

theorem UpperTheory.exists_place_over_l_locDeg_mul_card_eq :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (v : T.ι), ∃ w : HeightOneSpectrum (𝓞 T.F), IsPlaceOver (T.pl v) w ∧ ((l : ℕ) : 𝓞 T.F) ∈ w.asIdeal ∧ locDeg w * Nat.card T.ι = T.d := by
  intro Ω _ _ _ l _ c D T v
  haveI := T.nF
  haveI := T.abF
  haveI hac : IsAlgClosure T.F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  have hlt : ∀ (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 T.F)), IsPlaceOver A w →
      (A.valuation (l : Ω) < 1 ↔ ((l : ℕ) : 𝓞 T.F) ∈ w.asIdeal) := by
    intro A w hA
    rw [← hA]
    simp
  choose P hPS hP using fun u => GlobalTheory.DecLocal.exists_place_below (p := l) (F := T.F) (T.pl u) (T.ovl u)
  have hPl : ∀ u, ((l : ℕ) : 𝓞 T.F) ∈ (P u).asIdeal := fun u => hPS u
  refine ⟨P v, hP v, hPl v, td_count l T.F P ?_ hPl ?_ v⟩
  · intro u u' h
    obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver (hP u) (by rw [h]; exact hP u')
    obtain ⟨v0, -, huniq⟩ := T.cover (T.pl u) (T.ovl u)
    have e1 := huniq u ⟨1, fun x => by simp⟩
    have e2 := huniq u' ⟨σ⁻¹, fun x => by
      rw [← hσ, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]⟩
    exact e1.trans e2.symm
  · intro w hw
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    obtain ⟨u, ⟨g, hg⟩, -⟩ := T.cover A ((hlt A w hA).2 hw)
    exact ⟨u, eq_of_isPlaceOver (hP u) (td_move g hg hA)⟩
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem l_mem {l : ℕ} [Fact l.Prime] (c : Coef l) : (l : c.O) ∈ maximalIdeal c.O := by
  obtain ⟨-, -, hloc, -⟩ := dvrFacts l c.O
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← map_natCast (algebraMap ℤ_[l] c.O)]
  intro hu
  have h0 := IsUnit.of_map (algebraMap ℤ_[l] c.O) _ hu
  rw [PadicInt.isUnit_iff, PadicInt.norm_p, inv_eq_one] at h0
  have h1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  linarith

private theorem inc_mem {l : ℕ} [Fact l.Prime] {c c' : Coef l} (h : c.O ≤ c'.O) {x : c.O}
    (hx : x ∈ maximalIdeal c.O) : inc h x ∈ maximalIdeal c'.O := by
  obtain ⟨hinj, -⟩ := dvrFacts l c.O
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  have hx' : π ∣ x := by
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hx
    exact hx
  have hl0 : (l : c.O) ≠ 0 := by
    rw [← map_natCast (algebraMap ℤ_[l] c.O)]
    exact (map_ne_zero_iff _ hinj).2 (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hl0 hπ
  obtain ⟨w, hw⟩ : (l : c.O) ∣ x ^ n := hn.dvd_iff_dvd_left.2 (pow_dvd_pow_of_dvd hx' n)
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have hu' := hu.pow n
  rw [← map_pow, hw, map_mul, map_natCast] at hu'
  exact (IsLocalRing.mem_maximalIdeal _).1 (l_mem c') (isUnit_of_mul_isUnit_left hu')

theorem UpperTheory.deformationSpace_local_characters_continuous :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Ok → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (X : Space (T.fr ∅) (inc h)) (R : Type) [CommRing R] [IsLocalRing R] (f : X.B →+* R), (∀ b ∈ maximalIdeal X.B, f b ∈ maximalIdeal R) → (∀ a ∈ maximalIdeal c'.O, f (algebraMap c'.O X.B a) = 0) → (l : R) = 0 ∧ ∃ κ : ∀ v : T.ι, Fin 4 → Dec (F := T.F) (T.pl v) →* Rˣ, ∀ v i, (∀ s, ((κ v i s : Rˣ) : R) = f (X.ψ v i s)) ∧ AdicCont (maximalIdeal R) (fun s => ((κ v i s : Rˣ) : R)) ∧ ∀ s : Dec (F := T.F) (T.pl v), (s : G T.F Ω) ∈ Ine (F := T.F) (T.pl v) → ((κ v i s : Rˣ) : R) - 1 ∈ maximalIdeal R ∧ κ v i s * κ v i.rev s = 1 := by
  intro Ω _ _ _ l _ c D T hT c' h X R _ _ f hf hf0
  have hl' : f (algebraMap c'.O X.B (l : c'.O)) = 0 := hf0 _ (l_mem c')
  rw [map_natCast, map_natCast] at hl'
  have hP := UpperTheory.pseudoDeformation_diag_characters_mul_rev_eq_similitude (T.fr ∅) ((algebraMap c'.O X.A).comp (inc h)) X.P X.pair
  have one : ∀ v i, X.ψ v i 1 = 1 := by
    intro v i
    apply X.inj
    rw [X.ψ_map v i 1 (Subgroup.one_mem _), map_one]
    exact (hP v i).1
  have mul : ∀ v i, ∀ s ∈ (T.fr ∅).Gv v, ∀ t ∈ (T.fr ∅).Gv v,
      X.ψ v i (s * t) = X.ψ v i s * X.ψ v i t := by
    intro v i s hs t ht
    apply X.inj
    rw [map_mul, X.ψ_map v i _ (Subgroup.mul_mem _ hs ht), X.ψ_map v i s hs, X.ψ_map v i t ht]
    exact (hP v i).2.1 s hs t ht
  have nu : ∀ v i, ∀ s ∈ (T.fr ∅).Gv v,
      X.ψ v i s * X.ψ v i.rev s = algebraMap c'.O X.B (inc h ↑((T.fr ∅).ν s)) := by
    intro v i s hs
    apply X.inj
    rw [map_mul, X.ψ_map v i s hs, X.ψ_map v i.rev s hs, (hP v i).2.2 s hs, RingHom.comp_apply,
      IsScalarTower.algebraMap_apply c'.O X.B X.A]
  have hunit : ∀ (v : T.ι) (i : Fin 4) (s : Dec (F := T.F) (T.pl v)), IsUnit (f (X.ψ v i s)) := by
    intro v i s
    have hu : IsUnit (X.ψ v i s * X.ψ v i.rev s) := by
      rw [nu v i s s.2]
      exact ((Units.isUnit _).map (inc h)).map (algebraMap c'.O X.B)
    exact (isUnit_of_mul_isUnit_left hu).map f
  have key : ∀ u : (c.O)ˣ, residue c.O ↑u = 1 → f (algebraMap c'.O X.B (inc h ↑u)) = 1 := by
    intro u hu
    have h1 : (↑u : c.O) - 1 ∈ maximalIdeal c.O :=
      (residue_eq_zero_iff _).1 (by rw [map_sub, hu, map_one, sub_self])
    have h2 := hf0 _ (inc_mem h h1)
    rwa [map_sub, map_one, map_sub, map_one, map_sub, map_one, sub_eq_zero] at h2
  refine ⟨hl', fun v i => IsUnit.liftRight
    { toFun := fun s => f (X.ψ v i s)
      map_one' := by
        simp only [OneMemClass.coe_one]
        exact (congrArg f (one v i)).trans (map_one f)
      map_mul' := by
        intro s t
        simp only [Subgroup.coe_mul]
        rw [mul v i s s.2 t t.2, map_mul] } (fun s => hunit v i s), ?_⟩
  intro v i
  refine ⟨fun s => rfl, ?_, ?_⟩
  · intro N
    have hle : maximalIdeal X.B ^ N ≤ (maximalIdeal R ^ N).comap f := by
      rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
      exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 (fun b hb => Ideal.mem_comap.2 (hf b hb))) N
    exact (X.ψ_cont v i N).comp (Ideal.quotientMap (maximalIdeal R ^ N) f hle)
  · intro s hs
    have hr := hT.ineL (T.pl v) (T.ovl v) s hs
    have hps : ∀ j, residue c.O ↑(D.ps j (resQ T.F s)) = 1 := fun j => by
      have e := congrArg (fun M => M j j) hr
      simpa [Raw.rbar, Raw.r0, mapRep_apply, diagRep] using e
    refine ⟨?_, ?_⟩
    · show f (X.ψ v i s) - 1 ∈ maximalIdeal R
      have hres : residue c'.O (inc h ↑(D.ps (lab T.pr i) (resQ T.F s))) = 1 := by
        have h1 : (↑(D.ps (lab T.pr i) (resQ T.F s)) : c.O) - 1 ∈ maximalIdeal c.O :=
          (residue_eq_zero_iff _).1 (by rw [map_sub, hps, map_one, sub_self])
        have h2 := inc_mem h h1
        rw [map_sub, map_one, ← residue_eq_zero_iff, map_sub, map_one, sub_eq_zero] at h2
        exact h2
      have hB : X.ψ v i s - 1 ∈ maximalIdeal X.B := by
        rw [← res_eq_zero_iff c'.O X.B, map_sub, map_one, X.ψ_red v i s s.2]
        show residue c'.O (inc h ↑(D.ps (lab T.pr i) (resQ T.F s))) - 1 = 0
        rw [hres, sub_self]
      have := hf _ hB
      rwa [map_sub, map_one] at this
    · apply Units.ext
      show f (X.ψ v i s) * f (X.ψ v i.rev s) = 1
      rw [← map_mul, nu v i s s.2]
      exact key _ (hps 0)
end
