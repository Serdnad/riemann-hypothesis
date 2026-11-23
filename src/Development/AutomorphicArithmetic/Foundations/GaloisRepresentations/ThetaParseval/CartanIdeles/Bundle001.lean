module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.SpacesExOf
import GroundTheory.GlobalFields.Artin.Places
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
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open scoped nonZeroDivisors Matrix Pointwise
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.Gal.TP.Skew

theorem UpperTheory.Gal.TP.Skew.invFun :
    UpperTheory.Gal.TP.Skew.InvFun := by
  intro F E _ _ _ _ _ _ m hfin hinv
  have : IsGaloisGroup Gal(E/F) (𝓞 F) (𝓞 E) := IsGaloisGroup.of_isFractionRing _ _ _ F E
  have hex : ∀ v : HeightOneSpectrum (𝓞 F), ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v := by
    intro v
    obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
    refine ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext ?_⟩
    rw [HeightOneSpectrum.under_asIdeal]
    exact hl.over.symm
  choose W hW using hex
  have key : ∀ w : HeightOneSpectrum (𝓞 E), m (W (w.under (𝓞 F))) = m w := by
    intro w
    have h1 : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal :=
      ⟨by rw [HeightOneSpectrum.under_asIdeal]⟩
    have h2 : (W (w.under (𝓞 F))).asIdeal.LiesOver (w.under (𝓞 F)).asIdeal :=
      ⟨by conv_lhs => rw [← hW (w.under (𝓞 F)), HeightOneSpectrum.under_asIdeal]; rfl⟩
    obtain ⟨g, hg⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (w.under (𝓞 F)).asIdeal w.asIdeal
      (W (w.under (𝓞 F))).asIdeal Gal(E/F)
    have h3 : W (w.under (𝓞 F)) = g • w := HeightOneSpectrum.ext hg.symm
    rw [h3, hinv]
  have hn : ∀ᶠ v in Filter.cofinite, m (W v) = 0 := by
    rw [Filter.eventually_cofinite] at hfin ⊢
    refine (hfin.image fun w : HeightOneSpectrum (𝓞 E) => w.under (𝓞 F)).subset fun v hv => ?_
    exact ⟨W v, hv, hW v⟩
  obtain ⟨a, ha⟩ := toFractionalIdeal_surjective (K := F) (∏ᶠ v, primeIdealUnit v ^ m (W v))
  refine ⟨a, fun w => ?_⟩
  rw [toFractionalIdeal_eq_iff.1 ha, count_finprod_primeIdealUnit_zpow _ hn, key]
end

section

noncomputable section

open scoped nonZeroDivisors Matrix ComplexOrder
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace UpperTheory.Gal.TP.Skew

private lemma mem_one_iff {E : Type} [Field E] [NumberField E] (y : E) :
    y ∈ (1 : Submodule (𝓞 E) E) ↔ IsIntegral ℤ y := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨o, rfl⟩
    exact o.2
  · intro h
    exact ⟨⟨y, h⟩, rfl⟩

private lemma form_one {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (y x : Fin n → E) : form σ (1 : Matrix (Fin n) (Fin n) E) y x = ∑ i, y i * σ (x i) := by
  simp [form, dotProduct]

theorem stdHerm : StdHerm := by
  intro F E _ _ _ _ _ σ hc B hP n
  have hint : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (σ x) := fun x h =>
    h.map (σ.toRingHom.toIntAlgHom)
  have hL : ∀ y : Fin n → E, y ∈ (stdSpc F E n).L ↔ ∀ i, IsIntegral ℤ (y i) := by
    intro y
    have : (stdSpc F E n).L = Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E) := rfl
    rw [this, Submodule.mem_pi]
    exact forall_congr' fun i => by simp only [Set.mem_univ, true_imp_iff, mem_one_iff]
  have hs : ∀ i, (Pi.single i (1 : E) : Fin n → E) ∈ (stdSpc F E n).L := fun i =>
    (hL _).2 fun j => by
      by_cases e : j = i
      · subst e
        simpa using isIntegral_one
      · simpa [Pi.single_eq_of_ne e] using isIntegral_zero
  have hJ : ∀ w, (stdSpc F E n).J.map (B.emb w).1 = 1 := by
    intro w
    exact Matrix.map_one _ (map_zero _) (map_one _)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    simp only [stdSpc, Matrix.one_apply]
    by_cases h : i = j
    · simp [h]
    · have h' : ¬ j = i := fun e => h e.symm
      simp [h, h']
  · intro w
    rw [hJ]
    refine ⟨rfl, Matrix.fromCols 1 0, ?_⟩
    ext (i | i) (j | j)
    · simp only [Matrix.mul_one]
      simp [Matrix.mul_apply, Matrix.one_apply]
      by_cases e : i = j
      · simp [e]
      · have e' : ¬ j = i := fun h => e h.symm
        simp [e, e']
    all_goals first | exact i.elim0 | exact j.elim0
  · haveI : (stdSpc F E n).L.IsLattice E := by
      refine ⟨Submodule.fg_pi fun _ => ?_, ?_⟩
      · rw [Submodule.one_eq_span]
        exact Submodule.fg_span_singleton 1
      · intro s _ h
        exact (LinearIndependent.iff_fractionRing (𝓞 E) E).mp h
    refine ⟨?_⟩
    apply top_unique
    rw [← (Pi.basisFun E (Fin n)).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [Pi.basisFun_apply]
    exact Submodule.subset_span (hs i)
  · intro y
    rw [hL]
    constructor
    · intro hy x hx
      rw [hL] at hx
      simp only [stdSpc, form_one]
      exact IsIntegral.sum _ fun i _ => (hy i).mul (hint _ (hx i))
    · intro h i
      have := h _ (hs i)
      simpa [stdSpc, form_one, Pi.single_apply] using this
  · intro w
    rw [hJ]
    refine ⟨by simp [stdSpc], by simp [stdSpc], fun x hx => ?_⟩
    simp only [stdSpc, Matrix.one_mulVec]
    exact (Complex.pos_iff.1 (Matrix.dotProduct_self_star_pos_iff.2 hx)).1
  · intro v
    exact absurd v.2 (by simp [hP])

end UpperTheory.Gal.TP.Skew

end
end

section

noncomputable section

open scoped nonZeroDivisors Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace UpperTheory.Gal.TP.Skew

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem lineSkew : LineSkew := by
  intro F E _ _ _ _ _ σ δ 𝔞 hl B hpos hP d
  refine ⟨?skew, ?sig, ?lat, ?dual, ?cartan, ?bas⟩
  case skew =>
    intro i j
    simp only [skewSpc, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases h : j = i
    · subst h; simp [hl.skew]
    · simp [h, Ne.symm h]
  case bas =>
    intro v
    exact absurd v.2 (by simp [hP])
  case lat =>
    have hfg := Submodule.fg_pi (ι := Fin d) (p := fun _ => 𝔞) (fun _ => hl.lat.fg)
    haveI : Submodule.IsLattice E (skewSpc F δ 𝔞 d).L := Submodule.IsLattice.of_fg E hfg
    have ha : ∃ a : E, a ∈ 𝔞 ∧ a ≠ 0 := by
      by_contra h
      have hz : ∀ x ∈ 𝔞, x = 0 := by
        intro x hx
        by_contra hx0
        exact h ⟨x, hx, hx0⟩
      have h1 : (1 : E) ∈ 𝔞 := (hl.dual 1).2 (by
        intro x hx o
        simpa [hz x hx] using (isIntegral_zero : IsIntegral ℤ (0 : ℚ)))
      exact h ⟨1, h1, one_ne_zero⟩
    obtain ⟨a, ha, ha0⟩ := ha
    refine ⟨?_⟩
    apply top_unique
    intro x _
    rw [← Finset.univ_sum_single x]
    apply Submodule.sum_mem
    intro i _
    have hs : Pi.single i a ∈ (skewSpc F δ 𝔞 d).L := by
      change Pi.single i a ∈ Submodule.pi Set.univ (fun _ : Fin d => 𝔞)
      simp only [Submodule.mem_pi, Set.mem_univ, true_implies]
      intro j
      by_cases h : j = i
      · subst j; simpa using ha
      · simp [h]
    have hm := (Submodule.span E ((skewSpc F δ 𝔞 d).L : Set (Fin d → E))).smul_mem (x i / a) (Submodule.subset_span hs)
    simpa [← Pi.single_smul, smul_eq_mul, div_mul_cancel₀ _ ha0] using hm
  case dual =>
    intro y
    have hform : ∀ x : Fin d → E, form σ (skewSpc F δ 𝔞 d).J y x = ∑ i, y i * (δ * σ (x i)) := by
      intro x
      simp [form, skewSpc, Matrix.smul_mulVec, dotProduct, smul_eq_mul]
    have hmem : ∀ z : Fin d → E, z ∈ (skewSpc F δ 𝔞 d).L ↔ ∀ i, z i ∈ 𝔞 := by
      intro z
      show z ∈ Submodule.pi Set.univ (fun _ : Fin d => 𝔞) ↔ _
      simp [Submodule.mem_pi]
    rw [hmem]
    constructor
    · intro hy x hx o
      rw [hmem] at hx

      rw [hform, Finset.mul_sum, map_sum]
      exact IsIntegral.sum _ (fun i _ => (hl.dual (y i)).1 (hy i) (x i) (hx i) o)
    · intro h i
      rw [hl.dual]
      intro x hx o
      have hs : Pi.single i x ∈ (skewSpc F δ 𝔞 d).L := by
        rw [hmem]
        intro j
        by_cases hj : j = i
        · subst hj; simpa using hx
        · simp [hj]
      have := h _ hs o
      rw [hform, Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)] at this
      simpa using this
  case cartan =>
    intro w
    obtain ⟨c, hc, he⟩ := hpos w
    have hM : Complex.I • (skewSpc F δ 𝔞 d).J.map ⇑(B.emb w : E →+* ℂ) = (c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
      ext i j
      by_cases h : i = j
      · subst h; simp [skewSpc, he]
      · simp [skewSpc, h]
    have hθ : (skewSpc F δ 𝔞 d).θ w = 1 := rfl
    rw [hM, hθ]
    refine ⟨by simp, by simp, fun x hx => ?_⟩
    have key : (1 : Matrix (Fin d) (Fin d) ℂ) *ᵥ x ⬝ᵥ ((c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ star x = ((c * ∑ i, Complex.normSq (x i) : ℝ) : ℂ) := by
      simp [Matrix.smul_mulVec, dotProduct, Finset.mul_sum, Complex.mul_conj]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← Complex.mul_conj]
      ring
    rw [key, Complex.ofReal_re]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
    exact mul_pos hc (Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ _, Complex.normSq_pos.2 hi⟩)
  case sig =>
    intro w
    obtain ⟨c, hc, he⟩ := hpos w
    have hM : Complex.I • (skewSpc F δ 𝔞 d).J.map ⇑(B.emb w : E →+* ℂ) = (c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
      ext i j
      by_cases h : i = j
      · subst h; simp [skewSpc, he]
      · simp [skewSpc, h]
    rw [hM]
    refine ⟨by simp, Matrix.of fun (k : Fin d) (p : Fin d ⊕ Fin 0) => Sum.elim (fun i => if k = i then (((Real.sqrt c)⁻¹ : ℝ) : ℂ) else 0) (fun z => z.elim0) p, ?_⟩
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    ext (i | i) (j | j)
    · simp [Matrix.mul_apply, Matrix.one_apply, Function.swap_def, Sum.elim]
      split_ifs with h
      · rw [map_inv₀, Complex.conj_ofReal, ← mul_inv]
        have hs : ((√c : ℝ) : ℂ) * (√c : ℂ) = c := by rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc.le]
        rw [hs, mul_inv_cancel₀ (by exact_mod_cast hc.ne')]
      · simp
    all_goals (first | exact i.elim0 | exact j.elim0)

end UpperTheory.Gal.TP.Skew

end
end

section

open scoped nonZeroDivisors Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.Gal.TP.Skew

theorem UpperTheory.Gal.TP.Skew.conjAut :
    UpperTheory.Gal.TP.Skew.ConjAut := by
  classical
  intro F E _ _ _ _ _ σ hσ
  obtain ⟨_, hE, h2, hconj⟩ := hσ
  haveI hfin : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  have hgal : IsGalois F E := inferInstance
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hsq : ∀ x, σ (σ x) = x := fun x => τ.injective (by rw [hconj, hconj, star_star])
  have hsurj : Function.Surjective σ := fun x => ⟨σ x, hsq x⟩
  let s : Gal(E/F) := AlgEquiv.ofBijective σ ⟨σ.toRingHom.injective, hsurj⟩
  have hs : ∀ x, s x = σ x := fun x => rfl
  have hne : ∃ x, σ x ≠ x := by
    by_contra h
    push_neg at h
    apply IsTotallyComplex.complexEmbedding_not_isReal τ
    show star τ = τ
    ext x
    have := hconj τ x
    rw [h x] at this
    simpa using this.symm
  obtain ⟨x, hx⟩ := hne
  have hs1 : s ≠ 1 := fun h => hx (by rw [← hs, h]; rfl)
  have hcard : Fintype.card Gal(E/F) = 2 := by
    rw [← h2, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  refine ⟨hgal, s, hs, hs1, ?_, ?_, σ x - x, ?_, ?_⟩
  · ext y
    simp [hs, hsq]
  · intro g
    by_contra hg
    push_neg at hg
    have hle : ({1, s, g} : Finset Gal(E/F)).card ≤ Fintype.card Gal(E/F) := Finset.card_le_univ _
    rw [Finset.card_insert_of_notMem (by simp [hs1.symm, hg.1.symm]),
      Finset.card_pair hg.2.symm, hcard] at hle
    omega
  · exact sub_ne_zero.mpr hx
  · rw [map_sub, hsq]
    abel
end

section

open scoped nonZeroDivisors Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.Gal.TP.Skew

private theorem le_one_of_count {E : Type} [Field E] [NumberField E] (J : FractionalIdeal (𝓞 E)⁰ E) (hJ : J ≠ 0)
    (h : ∀ w : HeightOneSpectrum (𝓞 E), 0 ≤ FractionalIdeal.count E w J) : J ≤ 1 := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' E hJ]
  refine finprod_induction (p := fun X : FractionalIdeal (𝓞 E)⁰ E => X ≤ 1) le_rfl ?_ ?_
  · intro a b ha hb
    calc a * b ≤ 1 * b := mul_le_mul_left ha b
      _ ≤ 1 * 1 := mul_le_mul_right hb 1
      _ = 1 := one_mul 1
  · intro v
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (h v)
    rw [hn, zpow_natCast, ← FractionalIdeal.coeIdeal_pow]
    exact FractionalIdeal.coeIdeal_le_one

private theorem mem_iff {E : Type} [Field E] [NumberField E] (I : FractionalIdeal (𝓞 E)⁰ E) (hI : I ≠ 0)
    (y : E) (hy : y ≠ 0) : y ∈ I ↔ ∀ w, FractionalIdeal.count E w I ≤ ordE w y := by
  have hs : FractionalIdeal.spanSingleton (𝓞 E)⁰ y ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy
  constructor
  · intro h w
    exact FractionalIdeal.count_mono E w hs ((FractionalIdeal.spanSingleton_le_iff_mem).mpr h)
  · intro h
    have hJ : FractionalIdeal.spanSingleton (𝓞 E)⁰ y * I⁻¹ ≠ 0 := mul_ne_zero hs (inv_ne_zero hI)
    have hle : FractionalIdeal.spanSingleton (𝓞 E)⁰ y * I⁻¹ ≤ 1 := by
      refine le_one_of_count _ hJ fun w => ?_
      rw [FractionalIdeal.count_mul E w hs (inv_ne_zero hI), FractionalIdeal.count_inv]
      have := h w
      unfold ordE at this
      omega
    have h2 : FractionalIdeal.spanSingleton (𝓞 E)⁰ y ≤ I := by
      calc FractionalIdeal.spanSingleton (𝓞 E)⁰ y
          = (FractionalIdeal.spanSingleton (𝓞 E)⁰ y * I⁻¹) * I := by
            rw [mul_assoc, inv_mul_cancel₀ hI, mul_one]
        _ ≤ 1 * I := mul_le_mul_left hle I
        _ = I := one_mul I
    exact (FractionalIdeal.spanSingleton_le_iff_mem).mp h2

private theorem attained {E : Type} [Field E] [NumberField E] (I : FractionalIdeal (𝓞 E)⁰ E) (hI : I ≠ 0)
    (w : HeightOneSpectrum (𝓞 E)) : ∃ x ∈ I, x ≠ 0 ∧ ordE w x = FractionalIdeal.count E w I := by
  by_contra hcon
  push_neg at hcon
  have hP : ((w.asIdeal : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact w.ne_bot
  have hPI := mul_ne_zero hP hI
  have hle : I ≤ ((w.asIdeal : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) * I := by
    intro x hx
    by_cases hx0 : x = 0
    · rw [hx0]; exact FractionalIdeal.mem_coe.mp (Submodule.zero_mem _)
    refine (mem_iff _ hPI x hx0).mpr fun v => ?_
    rw [FractionalIdeal.count_mul E v hP hI]
    have h1 := (mem_iff I hI x hx0).mp hx v
    by_cases hv : v = w
    · subst hv
      rw [FractionalIdeal.count_self]
      have := hcon x hx hx0
      omega
    · rw [FractionalIdeal.count_maximal_coprime E v (Ne.symm hv)]
      omega
  have h3 := FractionalIdeal.count_mono E w hI hle
  rw [FractionalIdeal.count_mul E w hP hI, FractionalIdeal.count_self] at h3
  omega

private theorem lattice {E : Type} [Field E] [NumberField E] (I : FractionalIdeal (𝓞 E)⁰ E) (hI : I ≠ 0) :
    (I : Submodule (𝓞 E) E).IsLattice E := by
  exact Submodule.IsLattice.of_fg E (FractionalIdeal.fg_of_isUnit I (IsUnit.mk0 I hI))

theorem UpperTheory.Gal.TP.Skew.memOrd :
    UpperTheory.Gal.TP.Skew.MemOrd := by
  intro E _ _ I hI
  exact ⟨mem_iff I hI, attained I hI, lattice I hI⟩
end

section

noncomputable section

open scoped nonZeroDivisors Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GroundTheory.Global GroundTheory.Global.IdeleGroup

open UpperTheory.Gal.TP.Skew

private theorem ordE_mul {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {a b : E}
    (ha : a ≠ 0) (hb : b ≠ 0) : ordE w (a * b) = ordE w a + ordE w b := by
  unfold ordE
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul E w (FractionalIdeal.spanSingleton_ne_zero_iff.mpr ha)
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hb)]

theorem UpperTheory.Gal.TP.Skew.lineEx :
    UpperTheory.Gal.TP.Skew.OrdAut → UpperTheory.Gal.TP.Skew.OrdLine → UpperTheory.Gal.TP.Skew.MemOrd → UpperTheory.Gal.TP.Skew.MemDual → UpperTheory.Gal.TP.Skew.LineEx := by
  intro hA hL hM hD F E _ _ _ _ _ σ hc hu
  obtain ⟨s, δ, I, hs, hss, hδ, hsk, hI, hid⟩ := hL F E σ hc hu
  have hD0 : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
    FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero
  obtain ⟨m1, m2, m3⟩ := hM E I hI
  obtain ⟨d1, -, -⟩ := hM E _ hD0
  have hss' : ∀ w : HeightOneSpectrum (𝓞 E), s • s • w = w := fun w => by
    rw [smul_smul, hss, one_smul]
  have ordS : ∀ (w : HeightOneSpectrum (𝓞 E)) (x : E), ordE w (σ x) = ordE (s • w) x := fun w x => by
    have h := (hA F E s (s • w)).1 x
    rw [hss', hs] at h
    exact h
  have hσ0 : ∀ x : E, x ≠ 0 → σ x ≠ 0 := fun x hx h =>
    hx (by simpa using (map_eq_zero_iff σ σ.toRingHom.injective).mp h)
  have key : ∀ (w : HeightOneSpectrum (𝓞 E)) (y x : E), y ≠ 0 → x ≠ 0 →
      ordE w (y * (δ * σ x)) = ordE w y + ordE w δ + ordE (s • w) x := fun w y x hy hx => by
    rw [ordE_mul w hy (mul_ne_zero hδ (hσ0 x hx)), ordE_mul w hδ (hσ0 x hx), ordS]
    ring
  have hdual : ∀ y : E, (∀ x ∈ I, y * (δ * σ x) ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)) ↔
      ∀ x ∈ (I : Submodule (𝓞 E) E), ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * (y * (δ * σ x)))) :=
    fun y => forall₂_congr fun x _ => hD E _
  refine ⟨δ, (I : Submodule (𝓞 E) E), hδ, hsk, m3, fun y => ?_⟩
  rw [FractionalIdeal.mem_coe, ← hdual y]
  constructor
  · intro hy x hx
    by_cases hy0 : y = 0
    · simpa [hy0] using FractionalIdeal.mem_coe.mp (Submodule.zero_mem _)
    by_cases hx0 : x = 0
    · simpa [hx0] using FractionalIdeal.mem_coe.mp (Submodule.zero_mem _)
    refine (d1 _ (mul_ne_zero hy0 (mul_ne_zero hδ (hσ0 x hx0)))).mpr fun w => ?_
    have h1 := (m1 y hy0).mp hy w
    have h2 := (m1 x hx0).mp hx (s • w)
    have h3 := hid w
    rw [key w y x hy0 hx0]
    omega
  · intro h
    by_cases hy0 : y = 0
    · simpa [hy0] using FractionalIdeal.mem_coe.mp (Submodule.zero_mem _)
    refine (m1 y hy0).mpr fun w => ?_
    obtain ⟨x, hx, hx0, hxo⟩ := m2 (s • w)
    have h1 := (d1 _ (mul_ne_zero hy0 (mul_ne_zero hδ (hσ0 x hx0)))).mp (h x hx) w
    have h3 := hid w
    rw [key w y x hy0 hx0] at h1
    omega

end
end
