module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.WeilBound.ThetaLifts.TowerModels.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace PositivityTheory.ThKG.Tow

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem det_ne_zero_of_hasSig {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} {r s : ℕ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  subst hrs
  intro hM
  have key := congrArg Matrix.det hA
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one,
    Fintype.card_fin] at key
  let e : Fin r ⊕ Fin s ≃ Fin (r + s) := finSumFinEquiv
  have hsub : (Aᵀ * M * A.map star).submatrix e.symm e.symm =
      (A.submatrix id e.symm)ᵀ * M * (A.submatrix id e.symm).map star := by
    ext i j
    simp [Matrix.mul_apply, Matrix.submatrix, Matrix.transpose_apply]
  have h2 := congrArg Matrix.det hsub
  rw [Matrix.det_submatrix_equiv_self, key, Matrix.det_mul, Matrix.det_mul, hM, mul_zero, zero_mul] at h2
  exact pow_ne_zero _ (by norm_num) h2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E}

theorem det_herm {n : ℕ} {X : Spc F E n} {r s : ℕ} (hX : X.IsHerm σ B r s) : X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h := det_ne_zero_of_hasSig (hX.sig w)
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
  exact fun h0 => h (by rw [h0, map_zero])

end PositivityTheory.ThKG.Tow

end
end

section

noncomputable section

namespace PositivityTheory.ThKG.Tow.Pln

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_compl (n n₁ : ℕ) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) (hn : n = n₁ + 2)
    (hxx : form σ J x x = 0) (hyy : form σ J y y = 0) (hxy : form σ J x y = 1) (hyx : form σ J y x ≠ 0) :
    ∃ (ι : Matrix (Fin n) (Fin n₁) E) (P : Matrix (Fin n₁) (Fin n) E), P * ι = 1 ∧
      (∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) ∧
      ∀ z, form σ J z x = 0 → form σ J z y = 0 → ∃ u, z = ι *ᵥ u := by
  let f : (Fin n → E) →ₗ[E] E × E := (formL (σ := σ) J x).prod (formL (σ := σ) J y)
  have hf : LinearMap.range f = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨a, b⟩
    refine ⟨(a / form σ J y x) • y + b • x, Prod.ext ?_ ?_⟩
    · change form σ J _ x = a
      rw [form_add_left, form_smul_left, form_smul_left, hxx, div_mul_cancel₀ _ hyx, mul_zero, add_zero]
    · change form σ J _ y = b
      rw [form_add_left, form_smul_left, form_smul_left, hyy, hxy, mul_zero, mul_one, zero_add]
  have hk : Module.finrank E (LinearMap.ker f) = n₁ := by
    have := f.finrank_range_add_finrank_ker
    rw [hf, finrank_top] at this
    simp only [Module.finrank_prod, Module.finrank_self, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at this
    omega
  let b := Module.finBasisOfFinrankEq E (LinearMap.ker f) hk
  let g : (Fin n₁ → E) →ₗ[E] (Fin n → E) := (LinearMap.ker f).subtype ∘ₗ b.equivFun.symm.toLinearMap
  obtain ⟨p, hp⟩ := g.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2
    ((LinearMap.ker f).injective_subtype.comp b.equivFun.symm.injective))
  refine ⟨LinearMap.toMatrix' g, LinearMap.toMatrix' p, by rw [← LinearMap.toMatrix'_comp, hp, LinearMap.toMatrix'_id],
    fun u => ?_, fun z h1 h2 => ?_⟩
  · rw [LinearMap.toMatrix'_mulVec]
    have := (b.equivFun.symm u).2
    exact Prod.mk_eq_zero.1 this
  · refine ⟨b.equivFun ⟨z, Prod.mk_eq_zero.2 ⟨h1, h2⟩⟩, ?_⟩
    rw [LinearMap.toMatrix'_mulVec]
    change z = (b.equivFun.symm (b.equivFun _) : LinearMap.ker f)
    rw [LinearEquiv.symm_apply_apply]

theorem fg_comap {V W : Type} [AddCommGroup V] [Module (𝓞 E) V] [AddCommGroup W] [Module (𝓞 E) W]
    (f : V →ₗ[𝓞 E] W) (hf : Function.Injective f) (L : Submodule (𝓞 E) W) (hL : L.FG) : (L.comap f).FG :=
  Submodule.fg_of_fg_map_injective f hf (hL.of_le (Submodule.map_comap_le f L))

theorem isLattice_comap (n n₁ : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (ι : Matrix (Fin n) (Fin n₁) E)
    (P : Matrix (Fin n₁) (Fin n) E) (hP : P * ι = 1) (hL : L.IsFullLattice E) :
    (L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E))).IsLattice E :=
  Submodule.IsLattice.of_fg E (fg_comap _ (fun u u' e => by
    have := congrArg (P *ᵥ ·) (show ι *ᵥ u = ι *ᵥ u' from e)
    simpa [Matrix.mulVec_mulVec, hP] using this) L hL.fg)

theorem exists_ideal (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsLattice E) (x : Fin n → E) (hx : x ≠ 0) :
    ∃ 𝔟 : FractionalIdeal (𝓞 E)⁰ E, ∀ s : E, s ∈ 𝔟 ↔ s • x ∈ L :=
  ⟨⟨L.comap ((LinearMap.toSpanSingleton E _ x).restrictScalars (𝓞 E)), FractionalIdeal.isFractional_of_fg
    (fg_comap _ (smul_left_injective E hx) L hL.fg)⟩, fun _ => Iff.rfl⟩

end PositivityTheory.ThKG.Tow.Pln

end
end

section

noncomputable section

namespace PositivityTheory.ThKG.Tow.Pln

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_partner (h : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {ε : E} (hε : ε = 1 ∨ ε = -1)
    (hJ : ∀ i j, σ (J j i) = ε * J i j) (D : Submodule (𝓞 E) E) (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hd : ∀ y, y ∈ L ↔ ∀ x ∈ L, form σ J y x ∈ D) (θ : 𝓞 E) (hθ : (θ : E) + σ θ = 1) (x : Fin n → E)
    (hxx : form σ J x x = 0) (z₀ : Fin n → E) (hz₀ : z₀ ∈ L) (hz₀x : form σ J z₀ x ≠ 0) :
    ∃ y, form σ J y y = 0 ∧ form σ J x y = 1 ∧ ∀ z ∈ L, form σ J z x • y ∈ L ∧ form σ J z y • x ∈ L := by
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> simp
  have hσε : σ ε = ε := by rcases hε with rfl | rfl <;> simp
  have hεD : ∀ a ∈ D, ε * a ∈ D := fun a ha => by
    rcases hε with rfl | rfl
    · simpa using ha
    · simpa using ha
  have hεL : ∀ a ∈ L, ε • a ∈ L := fun a ha => by
    rcases hε with rfl | rfl
    · simpa using ha
    · simpa using ha
  have sw : ∀ a b, form σ J b a = ε * σ (form σ J a b) := fun a b => by
    rw [form_swap h hJ, ← mul_assoc, hεε, one_mul]
  let C₀ : Submodule (𝓞 E) E := L.map ((formL (σ := σ) J x).restrictScalars (𝓞 E))
  let C : FractionalIdeal (𝓞 E)⁰ E := ⟨C₀, FractionalIdeal.isFractional_of_fg (hfg.map _)⟩
  have hC : ∀ z ∈ L, form σ J z x ∈ C := fun z hz => ⟨z, hz, rfl⟩
  have hC0 : C ≠ 0 := fun e => hz₀x (by simpa [e] using hC z₀ hz₀)
  have hinv : C * C⁻¹ = 1 := mul_inv_cancel₀ hC0
  have key : ∀ t ∈ C * C⁻¹, ∃ y, form σ J y x = t ∧ ∀ c ∈ C, c • y ∈ L := fun t ht => by
    refine FractionalIdeal.mul_induction_on ht (fun a ha b hb => ?_) ?_
    · obtain ⟨z, hz, rfl⟩ := ha
      refine ⟨b • z, by rw [form_smul_left, mul_comm]; rfl, fun c hc => ?_⟩
      have := FractionalIdeal.mul_mem_mul hc hb
      rw [hinv, FractionalIdeal.mem_one_iff] at this
      obtain ⟨o, ho⟩ := this
      rw [smul_smul, ← ho, algebraMap_smul]
      exact L.smul_mem o hz
    · rintro _ _ ⟨y, rfl, hy⟩ ⟨y', rfl, hy'⟩
      exact ⟨y + y', form_add_left _ _ _ _, fun c hc => by rw [smul_add]; exact L.add_mem (hy c hc) (hy' c hc)⟩
  obtain ⟨y₁, hy₁, hy₁L⟩ := key 1 (by rw [hinv]; exact FractionalIdeal.one_mem_one _)
  obtain ⟨y₀, hy₀x, hy₀L⟩ : ∃ y₀, form σ J y₀ x = ε ∧ ∀ c ∈ C, c • y₀ ∈ L :=
    ⟨ε • y₁, by rw [form_smul_left, hy₁, mul_one], fun c hc => by rw [smul_comm]; exact hεL _ (hy₁L c hc)⟩
  have hxy₀ : form σ J x y₀ = 1 := by rw [sw, hy₀x, hσε, hεε]
  have crit : ∀ y, (∀ c ∈ C, c • y ∈ L) → ∀ z ∈ L, form σ J z y • x ∈ L := fun y hy z hz => by
    refine (hd _).2 fun z' hz' => ?_
    have := hεD _ ((hd z).1 hz _ (hy _ (hC z' hz')))
    rw [form_smul_right] at this
    rw [form_smul_left, sw z' x]
    convert this using 1
    ring
  set q := form σ J y₀ y₀ with hq
  have hqq : ε * σ q = q := (sw y₀ y₀).symm
  have hyL : ∀ c ∈ C, c • (y₀ - ((θ : E) * q) • x) ∈ L := fun c hc => by
    have := L.smul_mem θ (crit y₀ hy₀L _ (hy₀L c hc))
    rw [form_smul_left, ← algebraMap_smul E θ, smul_smul] at this
    rw [smul_sub, smul_smul]
    refine L.sub_mem (hy₀L c hc) ?_
    convert this using 2
    change _ = (θ : E) * _
    ring
  refine ⟨y₀ - ((θ : E) * q) • x, ?_, ?_, fun z hz => ⟨hyL _ (hC z hz), crit _ hyL z hz⟩⟩
  · rw [form_sub_left, form_sub_right, form_sub_right, form_smul_left, form_smul_left, form_smul_right, form_smul_right,
      hxx, hxy₀, hy₀x, ← hq, map_mul]
    linear_combination -q * hθ - σ θ * hqq
  · rw [form_sub_right, form_smul_right, hxx, hxy₀]; ring

theorem exists_max_val {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (L : Submodule (𝓞 E) V) (hfg : L.FG) (f : V →ₗ[E] E) (hf : ∃ z ∈ L, f z ≠ 0)
    (S : Finset (HeightOneSpectrum (𝓞 E))) :
    ∃ z₀ ∈ L, f z₀ ≠ 0 ∧ ∀ w ∈ S, ∀ z ∈ L, w.valuation E (f z) ≤ w.valuation E (f z₀) := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨w₀, hw₀⟩
  · obtain ⟨z, hz, hz0⟩ := hf
    exact ⟨z, hz, hz0, by simp⟩
  have h1 : ∀ w : HeightOneSpectrum (𝓞 E), ∃ c ∈ L, ∀ z ∈ L, w.valuation E (f z) ≤ w.valuation E (f c) := fun w => by
    obtain ⟨G, rfl⟩ := hfg
    obtain ⟨c, hc, hmax⟩ := (insert 0 G).exists_max_image (fun z => w.valuation E (f z)) (by simp)
    refine ⟨c, ?_, fun z hz => ?_⟩
    · rcases Finset.mem_insert.1 hc with rfl | hc
      · exact zero_mem _
      · exact Submodule.subset_span hc
    · induction hz using Submodule.span_induction with
      | mem x hx => exact hmax x (Finset.mem_insert_of_mem hx)
      | zero => simp
      | add x y _ _ hx hy => rw [map_add (f := _)]; exact (Valuation.map_add _ _ _).trans (max_le hx hy)
      | smul a x _ hx =>
        rw [← algebraMap_smul E a, map_smul, smul_eq_mul, map_mul]
        exact (mul_le_of_le_one_left' (w.valuation_le_one a)).trans hx
  choose c hcL hc using h1
  have hc0 : ∀ w : HeightOneSpectrum (𝓞 E), 0 < w.valuation E (f (c w)) := fun w => by
    obtain ⟨z, hz, hz0⟩ := hf
    exact lt_of_lt_of_le (zero_lt_iff.2 ((map_ne_zero _).2 hz0)) (hc w z hz)
  have h2 : ∀ w w' : HeightOneSpectrum (𝓞 E), ∃ p : 𝓞 E, p ∉ w.asIdeal ∧ (w' ≠ w → p ∈ w'.asIdeal) := fun w w' => by
    by_cases e : w' = w
    · exact ⟨1, (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top, fun h => absurd e h⟩
    · have : ¬ w'.asIdeal ≤ w.asIdeal := fun hle =>
        e (HeightOneSpectrum.ext (w'.isMaximal.eq_of_le w.isPrime.ne_top hle))
      obtain ⟨p, hp, hp'⟩ := Set.not_subset.1 this
      exact ⟨p, hp', fun _ => hp⟩
  choose p hp hp' using h2
  let e : HeightOneSpectrum (𝓞 E) → 𝓞 E := fun w => ∏ w' ∈ S, p w w'
  have he : ∀ w : HeightOneSpectrum (𝓞 E), w.valuation E (algebraMap _ E (e w)) = 1 := fun w => by
    simp only [e, map_prod]
    exact Finset.prod_eq_one fun w' _ => (w.valuation_eq_one_iff_notMem (K := E)).2 (hp w w')
  have he' : ∀ w, ∀ w' ∈ S, w' ≠ w → w'.valuation E (algebraMap _ E (e w)) < 1 := fun w w' hw' hne =>
    (w'.valuation_lt_one_iff_mem (K := E) _).2 (Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ hw') (hp' w w' hne))
  have hval : ∀ w ∈ S, w.valuation E (f (∑ w' ∈ S, e w' • c w')) = w.valuation E (f (c w)) := fun w hw => by
    have t : ∀ w', f (e w' • c w') = algebraMap _ E (e w') * f (c w') := fun w' => by
      rw [← algebraMap_smul E (e w'), map_smul, smul_eq_mul]

    rw [← Finset.add_sum_erase S _ hw, map_add (f := _), map_sum]
    have a1 : w.valuation E (f (e w • c w)) = w.valuation E (f (c w)) := by rw [t, map_mul, he, one_mul]
    rw [Valuation.map_add_eq_of_lt_left, a1]
    rw [a1]
    refine Valuation.map_sum_lt _ (hc0 w).ne' fun w' hw' => ?_
    rw [t, map_mul]
    calc _ ≤ w.valuation E (algebraMap _ E (e w')) * w.valuation E (f (c w)) := by
          gcongr; exact hc w _ (hcL w')
      _ < _ := mul_lt_of_lt_one_left (hc0 w) (he' w' w hw (Finset.ne_of_mem_erase hw').symm)
  refine ⟨∑ w' ∈ S, e w' • c w', L.sum_mem fun w _ => L.smul_mem _ (hcL w), fun h0 => ?_, fun w hw z hz => ?_⟩
  · have := hval w₀ hw₀
    rw [h0, map_zero] at this
    exact (hc0 w₀).ne this
  · rw [hval w hw]; exact hc w z hz

theorem exists_denom (C : Submodule (𝓞 E) E) (hfg : C.FG) (w : HeightOneSpectrum (𝓞 E))
    (hC : ∀ c ∈ C, w.valuation E c ≤ 1) : ∃ d : 𝓞 E, d ∉ w.asIdeal ∧ ∀ c ∈ C, ∃ o : 𝓞 E, (d : E) * c = o := by
  classical
  obtain ⟨G, rfl⟩ := hfg
  have h1 : ∀ c : E, ∃ d : 𝓞 E, d ∉ w.asIdeal ∧ (w.valuation E c ≤ 1 → ∃ o : 𝓞 E, (d : E) * c = o) := fun c => by
    by_cases hc : w.valuation E c ≤ 1
    · obtain ⟨o, ⟨d, hd⟩, e⟩ := w.exists_primeCompl_mul_eq_of_integer c hc
      exact ⟨d, hd, fun _ => ⟨o, by rw [mul_comm]; exact e⟩⟩
    · exact ⟨1, (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top, fun h => absurd h hc⟩
  choose d hd hd' using h1
  refine ⟨∏ c ∈ G, d c, fun hm => ?_, fun c hc => ?_⟩
  · obtain ⟨c, -, hc⟩ := (Ideal.IsPrime.prod_mem_iff (hp := w.isPrime)).1 hm
    exact hd c hc
  · induction hc using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨o, ho⟩ := hd' x (hC x (Submodule.subset_span hx))
      obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem d hx
      refine ⟨k * o, ?_⟩
      rw [hk]; push_cast; linear_combination (k : E) * ho
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by push_cast; rw [mul_add]; push_cast at ha hb; rw [ha, hb]⟩
    | smul a x _ hx =>
      obtain ⟨b, hb⟩ := hx
      refine ⟨a * b, ?_⟩
      change _ * ((a : E) * x) = (a : E) * (b : E)
      rw [← hb]
      ring

end PositivityTheory.ThKG.Tow.Pln

end
end

section

noncomputable section

namespace PositivityTheory.ThKG.Tow

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

def PlaneHerm : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n n₁ : ℕ), n = n₁ + 2 → 1 ≤ n₁ → ∀ (Y : Spc F E n) (r s : ℕ), 1 ≤ r → 1 ≤ s →
    Y.IsHerm σ B r s → ∀ i₀ i₁ : ℕ, i₀ < i₁ → i₁ < n → ∃ (Y' : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁),
      (GlobalTheory.ThK.reS Y Y').IsHerm σ B r s ∧ Y₁.IsHerm σ B (r - 1) (s - 1) ∧ H.IsAdapted σ B (GlobalTheory.ThK.reS Y Y') Y₁ i₀ i₁

def PlaneSkew : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n n₁ : ℕ), n = n₁ + 2 → 1 ≤ n₁ → ∀ (Y : Spc F E n) (r s : ℕ), 1 ≤ r → 1 ≤ s →
    Y.IsSkew σ B r s → ∀ i₀ i₁ : ℕ, i₀ < i₁ → i₁ < n → ∃ (Y' : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁),
      (GlobalTheory.ThK.reS Y Y').IsSkew σ B r s ∧ Y₁.IsSkew σ B (r - 1) (s - 1) ∧ H.IsAdapted σ B (GlobalTheory.ThK.reS Y Y') Y₁ i₀ i₁

def PlaneEx : Prop := PlaneHerm ∧ PlaneSkew

def ModelEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → W.IsSkew σ B r' s' → ∃ M : Model σ X W, M.IsGood B.ψ

def WeilEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → W.IsSkew σ B r' s' → ∀ M : Model σ X W, M.IsGood B.ψ →
    ∀ χX χW : Chr F E, IsHecke F E χX → IsHecke F E χW →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → ∃ om, M.IsWeil B.ψ χX χW om

def PairEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → W.IsSkew σ B r' s' → (∃ M : Model σ X W, M.IsGood B.ψ) ∧
    ∀ χX χW : Chr F E, IsHecke F E χX → IsHecke F E χW →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d →
      ∀ M : Model σ X W, M.IsGood B.ψ → ∃ om, IsPair B M χX χW om r s r' s'

theorem pairEx_of (h₁ : ModelEx) (h₂ : WeilEx) : PairEx := by
  intro F E _ _ _ _ _ σ B hB n d X W r s r' s' hX hW
  refine ⟨h₁ F E σ B hB n d X W r s r' s' hX hW, fun χX χW a b c e M hM => ?_⟩
  obtain ⟨om, hom⟩ := h₂ F E σ B hB n d X W r s r' s' hX hW M hM χX χW a b c e
  exact ⟨om, hB, hX, hW, hM, a, b, c, e, hom⟩

end PositivityTheory.ThKG.Tow

end
end

section

noncomputable section
namespace PositivityTheory.ThKG.Tow.Stab
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem mat_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem mat_mul_inv {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g * mat g⁻¹ = 1 := by
  show (g.1 * g.1⁻¹ : GL (Fin n) (AE F E)).1 = 1
  simp

theorem mat_inv_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g⁻¹ * mat g = 1 := by
  show (g.1⁻¹ * g.1 : GL (Fin n) (AE F E)).1 = 1
  simp

theorem mat_one {n : ℕ} {J : Matrix (Fin n) (Fin n) E} : mat (1 : UA σ J) = 1 := rfl

def stabK (B : Base F E) {n : ℕ} (X : Spc F E n) : Subgroup (UA σ X.J) where
  carrier := {g | (∀ w, Commute ((mat g).map (piInf (B.emb w))) (X.θ w)) ∧
    ∀ z ∈ latHat X, mat g *ᵥ z ∈ latHat X ∧ mat g⁻¹ *ᵥ z ∈ latHat X}
  one_mem' := by
    refine ⟨fun w => ?_, fun z hz => ?_⟩
    · rw [mat_one, Matrix.map_one _ (map_zero _) (map_one _)]; exact Commute.one_left _
    · simp only [inv_one, mat_one, Matrix.one_mulVec]; exact ⟨hz, hz⟩
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨fun w => ?_, fun z hz => ?_⟩
    · rw [mat_mul, Matrix.map_mul]; exact (hg1 w).mul_left (hh1 w)
    · rw [mul_inv_rev, mat_mul, mat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact ⟨(hg2 _ (hh2 z hz).1).1, (hh2 _ (hg2 z hz).2).2⟩
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    refine ⟨fun w => ?_, fun z hz => ?_⟩
    · set A := (mat g).map (piInf (B.emb w))
      set A' := (mat g⁻¹).map (piInf (B.emb w))
      have e1 : A * A' = 1 := by
        rw [← Matrix.map_mul, mat_mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
      have e2 : A' * A = 1 := by
        rw [← Matrix.map_mul, mat_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      have hc := hg1 w
      show A' * X.θ w = X.θ w * A'
      calc A' * X.θ w = A' * X.θ w * (A * A') := by rw [e1, Matrix.mul_one]
        _ = A' * (X.θ w * A) * A' := by simp only [Matrix.mul_assoc]
        _ = A' * (A * X.θ w) * A' := by rw [hc.eq]
        _ = (A' * A) * X.θ w * A' := by simp only [Matrix.mul_assoc]
        _ = X.θ w * A' := by rw [e2, Matrix.one_mul]
    · rw [inv_inv]; exact ⟨(hg2 z hz).2, (hg2 z hz).1⟩

theorem isStab_stabK (B : Base F E) {n : ℕ} (X : Spc F E n) : IsStab B (stabK (σ := σ) B X) := fun _ => Iff.rfl

theorem exists_haar_of_isCompact {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (K : Subgroup (UA σ J))
    (hK : IsCompact (K : Set (UA σ J))) : ∃ μ : Measure K, μ.IsHaarMeasure := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  exact ⟨Measure.haarMeasure ⊤, Measure.isHaarMeasure_haarMeasure _⟩

theorem exists_haar_idele : ∃ μ : Measure (AE F E)ˣ, μ.IsHaarMeasure := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : LocallyCompactSpace (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (AE F E)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  exact ⟨Measure.haar, inferInstance⟩

theorem isClosed_stabK (B : Base F E) {n : ℕ} (X : Spc F E n)
    (hL : IsClosed ((latHat X : AddSubgroup (Fin n → AE F E)) : Set (Fin n → AE F E))) :
    IsClosed ((stabK (σ := σ) B X : Subgroup (UA σ X.J)) : Set (UA σ X.J)) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hm : Continuous fun g : UA σ X.J => mat g := Units.continuous_val.comp continuous_subtype_val
  have hmi : Continuous fun g : UA σ X.J => mat g⁻¹ := hm.comp continuous_inv
  have hp : ∀ w, Continuous (piInf (B.emb w)) := fun w => GlobalTheory.Grow.continuous_infEmb_compInf F w (B.emb w)
  have h1 : IsClosed {g : UA σ X.J | ∀ w, Commute ((mat g).map (piInf (B.emb w))) (X.θ w)} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun w => isClosed_eq ((hm.matrix_map (hp w)).matrix_mul continuous_const)
      (continuous_const.matrix_mul (hm.matrix_map (hp w)))
  have h2 : IsClosed {g : UA σ X.J | ∀ z ∈ latHat X, mat g *ᵥ z ∈ latHat X ∧ mat g⁻¹ *ᵥ z ∈ latHat X} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun z => isClosed_iInter fun _ => ?_
    exact (hL.preimage (hm.matrix_mulVec continuous_const)).inter (hL.preimage (hmi.matrix_mulVec continuous_const))
  exact h1.inter h2

end PositivityTheory.ThKG.Tow.Stab
end
end
