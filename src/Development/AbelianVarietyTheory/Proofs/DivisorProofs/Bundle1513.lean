module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HSShortEnd

theorem claimS_of_numbers : ∀ (T D δ d y e : ℕ) (n Λ β Λ₀ ΛD ΛT Hf H' dg : ℝ), 1 ≤ D → D + 1 ≤ T → 1 ≤ δ → 1 ≤ n → 1 ≤ Λ → 1 ≤ β → 1 ≤ Λ₀ → 1 ≤ ΛD → 1 ≤ ΛT → (T - 1).choose D * δ + y ≤ d → ∀ b : ℕ, (D + 1) * b = (T - 1).choose D * (T + D * (D + 1)) → b * ((D + 1) * δ) + e = (T - 1).choose D * δ * T + y * (T - D) → -(cst n Λ * ((D + 1) * δ)) ≤ Hf → -(cst n Λ * e) ≤ H' → b * Hf + H' - (((T - 1).choose D * δ : ℕ) * Real.log (Real.sqrt β ^ T * Λ₀) + y * Real.log (Real.sqrt β ^ (T - D) * ΛD) + (d - (T - 1).choose D * δ - y : ℕ) * Real.log ΛT) ≤ dg → 0 < d ∧ ClaimS T D n Λ β Λ₀ ΛD ΛT δ (Hf / (((D : ℝ) + 1) * δ)) d dg := by
  intro T D δ d y e n Λ β Λ₀ ΛD ΛT Hf H' dg hD hDT hδ hn hΛ hβ hΛ₀ hΛD hΛT hd b hb he hHf hH' hdg
  have hDT' : D ≤ T - 1 := by omega
  have hR : 1 ≤ (T - 1).choose D := Nat.choose_pos hDT'
  set R := (T - 1).choose D with hRdef
  have hRδ : 1 ≤ R * δ := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hdpos : 0 < d := by omega
  refine ⟨hdpos, ?_⟩

  have hc : 0 ≤ cst n Λ := by
    unfold cst
    have h1 : 0 ≤ Real.log (n * Λ) := Real.log_nonneg (by nlinarith)
    have h2 : 0 ≤ Real.log n := Real.log_nonneg hn
    positivity
  set c := cst n Λ with hcdef

  have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hδR : (1 : ℝ) ≤ δ := by exact_mod_cast hδ
  have hRR : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDTR : (D : ℝ) + 1 ≤ T := by exact_mod_cast hDT
  have hdR' : (R : ℝ) * δ + y ≤ d := by exact_mod_cast hd
  have hbR : ((D : ℝ) + 1) * b = R * (T + D * (D + 1)) := by exact_mod_cast hb
  have hTD : D ≤ T := by omega
  have heR : (b : ℝ) * ((D + 1) * δ) + e = R * δ * T + y * ((T : ℝ) - D) := by
    have := congrArg (fun x : ℕ => (x : ℝ)) he
    push_cast [Nat.cast_sub hTD] at this
    linarith
  have hsub : ((d - R * δ - y : ℕ) : ℝ) = d - R * δ - y := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring
  have hsubTD : ((T - D : ℕ) : ℝ) = T - D := by rw [Nat.cast_sub hTD]

  have hβ0 : 0 < β := by linarith
  have hsq : 0 < Real.sqrt β := Real.sqrt_pos.mpr hβ0
  have hlb : Real.log (Real.sqrt β) = Real.log β / 2 := Real.log_sqrt hβ0.le
  have hL0 : Real.log (Real.sqrt β ^ T * Λ₀) = T * (Real.log β / 2) + Real.log Λ₀ := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, hlb]
  have hLD : Real.log (Real.sqrt β ^ (T - D) * ΛD) = ((T : ℝ) - D) * (Real.log β / 2) + Real.log ΛD := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, hlb, hsubTD]
  have lβ : 0 ≤ Real.log β := Real.log_nonneg hβ
  have lD : 0 ≤ Real.log ΛD := Real.log_nonneg hΛD
  have lT : 0 ≤ Real.log ΛT := Real.log_nonneg hΛT
  have l0 : 0 ≤ Real.log Λ₀ := Real.log_nonneg hΛ₀
  rw [hL0, hLD, hsub] at hdg
  push_cast at hdg

  set h := Hf / (((D : ℝ) + 1) * δ) with hhdef
  have hpos : (0 : ℝ) < ((D : ℝ) + 1) * δ := by positivity
  have hHfh : Hf = ((D : ℝ) + 1) * δ * h := by rw [hhdef]; field_simp
  have hh : -c ≤ h := by
    rw [hhdef, le_div_iff₀ hpos]; linarith
  have hbHf : (b : ℝ) * Hf = R * δ * (T + D * (D + 1)) * h := by
    rw [hHfh]
    calc (b : ℝ) * (((D : ℝ) + 1) * δ * h) = (((D : ℝ) + 1) * b) * δ * h := by ring
      _ = _ := by rw [hbR]; ring

  have he2 : (e : ℝ) = y * ((T : ℝ) - D) - R * δ * (D * (D + 1)) := by
    have : (b : ℝ) * ((D + 1) * δ) = R * δ * (T + D * (D + 1)) := by
      calc (b : ℝ) * ((D + 1) * δ) = (((D : ℝ) + 1) * b) * δ := by ring
        _ = _ := by rw [hbR]; ring
    linarith
  have hy0 : (0 : ℝ) ≤ y := Nat.cast_nonneg y
  have hRδ0 : (0 : ℝ) ≤ R * δ := by positivity
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hDD : (0 : ℝ) ≤ D * (D + 1) := by positivity
  have heT : (e : ℝ) ≤ T * (d - R * δ) := by
    rw [he2]
    linarith [mul_nonneg hRδ0 hDD, mul_nonneg hy0 hD0, mul_nonneg (sub_nonneg.mpr hdR') hT0]
  have hce : c * e ≤ c * (T * (d - R * δ)) := mul_le_mul_of_nonneg_left heT hc
  have hch : R * δ * (D * (D + 1)) * (-c) ≤ R * δ * (D * (D + 1)) * h :=
    mul_le_mul_of_nonneg_left hh (mul_nonneg hRδ0 hDD)
  have hX : 0 ≤ (d - R * δ - y) * (T * (Real.log β / 2) + Real.log ΛD) := by
    apply mul_nonneg (by linarith); positivity
  have hyD : 0 ≤ (y : ℝ) * D * Real.log β := by positivity
  have hyT : 0 ≤ (y : ℝ) * Real.log ΛT := by positivity
  have key : (R : ℝ) * δ * (T * h - D * (D + 1) * c - Real.log Λ₀ - T / 2 * Real.log β) -
      (d - R * δ) * (T * c + T / 2 * Real.log β + Real.log ΛD + Real.log ΛT) ≤ dg := by
    linarith [hbHf, hce, hch, hX, hyD, hyT, hdg, hH']
  unfold ClaimS
  have hρ0 : (0 : ℝ) ≤ R * δ / d := div_nonneg hRδ0 hdR.le
  have hρ1 : (R : ℝ) * δ / d ≤ 1 := by rw [div_le_one hdR]; linarith
  refine ⟨by push_cast; linarith, by push_cast; linarith, ?_⟩
  rw [le_div_iff₀ hdR]
  have hdne : (d : ℝ) ≠ 0 := hdR.ne'
  have expand : ((1 - (1 - ((R : ℕ) : ℝ) * δ / d)) * (T * h - D * (D + 1) * c - Real.log Λ₀ - T / 2 * Real.log β) -
      (1 - ((R : ℕ) : ℝ) * δ / d) * (T * c + T / 2 * Real.log β + Real.log ΛD + Real.log ΛT)) * d =
      (R : ℝ) * δ * (T * h - D * (D + 1) * c - Real.log Λ₀ - T / 2 * Real.log β) -
      (d - R * δ) * (T * c + T / 2 * Real.log β + Real.log ΛD + Real.log ΛT) := by
    field_simp
    ring
  push_cast at expand ⊢
  rw [expand]; exact key

end GlobalTheory.HSShortEnd
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

namespace GlobalTheory.HSShort.SymCols

variable {K A : Type} [Field K] [AddCommGroup A] [Module K A] {N : ℕ} (mul : (Fin N → K) →ₗ[K] Module.End K A)

theorem word_const (l : Fin N → K) (n : ℕ) : word mul (fun _ : Fin n => l) = mul l ^ n := by
  simp [word, List.ofFn_const, List.prod_replicate]

theorem join_fun {D : ℕ} (s : Fin D → Fin N → K) (l : Fin N → K) (b : Fin (D + 1)) :
    (fun k => join s l (b, k)) = Fin.lastCases (motive := fun _ => Fin N → K) l s b := by
  induction b using Fin.lastCases with
  | last => funext k; simp [join]
  | cast i => funext k; simp [join]

theorem word_join (hc : ∀ u v, mul u * mul v = mul v * mul u) {D t : ℕ} (s : Fin D → Fin N → K) (l : Fin N → K)
    (β : Fin t → Fin (D + 1)) (α : Fin D →₀ ℕ)
    (hα : ∀ i : Fin D, (Finset.univ.filter fun q => β q = i.castSucc).card = α i) :
    word mul (fun q k => join s l (β q, k)) =
      pw mul s α * mul l ^ (Finset.univ.filter fun q => β q = Fin.last D).card := by
  classical
  let P := Submonoid.closure (Set.range mul)
  letI : CommMonoid P := { P.toMonoid with
    mul_comm := by
      intro ⟨x, hx⟩ ⟨y, hy⟩
      apply Subtype.ext
      exact Submonoid.closure_induction₂
        (by rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩; exact hc u v)
        (by simp) (by simp)
        (by
          intro x y z _ _ _ h1 h2
          change x * z = z * x at h1
          change y * z = z * y at h2
          change (x * y) * z = z * (x * y)
          rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc])
        (by
          intro x y z _ _ _ h1 h2
          change z * x = x * z at h1
          change z * y = y * z at h2
          change z * (x * y) = (x * y) * z
          rw [← mul_assoc, h1, mul_assoc, h2, ← mul_assoc]) hx hy }
  let G : (Fin N → K) → P := fun u => ⟨mul u, Submonoid.subset_closure ⟨u, rfl⟩⟩
  let φ : P →* Module.End K A := P.subtype
  have key : ∀ {n : ℕ} (f : Fin n → P), (List.ofFn fun i => φ (f i)).prod = φ (∏ i, f i) := by
    intro n f
    rw [← List.prod_ofFn]
    change (List.ofFn (φ ∘ f)).prod = _
    rw [← List.map_ofFn, map_list_prod]
  let H : Fin (D + 1) → Fin N → K := Fin.lastCases (motive := fun _ => Fin N → K) l s
  have h1 : word mul (fun q k => join s l (β q, k)) = φ (∏ q, G (H (β q))) := by
    rw [← key]
    simp only [word, join_fun]
    rfl
  have h2 : pw mul s α = φ (∏ i, G (s i) ^ α i) := by
    rw [← key]
    simp only [pw, map_pow]
    rfl
  rw [h1, h2, show mul l ^ (Finset.univ.filter fun q => β q = Fin.last D).card = φ (G l ^ (Finset.univ.filter fun q => β q = Fin.last D).card) from (map_pow φ (G l) _).symm, ← map_mul]
  congr 1
  rw [Finset.prod_comp (fun b => G (H b)) β]
  rw [Finset.prod_subset (Finset.subset_univ _)]
  · rw [Fin.prod_univ_castSucc]
    apply congrArg₂ (fun (x y : P) => x * y)
    · refine Finset.prod_congr rfl fun i _ => ?_
      simp [H, hα]
    · simp [H]
  · intro b _ hb
    have : (Finset.univ.filter fun q => β q = b).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro q _ hq
      exact hb (Finset.mem_image.2 ⟨q, Finset.mem_univ _, hq⟩)
    rw [this]
    exact pow_zero _

theorem card_fibers {D t : ℕ} (β : Fin t → Fin (D + 1)) :
    ∑ i : Fin D, (Finset.univ.filter fun q => β q = i.castSucc).card +
      (Finset.univ.filter fun q => β q = Fin.last D).card = t := by
  classical
  have := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := β)
    (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_fin] at this
  rw [Fin.sum_univ_castSucc] at this
  exact this.symm

end GlobalTheory.HSShort.SymCols

open GlobalTheory.HSShort.SymCols in
theorem GlobalTheory.HSShort.symbols_of_columns : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → E) (δ : ℕ) (Φ : S.Flat E A' s δ) (d : ℕ) (col : Fin d → S.Col) (m : Fin δ → S.V 0) (ix : (Σ a : Fin (S.T - S.D), MonoDeg (Fin S.D) a) × Fin δ ↪ Fin d), S.Shape δ col m ix → ∀ l : Fin S.N → E, (∀ (a : Fin (S.T - S.D)) (α : MonoDeg (Fin S.D) a) (p : Fin δ), ∃ h : word Φ.mul (fun q k => join s l ((col (ix (⟨a, α⟩, p))).β q, k)) (Φ.ι (col (ix (⟨a, α⟩, p))).x) ∈ Φ.U a, ∀ α' p', Φ.sym a ⟨_, h⟩ (α', p') = if α'.1 = α.1 then (∑ k, l k * Φ.y p' k) ^ (S.T - a) * Φ.res (Φ.ι (m p)) p' else 0) ∧ ∀ k, k ∉ Set.range ix → (col k).j = S.D → word Φ.mul (fun q j => join s l ((col k).β q, j)) (Φ.ι (col k).x) ∈ Φ.U (S.T - S.D) := by
  intro F A _ _ _ _ _ _ S hS E A' _ _ _ _ s δ Φ d col m ix hsh l
  refine ⟨fun a α p => ?_, fun k hk hj => ?_⟩
  · set κ := col (ix (⟨a, α⟩, p)) with hκ
    have hj : κ.j = 0 := hsh.x_j _
    have hx : (κ.x : A) = m p := hsh.x_vec _
    have htype : ∀ i : Fin S.D, (Finset.univ.filter fun q => κ.β q = i.castSucc).card = α.1 i := hsh.x_type _
    have ht : κ.t = S.T := by have := κ.add; omega
    have hdeg : ∑ i : Fin S.D, α.1 i = a := by rw [← Finsupp.degree_eq_sum]; exact α.2
    have hlast : (Finset.univ.filter fun q => κ.β q = Fin.last S.D).card = S.T - a := by
      have := card_fibers κ.β
      simp only [htype, hdeg] at this
      omega
    have heq : word Φ.mul (fun q k => join s l (κ.β q, k)) (Φ.ι κ.x) =
        pw Φ.mul s α.1 (word Φ.mul (fun _ : Fin (S.T - a) => l) (Φ.ι (m p))) := by
      rw [word_join Φ.mul Φ.comm s l κ.β α.1 htype, hlast, word_const, Module.End.mul_apply, hx]
    obtain ⟨h, hsym⟩ := Φ.mono a (by omega) α (fun _ => l) (Φ.ι (m p))
      (Submodule.subset_span ⟨(m p : A), (m p).2, rfl⟩)
    rw [heq]
    refine ⟨h, fun α' p' => ?_⟩
    rw [hsym]
    simp
  · have hrest := hsh.rest k hk
    have hno : ∀ q, (col k).β q ≠ Fin.last S.D := by
      rcases hrest with h | h
      · exact h.2
      · have := hS.le_T; omega
    classical
    let α : Fin S.D →₀ ℕ := Finsupp.equivFunOnFinite.symm
      (fun i => (Finset.univ.filter fun q => (col k).β q = i.castSucc).card)
    have htype : ∀ i : Fin S.D, (Finset.univ.filter fun q => (col k).β q = i.castSucc).card = α i := fun i => rfl
    have h0 : (Finset.univ.filter fun q => (col k).β q = Fin.last S.D).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun q _ => hno q
    have ht : (col k).t = S.T - S.D := by have := (col k).add; omega
    have hdeg : α.degree = S.T - S.D := by
      rw [Finsupp.degree_eq_sum]
      have := card_fibers (col k).β
      rw [h0] at this
      simpa [α, ht] using this
    rw [word_join Φ.mul Φ.comm s l (col k).β α htype, h0, pow_zero, mul_one, Φ.div]
    refine Submodule.mem_iSup_of_mem ⟨α, hdeg⟩ (Submodule.mem_map_of_mem (Submodule.subset_span ⟨((col k).x : A), ?_, rfl⟩))
    have key : ∀ (j : ℕ) (x : S.V j), j = S.D → (x : A) ∈ S.V S.D := by rintro j x rfl; exact x.2
    exact key _ _ hj
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSShort.DetHom

section MH

variable {R : Type} [CommSemiring R] {B n : ℕ}

theorem mh_zero (a : Fin B → ℕ) : IsMultiHomogeneous a (0 : MvPolynomial (Fin B × Fin n) R) := by
  intro s hs; simp at hs

theorem mh_C (r : R) : IsMultiHomogeneous (0 : Fin B → ℕ) (C r : MvPolynomial (Fin B × Fin n) R) := by
  classical
  intro s hs b
  rw [mem_support_iff, coeff_C] at hs
  have : (0 : Fin B × Fin n →₀ ℕ) = s := by
    by_contra h; exact hs (if_neg h)
  subst this; simp

theorem mh_X (i : Fin B) (j : Fin n) :
    IsMultiHomogeneous (Pi.single i 1) (X (i, j) : MvPolynomial (Fin B × Fin n) R) := by
  classical
  intro s hs b
  rw [mem_support_iff, coeff_X'] at hs
  have : Finsupp.single (i, j) 1 = s := by
    by_contra h; exact hs (if_neg h)
  subst this
  by_cases hb : b = i
  · subst hb; simp [Finsupp.single_apply]
  · simp [Finsupp.single_apply, hb, Pi.single_apply]

theorem mh_add {a : Fin B → ℕ} {f g : MvPolynomial (Fin B × Fin n) R}
    (hf : IsMultiHomogeneous a f) (hg : IsMultiHomogeneous a g) : IsMultiHomogeneous a (f + g) := by
  classical
  intro s hs
  rcases Finset.mem_union.1 (support_add hs) with h | h
  exacts [hf s h, hg s h]

theorem mh_sum {ι : Type} (t : Finset ι) {a : Fin B → ℕ} (f : ι → MvPolynomial (Fin B × Fin n) R)
    (hf : ∀ i ∈ t, IsMultiHomogeneous a (f i)) : IsMultiHomogeneous a (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using mh_zero (R := R) (n := n) a
  | insert x t hx ih =>
    rw [Finset.sum_insert hx]
    exact mh_add (hf x (Finset.mem_insert_self _ _)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem mh_smul {S : Type} [SMulZeroClass S R] {a : Fin B → ℕ} (c : S) {f : MvPolynomial (Fin B × Fin n) R}
    (hf : IsMultiHomogeneous a f) : IsMultiHomogeneous a (c • f) :=
  fun s hs => hf s (support_smul hs)

theorem mh_mul {a b : Fin B → ℕ} {f g : MvPolynomial (Fin B × Fin n) R}
    (hf : IsMultiHomogeneous a f) (hg : IsMultiHomogeneous b g) : IsMultiHomogeneous (a + b) (f * g) := by
  classical
  intro s hs i
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.1 (support_mul f g hs)
  simp [Finset.sum_add_distrib, hf u hu i, hg v hv i]

theorem mh_prod {ι : Type} (t : Finset ι) (a : ι → Fin B → ℕ) (f : ι → MvPolynomial (Fin B × Fin n) R)
    (hf : ∀ i ∈ t, IsMultiHomogeneous (a i) (f i)) : IsMultiHomogeneous (∑ i ∈ t, a i) (∏ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using mh_C (R := R) (B := B) (n := n) 1
  | insert x t hx ih =>
    rw [Finset.sum_insert hx, Finset.prod_insert hx]
    exact mh_mul (hf x (Finset.mem_insert_self _ _)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end MH

def cnt {B t : ℕ} (β : Fin t → Fin B) (b : Fin B) : ℕ := (Finset.univ.filter fun q => β q = b).card

theorem sum_cnt {B t : ℕ} (β : Fin t → Fin B) : ∑ b, cnt β b = t := by
  classical
  unfold cnt
  rw [← Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (β x))]
  simp

theorem sum_single_eq_cnt {B t : ℕ} (β : Fin t → Fin B) :
    (∑ i, (Pi.single (β i) 1 : Fin B → ℕ)) = cnt β := by
  classical
  funext b
  simp only [Finset.sum_apply, Pi.single_apply, cnt]
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : β i = b
  · simp [h]
  · simp [h, Ne.symm h]

theorem mh_coordP {K A : Type} [Field K] [AddCommGroup A] [Module K A] {N B t : ℕ}
    (mul : (Fin N → K) →ₗ[K] Module.End K A) (c : A →ₗ[K] K) (β : Fin t → Fin B) (m : A) :
    IsMultiHomogeneous (cnt β) (coordP mul c β m) := by
  classical
  unfold coordP
  refine mh_sum _ _ fun e _ => ?_
  have h := mh_mul (mh_C (R := K) (B := B) (n := N) (c (word mul (fun i => Pi.single (e i) 1) m)))
    (mh_prod Finset.univ (fun i => (Pi.single (β i) 1 : Fin B → ℕ)) (fun i => (X (β i, e i) : MvPolynomial (Fin B × Fin N) K))
      fun i _ => mh_X (β i) (e i))
  rwa [zero_add, sum_single_eq_cnt] at h

end GlobalTheory.HSShort.DetHom


open GlobalTheory.HSShort.DetHom in
theorem GlobalTheory.HSShort.det_isMultiHomogeneous : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A) (d : ℕ) (c : Fin d → A →ₗ[F] F) (col : Fin d → S.Col), ∃ a : Fin (S.D + 1) → ℕ, IsMultiHomogeneous a (S.det c col) ∧ ∑ i, a i = ∑ k, (col k).t := by
  intro F A _ _ _ _ _ _ S d c col
  classical
  refine ⟨∑ k, cnt (col k).β, ?_, ?_⟩
  · unfold Sys.det
    rw [Matrix.det_apply]
    refine mh_sum _ _ fun σ _ => mh_smul _ ?_
    have h := mh_prod Finset.univ (fun k => cnt (col k).β)
      (fun k => (Matrix.of fun i k => coordP S.mul (c i) (col k).β ((col k).x : A)) (σ k) k)
      fun k _ => by simpa using mh_coordP S.mul (c (σ k)) (col k).β ((col k).x : A)
    exact h
  · simp only [Finset.sum_apply]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => sum_cnt (col k).β
end
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

namespace GlobalTheory.HSShort.Sys

variable {F A : Type} [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A]

theorem word_succ {K B : Type} [Field K] [AddCommGroup B] [Module K B] {N : ℕ} (mul : (Fin N → K) →ₗ[K] Module.End K B)
    {t : ℕ} (u : Fin (t + 1) → Fin N → K) : word mul u = mul (u 0) * word mul (fun i => u i.succ) := by
  simp [word, List.ofFn_succ]

theorem word_zero {K B : Type} [Field K] [AddCommGroup B] [Module K B] {N : ℕ} (mul : (Fin N → K) →ₗ[K] Module.End K B)
    (u : Fin 0 → Fin N → K) : word mul u = 1 := by
  simp [word]

theorem mul_mem_V_succ (S : Sys F A) (hS : S.Hyp) {j : ℕ} (hj : j < S.T) (u : Fin S.N → F) {x : A} (hx : x ∈ S.V j) :
    S.mul u x ∈ S.V (j + 1) := by
  have key : ∀ m ∈ S.M j, ∀ u : Fin S.N → F, S.mul u (m : A) ∈ S.V (j + 1) := by
    intro m hm u
    have hu : u ∈ Submodule.span F (Set.range S.w.col) := hS.lat.spans ▸ Submodule.mem_top
    let L : (Fin S.N → F) →ₗ[F] A := (LinearMap.applyₗ (m : A)) ∘ₗ S.mul
    have hle : Submodule.span F (Set.range S.w.col) ≤ (S.V (j + 1)).comap L := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      obtain ⟨g, -, hg⟩ := hS.stable j hj k m hm
      show L (S.w.col k) ∈ S.V (j + 1)
      simp only [L, LinearMap.coe_comp, Function.comp_apply, LinearMap.applyₗ_apply_apply]
      rw [← hg]
      exact g.2
    exact hle hu
  let P : Submodule F (S.V j) := (S.V (j + 1)).comap (S.mul u ∘ₗ (S.V j).subtype)
  have hP : Submodule.span F (S.M j : Set (S.V j)) ≤ P := by
    rw [Submodule.span_le]
    intro m hm
    exact key m hm u
  have hx' : (⟨x, hx⟩ : S.V j) ∈ Submodule.span F (S.M j : Set (S.V j)) :=
    (hS.full j hj.le).span ▸ Submodule.mem_top
  exact hP hx'

theorem word_mem (S : Sys F A) (hS : S.Hyp) (j t : ℕ) (hjt : j + t ≤ S.T) :
    (∀ (u : Fin t → Fin S.N → F), ∀ x ∈ S.V j, word S.mul u x ∈ S.V (j + t)) ∧
      ∀ (e : Fin t → Fin S.n), ∀ x ∈ S.M j, ∃ g ∈ S.M (j + t), (g : A) = word S.mul (fun i => S.w.col (e i)) x := by
  induction t with
  | zero =>
    refine ⟨fun u x hx => ?_, fun e x hx => ⟨x, hx, ?_⟩⟩
    · simpa [word_zero] using hx
    · simp [word_zero]
  | succ t ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hlt : j + t < S.T := by omega
    refine ⟨fun u x hx => ?_, fun e x hx => ?_⟩
    · rw [word_succ, Module.End.mul_apply]
      exact mul_mem_V_succ S hS hlt (u 0) (ih1 (fun i => u i.succ) x hx)
    · obtain ⟨g', hg', hg'e⟩ := ih2 (fun i => e i.succ) x hx
      obtain ⟨g, hg, hge⟩ := hS.stable (j + t) hlt (e 0) g' hg'
      refine ⟨g, hg, ?_⟩
      rw [word_succ, Module.End.mul_apply, hge, hg'e]

end GlobalTheory.HSShort.Sys

namespace GlobalTheory.HSShort

theorem wordMem : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (j t : ℕ), j + t ≤ S.T → (∀ (u : Fin t → Fin S.N → F), ∀ x ∈ S.V j, word S.mul u x ∈ S.V (j + t)) ∧ ∀ (e : Fin t → Fin S.n), ∀ x ∈ S.M j, ∃ g ∈ S.M (j + t), (g : A) = word S.mul (fun i => S.w.col (e i)) x :=
  fun _ _ _ _ _ _ _ _ S hS j t hjt => S.word_mem hS j t hjt

end GlobalTheory.HSShort
end
