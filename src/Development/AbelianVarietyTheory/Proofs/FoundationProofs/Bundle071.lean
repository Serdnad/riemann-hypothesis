module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle023
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsValuationSubringGaussModularFunction
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesCoeffRingHomMapCoeff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle026
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle034
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle035
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Lemma
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle001

@[expose] public section

section

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES

theorem exists_dom_gauss : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    ∀ V : ValuationSubring Ω, ∃ W : ValuationSubring X.K, Dom X V W ∧ Gauss X.jK V W := by
  intro Ω _ _ _ ε X V
  classical
  open GaussDom in
  haveI : (RingHom.ker (redA V X.exp)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨W, hA, hinv, hlt⟩ :=
    ReciprocityTheory.ChartRestriction.G.AR.Up.NOrd.exists_val_of_prime (GaussDom.intA V X.exp) (RingHom.ker (GaussDom.redA V X.exp))
  have hker : ∀ x : GaussDom.intA V X.exp, x ∈ RingHom.ker (GaussDom.redA V X.exp) ↔
      ∀ r, (X.exp x).coeff r ∈ V.nonunits :=
    fun x => (RingHom.mem_ker).trans (GaussDom.redA_eq_zero V X.exp x)
  have hone : ∀ x : GaussDom.intA V X.exp, x ∉ RingHom.ker (GaussDom.redA V X.exp) → W.valuation (x : X.K) = 1 := by
    intro x hx
    have hx0 : (x : X.K) ≠ 0 := by
      intro h0
      apply hx
      have : x = 0 := Subtype.ext h0
      rw [this]
      exact Ideal.zero_mem _
    have h1 := (W.valuation_le_one_iff _).2 (hA x)
    have h2 := (W.valuation_le_one_iff _).2 (hinv x hx)
    rw [map_inv₀] at h2
    have hv0 : W.valuation (x : X.K) ≠ 0 := by simpa using hx0
    exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 hv0)).1 h2)
  have hj3 : ∀ r, (X.exp X.jK).coeff r ∈ V := fun r => by
    obtain ⟨n, hn⟩ := X.j_exp.2.2 r
    rw [hn]
    exact intCast_mem V n
  have hj1 : (X.exp X.jK).coeff (-1) = 1 := X.j_exp.1
  have hj2 : ∀ r : ℚ, r < -1 → (X.exp X.jK).coeff r = 0 := X.j_exp.2.1
  refine ⟨W, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro f hf
    exact hA ⟨f, (GaussDom.mem_intA V X.exp f).2 hf⟩
  · intro f hf
    have hfi : f ∈ GaussDom.intA V X.exp :=
      (GaussDom.mem_intA V X.exp f).2 (fun r => V.valuation_le_one_iff _ |>.1 (le_of_lt
        ((ValuationSubring.mem_nonunits_iff _).1 (hf r))))
    exact hlt ⟨f, hfi⟩ ((hker _).2 hf)
  · rintro f ⟨hf, r, hr⟩
    apply hone ⟨f, (GaussDom.mem_intA V X.exp f).2 hf⟩
    intro hk
    have := (hker _).1 hk r
    rw [ValuationSubring.mem_nonunits_iff] at this
    exact absurd hr (ne_of_lt this)
  · intro a
    constructor
    · intro ha
      by_contra hnot
      have ha0 : a ≠ 0 := fun h => hnot (h ▸ V.zero_mem)
      have hinvV : a⁻¹ ∈ V := (V.mem_or_inv_mem a).resolve_left hnot
      have hnu : a⁻¹ ∈ V.nonunits := by
        rw [ValuationSubring.mem_nonunits_iff]
        refine lt_of_le_of_ne ((V.valuation_le_one_iff _).2 hinvV) ?_
        intro h1
        apply hnot
        rw [map_inv₀, inv_eq_one] at h1
        exact (V.valuation_le_one_iff a).1 (le_of_eq h1)
      have hm : algebraMap Ω X.K a⁻¹ ∈ GaussDom.intA V X.exp := GaussDom.const_mem V X.exp _ hinvV
      have hk : (⟨_, hm⟩ : GaussDom.intA V X.exp) ∈ RingHom.ker (GaussDom.redA V X.exp) := by
        rw [hker]
        intro r
        show (X.exp (algebraMap Ω X.K a⁻¹)).coeff r ∈ V.nonunits
        rw [GaussDom.coeff_const]
        split_ifs
        · exact hnu
        · exact GaussDom.zero_mem_nonunits V
      have h3 : W.valuation (algebraMap Ω X.K a⁻¹) < 1 := hlt _ hk
      have h4 := (W.valuation_le_one_iff _).2 ha
      have h5 : W.valuation (algebraMap Ω X.K a) * W.valuation (algebraMap Ω X.K a⁻¹) = 1 := by
        rw [← map_mul, ← map_mul, mul_inv_cancel₀ ha0, map_one, map_one]
      have h6 : W.valuation (algebraMap Ω X.K a) * W.valuation (algebraMap Ω X.K a⁻¹) ≤
          1 * W.valuation (algebraMap Ω X.K a⁻¹) := by gcongr
      rw [h5, one_mul] at h6
      exact absurd (lt_of_le_of_lt h6 h3) (lt_irrefl 1)
    · intro ha
      exact hA ⟨_, GaussDom.const_mem V X.exp a ha⟩
  · rintro P hP ⟨i0, hne, hi0, hi0'⟩
    have hjA : X.jK ∈ GaussDom.intA V X.exp := (GaussDom.mem_intA V X.exp X.jK).2 hj3
    obtain ⟨P', hP'⟩ : ∃ P' : Polynomial V, P'.map V.subtype = P :=
      (Polynomial.lifts_iff_coeff_lifts P).2 (fun n => ⟨⟨_, hP n⟩, rfl⟩)
    let ι : V →+* GaussDom.intA V X.exp :=
      ((algebraMap Ω X.K).comp V.subtype).codRestrict (GaussDom.intA V X.exp)
        (fun v => GaussDom.const_mem V X.exp v v.2)
    have hx : Polynomial.aeval X.jK P = (GaussDom.intA V X.exp).subtype (P'.eval₂ ι ⟨X.jK, hjA⟩) := by
      rw [Polynomial.hom_eval₂, ← hP', Polynomial.aeval_def, Polynomial.eval₂_map]
      rfl
    rw [hx]
    apply hone
    intro hk
    rw [RingHom.mem_ker, Polynomial.hom_eval₂] at hk
    have hc : (GaussDom.redA V X.exp).comp ι =
        (algebraMap (IsLocalRing.ResidueField V) (HahnSeries ℚ (IsLocalRing.ResidueField V))).comp
          (IsLocalRing.residue V) := by
      apply RingHom.ext
      intro v
      exact GaussDom.redA_const V X.exp v
    rw [hc, ← Polynomial.eval₂_map, ← Polynomial.aeval_def] at hk
    set J := GaussDom.redA V X.exp ⟨X.jK, hjA⟩ with hJdef
    have hJ : J.orderTop = ((-1 : ℚ) : WithTop ℚ) := by
      apply HahnSeries.orderTop_eq_of_le
      · rw [HahnSeries.mem_support, hJdef, GaussDom.redA_coeff]
        have h1 : (⟨(X.exp X.jK).coeff (-1), (GaussDom.mem_intA V X.exp X.jK).1 hjA (-1)⟩ : V) = 1 :=
          Subtype.ext hj1
        rw [h1, map_one]
        exact one_ne_zero
      · intro g hg
        rw [HahnSeries.mem_support, hJdef, GaussDom.redA_coeff] at hg
        by_contra hlt'
        apply hg
        have h0 : (⟨(X.exp X.jK).coeff g, (GaussDom.mem_intA V X.exp X.jK).1 hjA g⟩ : V) = 0 :=
          Subtype.ext (hj2 g (lt_of_not_ge hlt'))
        rw [h0, map_zero]
    have hQ : P'.map (IsLocalRing.residue V) ≠ 0 := by
      intro h0
      have hc0 := congrArg (fun Q => Q.coeff i0) h0
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hc0
      have hPi : ((P'.coeff i0 : V) : Ω) = P.coeff i0 := by
        rw [← hP', Polynomial.coeff_map]
        rfl
      have hu : IsUnit (P'.coeff i0) := by
        refine isUnit_iff_exists_inv.2 ⟨⟨(P.coeff i0)⁻¹, hi0'⟩, Subtype.ext ?_⟩
        show ((P'.coeff i0 : V) : Ω) * (P.coeff i0)⁻¹ = 1
        rw [hPi, mul_inv_cancel₀ hne]
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal] at hc0
      exact hc0 hu
    have hot := GaussDom.orderTop_aeval J hJ _ _ hQ rfl
    rw [hk, HahnSeries.orderTop_zero] at hot
    exact WithTop.top_ne_coe hot

end GlobalTheory.KZ.ES
end
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

noncomputable section

namespace GlobalTheory.KZ.ES


open GlobalTheory.KroneckerCongruence in
theorem nq_sub_gal_small : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    ∀ (M q : ℕ), 0 < M → q.Prime → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), FrobV V q s →
    ∀ a : X.K, Lev X M a → IntC X V a → SmallC X V (Nq X M q a - X.gal s a) := by
  intro Ω _ _ _ ε X M q hM hq V s hFr f hf hfV
  obtain ⟨hqV, hs⟩ := hFr
  have hε : Function.Injective ε := ε.injective
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  set ρ := IsLocalRing.residue V with hρ_def
  have hρ0 : ∀ x : V, ρ x = 0 ↔ V.valuation (x : Ω) < 1 := fun x => by
    rw [hρ_def, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  haveI : CharP (IsLocalRing.ResidueField V) q := (CharP.charP_iff_prime_eq_zero hq).2 (by
    have : ρ (q : V) = 0 := (hρ0 _).2 (by simpa [ValuationSubring.mem_nonunits_iff] using hqV)
    simpa using this)
  have hfrob : ∀ x : V, ρ ⟨s x, (hs x x.2).1⟩ = ρ x ^ q := by
    intro x
    rw [← sub_eq_zero, ← map_pow, ← map_sub, hρ0]
    simpa using (hs x x.2).2.2
  set c := X.exp f with hc
  have hdet : ∀ j : ℕ, 0 < (!![1, ((j : ℤ) * M : ℤ); 0, (q : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    intro j; simp [Matrix.det_fin_two]; exact_mod_cast hq.pos
  have hFj : ∀ (j : ℕ) (t : ℚ), (X.exp (X.sl (toGQ !![1, ((j : ℤ) * M : ℤ); 0, (q : ℤ)]) f)).coeff t =
      eOm ε (t * j * M) * c.coeff (t * q) := by
    intro j t
    have h := X.exp_upper (toGQ !![1, ((j : ℤ) * M : ℤ); 0, (q : ℤ)]) (by rw [ent_toGQ _ (hdet j)]; simp) f (t * q)
    rw [ent_toGQ _ (hdet j), ent_toGQ _ (hdet j), ent_toGQ _ (hdet j)] at h
    simp at h
    convert h using 2 <;> first | field_simp | (congr 1; field_simp)
  have hw : ∀ (j : ℕ) (t : ℚ), c.coeff (t * q) ≠ 0 → ∃ h : eOm ε (t * j * M) ∈ V, ρ ⟨_, h⟩ = 1 := by
    intro j t ht
    have h1 : eOm ε (t * j * M) ^ q = 1 := by
      rw [← eOm_mul_nat hε, show (q : ℚ) * (t * j * M) = j * (t * q * M) by ring, eOm_mul_nat hε,
        eOm_level X M f hf _ ht, one_pow]
    have hmem : eOm ε (t * j * M) ∈ V := mem_of_pow_eq_one V hq.ne_zero h1
    refine ⟨hmem, ?_⟩
    have h2 : (⟨_, hmem⟩ : V) ^ q = 1 := Subtype.ext (by simpa using h1)
    have h3 : (ρ ⟨_, hmem⟩ - 1) ^ q = 0 := by rw [sub_pow_char, ← map_pow, h2, map_one, one_pow, sub_self]
    exact sub_eq_zero.1 (pow_eq_zero_iff hq.ne_zero |>.1 h3)
  have memF : ∀ (j : ℕ) (t : ℚ), (X.exp (X.sl (toGQ !![1, ((j : ℤ) * M : ℤ); 0, (q : ℤ)]) f)).coeff t ∈ V := by
    intro j t
    rw [hFj]
    by_cases h0 : c.coeff (t * q) = 0
    · rw [h0, mul_zero]; exact zero_mem V
    · exact mul_mem (hw j t h0).1 (hfV _)
  have redF : ∀ (j : ℕ) (t : ℚ), ρ ⟨_, memF j t⟩ = ρ ⟨_, hfV (t * q)⟩ := by
    intro j t
    by_cases h0 : c.coeff (t * q) = 0
    · exact congrArg ρ (Subtype.ext (by simp only; rw [hFj, h0, mul_zero]))
    · obtain ⟨hm, h1⟩ := hw j t h0
      have e : (⟨_, memF j t⟩ : V) = ⟨_, hm⟩ * ⟨_, hfV (t * q)⟩ :=
        Subtype.ext (by simp only [MulMemClass.mk_mul_mk]; rw [hFj])
      rw [e, map_mul, h1, one_mul]
  have memC : ∀ t : ℚ, (X.exp (X.gal s f)).coeff t ∈ V := by
    intro t; rw [X.gal_exp]; exact (hs _ (hfV t)).1
  set LF : ℕ → HahnSeries ℚ V := fun j => liftV V _ (memF j) with hLF
  set LC := liftV V _ memC with hLC
  have h1 : ∀ j, hahnSeriesCoeffRingHomMap ρ (LF j) = hahnSeriesCoeffRingHomMap ρ (LF 0) := by
    intro j; ext t; rw [hahnSeriesCoeffRingHomMap_coeff, hahnSeriesCoeffRingHomMap_coeff]; exact (redF j t).trans (redF 0 t).symm
  have h2 : hahnSeriesCoeffRingHomMap ρ (LF 0) ^ q = hahnSeriesCoeffRingHomMap ρ LC := by
    ext t
    rw [coeff_pow_char q, hahnSeriesCoeffRingHomMap_coeff, hahnSeriesCoeffRingHomMap_coeff]
    show ρ ⟨_, memF 0 (t / q)⟩ ^ q = ρ ⟨_, memC t⟩
    rw [redF 0 (t / q), ← hfrob]
    exact congrArg ρ (Subtype.ext (by simp only; rw [X.gal_exp, div_mul_cancel₀ t hq0]))
  have hexp : X.exp ((∏ j ∈ Finset.range q, X.sl (toGQ !![1, ((j : ℤ) * M : ℤ); 0, (q : ℤ)]) f) - X.gal s f) =
      hahnSeriesCoeffRingHomMap V.subtype ((∏ j ∈ Finset.range q, LF j) - LC) := by
    simp only [map_sub, map_prod, hLF, hLC, map_liftV]
  have hW : hahnSeriesCoeffRingHomMap ρ ((∏ j ∈ Finset.range q, LF j) - LC) = 0 := by
    rw [map_sub, map_prod, Finset.prod_congr rfl (fun j _ => h1 j), Finset.prod_const, Finset.card_range, h2, sub_self]
  intro r
  unfold Nq
  rw [hexp, hahnSeriesCoeffRingHomMap_coeff, ValuationSubring.mem_nonunits_iff]
  refine (hρ0 (((∏ j ∈ Finset.range q, LF j) - LC).coeff r)).1 ?_
  rw [← hahnSeriesCoeffRingHomMap_coeff, hW]
  rfl

end GlobalTheory.KZ.ES
end
end

section

open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.TrOld

def rep (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) : Option (Fin l) → SL(2, ℤ)
  | none => 1
  | some j => gaOld N l a b h j

def sig (l : ℕ) [NeZero l] (x : SL(2, ℤ)) : Option (Fin l) :=
  if (l : ℤ) ∣ mat x 1 0 then none
  else some ⟨(((mat x 1 1 : ℤ) : ZMod l) * ((mat x 1 0 : ℤ) : ZMod l)⁻¹).val, ZMod.val_lt _⟩

lemma mul_11 (x y : SL(2, ℤ)) : mat (x * y) 1 1 = mat x 1 0 * mat y 0 1 + mat x 1 1 * mat y 1 1 := by
  simp only [mat, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

lemma mulInv_10 (x y : SL(2, ℤ)) : mat (x * y⁻¹) 1 0 = mat x 1 0 * mat y 1 1 - mat x 1 1 * mat y 1 0 := by
  simp [mat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  ring

lemma mulInv_11 (x y : SL(2, ℤ)) : mat (x * y⁻¹) 1 1 = -(mat x 1 0 * mat y 0 1) + mat x 1 1 * mat y 0 0 := by
  simp [mat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

lemma mem_iff (M : ℕ) (x : SL(2, ℤ)) : x ∈ Gamma0 M ↔ (M : ℤ) ∣ mat x 1 0 := by
  rw [Gamma0_mem]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd _ _

section
variable {N l : ℕ} {a b : ℤ} {h : (l : ℤ) * b - N * a = 1}

lemma rep_none_10 : mat (rep N l a b h none) 1 0 = 0 := rfl
lemma rep_none_11 : mat (rep N l a b h none) 1 1 = 1 := rfl
lemma rep_some_10 (j : Fin l) : mat (rep N l a b h (some j)) 1 0 = N := rfl
lemma rep_some_11 (j : Fin l) : mat (rep N l a b h (some j)) 1 1 = (N : ℤ) * (j : ℕ) + l * b := rfl

lemma rep_00 (o : Option (Fin l)) : mat (rep N l a b h o) 0 0 = 1 := by
  cases o <;> simp [rep, gaOld, mat]

lemma rep_10 (o : Option (Fin l)) : ((mat (rep N l a b h o) 1 0 : ℤ) : ZMod N) = 0 := by
  cases o with
  | none => rw [rep_none_10]; simp
  | some j => rw [rep_some_10]; simp

lemma rep_11 (o : Option (Fin l)) : ((mat (rep N l a b h o) 1 1 : ℤ) : ZMod N) = 1 := by
  cases o with
  | none => rw [rep_none_11]; simp
  | some j =>
    have hc := congrArg (Int.cast : ℤ → ZMod N) h
    push_cast at hc
    rw [ZMod.natCast_self, zero_mul, sub_zero] at hc
    rw [rep_some_11]
    push_cast
    rw [ZMod.natCast_self, zero_mul, zero_add, hc]

include h in
lemma cop : IsCoprime (N : ℤ) (l : ℤ) := ⟨-a, b, by linear_combination h⟩

lemma sig_mem [NeZero l] (hl : l.Prime) (x : SL(2, ℤ)) (hx : x ∈ Gamma0 N) :
    x * (rep N l a b h (sig l x))⁻¹ ∈ Gamma0 (N * l) := by
  have := Fact.mk hl
  have hc : IsCoprime (N : ℤ) l := cop (h := h)
  have hδ : ∀ o, (N : ℤ) ∣ mat (rep N l a b h o) 1 0 := fun o =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (rep_10 o)
  rw [mem_iff] at hx
  rw [mem_iff, mulInv_10]
  push_cast
  apply hc.mul_dvd
  · exact dvd_sub (Dvd.dvd.mul_right hx _) (Dvd.dvd.mul_left (hδ _) _)
  · unfold sig
    split_ifs with hd
    · rw [rep_none_10, rep_none_11]
      simpa using hd
    · rw [rep_some_10, rep_some_11, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      have hc0 : ((mat x 1 0 : ℤ) : ZMod l) ≠ 0 := by
        rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      have hu := mul_inv_cancel₀ hc0
      have hl0 : ((l : ℕ) : ZMod l) = 0 := ZMod.natCast_self l
      push_cast
      simp only [ZMod.natCast_zmod_val]
      linear_combination ((N : ZMod l) * ((mat x 1 1 : ℤ) : ZMod l)) * hu +
        (((mat x 1 0 : ℤ) : ZMod l) * (b : ZMod l)) * hl0

lemma not_dvd (hN : 0 < N) (hl : l.Prime) : ¬ ((N : ℤ) * l ∣ N) := by
  intro hd
  have h1 := Int.le_of_dvd (by exact_mod_cast hN) hd
  have h2 : (2 : ℤ) ≤ l := by exact_mod_cast hl.two_le
  have h3 : (0 : ℤ) < N := by exact_mod_cast hN
  nlinarith

lemma rep_inj (hN : 0 < N) (hl : l.Prime) (o₁ o₂ : Option (Fin l))
    (hm : rep N l a b h o₁ * (rep N l a b h o₂)⁻¹ ∈ Gamma0 (N * l)) : o₁ = o₂ := by
  have hc : IsCoprime (N : ℤ) l := cop (h := h)
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  rw [mem_iff, mulInv_10] at hm
  push_cast at hm
  rcases o₁ with _ | i <;> rcases o₂ with _ | j
  · rfl
  · exfalso
    rw [rep_none_10, rep_none_11, rep_some_10] at hm
    exact not_dvd hN hl (by simpa using hm)
  · exfalso
    rw [rep_some_10, rep_none_11, rep_none_10] at hm
    exact not_dvd hN hl (by simpa using hm)
  · rw [rep_some_10, rep_some_11, rep_some_10, rep_some_11] at hm
    have e : (N : ℤ) * (N * (j : ℕ) + l * b) - (N * (i : ℕ) + l * b) * N =
        N * (N * (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ))) := by ring
    rw [e] at hm
    have h1 : (l : ℤ) ∣ N * (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) := (mul_dvd_mul_iff_left hN'.ne').1 hm
    have h2 : (l : ℤ) ∣ ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) := hc.symm.dvd_of_dvd_mul_left h1
    have h3 : ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd h2
      have := i.isLt
      have := j.isLt
      rw [abs_lt]
      constructor <;> omega
    congr 1
    ext
    omega

end

end GlobalTheory.HeckeFamilyMatrices.TrOld


open GlobalTheory.HeckeFamilyMatrices.TrOld in
theorem GlobalTheory.HeckeFamilyMatrices.chiInv_trOld : ∀ (N l : ℕ) (k : ℤ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1)
    (χ : DirichletCharacter ℂ N) (G : ℍ → ℂ), 0 < N → l.Prime → ChiInv k N (N * l) χ G →
    ChiInv k N N χ (trOld k N l a b h G) := by
  intro N l k a b h χ G hN hl hG γ hγ
  have : NeZero l := ⟨hl.ne_zero⟩
  have rep_mem : ∀ o, rep N l a b h o ∈ Gamma0 N := fun o => Gamma0_mem.2 (rep_10 o)
  have hsum : trOld k N l a b h G = ∑ o : Option (Fin l), G ∣[k] rep N l a b h o := by
    rw [Fintype.sum_option]
    simp only [rep, SlashAction.slash_one]
    unfold trOld
    congr 1
    exact (Fin.sum_univ_eq_sum_range (fun j => G ∣[k] gaOld N l a b h j) l).symm
  have hterm : ∀ o, (G ∣[k] rep N l a b h o) ∣[k] γ =
      χ ((mat γ 1 1 : ℤ) : ZMod N) • (G ∣[k] rep N l a b h (sig l (rep N l a b h o * γ))) := by
    intro o
    have hA : rep N l a b h o * γ ∈ Gamma0 N := mul_mem (rep_mem o) hγ
    have hη := sig_mem (h := h) hl _ hA
    have hA0 : ((mat (rep N l a b h o * γ) 1 0 : ℤ) : ZMod N) = 0 := Gamma0_mem.1 hA
    have hchar : ((mat (rep N l a b h o * γ * (rep N l a b h (sig l (rep N l a b h o * γ)))⁻¹) 1 1 : ℤ)
        : ZMod N) = ((mat γ 1 1 : ℤ) : ZMod N) := by
      rw [mulInv_11, rep_00]
      push_cast
      rw [hA0, mul_11]
      push_cast
      rw [rep_10, rep_11]
      ring
    have e : G ∣[k] (rep N l a b h o * γ) =
        (G ∣[k] (rep N l a b h o * γ * (rep N l a b h (sig l (rep N l a b h o * γ)))⁻¹)) ∣[k]
          rep N l a b h (sig l (rep N l a b h o * γ)) := by
      rw [← SlashAction.slash_mul, inv_mul_cancel_right]
    rw [← SlashAction.slash_mul, e, hG _ hη, ModularForm.SL_smul_slash, hchar]
  have hinj : Function.Injective (fun o => sig l (rep N l a b h o * γ)) := by
    intro o₁ o₂ he
    apply rep_inj (h := h) hN hl
    have h1 := sig_mem (h := h) hl _ (mul_mem (rep_mem o₁) hγ)
    have h2 := sig_mem (h := h) hl _ (mul_mem (rep_mem o₂) hγ)
    simp only at he
    rw [he] at h1
    have h3 := mul_mem h1 (inv_mem h2)
    convert h3 using 1
    group
  rw [hsum, SlashAction.sum_slash, Finset.sum_congr rfl (fun o _ => hterm o), ← Finset.smul_sum]
  congr 1
  exact (Finite.injective_iff_bijective.mp hinj).sum_comp (fun o => G ∣[k] rep N l a b h o)
end
end

section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

theorem _root_.GlobalTheory.T.slash_sub_qExpansion_partialSum_isBigO : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ℍ → ℂ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ → IsMF Γ k f → ∀ x : SL(2, ℤ), (fun τ : ℍ => (f ∣[k] x) τ - ∑ n ∈ Finset.range M, co M k f x n * Function.Periodic.qParam (M : ℝ) (τ : ℂ) ^ n) =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
  first | exact @GlobalTheory.OddFrame.slash_sub_partialSum_isBigO | exact GlobalTheory.OddFrame.slash_sub_partialSum_isBigO | (intros; apply GlobalTheory.OddFrame.slash_sub_partialSum_isBigO <;> assumption)
end

section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

theorem _root_.GlobalTheory.T.exists_odd_weight_frame_det_ne_zero : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (τ₀ : ℍ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ → (-1 : SL(2, ℤ)) ∉ Γ → IsReps Γ s → (∀ (ι : Type) [Fintype ι] (x : ι → SL(2, ℤ)) (c : ι → ℂ), (∀ i j, x i * (x j)⁻¹ ∈ CongruenceSubgroup.Gamma M → i = j) → (∀ (k : ℤ) (f : ℍ → ℂ), IsMF (CongruenceSubgroup.Gamma M) k f → ∑ i, c i * (f ∣[k] x i) τ₀ = 0) → c = 0) → ∃ (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ), (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) ∧ (evM s w F τ₀).det ≠ 0 := by
  first | exact @GlobalTheory.OddFrame.exists_odd_det_evM_ne_zero | exact GlobalTheory.OddFrame.exists_odd_det_evM_ne_zero | (intros; apply GlobalTheory.OddFrame.exists_odd_det_evM_ne_zero <;> assumption)
end
