module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1742
import GroundTheory.GlobalFields.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle204
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.Bundle009
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

namespace UpperTheory.Gal.Gen.IntegralMatrixDenominatorBound

open GlobalTheory.CongW (IntMat)

section
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private lemma natCast_int (u : HeightOneSpectrum (𝓞 E)) (l : ℕ) :
    (l : u.adicCompletion E) ∈ u.adicCompletionIntegers E :=
  _root_.natCast_mem (u.adicCompletionIntegers E) l

private lemma v_lt_one (u : HeightOneSpectrum (𝓞 E)) {l : ℕ} (hu : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal) :
    Valued.v (l : u.adicCompletion E) < 1 := by
  have h := (u.valuation_lt_one_iff_mem (K := E) ((l : ℕ) : 𝓞 E)).2 hu
  have h2 := u.valuedAdicCompletion_eq_valuation (K := E) ((l : ℕ) : 𝓞 E)
  rw [← h2] at h
  simpa using h

private lemma exists_pow_int (u : HeightOneSpectrum (𝓞 E)) {l : ℕ} (hu : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal)
    (y : u.adicCompletion E) : ∃ d : ℕ, (l : u.adicCompletion E) ^ d * y ∈ u.adicCompletionIntegers E := by
  by_cases hy : y = 0
  · exact ⟨0, by simp [hy]⟩
  have hv : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  obtain ⟨d, hd⟩ := exists_pow_lt₀ (v_lt_one u hu) (Units.mk0 _ (inv_ne_zero hv))
  refine ⟨d, ?_⟩
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_pow]
  have h0 : (0 : _) < Valued.v y := zero_lt_iff.2 hv
  have := mul_le_mul_left (le_of_lt hd) (Valued.v y)
  simpa [hv] using this

private lemma intMat_mono (u : HeightOneSpectrum (𝓞 E)) (l : ℕ) (m : Matrix (Fin a) (Fin a) (u.adicCompletion E))
    {d e : ℕ} (hde : d ≤ e) (h : IntMat u ((l : u.adicCompletion E) ^ d • m)) :
    IntMat u ((l : u.adicCompletion E) ^ e • m) := by
  intro i j
  have h1 := h i j
  simp only [Matrix.smul_apply, smul_eq_mul] at h1 ⊢
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hde
  rw [pow_add, mul_comm (_ ^ d), mul_assoc]
  exact mul_mem (pow_mem (natCast_int u l) k) h1

private lemma exists_intMat (u : HeightOneSpectrum (𝓞 E)) {l : ℕ} (hu : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal)
    (m : Matrix (Fin a) (Fin a) (u.adicCompletion E)) :
    ∃ d : ℕ, IntMat u ((l : u.adicCompletion E) ^ d • m) := by
  choose D hD using fun p : Fin a × Fin a => exists_pow_int u hu (m p.1 p.2)
  refine ⟨Finset.univ.sup D, fun i j => ?_⟩
  have hle : D (i, j) ≤ Finset.univ.sup D := Finset.le_sup (Finset.mem_univ _)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [hk, pow_add, mul_comm (_ ^ D (i, j)), mul_assoc]
  exact mul_mem (pow_mem (natCast_int u l) k) (hD (i, j))

private lemma isOpen_intMat {X : Type*} [TopologicalSpace X] (u : HeightOneSpectrum (𝓞 E)) (c : u.adicCompletion E)
    (f : X → Matrix (Fin a) (Fin a) (u.adicCompletion E)) (hf : Continuous f) :
    IsOpen {x | IntMat u (c • f x)} := by
  have e : {x | IntMat u (c • f x)} = ⋂ i, ⋂ j, {x | c * f x i j ∈ u.adicCompletionIntegers E} := by
    ext x
    simp [IntMat]
  rw [e]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  have hc : Continuous fun x => c * f x i j :=
    continuous_const.mul ((continuous_apply j).comp ((continuous_apply i).comp hf))
  exact (GroundTheory.Global.isOpen_adicCompletionIntegers u).preimage hc

end

end UpperTheory.Gal.Gen.IntegralMatrixDenominatorBound

open GlobalTheory.CongW (IntMat) in
open UpperTheory.Gal.Gen.IntegralMatrixDenominatorBound in
theorem UpperTheory.Gal.Gen.denomBdd_pf :
    UpperTheory.Gal.Gen.DenomBdd := by
  intro E _ _ _ l hl n Z hZ
  have hl0 : ((l : ℕ) : 𝓞 E) ≠ 0 := by
    exact_mod_cast hl.ne_zero
  have hS : {u : HeightOneSpectrum (𝓞 E) | ((l : ℕ) : 𝓞 E) ∈ u.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {((l : ℕ) : 𝓞 E)}) ?_).subset ?_
    · simpa using hl0
    · intro u hu
      exact Ideal.dvd_span_singleton.2 hu
  have hopen : ∀ d : ℕ, IsOpen {g : UA E n | DenomLe l d g} := by
    intro d
    have e : {g : UA E n | DenomLe l d g} = ⋂ u ∈ {u : HeightOneSpectrum (𝓞 E) | ((l : ℕ) : 𝓞 E) ∈ u.asIdeal},
        ({g : UA E n | IntMat u (((l : u.adicCompletion E) ^ d) • ((cLoc u g : GL (Fin n) (u.adicCompletion E)) :
          Matrix (Fin n) (Fin n) (u.adicCompletion E)))} ∩
        {g : UA E n | IntMat u (((l : u.adicCompletion E) ^ d) • (((cLoc u g)⁻¹ : GL (Fin n) (u.adicCompletion E)) :
          Matrix (Fin n) (Fin n) (u.adicCompletion E)))}) := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff, DenomLe]
    rw [e]
    refine hS.isOpen_biInter fun u _ => ?_
    exact (isOpen_intMat u _ _ (Units.continuous_val.comp (GlobalTheory.BCT.GlobLev.continuous_cLoc u))).inter
      (isOpen_intMat u _ _ (Units.continuous_coe_inv.comp (GlobalTheory.BCT.GlobLev.continuous_cLoc u)))
  have hmono : ∀ {d e : ℕ}, d ≤ e → ∀ g : UA E n, DenomLe l d g → DenomLe l e g :=
    fun hde g h u hu => ⟨intMat_mono u l _ hde (h u hu).1, intMat_mono u l _ hde (h u hu).2⟩
  have hcover : ∀ g : UA E n, ∃ d : ℕ, DenomLe l d g := by
    intro g
    have h1 : ∀ u : HeightOneSpectrum (𝓞 E), ∃ d : ℕ, ((l : ℕ) : 𝓞 E) ∈ u.asIdeal →
        IntMat u (((l : u.adicCompletion E) ^ d) • ((cLoc u g : GL (Fin n) (u.adicCompletion E)) :
          Matrix (Fin n) (Fin n) (u.adicCompletion E))) ∧
        IntMat u (((l : u.adicCompletion E) ^ d) • (((cLoc u g)⁻¹ : GL (Fin n) (u.adicCompletion E)) :
          Matrix (Fin n) (Fin n) (u.adicCompletion E))) := by
      intro u
      by_cases hu : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal
      · obtain ⟨d₁, h₁⟩ := exists_intMat u hu ((cLoc u g : GL (Fin n) (u.adicCompletion E)) :
          Matrix (Fin n) (Fin n) (u.adicCompletion E))
        obtain ⟨d₂, h₂⟩ := exists_intMat u hu (((cLoc u g)⁻¹ : GL (Fin n) (u.adicCompletion E)) :
          Matrix (Fin n) (Fin n) (u.adicCompletion E))
        exact ⟨max d₁ d₂, fun _ => ⟨intMat_mono u l _ (le_max_left _ _) h₁, intMat_mono u l _ (le_max_right _ _) h₂⟩⟩
      · exact ⟨0, fun h => absurd h hu⟩
    choose D hD using h1
    refine ⟨hS.toFinset.sup D, fun u hu => ?_⟩
    have hle : D u ≤ hS.toFinset.sup D := Finset.le_sup (hS.mem_toFinset.2 hu)
    exact ⟨intMat_mono u l _ hle (hD u hu).1, intMat_mono u l _ hle (hD u hu).2⟩
  obtain ⟨d, hd⟩ := hZ.elim_directed_cover (fun d : ℕ => {g : UA E n | DenomLe l d g}) hopen
    (fun g _ => Set.mem_iUnion.2 (hcover g))
    (directed_of_isDirected_le fun _ _ hde g hg => hmono hde g hg)
  exact ⟨d, fun g hg => hd hg⟩
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

private theorem cAll_fin' {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {c : UA E n}
    (hc : c ∈ finU (E := E) (n := n)) : cAll c = 1 := by
  funext v
  have : cInf c = 1 := hc
  simp [cAll, cEmb, this]

theorem UpperTheory.Gal.Gen.frameW_pf :
    UpperTheory.Gal.Gen.Kappa → UpperTheory.Gal.Gen.DenomBdd → UpperTheory.Gal.Gen.RhoBound → UpperTheory.Gal.Gen.LatFacts → UpperTheory.Gal.Gen.LevelEx → UpperTheory.Gal.Gen.FrameW := by
  intro hK hD hR hL hE E _ _ _ l _ ι a W J t ht
  classical
  have hlp : l.Prime := Fact.out
  obtain ⟨κ, hκr, hκi, hκd⟩ := hK E l ι a
  let ρ := Formalism.L2.DIV.rhoK (K := ℂ) (ι := InfinitePlace E) W
  let M : UA E a → (InfinitePlace E → GL (Fin a) ℂ) := fun g => (cAll g)⁻¹ * κ g
  let b : UA E a → {x : W.Sp // CoefLe ι 1 x.1} → W.Sp := fun g x => ρ (M g) x.1
  have hl1 : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hlp.one_lt.le
  have hpow : ∀ d : ℕ, (1 : ℝ) ≤ (l : ℝ) ^ d := fun d => one_le_pow₀ hl1
  have hgrow : ∀ (c : UA E a) (d : ℕ), DenomLe l d c → ∀ x : W.Sp, CoefLe ι 1 x.1 →
      CoefLe ι (((l : ℝ) ^ d) ^ (a * GlobalTheory.CongW.wtSize W.at)) (ρ (κ c) x).1 := fun c d hc x hx =>
    hR E l ι a W (κ c) _ (hpow d) (fun τ i j => hκd c d hc τ i j) x hx
  have hgrowInv : ∀ (c : UA E a) (d : ℕ), DenomLe l d c → ∀ x : W.Sp, CoefLe ι 1 x.1 →
      CoefLe ι (((l : ℝ) ^ d) ^ (a * GlobalTheory.CongW.wtSize W.at)) (ρ (κ c)⁻¹ x).1 := fun c d hc x hx =>
    hR E l ι a W (κ c)⁻¹ _ (hpow d) (fun τ i j => by
      have h := hκd c d hc τ i j
      simp only [Pi.inv_apply, inv_inv]
      exact ⟨h.2, h.1⟩) x hx
  have hval : ∀ f : algForms W, ∀ γ ∈ ratU E a, ∀ s x, x ∈ infU E a → ∀ c : finU (E := E) (n := a),
      (∀ v g, f.1 v (g * (c : UA E a)) = f.1 v g) → ∀ v,
      f.1 (ρ (M (γ * s * x * c)) v) (γ * s * x * c) = f.1 (ρ (M s) (ρ (κ (c : UA E a)) v)) s := by
    intro f γ hγ s x hx c hf v
    have hM : cAll x * M (γ * s * x * c) = M s * κ (c : UA E a) := by
      simp only [M, map_mul, hκr γ hγ, hκi x hx, cAll_fin' c.2, mul_one]
      group
    have hA : ∀ v, f.1 v (γ * s * x * c) = f.1 v (s * c * x) := by
      intro v
      rw [mul_assoc γ s, mul_assoc γ, (f.2.1 v).left γ hγ, mul_assoc s x, ← fin_mul_inf c.2 hx, ← mul_assoc]
    have hB : ∀ v, f.1 v (s * c * x) = f.1 (W.rep ⟨x, hx⟩ v) (s * c) := by
      intro v
      rw [f.2.2 ⟨x, hx⟩ v]
      rfl
    have e3 : W.rep ⟨x, hx⟩ (ρ (M (γ * s * x * c)) v) = ρ (M s) (ρ (κ (c : UA E a)) v) := by
      change ρ (cAll x) (ρ (M _) v) = _
      rw [← Module.End.mul_apply, ← map_mul, hM, map_mul, Module.End.mul_apply]
    rw [hA, hB, hf, e3]
  refine ⟨{x : W.Sp // CoefLe ι 1 x.1}, b, ?_, ?_, ?_⟩
  · intro f
    obtain ⟨C, hC, hfC⟩ := hE E a W f
    obtain ⟨d, hd⟩ := hD E l hlp a C hC.compact
    let C₃ : Subgroup (finU (E := E) (n := a)) := C.subgroupOf (finU (E := E) (n := a))
    have hC₃o : IsOpen (C₃ : Set (finU (E := E) (n := a))) := by
      obtain ⟨N, hNo, hN1, hNC⟩ := hC.isOpen
      refine Subgroup.isOpen_of_mem_nhds _ (g := 1)
        (Filter.mem_of_superset ((hNo.preimage continuous_subtype_val).mem_nhds hN1) ?_)
      intro x hx
      exact Subgroup.mem_subgroupOf.2 (hNC ⟨hx, x.2⟩)
    obtain ⟨S, hS⟩ := GlobalTheory.DefU.ClassFin.classSet_finite E a C₃ hC₃o
    let φ : UA E a → (W.Sp →ₗ[ℂ] ℂ) := fun s => (LinearMap.proj s) ∘ₗ f.1 ∘ₗ (ρ (M s))
    have hφ : ∀ s, ∃ m : ℝ, 0 ≤ m ∧ ∀ (R : ℝ) (x : W.Sp), CoefLe ι R x.1 → ‖ι.symm (φ s x)‖ ≤ m * R :=
      fun s => (hL l ι _ (Formalism.L2.DIV.VV ℂ W)).1 (φ s)
    choose m hm0 hm using hφ
    refine ⟨(∑ s ∈ S, m s) * ((l : ℝ) ^ d) ^ (a * GlobalTheory.CongW.wtSize W.at), fun g i => ?_⟩
    obtain ⟨γ, hγ, s, hs, y, hy, c, hc, rfl⟩ := hS g
    have hcC : (c : UA E a) ∈ C := Subgroup.mem_subgroupOf.1 hc
    have e := hval f γ hγ s y hy c (fun v g => hfC _ hcC v g) i.1
    have hb : f.1 (b (γ * s * y * c) i) (γ * s * y * c) = φ s (ρ (κ (c : UA E a)) i.1) := e
    rw [hb]
    refine (hm s _ _ (hgrow _ d (hd _ hcC) i.1 i.2)).trans ?_
    exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun q _ => hm0 q) hs) (by positivity)
  · intro f h0
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    funext g
    obtain ⟨c, hc0, hc⟩ := (hL l ι _ (Formalism.L2.DIV.VV ℂ W)).2 (ρ (M g)⁻¹ v)
    have h1 := h0 g ⟨c • ρ (M g)⁻¹ v, hc⟩
    have h2 : b g ⟨c • ρ (M g)⁻¹ v, hc⟩ = c • v := by
      change ρ (M g) (c • ρ (M g)⁻¹ v) = c • v
      rw [map_smul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [h2, map_smul, Pi.smul_apply, smul_eq_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_left hc0
  · intro F R hF j g i
    have hR0 : 0 ≤ R := (norm_nonneg _).trans (hF g i)
    have e : opOf (RU E a) (t j) (F (b g i)) g = ∑ h ∈ (t j).support, t j h * F (b g i) (g * h) := by
      simp only [opOf, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, RU_apply, smul_eq_mul]

    rw [e, map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hR0 fun h hh => ?_
    obtain ⟨hfin, d, hd, hn⟩ := ht j h hh
    have hMh : M g = M (g * h) * (κ h)⁻¹ := by
      simp only [M, map_mul, cAll_fin' hfin, mul_one]
      group
    set y : W.Sp := ρ (κ h)⁻¹ i.1 with hy
    have hyc := hgrowInv h d hd i.1 i.2
    have hx : CoefLe ι 1 ((t j h • y : W.Sp) : Formalism.L2.DIV.Pol ℂ (InfinitePlace E) a) := by
      intro q
      have hq := hyc q
      have e1 : AddMonoidAlgebra.coeff ((t j h • y : W.Sp) : Formalism.L2.DIV.Pol ℂ (InfinitePlace E) a) q =
          t j h * AddMonoidAlgebra.coeff (y : Formalism.L2.DIV.Pol ℂ (InfinitePlace E) a) q := by
        simp [MvPolynomial.coeff_smul]
      rw [e1, map_mul, norm_mul]
      have hlpos : (0 : ℝ) < (l : ℝ) := by linarith
      calc _ ≤ ((l : ℝ)⁻¹) ^ (a * d * GlobalTheory.CongW.wtSize W.at) * ((l : ℝ) ^ d) ^ (a * GlobalTheory.CongW.wtSize W.at) :=
            mul_le_mul hn hq (norm_nonneg _) (by positivity)
        _ = 1 := by
            rw [← pow_mul, inv_pow, show d * (a * GlobalTheory.CongW.wtSize W.at) = a * d * GlobalTheory.CongW.wtSize W.at by ring]
            exact inv_mul_cancel₀ (by positivity)
    have hb : t j h * F (b g i) (g * h) = F (b (g * h) ⟨t j h • y, hx⟩) (g * h) := by
      have : b g i = ρ (M (g * h)) y := by
        change ρ (M g) i.1 = _
        rw [hMh, map_mul, Module.End.mul_apply]
      change _ = F (ρ (M (g * h)) (t j h • y)) (g * h)
      rw [this, map_smul, map_smul, Pi.smul_apply, smul_eq_mul]
    rw [hb]
    exact hF _ _
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.charSum_pf :
    UpperTheory.Gal.Gen.CharSum := by
  intro N _
  have hN : N ≠ 0 := NeZero.ne N
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ N := ⟨_, Complex.isPrimitiveRoot_exp N hN⟩
  have hz0 : ζ ≠ 0 := hζ.ne_zero hN
  let u : ℂˣ := Units.mk0 ζ hz0
  have huN : u ^ N = 1 := by
    ext
    simp [u, hζ.pow_eq_one]
  have hu : ∀ j : ℕ, (u ^ j) ^ N = 1 := by
    intro j
    rw [← pow_mul, mul_comm, pow_mul, huN, one_pow]
  let χ : Fin N → (Multiplicative (ZMod N) →* ℂˣ) := fun j => GlobalTheory.CongSc.zchar (u ^ (j : ℕ)) (hu j)
  have hval : ∀ (j : Fin N) (x : Multiplicative (ZMod N)),
      ((χ j x : ℂˣ) : ℂ) = (ζ ^ (j : ℕ)) ^ (Multiplicative.toAdd x).val := by
    intro j x
    simp [χ, GlobalTheory.CongSc.zchar_apply, u]
  have hone : ∀ j : Fin N, j ≠ 0 → ((χ j (Multiplicative.ofAdd 1) : ℂˣ) : ℂ) = ζ ^ (j : ℕ) := by
    intro j hj
    rw [hval]
    have hj' : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h)
    have h1 : 1 < N := by
      have := j.isLt
      omega
    rw [toAdd_ofAdd, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt h1, pow_one]
  refine ⟨(Finset.univ.erase 0).image χ, ?_, ?_⟩
  · intro c hc
    rw [Finset.mem_image] at hc
    obtain ⟨j, hj, rfl⟩ := hc
    have hj0 : j ≠ 0 := Finset.ne_of_mem_erase hj
    intro h
    have h2 : ζ ^ (j : ℕ) = 1 := by
      rw [← hone j hj0, h]
      simp
    have hd := (hζ.pow_eq_one_iff_dvd (j : ℕ)).mp h2
    exact hj0 (Fin.ext (Nat.eq_zero_of_dvd_of_lt hd j.isLt))
  · intro x
    rw [Finset.sum_image (by
      intro j hj k hk hjk
      have hj0 : j ≠ 0 := Finset.ne_of_mem_erase hj
      have hk0 : k ≠ 0 := Finset.ne_of_mem_erase hk
      have h3 := hone j hj0
      rw [hjk, hone k hk0] at h3
      exact (Fin.ext (hζ.pow_inj k.isLt j.isLt h3)).symm)]
    simp_rw [hval]
    have key := GlobalTheory.CongSc.sum_roots hζ (Multiplicative.toAdd x).val (ZMod.val_lt _)
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : Fin N))] at key
    simp only [Fin.val_zero, pow_zero, one_pow] at key
    split_ifs at key
    · exact Or.inr key
    · exact Or.inl key
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen
open GroundTheory.Automorphic

private theorem norm_unif_lt_one (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    {x : w.adicCompletion E} (hx : Formalism.UG.IsUnifV E w x) : ‖x‖ < 1 := by
  have hv : Valued.v x < 1 := by
    rw [hx]
    exact_mod_cast (by decide : (Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) < 1)
  exact Valued.toNormedField.norm_lt_one_iff.mpr hv

private theorem nonneg_of_pow_mem (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : ℕ)
    (hU : ‖(GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E)‖ < 1)
    {Z : Set (GL (Fin a) (w.adicCompletion E))} (hZ : IsCompact Z) (ν : Fin a → ℤ)
    (hν : ∀ m : ℕ, Cartan.diagPow (w.adicCompletion E) a ν ^ m ∈ Z) (i : Fin a) : 0 ≤ ν i := by
  by_contra hneg
  push_neg at hneg
  set ϖ : w.adicCompletion E := (GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E) with hϖ
  have h0 : ϖ ≠ 0 := Cartan.uniformizer_ne_zero _
  have hf : Continuous fun x : GL (Fin a) (w.adicCompletion E) =>
      (x : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i i :=
    Continuous.matrix_elem Units.continuous_val i i
  obtain ⟨C, hC⟩ := (hZ.image hf).isBounded.exists_norm_le
  have hentry : ∀ m : ℕ, ‖ϖ ^ ν i‖ ^ m ≤ C := by
    intro m
    have h : ‖((Cartan.diagPow (w.adicCompletion E) a ν ^ m : GL (Fin a) (w.adicCompletion E)) :
        Matrix (Fin a) (Fin a) (w.adicCompletion E)) i i‖ ≤ C := hC _ ⟨_, hν m, rfl⟩
    rw [Units.val_pow_eq_pow_val, Cartan.coe_diagPow, Matrix.diagonal_pow, Matrix.diagonal_apply_eq,
      Pi.pow_apply, norm_pow] at h
    exact h
  have hgt : 1 < ‖ϖ ^ ν i‖ := by
    rw [norm_zpow]
    have hp : 0 < ‖ϖ‖ := norm_pos_iff.2 h0
    exact one_lt_zpow_of_neg₀ hp hU hneg
  obtain ⟨m, hm⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hgt).eventually (Filter.eventually_gt_atTop C)).exists
  exact absurd (hentry m) (not_le.2 hm)

theorem UpperTheory.Gal.Gen.maxCpt_pf :
    UpperTheory.Gal.Gen.MaxCpt := by
  intro E _ _ w a H Z hZ hHZ hKH g hg
  obtain ⟨hK, hU, -⟩ := UpperTheory.V.Af.Smo.sphDict E a w
  obtain ⟨μ, -, k₁, hk₁, k₂, hk₂, rfl⟩ := Cartan.exists_eq_mul_diagPow_mul (w.adicCompletion E) a g
  rw [hK] at hk₁ hk₂
  have hD : Cartan.diagPow (w.adicCompletion E) a μ ∈ H := by
    have h := H.mul_mem (H.mul_mem (H.inv_mem (hKH hk₁)) hg) (H.inv_mem (hKH hk₂))
    simpa [mul_assoc] using h
  have hinv : Cartan.diagPow (w.adicCompletion E) a (-μ) = (Cartan.diagPow (w.adicCompletion E) a μ)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left (Units.ext ?_)
    rw [Units.val_mul, Cartan.coe_diagPow, Cartan.coe_diagPow, Matrix.diagonal_mul_diagonal, Units.val_one,
      ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← zpow_add₀ (Cartan.uniformizer_ne_zero _)]
    simp
  have hn := norm_unif_lt_one E w hU
  have h1 := nonneg_of_pow_mem E w a hn hZ μ fun m => hHZ (H.pow_mem hD m)
  have h2 := nonneg_of_pow_mem E w a hn hZ (-μ) fun m => hHZ (hinv ▸ H.pow_mem (H.inv_mem hD) m)
  have hμ : μ = 0 := by
    funext i
    have := h1 i
    have := h2 i
    simp only [Pi.neg_apply] at *
    simp only [Pi.zero_apply]
    omega
  have hone : Cartan.diagPow (w.adicCompletion E) a μ = 1 := by
    refine Units.ext ?_
    rw [Cartan.coe_diagPow, hμ]
    simp
  rw [hone, mul_one]
  exact (GlobalTheory.LFun.KGL w (n := a)).mul_mem hk₁ hk₂
end
