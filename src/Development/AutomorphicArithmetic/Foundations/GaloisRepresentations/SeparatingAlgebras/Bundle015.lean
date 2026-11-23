module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1742
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle212
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle210
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.tyStep_pf :
    UpperTheory.Gal.Gen.LevFacts → UpperTheory.Gal.Gen.Ell → UpperTheory.Gal.Gen.KerOpen → UpperTheory.Gal.Gen.CharSum → UpperTheory.Gal.Gen.TwistPart → UpperTheory.Gal.Gen.TyStep := by
  intro hLev hEll hKer hCS hTw E _ _ _ l _ ι a w₀ hs K hK W J hJo hJc htf m θ f hf
  classical
  obtain ⟨hLvl, -, hC, -, -, -⟩ := hLev E a w₀ hs K hK J hJo hJc
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  haveI : Finite (Multiplicative (ZMod (l ^ m))) :=
    inferInstanceAs (Finite (ZMod (l ^ m)))
  let lam : (lev K w₀ J) →* Multiplicative (ZMod (l ^ m)) :=
    θ.comp (((cLoc w₀).comp (lev K w₀ J).subtype).codRestrict J fun c => hC c.1 c.2)
  have hlam : ∀ c : lev K w₀ J, lam c = θ ⟨cLoc w₀ c.1, hC c.1 c.2⟩ := fun c => rfl
  obtain ⟨N, hNo, hN1, hN⟩ := hKer E w₀ a J hJo _ θ
  obtain ⟨ℓ, hℓi, hℓC, hℓa⟩ := hEll E a (lev K w₀ J) hLvl _ lam
    ⟨cLoc w₀ ⁻¹' N, hNo.preimage (GlobalTheory.BCT.GlobLev.continuous_cLoc w₀), by simpa using hN1,
      fun c hc => hN ⟨cLoc w₀ c.1, hC c.1 c.2⟩ hc⟩
    (fun c hc => by
      obtain ⟨k, hk0, hk⟩ := isOfFinOrder_iff_pow_eq_one.1 hc
      have h1 : (cLoc w₀ c.1) ^ k = 1 := by
        have h0 : c.1 ^ k = 1 := by simpa using congrArg Subtype.val hk
        rw [← map_pow, h0, map_one]
      have h2 := htf _ (hC c.1 c.2) k hk0 h1
      have h3 : (⟨cLoc w₀ c.1, hC c.1 c.2⟩ : J) = 1 := Subtype.ext h2
      rw [hlam, h3, map_one])
  obtain ⟨s, hs1, hs2⟩ := hCS (l ^ m)
  have hex : ∀ χ : Multiplicative (ZMod (l ^ m)) →* ℂˣ,
      ∃ F : algForms W, ∀ v g, F.1 v g = ((χ (ℓ g) : ℂˣ) : ℂ) * f.1 v g := fun χ =>
    GlobalTheory.T.exists_algebraicModularForm_mul_archInvariant E a W f (fun g => ((χ (ℓ g) : ℂˣ) : ℂ)) (hℓa fun y => ((χ y : ℂˣ) : ℂ))
      fun g x hx => by simp only [hℓi g x hx]
  choose F hF using hex
  have hpart : ∀ χ ∈ s, F χ ∈ part W K
      (fun U => ∃ χ : Multiplicative (ZMod (l ^ m)) →* ℂˣ, χ ≠ 1 ∧ GlobalTheory.CongW.HasTypeVec w₀ K J θ χ U) := by
    intro χ hχ
    have h := hTw E a w₀ K W J _ θ χ hC (fun k hk => hK.one k hk w₀ (not_apart_self w₀)) (F χ)
      (fun c hc v g => by
        rw [hF, hF, hℓC g ⟨c, hc⟩, hf c hc v g, map_mul, Units.val_mul, hlam, mul_comm (((χ (ℓ g) : ℂˣ) : ℂ))]
        ring)
    refine (?_ : part W K _ ≤ part W K _) h
    exact iSup₂_le fun π hπ => le_iSup₂_of_le π ⟨χ, hs1 χ hχ, hπ⟩ le_rfl
  refine ⟨-∑ χ ∈ s, F χ, neg_mem (sum_mem hpart), fun g => 1 + ∑ χ ∈ s, ((χ (ℓ g) : ℂˣ) : ℂ), ?_, ?_⟩
  · intro g
    rcases hs2 (ℓ g) with h | h
    · simp only [h, map_zero, norm_zero]
      positivity
    · simp only [h]
      rw [map_natCast, Nat.cast_pow, norm_pow]
  · intro v g
    have e : ((-∑ χ ∈ s, F χ : algForms W) : W.Sp →ₗ[ℂ] (UA E a → ℂ)) v g = -∑ χ ∈ s, (F χ).1 v g := by
      simp [Finset.sum_apply, LinearMap.sum_apply]
    change f.1 v g - ((-∑ χ ∈ s, F χ : algForms W) : W.Sp →ₗ[ℂ] (UA E a → ℂ)) v g = _
    rw [e, Finset.sum_congr rfl fun χ _ => hF χ v g, ← Finset.sum_mul]
    ring
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

private theorem norm_map_integer_le_one {E : Type} [Field E] [NumberField E] (l : ℕ) [Fact l.Prime]
    (u : HeightOneSpectrum (𝓞 E)) (j : u.adicCompletion E →+* Qbar l) (hl : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal)
    (hj : Continuous j) (y : u.adicCompletion E) (hy : y ∈ u.adicCompletionIntegers E) : ‖j y‖ ≤ 1 := by
  have hvl : Valued.v ((l : ℕ) : u.adicCompletion E) < 1 := by
    have h1 : u.valuation E (((l : ℕ) : 𝓞 E) : E) < 1 :=
      (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) u _).2 hl
    have h2 : (((l : ℕ) : u.adicCompletion E)) = algebraMap E (u.adicCompletion E) (((l : ℕ) : 𝓞 E) : E) := by simp
    rw [h2]
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u _).trans_lt h1
  have hlnorm : ‖j ((l : ℕ) : u.adicCompletion E)‖ = (l : ℝ)⁻¹ := by
    have h0 : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [map_natCast, h0, PadicAlgCl.norm_extends (p := l) (l : ℚ_[l]), Padic.norm_p]
  have hlt : ∀ k : ℕ, ‖j ((l : ℕ) : u.adicCompletion E)‖ * ‖j y‖ ^ k < 1 := by
    intro k
    have hyv : Valued.v y ≤ 1 := hy
    have hv : Valued.v (((l : ℕ) : u.adicCompletion E) * y ^ k) < 1 := by
      rw [map_mul, map_pow]
      exact mul_lt_one_of_lt_of_le hvl (pow_le_one' hyv k)
    have ht := Valued.tendsto_zero_pow_of_v_lt_one hv
    have ht2 : Filter.Tendsto (fun m : ℕ => (j (((l : ℕ) : u.adicCompletion E) * y ^ k)) ^ m) Filter.atTop (nhds 0) := by
      have := (hj.tendsto 0).comp ht
      simpa [Function.comp_def, map_pow] using this
    have := tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.1 ht2
    simpa [map_mul, map_pow, norm_mul, norm_pow] using this
  by_contra hcon
  have hgt : 1 < ‖j y‖ := not_le.1 hcon
  have hlpos : 0 < ‖j ((l : ℕ) : u.adicCompletion E)‖ := by
    rw [hlnorm]
    exact inv_pos.2 (by exact_mod_cast (Fact.out : l.Prime).pos)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (‖j ((l : ℕ) : u.adicCompletion E)‖⁻¹) hgt
  have := hlt k
  have h3 : 1 < ‖j ((l : ℕ) : u.adicCompletion E)‖ * ‖j y‖ ^ k := by
    rw [inv_lt_iff_one_lt_mul₀ hlpos] at hk
    exact hk.trans_eq (mul_comm _ _)
  linarith

private theorem norm_map_entry_le {E : Type} [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] {n : ℕ}
    (u : HeightOneSpectrum (𝓞 E)) (j : u.adicCompletion E →+* Qbar l) (hl : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal)
    (hj : Continuous j) (d : ℕ) (M : Matrix (Fin n) (Fin n) (u.adicCompletion E))
    (hM : GlobalTheory.CongW.IntMat u (((l : u.adicCompletion E) ^ d) • M)) (a b : Fin n) : ‖j (M a b)‖ ≤ (l : ℝ) ^ d := by
  have h1 := norm_map_integer_le_one l u j hl hj _ (hM a b)
  have hlnorm : ‖j ((l : ℕ) : u.adicCompletion E)‖ = (l : ℝ)⁻¹ := by
    have h0 : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [map_natCast, h0, PadicAlgCl.norm_extends (p := l) (l : ℚ_[l]), Padic.norm_p]
  have hl0 : (0 : ℝ) < (l : ℝ) ^ d := pow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) d
  rw [Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, norm_mul, norm_pow, hlnorm, inv_pow] at h1
  rwa [inv_mul_le_iff₀ hl0, mul_one] at h1

theorem UpperTheory.Gal.Gen.kappa_pf :
    UpperTheory.Gal.Gen.Kappa := by
  intro E _ _ _ l _ ι n
  have hex := fun v : InfinitePlace E =>
    GlobalTheory.LadicInf.exists_place E l (ι.symm.toRingHom.comp v.embedding)
  choose u j hl hj hjE using hex
  let f : InfinitePlace E → Af E →+* ℂ := fun v =>
    ι.toRingHom.comp ((j v).comp (pLoc E (u v)))
  let κ : UA E n →* (InfinitePlace E → GL (Fin n) ℂ) :=
    MonoidHom.pi fun v => (Matrix.GeneralLinearGroup.map ((f v).comp (pFin E))).comp (UA E n).subtype
  have hκ : ∀ (g : UA E n) (v : InfinitePlace E),
      κ g v = Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (j v)) (cLoc (u v) g) := by
    intro g v
    ext
    rfl
  refine ⟨κ, ?_, ?_, ?_⟩
  · rintro γ ⟨g₀, hg₀⟩
    funext v
    ext a b
    change (f v) (pFin E ((γ.1 : Matrix (Fin n) (Fin n) (Ad E)) a b)) =
      coord v.embedding (pInf E ((γ.1 : Matrix (Fin n) (Fin n) (Ad E)) a b))
    have hg₁ : (γ.1 : GL (Fin n) (Ad E)) = ratGL E n g₀ := hg₀.symm
    rw [hg₁]
    change (f v) (pFin E (algebraMap E (Ad E) ((g₀ : Matrix (Fin n) (Fin n) E) a b))) =
      coord v.embedding (pInf E (algebraMap E (Ad E) ((g₀ : Matrix (Fin n) (Fin n) E) a b)))
    rw [coord_algebraMap]
    have h := congrArg (fun φ : E →+* Qbar l => φ ((g₀ : Matrix (Fin n) (Fin n) E) a b)) (hjE v)
    simp only [RingHom.coe_comp, Function.comp_apply] at h
    change ι (j v (algebraMap E (u v |>.adicCompletion E) _)) = _
    rw [h]
    simp
  · intro x hx
    funext v
    have hx' : Matrix.GeneralLinearGroup.map (pFin E) x.1 = 1 := hx
    have h2 : Matrix.GeneralLinearGroup.map ((f v).comp (pFin E)) x.1 =
        Matrix.GeneralLinearGroup.map (f v) (Matrix.GeneralLinearGroup.map (pFin E) x.1) := by ext; rfl
    change Matrix.GeneralLinearGroup.map ((f v).comp (pFin E)) x.1 = 1
    rw [h2, hx', map_one]
  · intro g d hd v a b
    obtain ⟨h1, h2⟩ := hd (u v) (hl v)
    constructor
    · rw [hκ g v]
      change ‖ι.symm (ι (j v (((cLoc (u v) g : GL (Fin n) ((u v).adicCompletion E)) :
        Matrix (Fin n) (Fin n) ((u v).adicCompletion E)) a b)))‖ ≤ _
      rw [RingEquiv.symm_apply_apply]
      exact norm_map_entry_le l (u v) (j v) (hl v) (hj v) d _ h1 a b
    · rw [hκ g v, ← map_inv]
      change ‖ι.symm (ι (j v ((((cLoc (u v) g)⁻¹ : GL (Fin n) ((u v).adicCompletion E)) :
        Matrix (Fin n) (Fin n) ((u v).adicCompletion E)) a b)))‖ ≤ _
      rw [RingEquiv.symm_apply_apply]
      exact norm_map_entry_le l (u v) (j v) (hl v) (hj v) d _ h2 a b
end
