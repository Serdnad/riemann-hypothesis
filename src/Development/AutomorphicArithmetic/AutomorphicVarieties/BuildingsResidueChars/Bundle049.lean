module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle030
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle029
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Mon
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

theorem UpperTheory.traces_from_eigenvalues_rank2 :
    ∀ (p h e : ℕ), ∀ D : EigData 2 p ![(e : ℤ), -(e : ℤ)] 0, ∃ (T : TrData (p ^ h) e) (u : D.S ≃ T.S), ∀ s, T.t (u s) = 1 + ((D.β s).map fun b => b⁻¹ ^ h).sum := by
  intro p h e D
  refine ⟨⟨D.S, D.fin, fun s => 1 + ((D.β s).map fun b => b⁻¹ ^ h).sum, ?_, ?_, ?_⟩, Equiv.refl _, fun s => rfl⟩
  · intro σ
    obtain ⟨u, hu⟩ := D.conj σ
    refine ⟨u, fun s => ?_⟩
    rw [hu, map_add (f := _), map_one, map_multiset_sum, Multiset.map_map, Multiset.map_map]
    congr 2
    refine Multiset.map_congr rfl fun b _ => ?_
    simp only [Function.comp, map_pow, map_inv₀]
  · intro s
    obtain ⟨x, y, hxy⟩ := Multiset.card_eq_two.1 (D.card s)
    have hx : ‖x‖ = 1 := by simpa using D.pure s x (by rw [hxy]; simp)
    have hy : ‖y‖ = 1 := by simpa using D.pure s y (by rw [hxy]; simp)
    have e1 : ((D.β s).map fun b => b⁻¹ ^ h).sum = x⁻¹ ^ h + y⁻¹ ^ h := by
      rw [hxy]; simp
    have h1 : ‖x⁻¹ ^ h‖ = 1 := by simp [hx]
    have h2 : ‖y⁻¹ ^ h‖ = 1 := by simp [hy]
    rw [e1]
    have h3 := norm_add_le (1 : ℂ) (x⁻¹ ^ h + y⁻¹ ^ h)
    have h4 := norm_add_le (x⁻¹ ^ h) (y⁻¹ ^ h)
    rw [norm_one] at h3
    linarith
  · intro s
    obtain ⟨x, y, hxy⟩ := Multiset.card_eq_two.1 (D.card s)
    have hm : ∀ i, (![(e : ℤ), -(e : ℤ)] : Fin 2 → ℤ) i ≤ (e : ℤ) := by
      intro i
      fin_cases i
      · simp
      · simp
    have hx := D.intInv e hm s x (by rw [hxy]; simp)
    have hy := D.intInv e hm s y (by rw [hxy]; simp)
    rw [zpow_natCast] at hx hy
    have e1 : ((D.β s).map fun b => b⁻¹ ^ h).sum = x⁻¹ ^ h + y⁻¹ ^ h := by
      rw [hxy]; simp
    have e2 : (((p ^ h : ℕ) : ℂ)) ^ e * (1 + (x⁻¹ ^ h + y⁻¹ ^ h)) =
        ((p ^ (h * e) : ℕ) : ℂ) + (((p : ℂ) ^ e * x⁻¹) ^ h + ((p : ℂ) ^ e * y⁻¹) ^ h) := by
      push_cast; ring
    rw [e1, e2]
    refine IsIntegral.add ?_ ((hx.pow h).add (hy.pow h))
    exact_mod_cast (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := ((p ^ (h * e) : ℕ) : ℤ)))
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.mem_maximalCompact_and_congruent_of_mem_principalCongruence :
    ∀ (F : Type) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (n M : ℕ), ∀ g ∈ UpperTheory.V.Af.KLoc F w n M,
    g ∈ GlobalTheory.SplitWeil.KO (w.adicCompletion F) (Fin n) ∧
    ∀ i j, valuation (w.adicCompletion F) ((g.val - 1) i j) ≤ valuation (w.adicCompletion F) (M : w.adicCompletion F) := by
  intro F _ _ w n M g hg
  obtain ⟨k, hk, hkg⟩ := hg
  haveI : (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have hint : ∀ x : UpperTheory.V.Af.Ohat F,
      valuation (w.adicCompletion F) (GlobalTheory.CuspRep.pLoc F w x.1) ≤ 1 := fun x => by
    have h1 : Valued.v (GlobalTheory.CuspRep.pLoc F w x.1) ≤ 1 := Subring.mem_iInf.1 x.2 w
    rw [← map_one (valuation (w.adicCompletion F)), ← Valuation.Compatible.vle_iff_le,
      Valuation.Compatible.vle_iff_le
        (v := (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ)))), map_one]
    exact h1
  let φ : UpperTheory.V.Af.Ohat F →+* w.adicCompletion F := (GlobalTheory.CuspRep.pLoc F w).comp (UpperTheory.V.Af.Ohat F).subtype
  let ψ : UpperTheory.V.Af.Ohat F →+* 𝒪[w.adicCompletion F] := φ.codRestrict _ fun x => hint x
  have hent : ∀ i j, g.val i j = φ (k.val i j) := fun i j => by
    have h1 := GlobalTheory.CuspRep.pLoc_locGL w g
    rw [← hkg] at h1
    rw [← h1]
    rfl
  refine ⟨⟨Matrix.GeneralLinearGroup.map ψ k, ?_⟩, fun i j => ?_⟩
  · ext i j
    rw [hent]
    rfl
  · have h1 : Ideal.Quotient.mk (Ideal.span {(M : UpperTheory.V.Af.Ohat F)}) (k.val i j) =
        (1 : Matrix (Fin n) (Fin n) _) i j :=
      congrArg (fun u : GL (Fin n) (UpperTheory.V.Af.Ohat F ⧸ Ideal.span {(M : UpperTheory.V.Af.Ohat F)}) => u.val i j)
        (MonoidHom.mem_ker.1 hk)
    have h2 : (k.val - 1) i j ∈ Ideal.span {(M : UpperTheory.V.Af.Ohat F)} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, Matrix.sub_apply, map_sub, h1, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h2
    have h3 : (g.val - 1) i j = φ y * M := by
      rw [← map_natCast φ, ← map_mul, hy, Matrix.sub_apply, Matrix.sub_apply, map_sub, hent, Matrix.one_apply,
        Matrix.one_apply]
      split_ifs <;> simp
    rw [h3, map_mul]
    exact mul_le_of_le_one_left' (hint y)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

theorem UpperTheory.eisenstein_trace_difference_log_bound :
    ∀ (q e k : ℕ), 7 ≤ q → 1 ≤ e → 0 < k → ∀ z t : ℂ, z ^ k = 1 → ‖t‖ ≤ 3 → IsIntegral ℤ ((q : ℂ) ^ e * t) → t ≠ eis3 q e z ∧ IsIntegral ℤ ((q : ℂ) ^ e * (t - eis3 q e z)) ∧ Real.log ‖(q : ℂ) ^ e * (t - eis3 q e z)‖ ≤ 2 * e * Real.log q + 1 := by
  intro q e k hq he hk z t hz ht hI
  have hzn : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz hk.ne'
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hzn
  have hQN : 7 ≤ q ^ e := le_trans hq (Nat.le_self_pow (by omega) q)
  have hlogQ : Real.log ((q ^ e : ℕ) : ℝ) = e * Real.log q := by
    rw [Nat.cast_pow, Real.log_pow]
  have hcast : (q : ℂ) ^ e = ((q ^ e : ℕ) : ℂ) := by push_cast; rfl
  unfold eis3
  rw [hcast] at hI ⊢
  generalize q ^ e = N at hQN hlogQ hI
  have hN : (7 : ℝ) ≤ N := by exact_mod_cast hQN
  have hN0 : (N : ℂ) ≠ 0 := by
    have : N ≠ 0 := by omega
    exact_mod_cast this
  have hexp : (N : ℂ) * (t - ((N : ℂ)⁻¹ * z + 1 + (N : ℂ) * z⁻¹)) =
      (N : ℂ) * t - z - N - (N : ℂ) * N * z⁻¹ := by
    field_simp
    ring
  have hnA : ‖(N : ℂ) * t - z - N‖ ≤ 4 * N + 1 := by
    have h1 : ‖(N : ℂ) * t‖ ≤ 3 * N := by
      rw [norm_mul, Complex.norm_natCast]
      nlinarith
    have h2 := norm_sub_le ((N : ℂ) * t - z) (N : ℂ)
    have h3 := norm_sub_le ((N : ℂ) * t) z
    rw [Complex.norm_natCast] at h2
    linarith
  have hnB : ‖(N : ℂ) * N * z⁻¹‖ = N * N := by
    simp [hzn]
  have hne : (N : ℂ) * t - z - N - (N : ℂ) * N * z⁻¹ ≠ 0 := by
    intro h
    rw [sub_eq_zero.mp h, hnB] at hnA
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply hne
    rw [← hexp, ← h, sub_self, mul_zero]
  · rw [hexp]
    have hzI : IsIntegral ℤ z := IsIntegral.of_pow hk (by rw [hz]; exact isIntegral_one)
    have hzI' : IsIntegral ℤ z⁻¹ :=
      IsIntegral.of_pow hk (by rw [inv_pow, hz, inv_one]; exact isIntegral_one)
    have hNI : IsIntegral ℤ (N : ℂ) := by
      have := isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (N : ℤ))
      simpa using this
    exact ((hI.sub hzI).sub hNI).sub ((hNI.mul hNI).mul hzI')
  · rw [hexp]
    have hb : ‖(N : ℂ) * t - z - N - (N : ℂ) * N * z⁻¹‖ ≤ 2 * ((N : ℝ) * N) := by
      have := norm_sub_le ((N : ℂ) * t - z - N) ((N : ℂ) * N * z⁻¹)
      nlinarith
    have hNpos : (0 : ℝ) < N := by linarith
    have h1 := Real.log_le_log (norm_pos_iff.mpr hne) hb
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul hNpos.ne' hNpos.ne', hlogQ] at h1
    have h2 : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem eq_one_of_charpoly_dvd {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] (f : Module.End ℂ V)
    (hf : f.IsSemisimple) (hd : f.charpoly ∣ (1 : Module.End ℂ V').charpoly) : f = 1 := by
  rw [LinearMap.charpoly_one] at hd
  obtain ⟨q, hq⟩ := hd
  have h0 := congrArg (Polynomial.aeval f) hq
  rw [map_mul, LinearMap.aeval_self_charpoly, zero_mul, map_pow, map_sub, Polynomial.aeval_X,
    map_one] at h0
  have hs : (f - algebraMap ℂ (Module.End ℂ V) 1).IsSemisimple :=
    Module.End.isSemisimple_sub_algebraMap_iff.2 hf
  rw [map_one] at hs
  exact sub_eq_zero.1 (Module.End.eq_zero_of_isNilpotent_isSemisimple ⟨_, h0⟩ hs)

theorem UpperTheory.irreducible_constituent_of_level_weilDeligne_eq_character :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (M n : ℕ), 1 ≤ M →
    ∀ x z : WD h, UpperTheory.V.Af.IsLevelWD M n x → IsIrrWD z → (∀ σ, z.charPol σ ∣ x.charPol σ) →
    ∃ (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ), z = WD.lpOfChar h ξ hξ ∧
      ∀ s : ↥(Ine (F := F) A), (∀ ζ : Ω, ζ ^ M = 1 → (s : _root_.Formalism.ConjugateSelfDual.G F Ω) ζ = ζ) → ξ (ineIncl h s) = 1 := by
  intro F Ω _ _ _ _ _ w A h M n hM x z hx hz hd
  obtain ⟨χ, a, hχ, rfl, -, ha⟩ := hx
  obtain ⟨m, b, rfl, hb⟩ := hz
  have key : ∀ s : ↥(Ine (F := F) A), (∀ ζ : Ω, ζ ^ M = 1 → (s : _root_.Formalism.ConjugateSelfDual.G F Ω) ζ = ζ) →
      b.ρ (ineIncl h s) = 1 := by
    intro s hs
    have h1 : a.ρ (ineIncl h s) = 1 := by
      rw [ha s]
      have : (fun i => ((χ i s : ℂˣ) : ℂ)) = fun _ => 1 := by
        funext i
        rw [hχ i s hs]
        rfl
      rw [this, Matrix.diagonal_one, Matrix.toLin'_one]
      rfl
    have h2 := hd (ineIncl h s)
    rw [WD.charPol_mk, WD.charPol_mk, h1] at h2
    exact eq_one_of_charpoly_dvd _ (b.semisimple _) h2
  obtain ⟨ξ, hξ, h1, h2⟩ := UpperTheory.irreducible_weilDeligne_tame_level_eq_character F Ω w A h M hM m b hb key
  exact ⟨ξ, hξ, h1, fun s hs => h2 _ (key s hs)⟩
end

section

open NumberField QuadraticAlgebra

private theorem real_val {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (ψ : F →+* ℂ) (x : F) :
    starRingEnd ℂ (ψ x) = ψ x := by
  have hr := ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_mk_iff.mp (IsTotallyReal.isReal (InfinitePlace.mk ψ)))
  have := RingHom.congr_fun hr x
  rw [ComplexEmbedding.conjugate_coe_eq] at this
  exact this

private theorem sq_neg_one {z : ℂ} (h : z * z = -1) : starRingEnd ℂ z = -z := by
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.one_re,
    Complex.one_im] at h1 h2
  have hre : z.re = 0 := by
    rcases mul_eq_zero.mp (show z.re * z.im = 0 by linarith) with h3 | h3
    · exact h3
    · rw [h3] at h1
      nlinarith [mul_self_nonneg z.re]
  apply Complex.ext <;> simp [hre]

theorem UpperTheory.exists_CM_extension :
    UpperTheory.V.Af.BA.ExCM := by
  intro F _ _ _
  let ψ : F →+* ℂ := (IsAlgClosed.lift : F →ₐ[ℚ] ℂ).toRingHom
  haveI hfact : Fact (∀ r : F, r ^ 2 ≠ -1 + 0 * r) := by
    refine ⟨fun r hr => ?_⟩
    have h2 : ψ r * ψ r = -1 := by
      rw [← map_mul, ← pow_two, hr]
      simp
    have h3 := real_val ψ r
    rw [sq_neg_one h2] at h3
    have h4 : ψ r = 0 := by
      have : (2 : ℂ) * ψ r = 0 := by linear_combination -h3
      simpa using this
    rw [h4] at h2
    norm_num at h2
  haveI hNF : NumberField (QuadraticAlgebra F (-1) 0) :=
    { to_charZero := inferInstance
      to_finiteDimensional := Module.Finite.trans F (QuadraticAlgebra F (-1) 0) }
  have hωω : (ω : QuadraticAlgebra F (-1) 0) * ω = -1 := by
    rw [omega_mul_omega_eq_mk]
    ext <;> simp
  have hφω : ∀ φ : QuadraticAlgebra F (-1) 0 →+* ℂ, starRingEnd ℂ (φ ω) = - φ ω := by
    intro φ
    apply sq_neg_one
    rw [← map_mul, hωω, map_neg, map_one]
  have hTC : IsTotallyComplex (QuadraticAlgebra F (-1) 0) := by
    refine ⟨fun v => ?_⟩
    rw [← InfinitePlace.not_isReal_iff_isComplex]
    intro hv
    have hr := ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp hv)
    have h1 := RingHom.congr_fun hr ω
    rw [ComplexEmbedding.conjugate_coe_eq, hφω] at h1
    have h0 : v.embedding ω = 0 := by
      have : (2 : ℂ) * v.embedding ω = 0 := by linear_combination -h1
      simpa using this
    have h5 : v.embedding ω * v.embedding ω = -1 := by
      rw [← map_mul, hωω, map_neg, map_one]
    rw [h0] at h5
    norm_num at h5
  refine ⟨QuadraticAlgebra F (-1) 0, inferInstance, hNF, hTC, algebraMap F (QuadraticAlgebra F (-1) 0),
    starRingEnd (QuadraticAlgebra F (-1) 0), ?_, ?_⟩
  · intro φ x
    have hx : x = algebraMap F (QuadraticAlgebra F (-1) 0) x.re +
        algebraMap F (QuadraticAlgebra F (-1) 0) x.im * ω := by
      ext <;> simp
    have hsx : starRingEnd (QuadraticAlgebra F (-1) 0) x = algebraMap F (QuadraticAlgebra F (-1) 0) x.re -
        algebraMap F (QuadraticAlgebra F (-1) 0) x.im * ω := by
      show star x = _
      ext <;> simp
    have hreal : ∀ y : F, starRingEnd ℂ (φ (algebraMap F (QuadraticAlgebra F (-1) 0) y)) =
        φ (algebraMap F (QuadraticAlgebra F (-1) 0) y) :=
      fun y => real_val (φ.comp (algebraMap F (QuadraticAlgebra F (-1) 0))) y
    rw [hsx]
    conv_rhs => rw [hx]
    simp only [map_add (f := _), map_sub, map_mul, hreal, hφω]
    ring
  · intro x
    rw [RingHom.mem_range]
    constructor
    · intro hx
      have him := congrArg QuadraticAlgebra.im hx
      change (star x).im = x.im at him
      rw [im_star] at him
      have h0 : x.im = 0 := by
        have : (2 : F) * x.im = 0 := by linear_combination -him
        simpa using this
      refine ⟨x.re, ?_⟩
      ext <;> simp [h0]
    · rintro ⟨y, rfl⟩
      show star (algebraMap F (QuadraticAlgebra F (-1) 0) y) = _
      ext <;> simp
end

section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.Af.BA ComplexOrder in
theorem UpperTheory.adelicBaseChange_realPart :
    UpperTheory.V.Af.BA.RePart := by
  intro L _ _ N σ hσ k
  let A : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ :=
    fun w => Matrix.of fun i j => (((mat k w) i j).re : ℂ)
  have hre : ∀ w i j, ((mat k w) j i).re = ((mat k w) i j).re := by
    intro w i j
    have := (mat_herm k w).apply i j
    rw [← this]
    simp
  have hA : ∀ w, (A w).IsHermitian := by
    intro w
    ext i j
    simp [A, Matrix.conjTranspose_apply, hre w i j]
  have hmat : ∀ w, mat (mkHS A hA) w = A w := fun w => rfl
  have hAeq : ∀ w, A w = (1 / 2 : ℝ) • (mat k w + (mat k w).transpose) := by
    intro w
    ext i j
    have h1 := (mat_herm k w).apply i j
    have h2 : (mat k w) j i = star ((mat k w) i j) := by rw [← h1, star_star]
    simp only [A, Matrix.of_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, h2]
    apply Complex.ext <;> simp <;> ring
  refine ⟨⟨mkHS A hA, ?_⟩, ?_, ?_⟩
  · intro w i j
    show ((mat (mkHS A hA) w) i j).im = 0
    rw [hmat]
    simp [A]
  · intro y
    show q (mkHS A hA) y = _
    have hz : ∀ w i, toR (sLat σ y) w i = star (toR y w i) := fun w i => hσ w (y i)
    simp only [q, qR]
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [hmat]
    simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum, Complex.re_sum,
      ← Finset.sum_add_distrib, Finset.sum_div, hz]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [A, Matrix.of_apply, Complex.mul_re, Complex.mul_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  · intro hk
    have hpsd : ∀ w, (A w).PosSemidef := by
      intro w
      rw [hAeq w]
      exact ((hk w).add (hk w).transpose).smul (by norm_num)
    refine ⟨fun w => by rw [hmat]; exact hpsd w, fun h0 => ?_⟩
    apply HS_ext
    intro w
    have hA0 : A w = 0 := by
      have := congrArg (fun x : HR L N => mat (x : HS L N) w) h0
      simpa [hmat, mat_zero] using this
    rw [mat_zero]
    apply ((hk w).trace_eq_zero_iff).mp
    have hd : ∀ i, (mat k w) i i = (((mat k w) i i).re : ℂ) := by
      intro i
      apply Complex.ext
      · simp
      · have := (mat_herm k w).apply i i
        have h3 := congrArg Complex.im this
        simp at h3
        simp
        linarith
    rw [Matrix.trace]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Matrix.diag_apply, hd i]
    have := congrFun (congrFun hA0 i) i
    simpa [A] using this
end

section

open CategoryTheory Limits in
private theorem homologyMap_zero_of_f {C : Type*} [Category C] [Abelian C] {ι : Type*}
    {c : ComplexShape ι} {K L : HomologicalComplex C c} (Ψ : K ⟶ L) (q : ι) (h : Ψ.f q = 0) :
    HomologicalComplex.homologyMap Ψ q = 0 := by
  have h1 : HomologicalComplex.cyclesMap Ψ q = 0 := by
    rw [← cancel_mono (L.iCycles q), zero_comp, HomologicalComplex.cyclesMap_i, h, comp_zero]
  rw [← cancel_epi (K.homologyπ q), comp_zero, HomologicalComplex.homologyπ_naturality, h1, zero_comp]

open CategoryTheory Limits in
private theorem isZero_yoneda {R : Type*} [Ring R] {C : Type*} [Category C] [Abelian C]
    [Linear R C] {X : C} (Y : C) (P : ProjectiveResolution X) (e : P.complex ⟶ P.complex)
    (he : e ≫ P.π = P.π) (q : ℕ) (hq : e.f q = 0) :
    IsZero ((P.complex.linearYonedaObj R Y).homology q) := by
  let F := ((linearYoneda R C).obj Y).rightOp
  have h1 : Homotopy e (𝟙 P.complex) :=
    ProjectiveResolution.liftHomotopy (𝟙 X) e (𝟙 _) (by simpa using he) (by simp)
  have h2 := (F.mapHomotopy h1).unop
  have h3 := h2.homologyMap_eq q
  have hz : ((HomologicalComplex.unopFunctor (ModuleCat R) (ComplexShape.down ℕ)).map
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map e).op).f q = 0 := by
    show (F.map (e.f q)).unop = 0
    rw [hq, F.map_zero]
    rfl
  rw [homologyMap_zero_of_f _ q hz] at h3
  simp only [CategoryTheory.Functor.map_id, op_id, HomologicalComplex.homologyMap_id] at h3
  rw [IsZero.iff_id_eq_zero]
  exact h3.symm

open CategoryTheory Limits in
theorem UpperTheory.ext_vanishing_of_resolution_endo :
    UpperTheory.V.Af.BA.VanishOf := by
  intro Γ _ P e he q hq A
  have h2 : IsZero (groupCohomology A q) :=
    (isZero_yoneda (R := ℂ) A P e he q hq).of_iso (groupCohomologyIso A q P)
  haveI := ModuleCat.subsingleton_of_isZero h2
  exact rank_subsingleton' ℂ _
end

section

theorem UpperTheory.adelic_rep_bounded_comm_of_bounded_equiv :
    UpperTheory.V.Af.CohB.BddEquiv → UpperTheory.V.Af.BA.BddSub → UpperTheory.V.Af.BA.BddOver → UpperTheory.V.Af.BA.BddComm := by
  intro hEq hSub hOver G _ Γ Λ hc hΛ
  obtain ⟨h1, h2⟩ := hc
  have f1 : (Γ.subgroupOf Λ).FiniteIndex := Subgroup.isFiniteRelIndex_iff_finiteIndex.mp h1
  have f2 : (Λ.subgroupOf Γ).FiniteIndex := Subgroup.isFiniteRelIndex_iff_finiteIndex.mp h2
  have b1 := hSub Λ (Γ.subgroupOf Λ) f1 hΛ
  have e : (Γ.subgroupOf Λ) ≃* (Λ.subgroupOf Γ) :=
    { toFun := fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩
      invFun := fun y => ⟨⟨y.1.1, y.2⟩, y.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have b2 := hEq _ _ ⟨e⟩ b1
  exact hOver Γ (Λ.subgroupOf Γ) f2 b2
end

section

open CategoryTheory

theorem UpperTheory.pins_of_closed_subgroup_padic_character_inv :
    UpperTheory.V.Af.BA.LiftEquiv :=
  _root_.UpperTheory.Reformulated.B.Qe19.pins_of_closed_subgroup_padic_character_inv
end
