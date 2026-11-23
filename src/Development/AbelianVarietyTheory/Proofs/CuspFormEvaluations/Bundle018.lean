module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.LetAct
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.WeightVariableFormula
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortHarmonicFamilyUnimodular
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle017
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.JetSubstPCompJetBC
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameRead

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV
open scoped Classical Matrix

theorem det_gen_ne_zero {K : Type} [Field K] {Ix : Type} {n : ℕ} (t : Ix) : (gen K n t).det ≠ 0 := by
  intro h
  have h2 := congrArg (MvPolynomial.eval (fun v : Ix × Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) K) v.2.1 v.2.2)) h
  rw [RingHom.map_det] at h2
  have : (MvPolynomial.eval (fun v : Ix × Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) K) v.2.1 v.2.2)).mapMatrix
      (gen K n t) = 1 := by
    ext1 i j
    simp [gen]
  rw [this] at h2
  simp at h2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) {n : ℕ} {Ix : Type} [Fintype Ix]
  (pl : Ix → (E →+* ℂ))

theorem detFac_ne_zero (K : Type) [Field K] (a : (E →+* ℂ) × ℕ → ℕ) (s : Ix → ℤ) (lam : Ix → DomWeight n) :
    detFac Dw pl K a s lam ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun t _ => pow_ne_zero _ (det_gen_ne_zero t)

theorem cof_image : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (n : ℕ) (Ix : Type) [Fintype Ix] (pl : Ix → (E →+* ℂ)), IsEnum H pl → Dw.p + Dw.q ≤ n → ∀ (l : Level H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (s : Ix → ℤ) (lam : Ix → DomWeight n), (∀ τ, Antitone fun i => a (τ, i)) → WtIs Dw pl a s lam → (∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∃ F ∈ VV c.F lam, cof Dw pl c.F n P = detFac Dw pl c.F a s lam * F) ∧ (∀ F ∈ VV c.F lam, ∃! P, P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) ∧ cof Dw pl c.F n P = detFac Dw pl c.F a s lam * F) ∧ ∀ (g : Ix → GL (Fin n) c.F), ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∀ F ∈ VV c.F lam, cof Dw pl c.F n P = detFac Dw pl c.F a s lam * F → cof Dw pl c.F n (letAct Dw pl c.F g P) = (∏ t, ((g t : Matrix (Fin n) (Fin n) c.F).det) ^ (-(s t))) • (detFac Dw pl c.F a s lam * actP lam g F) := by
  first
  | exact @_root_.GlobalTheory.WeightOrderLemmas.main
  | exact _root_.GlobalTheory.WeightOrderLemmas.main
  | (apply _root_.GlobalTheory.WeightOrderLemmas.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.WeightOrderLemmas.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.WeightOrderLemmas.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.WeightOrderLemmas.main ..)

end GlobalTheory.FrameRead
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.sq_dvd_sum_alternating_forms_of_killed_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La → ∀ a a' : Fin n → Dw.La, (∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) → ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) → ∀ i, Dw.ModN (N ^ 2) (∑ j, cm i j • a j)) → (∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) → ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) → ∀ i, Dw.ModN (N ^ 2) (∑ j, cm i j • a' j)) → ((N : ℤ) ^ 2) ∣ ∑ b, Dw.EF (a b) (a' b) := by
  first | exact @GlobalTheory.sq_dvd_sum_EF_of_killed | exact GlobalTheory.sq_dvd_sum_EF_of_killed | (intros; apply GlobalTheory.sq_dvd_sum_EF_of_killed <;> assumption)
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open scoped TensorProduct

namespace GlobalTheory.ZCount

theorem finrank_fibre (O M k : Type) [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] [Field k] [Algebra O k] :
    Module.finrank k (k ⊗[O] M) = Module.finrank O M := by
  have : Module.FinitePresentation O M := Module.finitePresentation_of_projective O M
  have key : ∀ (K : Type) [Field K] [Algebra O K], Module.finrank K (K ⊗[O] M) =
      Module.rankAtStalk M (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O) := fun K _ _ => by
    have h := Module.rankAtStalk_baseChange (R := O) (M := M) (S := K) ⟨⊥, Ideal.isPrime_bot⟩
    rw [Module.rankAtStalk_eq_finrank_of_free] at h
    exact h.trans ((Module.isLocallyConstant_rankAtStalk (R := O) (M := M)).apply_eq_of_preconnectedSpace _ _)
  rw [key k, ← key (FractionRing O), (TensorProduct.isBaseChange O M (FractionRing O)).finrank_eq]

theorem exists_basis_mod (O M : Type) [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] (m : O) [Finite (O ⧸ Ideal.span {m})] (r : ℕ)
    (hr : Module.finrank O M = r) :
    ∃ e : Fin r → M, (∀ x : M, ∃ (c : Fin r → O) (y : M), x = ∑ k, c k • e k + m • y) ∧
      ∀ (c : Fin r → O) (y : M), ∑ k, c k • e k = m • y → ∀ k, m ∣ c k := by
  set I : Ideal O := Ideal.span {m} with hI
  have : Finite (Ideal (O ⧸ I)) := Finite.of_injective _ SetLike.coe_injective
  have : Finite (MaximalSpectrum (O ⧸ I)) :=
    Finite.of_injective (fun P => P.asIdeal) fun _ _ h => MaximalSpectrum.ext h
  obtain ⟨B⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (O ⧸ I) ((O ⧸ I) ⊗[O] M) r fun P => by
    let := P.isMaximal
    let := Ideal.Quotient.field P.asIdeal
    rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange O (O ⧸ I) ((O ⧸ I) ⧸ P.1) ((O ⧸ I) ⧸ P.1) M).finrank_eq,
      finrank_fibre, hr]
  have hs : Function.Surjective (TensorProduct.mk O (O ⧸ I) M 1) :=
    TensorProduct.mk_surjective O M (O ⧸ I) Ideal.Quotient.mk_surjective
  have hk : ∀ x : M, TensorProduct.mk O (O ⧸ I) M 1 x = 0 ↔ ∃ y, x = m • y := fun x => by
    rw [← (TensorProduct.quotTensorEquivQuotSMul M I).map_eq_zero_iff, TensorProduct.mk_apply,
      TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero, hI,
      Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨fun ⟨y, _, h⟩ => ⟨y, h.symm⟩, fun ⟨y, h⟩ => ⟨y, trivial, h.symm⟩⟩
  choose e he using fun k => hs (B k)
  have hc : ∀ c : Fin r → O, TensorProduct.mk O (O ⧸ I) M 1 (∑ k, c k • e k) =
      ∑ k, Ideal.Quotient.mk I (c k) • B k := fun c => by

    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, he, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
  refine ⟨e, fun x => ?_, fun c y h k => ?_⟩
  · choose c hc' using fun k => Ideal.Quotient.mk_surjective (B.repr (TensorProduct.mk O (O ⧸ I) M 1 x) k)
    obtain ⟨y, hy⟩ := (hk (x - ∑ k, c k • e k)).1 (by
      rw [map_sub, hc]
      simp only [hc']
      rw [B.sum_repr, sub_self])
    exact ⟨c, y, by rw [← hy]; abel⟩
  · have h0 := (hk _).2 ⟨y, h⟩
    rw [hc] at h0
    have := Fintype.linearIndependent_iff.1 B.linearIndependent _ h0 k
    rwa [Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_singleton] at this

section

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem mem_stdLat (v : Fin n → E) :
    v ∈ stdLat E n ↔ ∃ u : Fin n → 𝓞 E, ∀ b, v b = (u b : E) := by
  simp only [stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
  constructor
  · intro h
    choose u hu using h
    exact ⟨u, fun b => (hu b).symm⟩
  · rintro ⟨u, hu⟩ b
    exact ⟨u b, (hu b).symm⟩

theorem mem_smul_stdLat (N : ℕ) (v : Fin n → E) :
    v ∈ Ideal.span {(N : 𝓞 E)} • stdLat E n ↔ ∃ u : Fin n → 𝓞 E, ∀ b, v b = (N : E) * (u b : E) := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨u, hu⟩ := (mem_stdLat w).1 hw
    exact ⟨u, fun b => by simp [hu, Algebra.smul_def]⟩
  · rintro ⟨u, hu⟩
    exact ⟨fun b => u b, (mem_stdLat _).2 ⟨u, fun _ => rfl⟩, funext fun b => by simp [hu, Algebra.smul_def]⟩

theorem mul_integral [IsCMField E] (Λ : GenLat E n) (N : ℕ) (hU : Λ.Unimod)
    (hN : Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La) (w : Fin n → E) (hw : w ∈ Λ.La) :
    ∃ v : Fin n → 𝓞 E, ∀ b, (v b : E) = (N : E) * w b := by
  have h : ∀ b, ∃ a : 𝓞 E, (a : E) = (N : E) * w b := fun b => by
    have hb : (Pi.single b (N : E) : Fin n → E) ∈ Λ.La := hN ((mem_smul_stdLat N _).2
      ⟨Pi.single b 1, fun j => by
        by_cases hj : j = b
        · subst hj; simp
        · simp [hj]⟩)
    obtain ⟨a, ha⟩ := (hU _).1 hb w hw
    refine ⟨a, ha.trans ?_⟩
    rw [Finset.sum_eq_single b (fun j _ hj => by simp [hj]) (by simp)]
    simp
  choose v hv using h
  exact ⟨v, hv⟩

end

theorem exists_class_representatives : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La → ∃ zz : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → Dw.La, (∀ i₀, (∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) → ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) → ∀ i, Dw.ModN (N ^ 2) (∑ j, cm i j • zz i₀ j))) ∧ (∀ i i', (∀ b, Dw.ModN (N ^ 2) (zz i b - zz i' b)) → i = i') ∧ ∀ a : Fin n → Dw.La, (∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) → ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) → ∀ i, Dw.ModN (N ^ 2) (∑ j, cm i j • a j)) → ∃ i, ∀ b, Dw.ModN (N ^ 2) (a b - zz i b) := by
  intro E _ _ _ H Dw n Λ N hU hN0 hN
  have := Dw.fin
  have := Dw.proj
  have hNE : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN0.ne'
  have hNO : (N : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hN0.ne'
  have : Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E) ^ 2}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hN0.ne')
  obtain ⟨e, he1, he2⟩ := exists_basis_mod (𝓞 E) Dw.La ((N : 𝓞 E) ^ 2) (Dw.p + Dw.q) Dw.rank
  set K := (Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup with hK
  choose V hV using fun w : Λ.La.toAddSubgroup => mul_integral Λ N hU hN w.1 w.2
  have hKV : ∀ w w' : Λ.La.toAddSubgroup, (w : Λ.La.toAddSubgroup ⧸ K) = w' ↔
      ∀ b, (N : 𝓞 E) ^ 2 ∣ V w' b - V w b := fun w w' => by
    rw [QuotientAddGroup.eq, hK, AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup,
      mem_smul_stdLat]
    constructor
    · rintro ⟨u, hu⟩ b
      refine ⟨u b, RingOfIntegers.ext ?_⟩
      have := hu b
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, Pi.add_apply, Pi.neg_apply] at this
      have e1 := hV w b
      have e2 := hV w' b
      simp only [RingOfIntegers.coe_eq_algebraMap] at *
      rw [map_sub, map_mul, map_pow, map_natCast, e1, e2]
      linear_combination (N : E) * this
    · intro h
      choose u hu using h
      refine ⟨u, fun b => mul_left_cancel₀ hNE ?_⟩
      have := congrArg (algebraMap (𝓞 E) E) (hu b)
      have e1 := hV w b
      have e2 := hV w' b
      simp only [RingOfIntegers.coe_eq_algebraMap] at *
      rw [map_sub, map_mul, map_pow, map_natCast, e1, e2] at this
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, Pi.add_apply, Pi.neg_apply]
      linear_combination this
  have : Finite (Λ.La.toAddSubgroup ⧸ K) :=
    Finite.of_injective (fun q b => Ideal.Quotient.mk (Ideal.span {(N : 𝓞 E) ^ 2}) (V q.out b))
      fun q q' h => by
        rw [← q.out_eq, ← q'.out_eq]
        refine (hKV _ _).2 fun b => ?_
        rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
        exact (congrFun h b).symm
  have hcard : Nat.card (Fin (Dw.p + Dw.q) → Λ.La.toAddSubgroup ⧸ K) = Λ.zCard N (Dw.p + Dw.q) := by
    rw [Nat.card_fun, Nat.card_fin]
    rfl
  let σ := (Finite.equivFinOfCardEq hcard).symm
  have hM : ∀ x : Dw.La, Dw.ModN (N ^ 2) x ↔ ∃ y, x = ((N : 𝓞 E) ^ 2) • y := fun x => by
    simp only [Datum.ModN, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  refine ⟨fun i b => ∑ k, V (σ i k).out b • e k, fun i => ?_, fun i i' h => ?_, fun a ha => ?_⟩
  · exact (GlobalTheory.T.modN_sq_sum_iff_exists_genLat_decomposition E H Dw n Λ N hU hN0 hN _).2
      ⟨_, e, fun k => V (σ i k).out, fun k => ⟨_, (σ i k).out.2, hV _⟩, fun _ => rfl⟩
  · refine σ.injective (funext fun k => ?_)
    rw [← (σ i k).out_eq, ← (σ i' k).out_eq]
    refine ((hKV _ _).2 fun b => ?_).symm
    obtain ⟨y, hy⟩ := (hM _).1 (h b)
    refine he2 (fun k => V (σ i k).out b - V (σ i' k).out b) y ?_ k
    rw [← hy, ← Finset.sum_sub_distrib]
    simp only [sub_smul]
  · obtain ⟨m, x, v, hv, hav⟩ := (GlobalTheory.T.modN_sq_sum_iff_exists_genLat_decomposition E H Dw n Λ N hU hN0 hN a).1 ha
    choose w hw hvw using hv
    choose c y hcy using fun i => he1 (x i)
    let W : Fin (Dw.p + Dw.q) → Λ.La.toAddSubgroup := fun k =>
      ⟨∑ i, c i k • w i, Λ.La.sum_mem fun i _ => Λ.La.smul_mem _ (hw i)⟩
    have hW : ∀ k b, V (W k) b = ∑ i, v i b * c i k := fun k b => by
      refine RingOfIntegers.ext ?_
      rw [hV]
      simp only [RingOfIntegers.coe_eq_algebraMap] at *

      simp only [W, map_sum, map_mul, hvw, Finset.sum_apply, Pi.smul_apply, Algebra.smul_def,
      Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    refine ⟨σ.symm fun k => (W k : Λ.La.toAddSubgroup ⧸ K), fun b => (hM _).2 ?_⟩
    simp only [Equiv.apply_symm_apply]
    choose t ht using fun k => (hKV _ (W k)).1 (QuotientAddGroup.out_eq' (W k : Λ.La.toAddSubgroup ⧸ K)) b
    refine ⟨∑ k, t k • e k + ∑ i, v i b • y i, ?_⟩
    have h1 : a b = ∑ k, V (W k) b • e k + (N : 𝓞 E) ^ 2 • ∑ i, v i b • y i := by
      rw [hav b]
      simp only [hW, Finset.sum_smul]
      rw [Finset.sum_comm, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcy i, smul_add, Finset.smul_sum, smul_comm (v i b)]
      simp only [mul_smul]
    rw [h1, smul_add, add_sub_right_comm, ← Finset.sum_sub_distrib, add_left_inj, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← sub_smul, ht, mul_smul]

end GlobalTheory.ZCount
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem _root_.GlobalTheory.T.exists_short_harmonic_family_unimodular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (n : ℕ) (Λ : GenLat E n), Λ.Unimod → Λ.La.FG → Dw.p + Dw.q ≤ n → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (L : ℝ), 2 ≤ L → Real.log (FD.rdE E) ≤ 2 * L → Real.log (FD.fdeg E) ≤ 2 * L → Real.log (1 + DF Dw a) ≤ 2 * L → Real.log n ≤ L → ∃ S : Finset (MvPolynomial (LtN Dw n) c.F), (∀ Q ∈ S, Q ∈ harmL c Λ a ∧ ∀ σ' : c.F →+* ℂ, Real.log (∑ m ∈ Q.support, ‖σ' (Q.coeff m)‖) ≤ 140 * (Dw.p + Dw.q : ℕ) * L * DF Dw a) ∧ (∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), P ∈ Submodule.span c.F (S : Set (MvPolynomial (LtN Dw n) c.F))) ∧ S.card ≤ ((2 * (Dw.p + Dw.q) + 1) * DF Dw a + 1) ^ (2 * FD.fdeg E * n * (2 * Dw.p + Dw.q)) := by
  first | exact @GlobalTheory.Harm.exists_short_harmL_family | exact GlobalTheory.Harm.exists_short_harmL_family | (intros; apply GlobalTheory.Harm.exists_short_harmL_family <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RawFrameBC

private theorem pull2_lemma_9 {Z' Y' Z Y : Scheme.{0}} (a : Z' ⟶ Y') (g : Y' ⟶ Y) (r : Z' ⟶ Z) (b : Z ⟶ Y)
    (hab : a ≫ g = r ≫ b) (U : Y.Opens) (V : Y'.Opens) (hV : V ≤ g ⁻¹ᵁ U) (W1 : Z'.Opens) (hW1 : W1 ≤ a ⁻¹ᵁ V)
    (V' : Z.Opens) (hV' : V' ≤ b ⁻¹ᵁ U) (W1' : Z'.Opens) (hW1' : W1' ≤ r ⁻¹ᵁ V') (W2 : Z'.Opens)
    (h12 : W2 ≤ W1) (h12' : W2 ≤ W1') (u : Γ(Y, U)ˣ) :
    Units.map (Z'.presheaf.map (homOfLE h12).op).hom.toMonoidHom (Units.map (Z'.presheaf.map (homOfLE hW1).op).hom.toMonoidHom
      (Units.map (a.app V).hom.toMonoidHom (Units.map (Y'.presheaf.map (homOfLE hV).op).hom.toMonoidHom (Units.map (g.app U).hom.toMonoidHom u)))) =
    Units.map (Z'.presheaf.map (homOfLE h12').op).hom.toMonoidHom (Units.map (Z'.presheaf.map (homOfLE hW1').op).hom.toMonoidHom
      (Units.map (r.app V').hom.toMonoidHom (Units.map (Z.presheaf.map (homOfLE hV').op).hom.toMonoidHom (Units.map (b.app U).hom.toMonoidHom u)))) := by
  have hW : W2 ≤ (a ≫ g) ⁻¹ᵁ U := fun z hz => hV (hW1 (h12 hz))
  have hW' : W2 ≤ (r ≫ b) ⁻¹ᵁ U := fun z hz => hV' (hW1' (h12' hz))
  have e1 : g.app U ≫ Y'.presheaf.map (homOfLE hV).op ≫ a.app V ≫ Z'.presheaf.map (homOfLE hW1).op ≫
      Z'.presheaf.map (homOfLE h12).op = (a ≫ g).appLE U W2 hW := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.comp_app, Scheme.Hom.naturality_assoc, ← Functor.map_comp]
    rfl
  have e2 : b.app U ≫ Z.presheaf.map (homOfLE hV').op ≫ r.app V' ≫ Z'.presheaf.map (homOfLE hW1').op ≫
      Z'.presheaf.map (homOfLE h12').op = (r ≫ b).appLE U W2 hW' := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.comp_app, Scheme.Hom.naturality_assoc, ← Functor.map_comp]
    rfl
  have e3 : ∀ (f f' : Z' ⟶ Y) (hf : f = f') (h : W2 ≤ f ⁻¹ᵁ U) (h' : W2 ≤ f' ⁻¹ᵁ U),
      f.appLE U W2 h = f'.appLE U W2 h' := by
    intro f f' hf h h'
    subst hf
    rfl
  have key := congrArg (fun F => F.hom (u : Γ(Y, U))) (e1.trans ((e3 _ _ hab hW hW').trans e2.symm))
  apply Units.ext
  simpa using key

theorem exists_reindexed_pull {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (c : LB.Gen (LB.LinComb L φ ε)) (hc : c.IsGen) (g : Y' ⟶ Y)
    (φ' : K → (Y' ⟶ X)) (h : φ' = fun k => g ≫ φ k) :
    ∃ c' : LB.Gen (LB.LinComb L φ' ε), c'.IsGen ∧ LB.Gen.Corr L _ _ _ _ c' (LB.pullGen L φ ε c g) ∧
      ∀ (Z Z' : Scheme.{0}) (a : Z' ⟶ Y') (b : Z ⟶ Y) (r : Z' ⟶ Z), a ≫ g = r ≫ b →
        LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ' ε c' a) (LB.pullGen L _ _ (LB.pullGen L φ ε c b) r) := by
  subst h
  refine ⟨LB.pullGen L φ ε c g, DVR.pullGen_isGen L φ ε c hc g, corr_of_val hL fun y J => congrFun rfl, ?_⟩
  intro Z Z' a b r hab j j' hj hj' hjj
  have hjj' : j = j' := funext fun k => hjj k k (by
    show a ≫ g ≫ φ k = r ≫ b ≫ φ k
    rw [← Category.assoc, hab, Category.assoc])
  subst hjj'
  simp only [LB.pullGen]
  unfold pullU res
  exact pull2_lemma_9 a g r b hab _ _ _ _ _ _ _ _ _ _ _ _ (c.s j)

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [spMap, spMap, ← Spec.map_comp]
  rfl

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X) (d : ℕ)

theorem sq_of_ring {m n n' : ℕ} (f : Jet S (Fin n × Fin d) m →ₐ[S] Jet S (Fin n' × Fin d) m)
    (f' : Jet S' (Fin n × Fin d) m →ₐ[S'] Jet S' (Fin n' × Fin d) m)
    (h : f'.toRingHom.comp (jetBC ψ _ m) = (jetBC ψ _ m).comp f.toRingHom) :
    homAt (spMap ψ ≫ x0) f' ≫ rjBC ψ x0 d m n = rjBC ψ x0 d m n' ≫ homAt x0 f := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Formalism.L2.Pj.homAt, rjBC, Over.homMk_left]
  rw [spMap_comp_eq, spMap_comp_eq]
  congr 1

private theorem jetCopy_eq_lemma {R : Type} [CommRing R] {d n : ℕ} (m : ℕ) (i : Fin n) :
    (jetCopy d m i : Jet R (Fin 1 × Fin d) m →ₐ[R] Jet R (Fin n × Fin d) m) =
      jetSubstP m (fun p : Fin 1 × Fin d => (MvPolynomial.X (i, p.2) : MvPolynomial (Fin n × Fin d) R)) := by
  unfold jetCopy jetSubstP
  congr 1
  funext p
  simp only [MvPolynomial.constantCoeff_X, map_zero, sub_zero]

theorem sq_copy {n : ℕ} (m : ℕ) (i : Fin n) :
    homAt (spMap ψ ≫ x0) (jetCopy d m i) ≫ rjBC ψ x0 d m 1 = rjBC ψ x0 d m n ≫ homAt x0 (jetCopy d m i) := by
  rw [jetCopy_eq_lemma, jetCopy_eq_lemma]
  have := sq_of_ring ψ x0 d _ _
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.jetSubstP_comp_jetBC ψ m
      (fun p : Fin 1 × Fin d => (MvPolynomial.X (i, p.2) : MvPolynomial (Fin n × Fin d) S)))
  simpa only [MvPolynomial.map_X] using this

theorem sq_subst {n n' : ℕ} (m : ℕ) (φ : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S) :
    homAt (spMap ψ ≫ x0) (jetSubstP m fun p => MvPolynomial.map ψ (φ p)) ≫ rjBC ψ x0 d m n =
      rjBC ψ x0 d m n' ≫ homAt x0 (jetSubstP m φ) := sq_of_ring ψ x0 d _ _ (ReciprocityTheory.ChartRestriction.G.PullbackSections.jetSubstP_comp_jetBC ψ m φ)

theorem rjpt_bc (x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G) (x' : ∀ m, rjO (spMap ψ ≫ x0) d m 1 ⟶ Xo.univ.t.G)
    (hx : ∀ m, x' m = rjBC ψ x0 d m 1 ≫ x m) {n : ℕ} (m : ℕ) (i : Fin n) :
    rjpt (spMap ψ ≫ x0) d x' m i = rjBC ψ x0 d m n ≫ rjpt x0 d x m i := by
  unfold rjpt
  rw [hx, ← Category.assoc, sq_copy, Category.assoc]

private theorem padd_lemma_2 {T T' : Over Xo.X} (ρ : T' ⟶ T) (a b : T ⟶ Xo.univ.t.G) :
    ρ ≫ padd Xo.univ.t.G a b = padd Xo.univ.t.G (ρ ≫ a) (ρ ≫ b) := by
  unfold padd
  rw [← Category.assoc, comp_lift]

private theorem pzero_lemma_3 {T T' : Over Xo.X} (ρ : T' ⟶ T) :
    ρ ≫ pzero Xo.univ.t.G T = pzero Xo.univ.t.G T' := by
  unfold pzero
  rw [← Category.assoc]
  congr 1
  exact toUnit_unique _ _

private theorem foldr_lemma_4 {T T' : Over Xo.X} (ρ : T' ⟶ T) {n : ℕ} (v : Fin n → (T ⟶ Xo.univ.t.G))
    (v' : Fin n → (T' ⟶ Xo.univ.t.G)) (hv : ∀ k, v' k = ρ ≫ v k) (l : List (Fin n)) :
    ρ ≫ l.foldr (fun k acc => padd Xo.univ.t.G (v k) acc) (pzero Xo.univ.t.G T) =
      l.foldr (fun k acc => padd Xo.univ.t.G (v' k) acc) (pzero Xo.univ.t.G T') := by
  induction l with
  | nil => exact pzero_lemma_3 ρ
  | cons k l ih => simp only [List.foldr_cons]; rw [padd_lemma_2, ih, hv]

theorem cφ_comp {T T' : Over Xo.X} (ρ : T' ⟶ T) (a b : T ⟶ Xo.univ.t.G) :
    cφ ![ρ ≫ a, ρ ≫ b] = fun I => ρ.left ≫ cφ ![a, b] I := by
  funext I
  unfold cφ psum
  exact (congrArg Over.Hom.left (foldr_lemma_4 ρ ![a, b] ![ρ ≫ a, ρ ≫ b] (fun k => by fin_cases k <;> rfl) _)).symm

end

theorem exists_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G) (x' : ∀ m, rjO (spMap ψ ≫ x0) d m 1 ⟶ Xo.univ.t.G), (∀ m, x' m = rjBC ψ x0 d m 1 ≫ x m) → ∀ (e : ∀ m, RFrTy x0 d x m), (∀ m, (e m).IsGen) → ∃ e' : ∀ m, RFrTy (spMap ψ ≫ x0) d x' m, (∀ m, (e' m).IsGen) ∧ (∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (LB.pullGen Xo.univ.t.PP.L (cφ ![rjpt x0 d x m (0 : Fin 2), rjpt x0 d x m (1 : Fin 2)]) (cε 2) (e m) (rjBC ψ x0 d m 2).left)) ∧ ∀ (m n' : ℕ) (φ : Fin 2 → Fin d → MvPolynomial (Fin n' × Fin d) S), LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (rpe (spMap ψ ≫ x0) d x' e' m (fun i j => MvPolynomial.map ψ (φ i j))) (LB.pullGen Xo.univ.t.PP.L _ _ (rpe x0 d x e m φ) (rjBC ψ x0 d m n').left) := by
  intro E _ _ _ H Dw l Xo S S' _ _ ψ x0 d F act x x' hx e he
  have hφ : ∀ m, cφ ![rjpt (spMap ψ ≫ x0) d x' m (0 : Fin 2), rjpt (spMap ψ ≫ x0) d x' m (1 : Fin 2)] =
      fun k => (rjBC ψ x0 d m 2).left ≫ cφ ![rjpt x0 d x m (0 : Fin 2), rjpt x0 d x m (1 : Fin 2)] k := by
    intro m
    rw [rjpt_bc ψ x0 d x x' hx m 0, rjpt_bc ψ x0 d x x' hx m 1, cφ_comp]
  choose e' he' hcorr hnat using fun m =>
    exists_reindexed_pull Xo.univ.t.PP.isLB (cφ ![rjpt x0 d x m (0 : Fin 2), rjpt x0 d x m (1 : Fin 2)]) (cε 2)
      (e m) (he m) (rjBC ψ x0 d m 2).left _ (hφ m)
  refine ⟨e', he', fun m => hcorr m, fun m n' φ => ?_⟩
  have hab := congrArg Over.Hom.left (sq_subst ψ x0 d m (fun p : Fin 2 × Fin d => φ p.1 p.2))
  simp only [Over.comp_left] at hab
  unfold rpe
  exact hnat m _ _ _ _ _ hab

end GlobalTheory.RawFrameBC
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_symLift_pullback_isActOf : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left), L.IsLB → ∀ (k : ℤ) (T T' : Over S) (h : T' ⟶ T) (θ : ThetaGrp A L k T), ∃ θ' : ThetaGrp A L k T', θ'.pt = h ≫ θ.pt ∧ LB.Gen.Corr L _ _ _ _ θ'.φ (LB.pullGen L _ _ θ.φ (h ▷ A).left) ∧ (∀ (n : ℕ) (x : T ⟶ A), SymLift A L k n x θ → SymLift A L k n (h ≫ x) θ') ∧ ∀ (s t : LB.Sec (LPow A L k T)) (s' t' : LB.Sec (LPow A L k T')), IsActOf A L k θ s t → IsPullSec A L k (h ▷ A) (whiskerRight_snd _ _) s s' → IsPullSec A L k (h ▷ A) (whiskerRight_snd _ _) t t' → IsActOf A L k θ' s' t' := by
  first | exact @GlobalTheory.ThetaPullback.exists_thetaGrp_pullback | exact GlobalTheory.ThetaPullback.exists_thetaGrp_pullback | (intros; apply GlobalTheory.ThetaPullback.exists_thetaGrp_pullback <;> assumption)
end
