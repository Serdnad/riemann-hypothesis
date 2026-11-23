module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Flat.Basic
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle005
public import Mathlib.RingTheory.Ideal.Height
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne
public import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Ideal.GoingDown

@[expose] public section

section

namespace ReciprocityTheory.AnForm.R.BaseChangeC

open MvPolynomial TensorProduct

variable {σ : Type} [Fintype σ]

section Rad

end Rad

section GD

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem flat_mvPolynomial_rat_complex :
    Module.Flat (MvPolynomial σ ℚ) (MvPolynomial σ ℂ) :=
  Module.Flat.isBaseChange ℚ (MvPolynomial σ ℚ) ℂ (MvPolynomial σ ℂ)
    (Algebra.IsPushout.out (R := ℚ) (S := MvPolynomial σ ℚ) (R' := ℂ) (S' := MvPolynomial σ ℂ))

theorem comap_of_mem_minimalPrimes_map (𝔭 : Ideal (MvPolynomial σ ℚ)) [𝔭.IsPrime]
    (Q : Ideal (MvPolynomial σ ℂ))
    (hQ : Q ∈ (Ideal.map (MvPolynomial.map (algebraMap ℚ ℂ)) 𝔭).minimalPrimes) :
    Q.comap (MvPolynomial.map (algebraMap ℚ ℂ)) = 𝔭 := by
  have := flat_mvPolynomial_rat_complex (σ := σ)
  have hQp : Q.IsPrime := hQ.1.1
  have hle : Ideal.map (algebraMap (MvPolynomial σ ℚ) (MvPolynomial σ ℂ)) 𝔭 ≤ Q := hQ.1.2
  set q := Q.comap (algebraMap (MvPolynomial σ ℚ) (MvPolynomial σ ℂ)) with hq
  have : q.IsPrime := Ideal.comap_isPrime _ _
  have : Q.LiesOver q := ⟨rfl⟩
  have hpq : 𝔭 ≤ q := Ideal.map_le_iff_le_comap.mp hle
  obtain ⟨P, hPQ, hP, hPl⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := 𝔭) Q hpq
  have hPext : Ideal.map (MvPolynomial.map (algebraMap ℚ ℂ)) 𝔭 ≤ P := by
    rw [Ideal.map_le_iff_le_comap]
    exact hPl.over.le
  have hQP : Q ≤ P := hQ.2 ⟨hP, hPext⟩ hPQ
  have hPQe : P = Q := le_antisymm hPQ hQP
  subst hPQe
  exact hPl.over.symm

theorem height_eq_of_mem_minimalPrimes_map (𝔭 : Ideal (MvPolynomial σ ℚ)) [𝔭.IsPrime]
    (Q : Ideal (MvPolynomial σ ℂ))
    (hQ : Q ∈ (Ideal.map (MvPolynomial.map (algebraMap ℚ ℂ)) 𝔭).minimalPrimes) :
    Q.height = 𝔭.height := by
  have := flat_mvPolynomial_rat_complex (σ := σ)
  have : Q.IsPrime := hQ.1.1
  have hc := comap_of_mem_minimalPrimes_map 𝔭 Q hQ
  have : Q.LiesOver 𝔭 := ⟨hc.symm⟩
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown 𝔭 Q]
  have h0 : (Q.map (Ideal.Quotient.mk (𝔭.map (algebraMap (MvPolynomial σ ℚ) (MvPolynomial σ ℂ))))).height = 0 := by
    have hQ' : Q ∈ (𝔭.map (algebraMap (MvPolynomial σ ℚ) (MvPolynomial σ ℂ))).minimalPrimes := hQ
    rw [Ideal.minimalPrimes_eq_comap] at hQ'
    obtain ⟨Q', hQ'm, hQ'e⟩ := hQ'
    have : Q'.IsPrime := hQ'm.1.1
    rw [← hQ'e, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    exact Ideal.height_eq_zero_iff.mpr hQ'm
  rw [h0, add_zero]

end GD

theorem height_add_ringKrullDim_quotient_fintype (k : Type) [Field k]
    (P : Ideal (MvPolynomial σ k)) [P.IsPrime] :
    (P.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial σ k ⧸ P) = Fintype.card σ := by
  let e : MvPolynomial σ k ≃+* MvPolynomial (Fin (Fintype.card σ)) k :=
    (MvPolynomial.renameEquiv k (Fintype.equivFin σ)).toRingEquiv
  have : (P.map e).IsPrime := Ideal.map_isPrime_of_equiv e
  have h := ReciprocityTheory.CA.height_add_ringKrullDim_quotient_mvPolynomial_field k _ (P.map e)
  rw [RingEquiv.height_map,
    ← ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv P (P.map e) e rfl)] at h
  exact h

theorem withBot_enat_cancel {h : ℕ∞} {a b : WithBot ℕ∞} {N : ℕ}
    (ha : (h : WithBot ℕ∞) + a = N) (hb : (h : WithBot ℕ∞) + b = N) : a = b := by
  induction a using WithBot.recBotCoe with
  | bot => simp at ha
  | coe a =>
    induction b using WithBot.recBotCoe with
    | bot => simp at hb
    | coe b =>
      have ha' : h + a = N := by exact_mod_cast ha
      have hb' : h + b = N := by exact_mod_cast hb
      congr 1
      induction h using ENat.recTopCoe with
      | top => simp at ha'
      | coe h => exact WithTop.add_left_cancel (ENat.coe_ne_top h) (ha'.trans hb'.symm)

theorem ringKrullDim_of_mem_minimalPrimes_map (𝔭 : Ideal (MvPolynomial σ ℚ)) [𝔭.IsPrime]
    (Q : Ideal (MvPolynomial σ ℂ))
    (hQ : Q ∈ (Ideal.map (MvPolynomial.map (algebraMap ℚ ℂ)) 𝔭).minimalPrimes) :
    ringKrullDim (MvPolynomial σ ℂ ⧸ Q) = ringKrullDim (MvPolynomial σ ℚ ⧸ 𝔭) := by
  have : Q.IsPrime := hQ.1.1
  have h1 := height_add_ringKrullDim_quotient_fintype ℂ Q
  have h2 := height_add_ringKrullDim_quotient_fintype ℚ 𝔭
  rw [height_eq_of_mem_minimalPrimes_map 𝔭 Q hQ] at h1
  exact withBot_enat_cancel h1 h2

end ReciprocityTheory.AnForm.R.BaseChangeC
end

section

namespace ReciprocityTheory.AnForm.R

open MvPolynomial

variable {n : ℕ}

private theorem withBot_add_right_cancel {a b : WithBot ℕ∞} {c : ℕ∞} {N : ℕ}
    (h : a + (c : WithBot ℕ∞) = b + c) (hb : b + (c : WithBot ℕ∞) = N) : a = b := by
  induction b using WithBot.recBotCoe with
  | bot => simp at hb
  | coe y =>
    induction a using WithBot.recBotCoe with
    | bot => rw [← h] at hb; simp at hb
    | coe x =>
      rw [← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_inj] at h
      rw [← WithBot.coe_add] at hb
      have hc : c ≠ ⊤ := by
        rintro rfl
        rw [add_top] at hb
        rw [← WithBot.coe_natCast, WithBot.coe_inj] at hb
        exact ENat.top_ne_natCast N hb
      exact congrArg _ (WithTop.add_right_cancel hc h)

theorem regular_point_unique_minimalPrime (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    [IsRegularLocalRing (locRing K p)] :
    ∃ 𝔮 ∈ K.minimalPrimes, 𝔮 ≤ ptIdeal p ∧
      (∀ 𝔮' ∈ K.minimalPrimes, 𝔮' ≤ ptIdeal p → 𝔮' = 𝔮) ∧
      ringKrullDim (locRing K p) + (𝔮.height : WithBot ℕ∞) = n := by
  set A := MvPolynomial (Fin n) ℂ
  set P := ptIdeal p
  set S := locPt p
  set I : Ideal S := Ideal.map (algebraMap A S) K with hI
  have : IsDomain (S ⧸ I) := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain _
  have hIp : I.IsPrime := (Ideal.Quotient.isDomain_iff_prime I).mp inferInstance
  set 𝔮 : Ideal A := I.under A with h𝔮
  have h𝔮p : 𝔮.IsPrime := Ideal.IsPrime.under A I
  have hdisj : Disjoint (P.primeCompl : Set A) 𝔮 :=
    ((IsLocalization.isPrime_iff_isPrime_disjoint P.primeCompl S I).mp hIp).2
  have h𝔮P : 𝔮 ≤ P := by
    intro x hx
    by_contra hxP
    exact Set.disjoint_left.mp hdisj (show x ∈ (P.primeCompl : Set A) from hxP) hx
  have hK𝔮 : K ≤ 𝔮 := fun x hx => Ideal.mem_map_of_mem _ hx

  have key : ∀ Q : Ideal A, Q.IsPrime → K ≤ Q → Q ≤ P → 𝔮 ≤ Q := by
    intro Q hQ hKQ hQP
    have hd : Disjoint (P.primeCompl : Set A) Q := by
      rw [Set.disjoint_left]
      intro x hx hxQ
      exact hx (hQP hxQ)
    have hmap : I ≤ Ideal.map (algebraMap A S) Q := Ideal.map_mono hKQ
    calc 𝔮 ≤ (Ideal.map (algebraMap A S) Q).under A := Ideal.comap_mono hmap
      _ = Q := IsLocalization.under_map_of_isPrime_disjoint P.primeCompl S hQ hd
  have hmin : 𝔮 ∈ K.minimalPrimes :=
    ⟨⟨h𝔮p, hK𝔮⟩, fun Q ⟨hQ, hKQ⟩ hQ𝔮 => key Q hQ hKQ (hQ𝔮.trans h𝔮P)⟩
  refine ⟨𝔮, hmin, h𝔮P, ?_, ?_⟩
  · intro 𝔮' h' h'P
    exact le_antisymm (h'.2 ⟨h𝔮p, hK𝔮⟩ (key 𝔮' h'.1.1 h'.1.2 h'P)) (key 𝔮' h'.1.1 h'.1.2 h'P)
  ·
    set 𝔪 : Ideal (A ⧸ 𝔮) := P.map (Ideal.Quotient.mk 𝔮) with h𝔪
    have hmem : ∀ a : A, Ideal.Quotient.mk 𝔮 a ∈ 𝔪 ↔ a ∈ P := fun a =>
      Ideal.mem_quotient_iff_mem h𝔮P
    have hPmax : P.IsMaximal := ptIdeal_isMaximal p
    have h𝔪max : 𝔪.IsMaximal := by
      rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk 𝔮) Ideal.Quotient.mk_surjective hPmax with h | h
      · exfalso
        have h1 : Ideal.Quotient.mk 𝔮 1 ∈ 𝔪 := by rw [h𝔪, h]; exact Submodule.mem_top
        exact hPmax.ne_top ((Ideal.eq_top_iff_one (I := P)).mpr ((hmem 1).mp h1))
      · exact h
    let f : A ⧸ 𝔮 →+* S ⧸ I := Ideal.quotientMap I (algebraMap A S) le_rfl
    letI : Algebra (A ⧸ 𝔮) (S ⧸ I) := f.toAlgebra
    have hf : ∀ a : A, algebraMap (A ⧸ 𝔮) (S ⧸ I) (Ideal.Quotient.mk 𝔮 a) =
        Ideal.Quotient.mk I (algebraMap A S a) := fun a => Ideal.quotientMap_mk
    have hloc : IsLocalization.AtPrime (S ⧸ I) 𝔪 := by
      show IsLocalization 𝔪.primeCompl (S ⧸ I)
      rw [isLocalization_iff]
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨y, hy⟩
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
        have ha : a ∈ P.primeCompl := fun h => hy ((hmem a).mpr h)
        rw [hf]
        exact (IsLocalization.map_units S (⟨a, ha⟩ : P.primeCompl)).map _
      · intro z
        obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective z
        obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl s
        have ht : Ideal.Quotient.mk 𝔮 (t : A) ∈ 𝔪.primeCompl := fun h => t.2 ((hmem _).mp h)
        refine ⟨⟨Ideal.Quotient.mk 𝔮 a, ⟨_, ht⟩⟩, ?_⟩
        simp only [hf, ← map_mul]
        rw [IsLocalization.mk'_spec]
      · intro x y hxy
        exact ⟨1, by rw [Ideal.quotientMap_injective hxy]⟩
    have hdim : ringKrullDim (S ⧸ I) = 𝔪.height :=
      IsLocalization.AtPrime.ringKrullDim_eq_height 𝔪 (S ⧸ I)
    have hsum := ReciprocityTheory.CA.height_add_height_maximal_quotient_field ℂ n 𝔮 𝔪
    show ringKrullDim (S ⧸ I) + _ = _
    rw [hdim, ← WithBot.coe_add, add_comm, hsum]
    rfl

theorem ringKrullDim_locRing_eq_of_minimalPrime (K : Ideal (MvPolynomial (Fin n) ℂ))
    (p p' : Fin n → ℂ) [IsRegularLocalRing (locRing K p)] [IsRegularLocalRing (locRing K p')]
    (𝔮 : Ideal (MvPolynomial (Fin n) ℂ)) (h𝔮 : 𝔮 ∈ K.minimalPrimes)
    (hp : 𝔮 ≤ ptIdeal p) (hp' : 𝔮 ≤ ptIdeal p') :
    ringKrullDim (locRing K p) = ringKrullDim (locRing K p') := by
  obtain ⟨q1, -, -, hu1, hd1⟩ := regular_point_unique_minimalPrime K p
  obtain ⟨q2, -, -, hu2, hd2⟩ := regular_point_unique_minimalPrime K p'
  obtain rfl := hu1 𝔮 h𝔮 hp
  obtain rfl := hu2 𝔮 h𝔮 hp'
  rw [← hd2] at hd1
  exact withBot_add_right_cancel hd1 hd2

end ReciprocityTheory.AnForm.R
end

section

namespace ReciprocityTheory.AnForm.R

open MvPolynomial ReciprocityTheory.AnForm.M Topology Filter

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem AlgRes.fderiv_affCoord_ker_eq_bot {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}
    (R : AlgRes ι P D e) (A : FinHolAtlas e R.M) (hA : R.IsGoodAtlas A) (i : Fin R.n)
    (x : R.M) (hx : x ∈ R.src i) (hxD : (fun q => eval (R.coord i x) (R.lift i q)) ∉ conePts D)
    (p : (k : K) → ι k) (hp : ∀ k, eval (R.coord i x) (R.lift i ⟨k, p k⟩) ≠ 0)
    (j : Fin A.n) (hj : x ∈ (A.chart j).source) :
    (fderiv ℂ (fun y => affCoord p (fun q => eval (R.coord i ((A.chart j).symm y)) (R.lift i q)))
      (A.chart j x)).ker = ⊥ := by
  classical
  have hy0t : A.chart j x ∈ (A.chart j).target := (A.chart j).map_source hj
  have hsy0 : (A.chart j).symm (A.chart j x) = x := (A.chart j).left_inv hj
  set f : (Fin e → ℂ) → (Σ k, ι k) → ℂ :=
    fun y => affCoord p (fun q => eval (R.coord i ((A.chart j).symm y)) (R.lift i q)) with hfdef
  obtain ⟨O, hO, hxO, -, q, F, hOF⟩ := R.inv i x hx hxD p hp
  obtain ⟨ψ, hψc, hxψ, hψs, hψ⟩ :=
    hA.2 i x hx (R.sncAt i x hx).r (R.sncAt i x hx).span_eq O hO hxO
  set r := (R.sncAt i x hx).r with hr
  have hw0 : f (A.chart j x) = affCoord p (fun q => eval (R.coord i x) (R.lift i q)) := by
    simp only [f, hsy0]
  have hqw0 : eval (f (A.chart j x)) q ≠ 0 := by rw [hw0]; exact (hOF x hxO).2.1
  let H : ((Σ k, ι k) → ℂ) → Fin (R.amb i) → ℂ := fun w l => eval w (F l) / eval w q
  let G : ((Σ k, ι k) → ℂ) → Fin e → ℂ := fun w => (A.chart j ∘ ψ.symm) (evalFam r (H w))
  have hHx : ∀ y ∈ O, H (affCoord p fun q => eval (R.coord i y) (R.lift i q)) = R.coord i y := by
    intro y hy; funext l; simp only [H]; rw [div_eq_iff (hOF y hy).2.1]; exact ((hOF y hy).2.2 l).symm
  have hH0 : H (f (A.chart j x)) = R.coord i x := by rw [hw0]; exact hHx x hxO
  have hHan : AnalyticAt ℂ H (f (A.chart j x)) := by
    rw [analyticAt_pi_iff]; intro l
    exact (AnalyticOnNhd.eval_mvPolynomial (F l) _ (Set.mem_univ _)).div
      (AnalyticOnNhd.eval_mvPolynomial q _ (Set.mem_univ _)) hqw0
  have hEan : AnalyticAt ℂ (evalFam r) (H (f (A.chart j x))) := by
    rw [analyticAt_pi_iff]; intro l
    exact AnalyticOnNhd.eval_mvPolynomial (r l) _ (Set.mem_univ _)
  have hTan : AnalyticAt ℂ (A.chart j ∘ ψ.symm) (evalFam r (H (f (A.chart j x)))) := by
    rw [hH0, ← hψ x hxψ]
    refine (hψc j).2 (ψ x) ⟨ψ.map_source hxψ, ?_⟩
    show ψ.symm (ψ x) ∈ (A.chart j).source
    rw [ψ.left_inv hxψ]; exact hj
  have hGd : DifferentiableAt ℂ G (f (A.chart j x)) :=
    DifferentiableAt.comp (g := A.chart j ∘ ψ.symm) (f := evalFam r ∘ H) (f (A.chart j x))
      hTan.differentiableAt
      (DifferentiableAt.comp (f (A.chart j x)) hEan.differentiableAt hHan.differentiableAt)
  have hfd : DifferentiableAt ℂ f (A.chart j x) := by
    rw [differentiableAt_pi]; intro q'
    have hmem : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' R.src i :=
      ⟨hy0t, by show (A.chart j).symm (A.chart j x) ∈ R.src i; rw [hsy0]; exact hx⟩
    have h1 := hA.1 i (R.lift i q') j (A.chart j x) hmem
    have h2 := hA.1 i (R.lift i ⟨q'.1, p q'.1⟩) j (A.chart j x) hmem
    have hne : ((fun y => eval (R.coord i y) (R.lift i ⟨q'.1, p q'.1⟩)) ∘ (A.chart j).symm)
        (A.chart j x) ≠ 0 := by
      simp only [Function.comp, hsy0]; exact hp q'.1
    exact (h1.div h2 hne).differentiableAt
  have hev : (G ∘ f) =ᶠ[𝓝 (A.chart j x)] id := by
    have h1 : ∀ᶠ y in 𝓝 (A.chart j x), y ∈ (A.chart j).target :=
      (A.chart j).open_target.mem_nhds hy0t
    have h2 : ∀ᶠ y in 𝓝 (A.chart j x), (A.chart j).symm y ∈ ψ.source :=
      ((A.chart j).continuousAt_symm hy0t).preimage_mem_nhds
        (ψ.open_source.mem_nhds (by rw [hsy0]; exact hxψ))
    filter_upwards [h1, h2] with y hy1 hy2
    have hy'O : (A.chart j).symm y ∈ O := (hψs hy2).1
    show (A.chart j) (ψ.symm (evalFam r (H (f y)))) = y
    have hfy : f y = affCoord p (fun q => eval (R.coord i ((A.chart j).symm y)) (R.lift i q)) := rfl
    rw [hfy, hHx _ hy'O, ← hψ _ hy2, ψ.left_inv hy2, (A.chart j).right_inv hy1]
  have hcomp := hGd.hasFDerivAt.comp (A.chart j x) hfd.hasFDerivAt
  have huniq := hcomp.unique ((hasFDerivAt_id (A.chart j x)).congr_of_eventuallyEq hev)
  rw [LinearMap.ker_eq_bot']
  intro v hv
  have := congrArg (fun L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ) => L v) huniq
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this
  have hv' : fderiv ℂ f (A.chart j x) v = 0 := hv
  rw [← this, hv', map_zero]

end ReciprocityTheory.AnForm.R
end
