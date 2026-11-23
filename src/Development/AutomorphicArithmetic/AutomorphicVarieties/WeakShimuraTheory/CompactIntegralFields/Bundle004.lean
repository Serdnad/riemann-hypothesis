module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle002
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsValuationExtensionIntegral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
public import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.Valuation.LocalSubring
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

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem isDvr_coef {l : ℕ} [Fact l.Prime] (𝔞 : Amb l) (e : 𝔞.K ≃+* PadicAlgCl l) (h : 𝔞.IsZero e) (c : Coef l) :
    𝔞.IsDvr (𝔞.a c) := by
  haveI : CharZero c.O := charZero_of_injective_algebraMap (dvrFacts l c.O).1
  refine ⟨fun x y hxy => Subtype.ext ?_, 𝔞.loc c, inferInstance, (UpperTheory.V.abelian₂.dvr_finite l c.O).2.1, fun x => ?_⟩
  · rw [← h.1 c x, ← h.1 c y, hxy]
  · have h1 : IsAlgebraic ℚ_[l] (e x) := Algebra.IsAlgebraic.isAlgebraic _
    have h2 : IsAlgebraic ℤ_[l] (e x) := (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] _).2 h1
    have h3 : IsAlgebraic c.O (e x) := h2.extendScalars (dvrFacts l c.O).1
    obtain ⟨p, hp, hx⟩ := h3
    refine ⟨p, hp, e.injective ?_⟩
    have h4 : (e : 𝔞.K →+* PadicAlgCl l).comp (𝔞.toK.comp (𝔞.a c)) = algebraMap c.O (PadicAlgCl l) :=
      RingHom.ext fun z => h.1 c z
    have h5 := hom_eval₂ p (𝔞.toK.comp (𝔞.a c)) (e : 𝔞.K →+* PadicAlgCl l) x
    rw [h4] at h5
    rw [map_zero]
    exact h5.trans hx

theorem UpperTheory.V.Ws.eptV :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (𝔞 : Amb l) (e : 𝔞.K ≃+* PadicAlgCl l), 𝔞.IsZero e → ∀ r, D.EPt r → ∃ r', VPt D 𝔞 r' ∧ mapRep ((e : 𝔞.K →+* PadicAlgCl l).comp 𝔞.toK) r' = r := by
  intro Ω _ _ _ l _ c D _ 𝔞 e h r hr
  obtain ⟨R, _, _, _, ρ, y, hρ, rfl⟩ := hr
  obtain ⟨⟨c', hc', hy'⟩, a, ha1, -, hy⟩ := (coPt c R).1 y
  let y' : R →+* c'.O := (y : R →+* PadicAlgCl l).codRestrict c'.O hy'
  have hn : ∀ z : c'.O, ‖(z : PadicAlgCl l)‖ ≤ 1 := fun z => by
    rw [← h.1 c' z]
    exact (h.2 _).1 (𝔞.a c' z).2
  have hm : ∀ x ∈ maximalIdeal R, y' x ∈ maximalIdeal c'.O := by
    intro x hx hu
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    have h1 : y x * (w : PadicAlgCl l) = 1 := congrArg Subtype.val hw
    have h2 : ‖y x‖ ≤ a := by simpa using hy 1 x (by rwa [pow_one])
    have h3 := congrArg norm h1
    rw [norm_mul, norm_one] at h3
    have h4 := mul_le_of_le_one_right (norm_nonneg (y x)) (hn w)
    linarith
  refine ⟨mapRep ((𝔞.a c').comp y') ρ.hom, ⟨⟨c'.O, inferInstance, inferInstance, inferInstance, 𝔞.a c',
    ⟨mapRep y' ρ.hom, fun _ => 1⟩, isDvr_coef 𝔞 e h c', fun i j N => ?_, ?_⟩,
    R, _, _, _, ρ, (𝔞.a c').comp y', hρ, RingHom.ext fun x => ?_, fun x hx => ?_, rfl⟩, ?_⟩
  · have hle : maximalIdeal R ^ N ≤ (maximalIdeal c'.O ^ N).comap y' :=
      le_trans (Ideal.pow_right_mono hm N) (Ideal.le_comap_pow _ N)
    exact (ρ.cont i j N).comp (Ideal.quotientMap _ y' hle)
  · refine PD.ext rfl (funext fun _ => ?_)
    exact Matrix.map_one _ (map_zero _) (map_one _)
  · rw [← 𝔞.compat c c' hc' x]
    exact congrArg (𝔞.a c') (Subtype.ext (y.commutes x))
  · exact map_nonunit (𝔞.a c') _ (hm x hx)
  · ext g i j
    exact h.1 c' (y' (ρ.hom g i j))
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem coc_zero {Γ O k : Type} [Group Γ] [CommRing O] [Field k] (a : O →+* k) (A B : Γ →* Oˣ) (f : Γ → k)
    (hf : ∀ g h, f (g * h) = a (A g) * f h + f g * a (B h)) (h : Γ) (hh : a (A h) ≠ a (B h))
    (h0 : ∀ g, f (g * h * g⁻¹) = 0) (g : Γ) : f g = 0 := by
  have h1 : f h = 0 := by simpa using h0 1
  have h2 := hf (g * h * g⁻¹) g
  have h3 : A (g * h * g⁻¹) = A h := by simp [mul_comm (A g) (A h)]
  rw [h0, h3, inv_mul_cancel_right, hf, h1] at h2
  have h4 : f g * (a (A h) - a (B h)) = 0 := by linear_combination -h2
  exact (mul_eq_zero.1 h4).resolve_right (sub_ne_zero.2 hh)

private theorem conj_mem {Ω : Type} [Field Ω] [CharZero Ω] (F : IntermediateField ℚ Ω) [Normal ℚ F]
    (h : G F Ω) (g : G ℚ Ω) : ∃ h' : G F Ω, resQ F h' = g * resQ F h * g⁻¹ := by
  refine ⟨{ (g * resQ F h * g⁻¹).toRingEquiv with commutes' := fun x => ?_ }, rfl⟩
  have h1 := AlgEquiv.restrictNormal_commutes g⁻¹ F x
  have h2 := h.commutes ((AlgEquiv.restrictNormal g⁻¹ F) x)
  rw [h1] at h2
  show g (h (g⁻¹ (algebraMap F Ω x))) = algebraMap F Ω x
  rw [h2]
  exact g.apply_symm_apply _

private theorem ne_of_res {O k : Type} [CommRing O] [IsLocalRing O] [Field k] (a : O →+* k) {x y : O}
    (h : residue O x ≠ residue O y) : a x ≠ a y := by
  have h1 : IsUnit (x - y) := by
    by_contra hn
    apply h
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hn
  have h2 := (h1.map a).ne_zero
  rwa [map_sub, sub_ne_zero] at h2

private theorem flag_facts {k : Type} [Field k] (n n' r : M4 k) (hn : IsLow n) (hq : SuppM qQ n) (hn' : IsLow n')
    (hr : SuppM nP r) (h1 : r 1 1 ≠ 0) (hu : IsUp (adj n' * r * n)) :
    n' 2 1 = 0 ∧ n' 2 0 * r 0 0 = r 2 0 + r 2 2 * n 2 0 ∧ n' 1 0 * r 0 0 = r 1 0 + r 1 1 * n 1 0 + r 1 2 * n 2 0 := by
  have a21 : n 2 1 = 0 := hq 2 1 (by decide) (by decide)
  have r01 : r 0 1 = 0 := hr 0 1 (by decide) (by decide)
  have r02 : r 0 2 = 0 := hr 0 2 (by decide) (by decide)
  have r03 : r 0 3 = 0 := hr 0 3 (by decide) (by decide)
  have r13 : r 1 3 = 0 := hr 1 3 (by decide) (by decide)
  have r21 : r 2 1 = 0 := hr 2 1 (by decide) (by decide)
  have r23 : r 2 3 = 0 := hr 2 3 (by decide) (by decide)
  obtain ⟨-, d, u⟩ := hn
  obtain ⟨g', d', u'⟩ := hn'
  have a01 := u 0 1 (by decide)
  have b01 := u' 0 1 (by decide)
  have b02 := u' 0 2 (by decide)
  have b12 := u' 1 2 (by decide)
  have e21 := hu 2 1 (by decide)
  have e20 := hu 2 0 (by decide)
  have e10 := hu 1 0 (by decide)
  have g20 := congrFun (congrFun g' 2) 0
  have g10 := congrFun (congrFun g' 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev, a21, r01, r02, r03, r13, r21, r23, a01, b01, b02, b12, d, d', h1] at e21 e20 e10 g20 g10
  rw [e21] at e20 g20
  refine ⟨e21, ?_, ?_⟩
  · linear_combination (r 0 0) * g20 - e20
  · linear_combination (r 0 0) * g10 - e10

theorem UpperTheory.V.Ws.goodQ :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ T : Tower D, T.Fit → ∀ (k : Type) [Field k] (a : c.O →+* k), (∀ x ∈ maximalIdeal c.O, a x = 0) → ∀ (g0 : G ℚ Ω) (s : PD Unit (G ℚ Ω) k) (s' : PD T.ι (G T.F Ω) k), LatShape D T.pr g0 a s → (∀ w ∈ roots, a ((frQ D T.pr g0).rt w g0) ≠ 1) →
      T.OverQ s s' → (T.fr ∅).IsRes a s' → ∀ W : Finset ℕ, (T.fr W).IsRes a s' ∧ s'.In nP ∧
        (Ent s'.r (-wPs) ∧ Ent s'.r wBe ∨ Fr.InV (Φ := T.fr ∅) s' ∧ Ent s'.r (-wAl)) := by
  intro Ω _ _ _ l _ c D _ T hT k _ a _ g0 s s' hs _ hov hres W
  obtain ⟨hr, hfl⟩ := hov
  have hre : ∀ g, s'.r g = s.r (resQ T.F g) := fun g => by rw [hr]; rfl
  have diag : ∀ g i, s.r g i i = a (chi D T.pr i g) := hs.res.res.diag
  have ne0 : ∀ g i, s.r g i i ≠ 0 := fun g i => by
    rw [diag]; exact ((chi D T.pr i g).isUnit.map a).ne_zero
  have low : IsLow (s.n ()) := hs.res.pair.low ()
  have low' : ∀ v, IsLow (s'.n v) := hres.pair.low

  have key : ∀ i j, i ≠ j → (∀ g h, s.r (g * h) i j = s.r g i i * s.r h i j + s.r g i j * s.r h j j) →
      (∀ g, s'.r g i j = 0) → ∀ g, s.r g i j = 0 := by
    intro i j hij hc h0
    refine coc_zero a (chi D T.pr i) (chi D T.pr j) (fun g => s.r g i j) (fun g h => by rw [hc, diag, diag])
      (resQ T.F T.g0) (ne_of_res a (hT.1.dist i j hij)) fun g => ?_
    obtain ⟨h', e⟩ := conj_mem T.F T.g0 g
    rw [← e, ← hre]
    exact h0 h'
  have z : ∀ g i j, i ≠ j → wt i j ∉ nP → s.r g i j = 0 := hs.supp
  have ff : ∀ v, ∃ g, s'.n v 2 1 = 0 ∧ s'.n v 2 0 * s.r g 0 0 = s.r g 2 0 + s.r g 2 2 * s.n () 2 0 := by
    intro v
    obtain ⟨u, g, -, hu⟩ := hfl v
    have := flag_facts (s.n ()) (s'.n v) (s.r g) low hs.flag (low' v) (hs.supp g) (ne0 g 1) hu
    exact ⟨g, this.1, this.2.1⟩
  have hq : ∀ v, SuppM qQ (s'.n v) := by
    intro v i j hij hw
    obtain ⟨g, h21, -⟩ := ff v
    have : i < j ∨ (i = 2 ∧ j = 1) := by revert i j; decide
    rcases this with h | ⟨rfl, rfl⟩
    · exact (low' v).2.2 i j h
    · exact h21
  refine ⟨⟨⟨hres.pair.mult, fun g hg => hres.pair.kill g ?_, hres.pair.nrm, hres.pair.low, hres.pair.flag, hres.pair.mu⟩,
    ⟨hres.res.diag, hres.res.char, hres.res.shape⟩, hres.cont⟩, ⟨fun g => by rw [hre]; exact hs.supp _, hq⟩, ?_⟩
  · obtain ⟨A, hA, h⟩ := hg
    exact ⟨A, fun p hp => hA p (Finset.insert_subset_insert l (Finset.empty_subset W) hp), h⟩
  rcases hs.ps with hps | ⟨hv, h20, -, hnc⟩
  · left
    constructor
    · by_contra hn
      obtain ⟨g, i, j, hw, hg⟩ := hps
      refine hg (key i j ?_ (fun g h => ?_) (fun g => by_contra fun h => hn ⟨g, i, j, hw, h⟩) g)
      · clear hg; revert i j; decide
      · have : (i = 2 ∧ j = 0) ∨ (i = 3 ∧ j = 1) := by clear hg; revert i j; decide
        rw [map_mul, Matrix.mul_apply, Fin.sum_univ_four]
        rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [z g 2 1 (by decide) (by decide), z g 2 3 (by decide) (by decide)]; ring
        · rw [z h 0 1 (by decide) (by decide), z h 2 1 (by decide) (by decide)]; ring
    · by_contra hn
      obtain ⟨g, i, j, hw, hg⟩ := hs.be
      have : i = 1 ∧ j = 2 := by clear hg; revert i j; decide
      obtain ⟨rfl, rfl⟩ := this
      refine hg (key 1 2 (by decide) (fun g h => ?_) (fun g => by_contra fun h => hn ⟨g, 1, 2, hw, h⟩) g)
      rw [map_mul, Matrix.mul_apply, Fin.sum_univ_four, z h 0 2 (by decide) (by decide), z g 1 3 (by decide) (by decide)]
      ring
  · right
    have y0 : ∀ g, s.r g 2 0 = 0 := fun g => hv g 2 0 (by decide) (by decide)
    refine ⟨⟨fun g => by rw [hre]; exact hv _, fun v => ⟨hq v, fun h => ?_⟩⟩, ?_⟩
    · obtain ⟨g, -, e⟩ := ff v
      have h' : s'.n v 2 0 = 0 := h
      rw [h', y0, zero_mul, zero_add] at e
      exact mul_ne_zero (ne0 g 2) h20 e.symm
    · by_contra hn
      have x0 : ∀ g, s.r g 1 0 = 0 := by
        refine key 1 0 (by decide) (fun g h => ?_) (fun g => by_contra fun h => hn ⟨g, 1, 0, by decide, h⟩)
        rw [map_mul, Matrix.mul_apply, Fin.sum_univ_four, y0, z g 1 3 (by decide) (by decide)]
        ring
      refine hnc ⟨s.n () 1 0 / s.n () 2 0, fun g hg => ?_⟩
      obtain ⟨-, e1, e2⟩ := flag_facts (s.n ()) (s.n ()) (s.r g) low hs.flag low (hs.supp g) (ne0 g 1)
        (hs.res.pair.flag () g hg)
      rw [y0, zero_add, mul_comm] at e1
      have e3 := mul_right_cancel₀ h20 e1
      rw [x0, e3] at e2
      rw [← diag, ← diag]
      field_simp
      linear_combination -e2
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem cont_of_adic {Γ R K : Type} [TopologicalSpace Γ] [CommRing R] [NormedRing K] (I : Ideal R)
    (y : R →+* K) (a : ℝ) (ha1 : a < 1) (hy : ∀ n, ∀ x ∈ I ^ n, ‖y x‖ ≤ a ^ n)
    (f : Γ → R) (hf : AdicCont I f) : Continuous fun g => y (f g) := by
  have ha0 : 0 ≤ a := by simpa using hy 1 0 (Ideal.zero_mem _)
  rw [Metric.continuous_iff']
  intro g0 ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε ha1
  have hopen := (hf N).isOpen_fiber ((Ideal.Quotient.mk (I ^ N)) (f g0))
  filter_upwards [hopen.mem_nhds rfl] with g hg
  rw [dist_eq_norm, ← map_sub]
  exact lt_of_le_of_lt (hy N _ (Ideal.Quotient.eq.mp hg)) hN

theorem UpperTheory.V.Ws.smallCont :
    ∀ {l : ℕ} [Fact l.Prime] (𝔞 : Amb l) (e : 𝔞.K ≃+* PadicAlgCl l), 𝔞.IsZero e → ∀ {ι Γ : Type} [Group Γ] [TopologicalSpace Γ]
          (P : PD ι Γ 𝔞.V), 𝔞.Small P → Continuous (mapRep ((e : 𝔞.K →+* PadicAlgCl l).comp 𝔞.toK) P.r) := by
  intro l _ 𝔞 e he ι Γ _ _ P hP
  obtain ⟨A, _, _, _, f, P₁, hf, hc, rfl⟩ := hP
  obtain ⟨inj, loc, -, -, -⟩ := hf
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  let y : A →+* PadicAlgCl l := (e : 𝔞.K →+* PadicAlgCl l).comp (𝔞.toK.comp f)
  have hV : ∀ v : 𝔞.V, ‖e (v : 𝔞.K)‖ ≤ 1 := fun v => (he.2 _).mp v.2
  have hle : ∀ x : A, ‖y x‖ ≤ 1 := fun x => hV (f x)
  have hlt : ‖y ϖ‖ < 1 := by
    refine lt_of_le_of_ne (hle ϖ) fun h1 => hϖ.not_isUnit ?_
    have hne : (f ϖ : 𝔞.K) ≠ 0 := by
      intro h0
      have h0' : f ϖ = 0 := Subtype.ext h0
      exact hϖ.ne_zero (inj (by rw [h0', map_zero]))
    have h1' : ‖e (f ϖ : 𝔞.K)‖ = 1 := h1
    have hinv : ((f ϖ : 𝔞.K))⁻¹ ∈ 𝔞.V := by
      rw [he.2, map_inv₀, norm_inv, h1', inv_one]
    have hu : IsUnit (f ϖ) := IsUnit.of_mul_eq_one (⟨_, hinv⟩ : 𝔞.V) (Subtype.ext (mul_inv_cancel₀ hne))
    haveI := loc
    exact (isUnit_map_iff f ϖ).mp hu
  have hpow : ∀ n, ∀ x ∈ maximalIdeal A ^ n, ‖y x‖ ≤ ‖y ϖ‖ ^ n := by
    intro n x hx
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
    obtain ⟨c, rfl⟩ := hx
    rw [map_mul, map_pow, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) (hle c)
  refine continuous_matrix fun i j => ?_
  have hc' : AdicCont (maximalIdeal A) fun g => P₁.r g i j := by
    unfold PD.Cont at hc
    exact hc i j
  exact cont_of_adic (maximalIdeal A) y _ hlt hpow (fun g => P₁.r g i j) hc'
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem al_loc {l : ℕ} [Fact l.Prime] (c : Coef l) {B : Type} [CommRing B] [IsDomain B] [CharP B l] (g : c.O →+* B) :
    IsLocalHom g := by
  have hl : (l : c.O) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hk : RingHom.ker g ≠ ⊥ := fun h => hl (by
    have : (l : c.O) ∈ RingHom.ker g := by rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
    rwa [h, Ideal.mem_bot] at this)
  have hm : RingHom.ker g = maximalIdeal c.O := eq_maximalIdeal ((RingHom.ker_isPrime g).isMaximal hk)
  refine ⟨fun x hx => by_contra fun h => hx.ne_zero ?_⟩
  have : x ∈ RingHom.ker g := hm ▸ (mem_maximalIdeal x).2 h
  exact this

private theorem al_le {l : ℕ} [Fact l.Prime] (c : Coef l) : c.O ≤ integralClosure ℤ_[l] (PadicAlgCl l) := fun x hx =>
  (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val

theorem UpperTheory.V.Ws.ambL :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A]
      [Finite (ResidueField A)] [CharP A l] (a : c.O →+* A), ∃ (𝔞 : Amb l) (f : A →+* 𝔞.V), CharP 𝔞.K l ∧ 𝔞.IsDvr f ∧ f.comp a = 𝔞.a c := by
  intro l _ c A _ _ _ _ _ _ a
  haveI := c.dvr
  haveI := c.fin
  let K := AlgebraicClosure (FractionRing A)
  let g0 : A →+* K := (algebraMap (FractionRing A) K).comp (algebraMap A (FractionRing A))
  have hg0 : Function.Injective g0 :=
    (algebraMap (FractionRing A) K).injective.comp (IsFractionRing.injective A (FractionRing A))
  obtain ⟨V, hV, hloc⟩ := IsLocalRing.exists_factor_valuationRing g0
  let f : A →+* V := g0.codRestrict V hV
  have hfinj : Function.Injective f := fun x y h => hg0 (congrArg Subtype.val h)
  have hfloc : IsLocalHom f := hloc
  haveI hK : CharP K l := charP_of_injective_ringHom hg0 l
  haveI : CharP V l := charP_of_injective_ringHom hfinj l
  have heq : V.subtype.comp f = g0 := RingHom.ext fun _ => rfl
  have halg : ∀ z : K, ∃ p : A[X], p ≠ 0 ∧ eval₂ (V.subtype.comp f) z p = 0 := by
    intro z
    obtain ⟨q, hq0, hq⟩ := Algebra.IsAlgebraic.isAlgebraic (R := FractionRing A) z
    refine ⟨IsLocalization.integerNormalization (nonZeroDivisors A) q, ?_, ?_⟩
    · rwa [Ne, IsFractionRing.integerNormalization_eq_zero_iff]
    · rw [Polynomial.aeval_def] at hq
      rw [heq]
      exact IsLocalization.integerNormalization_eval₂_eq_zero (nonZeroDivisors A)
        (algebraMap (FractionRing A) K) q hq
  let S := integralClosure c.O (PadicAlgCl l)
  have hinj : Function.Injective (algebraMap c.O S) := by
    intro x y h
    apply Subtype.ext
    have h2 := congrArg Subtype.val h
    exact h2
  obtain ⟨Φ, hΦ⟩ := UpperTheory.exists_valuation_extension_integral c.O S K V hinj (f.comp a)
  have hS : ∀ c' : Coef l, ∀ x : c'.O, (x : PadicAlgCl l) ∈ S := fun c' x =>
    IsIntegral.tower_top (A := c.O) (al_le c' x.2)
  let ι : ∀ c' : Coef l, c'.O →+* S := fun c' => c'.O.val.toRingHom.codRestrict S (hS c')
  refine ⟨Amb.mk K V (fun c' => Φ.comp (ι c')) ?_ ?_ ?_, f, hK, ⟨hfinj, hfloc, inferInstance, inferInstance, halg⟩, ?_⟩
  · intro c1 c2 h x
    exact congrArg Φ (Subtype.ext rfl)
  · intro c'
    exact al_loc c' _
  · intro x
    obtain ⟨p, hp0, hp⟩ := halg x
    have hint := UpperTheory.residue_isIntegral_of_algebraic_over_dvr A K V f hfinj hfloc x ⟨p, hp0, hp⟩
    obtain ⟨y, hy⟩ := UpperTheory.exists_integralClosure_preimage_of_isIntegral c.O (PadicAlgCl l) (ResidueField V)
      ((IsLocalRing.residue V).comp Φ) (IsLocalRing.residue V x) hint
    have hyl : IsIntegral ℤ_[l] (y : PadicAlgCl l) := isIntegral_trans (A := c.O) _ y.2
    obtain ⟨c', -, hc'⟩ := (coefSup l).2.2.1 c y.1 hyl
    refine ⟨c', ⟨y.1, hc'⟩, ?_⟩
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, ← hy]
    rfl
  · exact hΦ.symm.trans (congrArg Φ.comp (RingHom.ext fun x => Subtype.ext rfl))
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem az_intIff {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

open Cardinal in
private theorem az_card (l : ℕ) [Fact l.Prime] : #(PadicAlgCl l) = 𝔠 := by
  have h1 : #ℚ_[l] ≤ #(CauSeq ℚ (padicNorm l)) :=
    mk_le_of_surjective (f := (Quotient.mk'' : CauSeq ℚ (padicNorm l) → ℚ_[l])) Quotient.mk''_surjective
  have h2 : #(CauSeq ℚ (padicNorm l)) ≤ #(ℕ → ℚ) := mk_subtype_le _
  have h3 : #(ℕ → ℚ) = 𝔠 := by simp
  apply le_antisymm
  · refine (Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[l] (PadicAlgCl l)).trans ?_
    exact max_le (h1.trans (h2.trans h3.le)) aleph0_le_continuum
  · have h : 𝔠 ≤ #ℚ_[l] := continuum_le_cardinal_of_nontriviallyNormedField ℚ_[l]
    exact h.trans (mk_le_of_injective (algebraMap ℚ_[l] (PadicAlgCl l)).injective)

private noncomputable def azV (l : ℕ) [Fact l.Prime] : ValuationSubring (PadicAlgCl l) :=
  (NormedField.valuation : Valuation (PadicAlgCl l) NNReal).valuationSubring

private theorem mem_azV {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : x ∈ azV l ↔ ‖x‖ ≤ 1 := by
  show ‖x‖₊ ≤ 1 ↔ _
  exact_mod_cast Iff.rfl

private noncomputable def azA {l : ℕ} [Fact l.Prime] (c : Coef l) : c.O →+* azV l :=
  (c.O.val : c.O →+* PadicAlgCl l).codRestrict (azV l) fun x =>
    (mem_azV _).2 ((az_intIff _).1 ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x).map c.O.val))

private theorem azA_loc {l : ℕ} [Fact l.Prime] (c : Coef l) : IsLocalHom (azA c) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := hx.exists_left_inv
  have hy' : (y : PadicAlgCl l) * (x : PadicAlgCl l) = 1 := congrArg Subtype.val hy
  have h0 : (x : PadicAlgCl l) ≠ 0 := right_ne_zero_of_mul_eq_one hy'
  have hm : (y : PadicAlgCl l) ∈ c.O :=
    (coefSup l).2.2.2 c y ((az_intIff _).2 ((mem_azV _).1 y.2)) ⟨1, x, h0, hy'⟩
  exact IsUnit.of_mul_eq_one_right (⟨y, hm⟩ : c.O) (Subtype.ext hy')

theorem UpperTheory.V.Ws.ambZero :
    ∀ (l : ℕ) [Fact l.Prime], (∃ (𝔞 : Amb l) (e : 𝔞.K ≃+* PadicAlgCl l), 𝔞.IsZero e) ∧ Nonempty (PadicAlgCl l ≃+* ℂ) := by
  intro l hl
  refine ⟨⟨{ K := PadicAlgCl l, V := azV l, a := azA, compat := fun _ _ _ _ => rfl, loc := azA_loc, alg := fun x => ?_ },
    RingEquiv.refl _, fun _ _ => rfl, mem_azV⟩, ?_⟩
  · obtain ⟨c, -⟩ := (coefSup l).2.1 1 (by rw [Nat.dvd_one]; exact hl.out.ne_one)
    obtain ⟨c', -, hx⟩ := (coefSup l).2.2.1 c x ((az_intIff _).2 ((mem_azV _).1 x.2))
    refine ⟨c', ⟨x, hx⟩, ?_⟩
    have : azA c' ⟨x, hx⟩ = x := rfl
    rw [this, sub_self]
    exact Ideal.zero_mem _
  · apply IsAlgClosed.ringEquiv_of_equiv_of_charZero
    · rw [az_card]; exact Cardinal.aleph0_lt_continuum
    · exact Cardinal.eq.1 (by rw [az_card, Cardinal.mk_complex])
end
