module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle003
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle070
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle067
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.RingTheory.MvPowerSeries.Order
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
import Mathlib.Tactic.Lemma
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
public import Mathlib.RingTheory.Ideal.BigOperators
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

section

variable {O R : Type} [CommRing O] [CommRing R] [Algebra O R] {X : Type} [AddCommGroup X]

private lemma prod_pow_mem {S σ : Type} [CommRing S] (I : Ideal S) (z : σ → S) (hz : ∀ i, z i ∈ I)
    (m : σ →₀ ℕ) {n : ℕ} (hn : n ≤ m.degree) : (m.prod fun i k => z i ^ k) ∈ I ^ n := by
  refine Ideal.pow_le_pow_right hn ?_
  rw [Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (hz i) _

private lemma π_monomial (W : WPres O X R) (m : W.σ →₀ ℕ) :
    W.π (monomial m 1) = m.prod fun i k => W.z i ^ k := by
  rw [MvPowerSeries.monomial_one_eq, Finsupp.prod, Finsupp.prod, map_prod]
  simp [WPres.z]

private lemma exists_order (W : WPres O X R) (h : W.HasOrigin) (n : ℕ) :
    ∀ x ∈ RingHom.ker (W.origin h) ^ n, ∃ f, W.π f = x ∧ (n : ℕ∞) ≤ f.order := by
  induction n with
  | zero =>
    intro x _
    obtain ⟨f, hf⟩ := W.surj x
    exact ⟨f, hf, by simp⟩
  | succ n ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) ?_
    · obtain ⟨f, rfl, hf⟩ := ih a ha
      obtain ⟨g, rfl⟩ := W.surj b
      rw [RingHom.mem_ker, W.origin_π] at hb
      refine ⟨f * g, map_mul _ _ _, le_trans ?_ (le_order_mul)⟩
      push_cast
      exact add_le_add hf (one_le_order_iff_constCoeff_eq_zero.2 hb)
    · rintro _ _ ⟨f, rfl, hf⟩ ⟨g, rfl, hg⟩
      exact ⟨f + g, map_add _ _ _, le_trans (le_min hf hg) (min_order_le_add)⟩

private lemma z_mem_ker (W : WPres O X R) (h : W.HasOrigin) (i : W.σ) : W.z i ∈ RingHom.ker (W.origin h) := by
  rw [RingHom.mem_ker, WPres.z, W.origin_π]
  simp

private lemma monomial_mem {σ : Type} (wt : σ → X) (m : σ →₀ ℕ) (c : O) :
    monomial m c ∈ wtPart O wt (Finsupp.weight wt m) := fun k hk => by
  classical
  rw [coeff_monomial, if_neg]
  rintro rfl
  exact hk rfl

private lemma A_fin (W : WPres O X R) (x : R) (hx : x ∈ W.A) :
    ∃ (T : Finset X) (f : MvPowerSeries W.σ O), W.π f = x ∧
      ∀ m, Finsupp.weight W.wt m ∉ T → coeff m f = 0 := by
  classical
  have hx' : x ∈ ⨆ j, W.part j := hx
  refine Submodule.iSup_induction W.part (motive := fun x => ∃ (T : Finset X) (f : MvPowerSeries W.σ O),
    W.π f = x ∧ ∀ m, Finsupp.weight W.wt m ∉ T → coeff m f = 0) hx' ?_ ?_ ?_
  · rintro j _ ⟨f, hf, rfl⟩
    exact ⟨{j}, f, rfl, fun m hm => hf m (by simpa using hm)⟩
  · exact ⟨∅, 0, map_zero _, fun _ _ => map_zero _⟩
  · rintro _ _ ⟨T, f, rfl, hf⟩ ⟨U, g, rfl, hg⟩
    refine ⟨T ∪ U, f + g, map_add _ _ _, fun m hm => ?_⟩
    rw [Finset.mem_union, not_or] at hm
    rw [map_add (f := _), hf m hm.1, hg m hm.2, add_zero]

private lemma A_sum (W : WPres O X R) (g : MvPowerSeries W.σ O) (hx : W.π g ∈ W.A) :
    ∃ T : Finset X, W.π g = ∑ j ∈ T, W.π (wcomp O W.wt j g) := by
  classical
  obtain ⟨T, f, hf, hT⟩ := A_fin W _ hx
  refine ⟨T, ?_⟩
  have h1 : f = ∑ j ∈ T, wcomp O W.wt j f := by
    ext m

    rw [map_sum]
    simp only [coeff_wcomp]
    rw [Finset.sum_ite_eq]
    split_ifs with hm
    · rfl
    · exact hT m hm
  have h2 : f - g ∈ RingHom.ker W.π := by rw [RingHom.mem_ker, map_sub, hf, sub_self]
  rw [← hf]

  conv_lhs => rw [h1, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := W.homog _ h2 j
  rwa [RingHom.mem_ker, map_sub, map_sub, sub_eq_zero] at this

end

theorem UpperTheory.V.Alg.ker_pow :
    ∀ (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (W : WPres O X R) (h : W.HasOrigin) (n : ℕ),
      (RingHom.ker (W.origin h) ^ n).comap W.A.val = RingHom.ker (W.originA h) ^ n ∧ ∀ x : R, ∃ y : W.A, x - y ∈ RingHom.ker (W.origin h) ^ n := by
  intro O R _ _ _ X _ _ _ _ W h n
  classical
  refine ⟨le_antisymm (fun x hx => ?_) ?_, fun x => ?_⟩
  · obtain ⟨g, hg, hgn⟩ := exists_order W h n _ hx
    have hg' : W.π g = (x : R) := hg
    obtain ⟨T, hT⟩ := A_sum W g (hg' ▸ x.2)
    have hx' : x = ∑ j ∈ T, (⟨W.π (wcomp O W.wt j g), W.part_le_A ⟨_, wcomp_mem O W.wt j g, rfl⟩⟩ : W.A) := by
      apply Subtype.ext
      rw [← hg', hT]
      simp
    rw [hx']
    refine Ideal.sum_mem _ fun j _ => ?_
    obtain ⟨μ, hμ, hs⟩ := part_span O R X W {m | Finsupp.weight W.wt m = j ∧ n ≤ m.degree} j (fun _ hm => hm.1)
    obtain ⟨b, hb, hbs⟩ := hs (wcomp O W.wt j g) (fun m hm => by
      rw [coeff_wcomp]
      split_ifs with h1
      · refine coeff_of_lt_order (lt_of_lt_of_le ?_ hgn)
        have : ¬ n ≤ m.degree := fun h2 => hm ⟨h1, h2⟩
        exact_mod_cast not_le.1 this
      · rfl)
    have h3 : (⟨W.π (wcomp O W.wt j g), W.part_le_A ⟨_, wcomp_mem O W.wt j g, rfl⟩⟩ : W.A) =
        ∑ m ∈ μ, (⟨W.π (b m), W.part_le_A ⟨_, hb m, rfl⟩⟩ : W.A) * m.prod fun i k => W.zA i ^ k := by
      apply Subtype.ext
      show W.π (wcomp O W.wt j g) = _

      rw [hbs, map_sum]
      simp [π_monomial, Finsupp.prod, WPres.zA]
    rw [h3]
    exact Ideal.sum_mem _ fun m hm => Ideal.mul_mem_left _ _
      (prod_pow_mem (RingHom.ker (W.originA h)) W.zA (fun i => z_mem_ker W h i) m (hμ hm).2)
  · exact Ideal.le_comap_pow (K := RingHom.ker (W.origin h)) W.A.val n
  · obtain ⟨f, rfl⟩ := W.surj x
    have hfin : {m : W.σ →₀ ℕ | m.degree < n}.Finite :=
      (Finsupp.finite_of_degree_le n).subset fun m (hm : m.degree < n) => hm.le
    set t : MvPowerSeries W.σ O := ∑ m ∈ hfin.toFinset, monomial m (coeff m f) with ht
    have htA : W.π t ∈ W.A := by

      rw [ht, map_sum]
      exact Subalgebra.sum_mem _ fun m _ => W.part_le_A ⟨_, monomial_mem W.wt m _, rfl⟩
    refine ⟨⟨_, htA⟩, ?_⟩
    have key : ∃ μ : Finset (W.σ →₀ ℕ), (μ : Set _) ⊆ {m : W.σ →₀ ℕ | n ≤ m.degree} ∧
        ∀ f : MvPowerSeries W.σ O, (∀ m, m ∉ {m : W.σ →₀ ℕ | n ≤ m.degree} → coeff m f = 0) →
        ∃ b : (W.σ →₀ ℕ) → MvPowerSeries W.σ O, (∀ m, b m ∈ wtPart O (fun _ : W.σ => (0 : X)) 0) ∧
          f = ∑ m ∈ μ, b m * monomial m 1 :=
      part_span O (MvPowerSeries W.σ O) X (WPres.free O fun _ : W.σ => (0 : X))
        {m : W.σ →₀ ℕ | n ≤ m.degree} 0 (fun (m : W.σ →₀ ℕ) _ => by
          show Finsupp.weight (fun _ : W.σ => (0 : X)) m = 0
          simp [Finsupp.weight_apply, Finsupp.sum])
    obtain ⟨μ, hμ, hs⟩ := key
    obtain ⟨b, -, hbs'⟩ := hs (f - t) (fun m hm => by
      have hm0 : m.degree < n := not_le.1 hm
      have hm' : m ∈ hfin.toFinset := hfin.mem_toFinset.2 hm0

      rw [map_sub, ht, map_sum]
      simp only [coeff_monomial]
      rw [Finset.sum_ite_eq, if_pos hm', sub_self])
    show W.π f - W.π t ∈ _

    rw [← map_sub, hbs', map_sum]
    refine Ideal.sum_mem _ fun m hm => ?_
    rw [map_mul, π_monomial]
    exact Ideal.mul_mem_left _ _ (prod_pow_mem _ _ (fun i => z_mem_ker W h i) m (hμ hm))
end

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem pi_span_X {O σ : Type} [CommRing O] (s : Finset σ) :
    ∀ f : MvPowerSeries σ O, (∀ n : σ →₀ ℕ, (∀ i ∈ s, n i = 0) → coeff n f = 0) →
      f ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) :=
  _root_.UpperTheory.Reformulated.B.PowerSeriesMemSpanAllVariables.pi_span_X s

private theorem pi_wcomp_mul {O σ X : Type} [CommRing O] [AddCommGroup X] (wt : σ → X) {c : X} (j : X)
    (a : MvPowerSeries σ O) {h : MvPowerSeries σ O} (hh : h ∈ wtPart O wt c) :
    wcomp O wt j (a * h) = wcomp O wt (j - c) a * h := by
  classical
  ext n
  rw [coeff_wcomp, coeff_mul, coeff_mul]
  have key : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal n, coeff p.1 (wcomp O wt (j - c) a) * coeff p.2 h =
      if Finsupp.weight wt n = j then coeff p.1 a * coeff p.2 h else 0 := by
    intro p hp
    by_cases h2 : Finsupp.weight wt p.2 = c
    · have hn : Finsupp.weight wt n = Finsupp.weight wt p.1 + c := by
        rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hp, map_add (f := _), h2]
      rw [coeff_wcomp, hn]
      by_cases h1 : Finsupp.weight wt p.1 = j - c
      · rw [if_pos h1, if_pos (by rw [h1]; abel)]
      · rw [if_neg h1, if_neg (fun h => h1 (by rw [← h]; abel)), zero_mul]
    · rw [hh _ h2]; simp
  rw [Finset.sum_congr rfl key]
  split_ifs <;> simp

section

variable {O : Type} [CommRing O] [IsLocalRing O] {X : Type} [AddCommGroup X] {R : Type} [CommRing R]
  [Algebra O R] [IsCO O R] (W : WPres O X R)

private theorem pi_max_le (hz : ∀ s, W.z s ∈ maximalIdeal R) :
    maximalIdeal R ≤ Ideal.span {y | y ∈ maximalIdeal R ∧ ∃ i, y ∈ W.part i} := by
  intro x hx
  obtain ⟨f, rfl⟩ := W.surj x
  have h1 := pi_span_X Finset.univ (f - algebraMap O _ (constantCoeff f)) (fun n hn => by
    have : n = 0 := Finsupp.ext fun i => hn i (Finset.mem_univ i)
    subst this
    simp [MvPowerSeries.algebraMap_apply])
  have h2 : ∀ I : Ideal R, (∀ s, W.z s ∈ I) → W.π f - algebraMap O R (constantCoeff f) ∈ I := by
    intro I hI
    have hle : Ideal.span (Set.range (MvPowerSeries.X : W.σ → MvPowerSeries W.σ O)) ≤ I.comap W.π := by
      rw [Ideal.span_le]
      rintro _ ⟨s, rfl⟩
      exact hI s
    have := hle h1
    rwa [Ideal.mem_comap, map_sub, AlgHom.commutes] at this
  have h3 : algebraMap O R (constantCoeff f) ∈ maximalIdeal R := by
    simpa using sub_mem hx (h2 _ hz)
  have h4 : algebraMap O R (constantCoeff f) ∈ W.part 0 := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ SetLike.GradedOne.one_mem
  have h5 := h2 (Ideal.span {y | y ∈ maximalIdeal R ∧ ∃ i, y ∈ W.part i})
    fun s => Ideal.subset_span ⟨hz s, _, W.z_mem s⟩
  simpa using add_mem h5 (Ideal.subset_span ⟨h3, _, h4⟩)

private theorem pi_pow_le (hz : ∀ s, W.z s ∈ maximalIdeal R) (N : ℕ) :
    maximalIdeal R ^ N ≤ Ideal.span {y | y ∈ maximalIdeal R ^ N ∧ ∃ i, y ∈ W.part i} := by
  induction N with
  | zero =>
    intro x _
    have : (1 : R) ∈ Ideal.span {y | y ∈ maximalIdeal R ^ 0 ∧ ∃ i, y ∈ W.part i} :=
      Ideal.subset_span ⟨by simp, 0, SetLike.GradedOne.one_mem⟩
    simpa using Ideal.mul_mem_left _ x this
  | succ N ih =>
    refine le_trans (le_of_eq (pow_succ _ _)) (le_trans (Ideal.mul_mono ih (pi_max_le W hz)) ?_)
    rw [Ideal.span_mul_span', Ideal.span_le]
    rintro _ ⟨a, ⟨ha, i, hi⟩, b, ⟨hb, k, hk⟩, rfl⟩
    refine Ideal.subset_span ⟨?_, i + k, SetLike.GradedMul.mul_mem hi hk⟩
    rw [pow_succ]
    exact Ideal.mul_mem_mul ha hb

private theorem pi_dense (hz : ∀ s, W.z s ∈ maximalIdeal R) (N : ℕ) (x : R) :
    ∃ a ∈ W.A, x - a ∈ maximalIdeal R ^ N :=
  by apply _root_.UpperTheory.Reformulated.B.AdicDensityOfPresentationSubalgebra.pi_dense <;> assumption

private theorem pi_homog (hz : ∀ s, W.z s ∈ maximalIdeal R) (N : ℕ) (f : MvPowerSeries W.σ O)
    (hf : W.π f ∈ maximalIdeal R ^ N) (j : X) : W.π (wcomp O W.wt j f) ∈ maximalIdeal R ^ N := by
  have key : ∀ y ∈ Ideal.span {y | y ∈ maximalIdeal R ^ N ∧ ∃ i, y ∈ W.part i},
      ∃ g, W.π g = y ∧ ∀ a j, W.π (wcomp O W.wt j (a * g)) ∈ maximalIdeal R ^ N := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨ht, i, g, hg, rfl⟩ := ht
      refine ⟨g, rfl, fun a j => ?_⟩
      rw [pi_wcomp_mul W.wt j a hg, map_mul]
      exact Ideal.mul_mem_left _ _ ht
    | zero => exact ⟨0, map_zero _, fun a j => by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨g, rfl, hg⟩ := hy
      obtain ⟨g', rfl, hg'⟩ := hz
      refine ⟨g + g', map_add _ _ _, fun a j => ?_⟩
      rw [mul_add, map_add (f := _), map_add (f := _)]
      exact add_mem (hg a j) (hg' a j)
    | smul r y _ hy =>
      obtain ⟨g, rfl, hg⟩ := hy
      obtain ⟨q, rfl⟩ := W.surj r
      refine ⟨q * g, map_mul _ _ _, fun a j => ?_⟩
      rw [← mul_assoc]
      exact hg _ j
  obtain ⟨g, hg, hg'⟩ := key _ (pi_pow_le W hz N hf)
  have h1 : f - g ∈ RingHom.ker W.π := by rw [RingHom.mem_ker, map_sub, hg, sub_self]
  have h2 := W.homog _ h1 j
  rw [RingHom.mem_ker, map_sub, map_sub, sub_eq_zero] at h2
  rw [h2]
  simpa using hg' 1 j

end

theorem UpperTheory.V.Alg.pres_indep :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ W' : WPres O X R, (∀ s, W'.z s ∈ maximalIdeal R) → (∀ s, W'.z s ∈ W.part (W'.wt s)) → ∀ j, W'.part j = W.part j := by
  intro O _ _ _ _ X _ _ _ _ R _ _ _ W hz W' hz' hw j
  have hle : ∀ i, ∀ x ∈ W'.part i, x ∈ W.part i :=
    UpperTheory.V.Alg.map_part O X R W' hz' R W hz (AlgHom.id O R) hw
  refine le_antisymm (hle j) fun x hx => ?_
  refine UpperTheory.V.Alg.part_closed O X R W' hz' j x fun N => ?_
  obtain ⟨a, ha, hxa⟩ := pi_dense W' hz' N x
  have ha' : a ∈ ⨆ i, W'.part i := ha
  have hself : ∀ g ∈ wtPart O W.wt j, wcomp O W.wt j g = g := by
    intro g hg
    ext n
    rw [coeff_wcomp]
    split_ifs with h
    · rfl
    · exact (hg n h).symm
  have key : ∃ f, W.π f = a ∧ W.π (wcomp O W.wt j f) ∈ W'.part j := by
    refine Submodule.iSup_induction W'.part
      (motive := fun a => ∃ f, W.π f = a ∧ W.π (wcomp O W.wt j f) ∈ W'.part j) ha' ?_ ?_ ?_
    · intro i y hy
      obtain ⟨f, hf, hfy⟩ := hle i y hy
      have hfy' : W.π f = y := hfy
      refine ⟨f, hfy', ?_⟩
      by_cases hij : i = j
      · subst hij
        rw [hself f hf, hfy']
        exact hy
      · have : wcomp O W.wt j f = 0 := by
          ext n
          rw [coeff_wcomp]
          split_ifs with h
          · rw [hf n (fun h' => hij (h'.symm.trans h))]; simp
          · simp
        rw [this, map_zero]
        exact zero_mem _
    · exact ⟨0, map_zero _, by simp⟩
    · rintro a b ⟨f, hf, hf'⟩ ⟨g, hg, hg'⟩
      refine ⟨f + g, by rw [map_add (f := _), hf, hg], ?_⟩
      rw [map_add (f := _), map_add (f := _)]
      exact add_mem hf' hg'
  obtain ⟨f, hf, hf'⟩ := key
  obtain ⟨g, hg, hgx⟩ := hx
  have hgx' : W.π g = x := hgx
  refine ⟨_, hf', ?_⟩
  have := pi_homog W hz N (g - f) (by rwa [map_sub, hgx', hf]) j
  rwa [map_sub, hself g hg, map_sub, hgx'] at this
end
