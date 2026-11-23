module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibAbs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NnDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.Bundle001
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
public import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.Wcount

@[expose] public section

section

open MulAction UpperTheory.V.Z.Sym

private structure PairSp (H G : Type) [Group G] (U : Subgroup G) : Type where
  fst : H
  snd : G ⧸ U

@[instance_reducible] private def pairAct {H G : Type} [Group H] [Group G] (j : H →* G) (U : Subgroup G) :
    MulAction H (PairSp H G U) where
  smul h p := ⟨h * p.1 * h⁻¹, j h • p.2⟩
  one_smul p := by
    show (⟨(1 : H) * p.1 * (1 : H)⁻¹, j 1 • p.2⟩ : PairSp H G U) = p
    simp
  mul_smul a b p := by
    show (⟨a * b * p.1 * (a * b)⁻¹, j (a * b) • p.2⟩ : PairSp H G U) =
      ⟨a * (b * p.1 * b⁻¹) * a⁻¹, j a • j b • p.2⟩
    simp [mul_assoc, mul_smul]

private theorem out_eq_mul {G : Type} [Group G] (U : Subgroup G) (g : G) :
    ∃ u ∈ U, ((g : G ⧸ U).out : G) = g * u := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul U g
  exact ⟨h, h.2, hh⟩

private theorem pair_inv_mul_eq_of_mul_self_eq_one {H G : Type} [Group H] [Group G] (a b o u : G) (key : a⁻¹ * (b * a) = b) :
    (a * o * u)⁻¹ * b * (a * o * u) = u⁻¹ * (o⁻¹ * b * o) * u := by
  calc (a * o * u)⁻¹ * b * (a * o * u) = u⁻¹ * o⁻¹ * (a⁻¹ * (b * a)) * o * u := by group
    _ = u⁻¹ * (o⁻¹ * b * o) * u := by rw [key]; group

theorem UpperTheory.orbitalFiber_pair_correspondence :
    UpperTheory.V.Z.Sym.Glob.Fib.Pair := by
  classical
  intro H G I _ _ j H₀ U c f δ Hi _ φ hcen hfix hc hf hfin hT hidx hrange hδ hcov
  letI : MulAction H (PairSp H G U) := pairAct j U
  letI : MulAction H (G ⧸ U) := MulAction.compHom (G ⧸ U) j
  letI : ∀ i, MulAction (Hi i) (G ⧸ U) := fun i => MulAction.compHom (G ⧸ U) (j.comp (φ i))
  have hnorm : H₀.Normal := ⟨fun n hn g => by
    have hc' := Subgroup.mem_center_iff.1 (hcen hn) g
    rw [hc', mul_inv_cancel_right]
    exact hn⟩
  have hout : ∀ (a : G) (y : G ⧸ U), ∃ u ∈ U, ((a • y : G ⧸ U).out) = a * y.out * u := by
    intro a y
    have hy : (a • y : G ⧸ U) = ((a * y.out : G) : G ⧸ U) := by
      conv_lhs => rw [← QuotientGroup.out_eq' y]
      rfl
    rw [hy]
    exact out_eq_mul U _
  let K' : PairSp H G U → ℂ := fun p => c p.1 * f (p.2.out⁻¹ * j p.1 * p.2.out)
  have hKinv : ∀ (h : H) (p : PairSp H G U), K' (h • p) = K' p := by
    intro h p
    obtain ⟨u, hu, he⟩ := hout (j h) p.2
    show c (h * p.1 * h⁻¹) * f ((j h • p.2).out⁻¹ * j (h * p.1 * h⁻¹) * (j h • p.2).out) =
      c p.1 * f (p.2.out⁻¹ * j p.1 * p.2.out)
    rw [hc, he, map_mul, map_mul, map_inv]
    congr 1
    rw [show (j h * p.2.out * u)⁻¹ * (j h * j p.1 * (j h)⁻¹) * (j h * p.2.out * u) =
        u⁻¹ * (p.2.out⁻¹ * j p.1 * p.2.out) * u by group]
    exact hf u hu _
  have hfib : ∀ x : G ⧸ U, {p : PairSp H G U | p.2 = x ∧ K' p ≠ 0}.Finite := by
    intro x
    refine ((hfin x.out).image (fun γ => (⟨γ, x⟩ : PairSp H G U))).subset ?_
    rintro ⟨γ, y⟩ ⟨hy, hne⟩
    change y = x at hy
    subst hy
    exact ⟨γ, hne, rfl⟩
  obtain ⟨T, hTc⟩ := hT
  have hT'fin : (⋃ s ∈ T, {p : PairSp H G U | p.2 = (s : G ⧸ U) ∧ K' p ≠ 0}).Finite :=
    Set.Finite.biUnion T.finite_toSet (fun s _ => hfib _)
  have hcoverP : ∀ p : PairSp H G U, K' p ≠ 0 → ∃ h : H, ∃ s ∈ hT'fin.toFinset, p = h • s := by
    intro p hp
    obtain ⟨γ0, s, hs, u, hu, he⟩ := hTc p.2.out
    refine ⟨γ0, γ0⁻¹ • p, ?_, ?_⟩
    · rw [Set.Finite.mem_toFinset, Set.mem_iUnion₂]
      refine ⟨s, hs, ?_, ?_⟩
      · show j γ0⁻¹ • p.2 = (s : G ⧸ U)
        conv_lhs => rw [← QuotientGroup.out_eq' p.2, he]
        show ((j γ0⁻¹ * (j γ0 * s * u) : G) : G ⧸ U) = s
        rw [QuotientGroup.eq, map_inv]
        simpa [mul_assoc] using U.inv_mem hu
      · rw [hKinv]
        exact hp
    · rw [smul_smul, mul_inv_cancel, one_smul]
  have hfixP : ∀ z ∈ H₀, ∀ p : PairSp H G U, z • p = p := by
    intro z hz p
    obtain ⟨γ, y⟩ := p
    show (⟨z * γ * z⁻¹, j z • y⟩ : PairSp H G U) = ⟨γ, y⟩
    rw [← Subgroup.mem_center_iff.1 (hcen hz) γ, mul_inv_cancel_right, hfix z hz y]
  have hpush := UpperTheory.orbitalFiber_pushforward H (PairSp H G U) (G ⧸ U) H₀ (fun p => p.2) K' hnorm
    (fun _ _ => rfl) hfixP hKinv ⟨hT'fin.toFinset, hcoverP⟩ hfib (fun p _ => hidx p.2)
  have hfibsum : ∀ x : G ⧸ U, (∑ᶠ (p : PairSp H G U) (_ : p.2 = x), K' p) =
      ∑ᶠ γ : H, c γ * f (x.out⁻¹ * j γ * x.out) := by
    intro x
    have hr : ∀ p : PairSp H G U,
        (p.2 = x) = (p ∈ Set.range (fun γ : H => (⟨γ, x⟩ : PairSp H G U))) := by
      intro p
      apply propext
      constructor
      · intro hp
        exact ⟨p.1, by rw [← hp]⟩
      · rintro ⟨γ, rfl⟩
        rfl
    simp only [hr]
    rw [finsum_mem_range (fun a b hab => congrArg PairSp.fst hab)]
  have hcomm : ∀ i (a : Hi i), φ i a * δ i * (φ i a)⁻¹ = δ i := by
    intro i a
    rw [(hrange i (φ i a)).1 ⟨a, rfl⟩, mul_inv_cancel_right]
  have hequi : ∀ i (a : Hi i) (y : G ⧸ U),
      (⟨δ i, a • y⟩ : PairSp H G U) = φ i a • (⟨δ i, y⟩ : PairSp H G U) := by
    intro i a y
    show (⟨δ i, j (φ i a) • y⟩ : PairSp H G U) = ⟨φ i a * δ i * (φ i a)⁻¹, j (φ i a) • y⟩
    rw [hcomm]
  have hkiinv : ∀ i (a : Hi i) (y : G ⧸ U),
      c (δ i) * f ((a • y).out⁻¹ * j (δ i) * (a • y).out) = c (δ i) * f (y.out⁻¹ * j (δ i) * y.out) := by
    intro i a y
    obtain ⟨u, hu, he⟩ := hout (j (φ i a)) y
    show c (δ i) * f ((j (φ i a) • y).out⁻¹ * j (δ i) * (j (φ i a) • y).out) = _
    rw [he, pair_inv_mul_eq_of_mul_self_eq_one (H := H) _ _ _ _ ?_, hf u hu]
    have h1 := (hrange i (φ i a)).1 ⟨a, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul, ← h1, inv_mul_cancel_left]
  have hcovD : ∀ p : PairSp H G U, K' p ≠ 0 → ∃ i, ∃ y : G ⧸ U, ∃ h : H,
      c (δ i) * f (y.out⁻¹ * j (δ i) * y.out) ≠ 0 ∧ p = h • (⟨δ i, y⟩ : PairSp H G U) := by
    rintro ⟨γ, y⟩ hp
    obtain ⟨i, h, hγ⟩ := hcov γ y.out hp
    refine ⟨i, j h⁻¹ • y, h, ?_, ?_⟩
    · have h2 := hKinv h⁻¹ ⟨γ, y⟩
      have h3 : h⁻¹ * γ * h⁻¹⁻¹ = δ i := by rw [hγ]; group
      change c (h⁻¹ * γ * h⁻¹⁻¹) * f ((j h⁻¹ • y).out⁻¹ * j (h⁻¹ * γ * h⁻¹⁻¹) * (j h⁻¹ • y).out) =
        K' ⟨γ, y⟩ at h2
      rw [h3] at h2
      rw [h2]
      exact hp
    · show (⟨γ, y⟩ : PairSp H G U) = ⟨h * δ i * h⁻¹, j h • j h⁻¹ • y⟩
      rw [← hγ, smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
  have huniq : ∀ (i i' : I) (y y' : G ⧸ U) (h : H),
      c (δ i) * f (y.out⁻¹ * j (δ i) * y.out) ≠ 0 → c (δ i') * f (y'.out⁻¹ * j (δ i') * y'.out) ≠ 0 →
      h • (⟨δ i, y⟩ : PairSp H G U) = ⟨δ i', y'⟩ → i = i' ∧ h ∈ (φ i).range := by
    intro i i' y y' h _ _ he
    have h1 : h * δ i * h⁻¹ = δ i' := congrArg PairSp.fst he
    have hii := hδ i i' h h1.symm
    subst hii
    refine ⟨rfl, (hrange i h).2 ?_⟩
    calc h * δ i = h * δ i * h⁻¹ * h := by group
      _ = δ i * h := by rw [h1]
  have hdec := UpperTheory.orbitalFiber_decomposition H (PairSp H G U) I H₀ K' Hi (fun _ => G ⧸ U) φ
    (fun i y => (⟨δ i, y⟩ : PairSp H G U))
    (fun i y => c (δ i) * f (y.out⁻¹ * j (δ i) * y.out)) hnorm hKinv ⟨hT'fin.toFinset, hcoverP⟩
    hequi (fun _ _ _ hab => congrArg PairSp.snd hab) hkiinv (fun _ _ _ => rfl) hcovD huniq
  show gq H₀ (fun y : G ⧸ U => ∑ᶠ γ : H, c γ * f (y.out⁻¹ * j γ * y.out)) = _
  simp only [← hfibsum]
  rw [← hpush, hdec]
  apply finsum_congr
  intro i
  exact (UpperTheory.orbitalFiber_of_bot (Hi i) (G ⧸ U) (Subgroup.comap (φ i) H₀)
    (fun y => f (y.out⁻¹ * j (δ i) * y.out))).1 (c (δ i))
end

section

open MulAction

theorem UpperTheory.symmetric_fiber_covering : UpperTheory.V.Z.Sym.Glob.Fib.Cover := by
  intro H G _ _ S U U' x Ux ι Φ hS hU hUx hr hL hR hT hfin
  classical
  letI a1 : MulAction H (S ⧸ Ux) := MulAction.compHom _ ι
  letI a2 : MulAction H (G ⧸ U') := MulAction.compHom _ (S.subtype.comp ι)
  let q : S ⧸ Ux → G ⧸ U' := fun y => (((y.out : S) : G) * x : G)
  let k : S ⧸ Ux → ℂ := fun y => Φ (((y.out : S) : G) * x)
  have hΦ : ∀ a b : G, (a : G ⧸ U') = b → Φ a = Φ b := by
    intro a b e
    have hm : a⁻¹ * b ∈ U' := QuotientGroup.eq.1 e
    have := hR _ hm a
    rw [← this]
    congr 1
    group
  have hq0 : ∀ s : S, q (s : S ⧸ Ux) = (((s : G) * x : G) : G ⧸ U') := by
    intro s
    have h1 : ((s : S ⧸ Ux).out)⁻¹ * s ∈ Ux := QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
    have h2 := hU ((hUx _).1 h1)
    show ((((s : S ⧸ Ux).out : G) * x : G) : G ⧸ U') = _
    rw [QuotientGroup.eq]
    have e : (((s : S ⧸ Ux).out : G) * x)⁻¹ * ((s : G) * x) = x⁻¹ * ((((s : S ⧸ Ux).out)⁻¹ * s : S) : G) * x := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact h2
  have hq : ∀ (h : H) (y : S ⧸ Ux), q (h • y) = h • q y := by
    intro h y
    induction y using QuotientGroup.induction_on with | H s => ?_
    have e1 : h • (s : S ⧸ Ux) = ((ι h * s : S) : S ⧸ Ux) := rfl
    rw [e1, hq0, hq0]
    have e2 : ∀ z : G ⧸ U', h • z = ((ι h : S) : G) • z := fun _ => rfl
    rw [e2, Subgroup.coe_mul, mul_assoc]
    rfl
  have hkq : ∀ y, k y = Φ (q y).out := fun y => hΦ _ _ (QuotientGroup.out_eq' (q y)).symm
  have hk : ∀ (h : H) y, k (h • y) = k y := by
    intro h y
    rw [hkq, hkq, hq]
    have e2 : h • q y = ((((ι h : S) : G) * (q y).out : G) : G ⧸ U') := by
      conv_lhs => rw [← QuotientGroup.out_eq' (q y)]
      rfl
    have := hΦ _ _ ((QuotientGroup.out_eq' (h • q y)).trans e2)
    rw [this]
    exact hL h _
  have hT' : ∃ T : Finset (S ⧸ Ux), ∀ y, k y ≠ 0 → ∃ h : H, ∃ s ∈ T, y = h • s := by
    obtain ⟨T, hT⟩ := hT
    refine ⟨T.image (fun t : S => (QuotientGroup.mk t : S ⧸ Ux)), fun y _ => ?_⟩
    induction y using QuotientGroup.induction_on with | H s => ?_
    obtain ⟨h, t, ht, u, hu, e⟩ := hT s
    refine ⟨h, (QuotientGroup.mk t : S ⧸ Ux), Finset.mem_image_of_mem (fun t : S => (QuotientGroup.mk t : S ⧸ Ux)) ht, ?_⟩
    rw [e]
    show ((ι h * t * u : S) : S ⧸ Ux) = ((ι h * t : S) : S ⧸ Ux)
    exact QuotientGroup.mk_mul_of_mem _ hu
  have hcard : ∀ s₀ : S, {y | q y = (((s₀ : G) * x : G) : G ⧸ U')}.ncard = U.relIndex (U' ⊓ S) :=
    fun s₀ => UpperTheory.orbitalFiber_card_formula G S U U' x Ux s₀ hS hU hUx
  have hfinF : ∀ s₀ : S, {y | q y = (((s₀ : G) * x : G) : G ⧸ U')}.Finite := fun s₀ =>
    Set.finite_of_ncard_ne_zero (by rw [hcard]; exact hr)
  have hfib : ∀ z, {y | q y = z ∧ k y ≠ 0}.Finite := by
    intro z
    by_cases hz : ∃ y, q y = z
    · obtain ⟨y, rfl⟩ := hz
      exact (hfinF y.out).subset fun w hw => hw.1
    · refine Set.Finite.subset Set.finite_empty fun w hw => hz ⟨w, hw.1⟩
  have hrel : ∀ y, k y ≠ 0 → (⊥ : Subgroup H).relIndex (stabilizer H (q y)) ≠ 0 := by
    intro y _
    rw [Subgroup.relIndex_bot_left]
    have hs : ((stabilizer H (q y) : Subgroup H) : Set H).Finite := by
      refine (hfin (q y).out).subset fun h hh => ?_
      have hh' : h • q y = q y := hh
      have e2 : h • q y = ((((ι h : S) : G) * (q y).out : G) : G ⧸ U') := by
        conv_lhs => rw [← QuotientGroup.out_eq' (q y)]
        rfl
      rw [e2] at hh'
      have e3 : (((q y).out : G) : G ⧸ U') = ((((ι h : S) : G) * (q y).out : G) : G ⧸ U') :=
        (QuotientGroup.out_eq' (q y)).trans hh'.symm
      have := QuotientGroup.eq.1 e3
      show ((q y).out)⁻¹ * ((ι h : S) : G) * (q y).out ∈ U'
      rwa [mul_assoc]
    haveI : Finite (stabilizer H (q y)) := hs.to_subtype
    exact Nat.card_pos.ne'
  have hpush := UpperTheory.orbitalFiber_pushforward H (S ⧸ Ux) (G ⧸ U') ⊥ q k inferInstance hq
    (fun z hz y => by rw [Subgroup.mem_bot.1 hz, one_smul]) hk hT' hfib hrel
  have hK : (fun z : G ⧸ U' => ∑ᶠ (y : S ⧸ Ux) (_ : q y = z), k y) =
      fun z => (U.relIndex (U' ⊓ S) : ℂ) * (orbit S (x : G ⧸ U')).indicator (fun y => Φ y.out) z := by
    funext z
    by_cases hz : z ∈ orbit S (x : G ⧸ U')
    · rw [Set.indicator_of_mem hz]
      obtain ⟨s₀, rfl⟩ := hz
      have e0 : (fun m : S => m • (x : G ⧸ U')) s₀ = (((s₀ : G) * x : G) : G ⧸ U') := rfl
      rw [e0]
      set z : G ⧸ U' := (((s₀ : G) * x : G) : G ⧸ U') with hzdef
      have step : (∑ᶠ (y : S ⧸ Ux) (_ : q y = z), k y) = ∑ᶠ y ∈ {y | q y = z}, Φ z.out :=
        by
          change (∑ᶠ y ∈ {y | q y = z}, k y) = ∑ᶠ y ∈ {y | q y = z}, Φ z.out
          exact finsum_mem_congr rfl fun y hy => by
            have hy' : q y = z := hy
            rw [hkq, hy']
      rw [step, finsum_mem_eq_finite_toFinset_sum _ (hfinF s₀), Finset.sum_const, nsmul_eq_mul,
        ← Set.ncard_eq_toFinset_card _ (hfinF s₀), hcard]
    · rw [Set.indicator_of_notMem hz, mul_zero]
      have h0 : ∀ y : S ⧸ Ux, (∑ᶠ (_ : q y = z), k y) = 0 := by
        intro y
        refine finsum_eq_if.trans (if_neg fun e => hz ?_)
        exact ⟨y.out, e⟩
      simp only [h0, finsum_zero]
  have hbot := (UpperTheory.orbitalFiber_of_bot H (G ⧸ U') ⊥ ((orbit S (x : G ⧸ U')).indicator fun y => Φ y.out)).1
    (U.relIndex (U' ⊓ S) : ℂ)
  show UpperTheory.V.Z.Sym.gq ⊥ k = (U.relIndex (U' ⊓ S) : ℂ) *
    UpperTheory.V.Z.Sym.gq ⊥ ((orbit S (x : G ⧸ U')).indicator fun y => Φ y.out)
  rw [hpush, hK]
  exact hbot
end

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.Ws

section
open UpperTheory.V.W

end

private theorem exists_pow_l_pow_eq_one_of_mem_muG {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (ψ : G →* Rˣ) (hψc : AdicCont (maximalIdeal R) fun g => ((ψ g : Rˣ) : R))
    (g : G) (hg : g ∈ UpperTheory.V.W.muG l G) : ∃ n : ℕ, ψ g ^ (l ^ n) = 1 := by
  obtain ⟨n, hn⟩ := CommGroup.mem_primaryComponent.1 hg
  refine ⟨n, ?_⟩
  have h1 : g ^ (l ^ n) ∈ (commutator G).topologicalClosure := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hn
  have hker : (commutator G).topologicalClosure ≤ ψ.ker :=
    Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker ψ)
      (isClosed_ker_of_adicCont ψ hψc)
  rw [← map_pow]
  exact hker h1

theorem UpperTheory.exists_pinning_elements_of_locAb :
    ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (I : Subgroup G) (d : ℕ), UpperTheory.V.W.LocAb l G I d → ∃ s : Fin d → G, (∀ k, s k ∈ I) ∧ Pins l I (Set.range s) := by
  intro l _ G _ _ _ _ I d A
  have hlp : l.Prime := Fact.out
  have hs : ∀ k : Fin d, ∃ g ∈ I,
      A.a g = Multiplicative.ofAdd ((Pi.single k 1 : Fin d → ℤ_[l]), (0 : ℤ_[l])) :=
    fun k => (A.inertia _).2 rfl
  choose s hsI hsa using hs
  refine ⟨s, hsI, ?_⟩
  intro R _ _ _ _ hl ψ hψc hψI hψs g hg
  haveI : CharP R l := (CharP.charP_iff_prime_eq_zero hlp).2 hl
  have hsk : ∀ k, ψ (s k) = 1 := fun k => hψs _ ⟨k, rfl⟩
  have hq : ∀ (N : ℕ) (u : Rˣ),
      Units.map (↑(Ideal.Quotient.mk (maximalIdeal R ^ N)) : R →* R ⧸ maximalIdeal R ^ N) u = 1 ↔
        (u : R) - 1 ∈ maximalIdeal R ^ N := by
    intro N u
    rw [Units.ext_iff]
    show Ideal.Quotient.mk (maximalIdeal R ^ N) (u : R) = 1 ↔ _
    rw [← map_one (Ideal.Quotient.mk (maximalIdeal R ^ N)), Ideal.Quotient.eq]
  let ρN : (N : ℕ) → G →* (R ⧸ maximalIdeal R ^ N)ˣ := fun N =>
    (Units.map (↑(Ideal.Quotient.mk (maximalIdeal R ^ N)) : R →* R ⧸ maximalIdeal R ^ N)).comp ψ
  have hloc : ∀ N, IsLocallyConstant (ρN N) := fun N => (adicCont_units _ _).1 hψc N
  haveI hfin1 : Finite (ρN 1).range := (hloc 1).range_finite.to_subtype
  set M := Nat.card (ρN 1).range with hMdef
  have hM0 : M ≠ 0 := Nat.card_pos.ne'
  have hres : ∀ g, ((ψ g ^ M : Rˣ) : R) - 1 ∈ maximalIdeal R := by
    intro g
    have h1 := congrArg (fun u : (ρN 1).range => (u : (R ⧸ maximalIdeal R ^ 1)ˣ))
      (pow_card_eq_one' (G := (ρN 1).range) (x := ⟨ρN 1 g, g, rfl⟩))
    simp only [Subgroup.coe_pow, OneMemClass.coe_one, ← hMdef] at h1
    rw [← map_pow] at h1
    simpa using (hq 1 _).1 h1
  have hmu : ∀ g ∈ UpperTheory.V.W.muG l G, ψ g ^ M = 1 := by
    intro g hg
    obtain ⟨n, hn⟩ := exists_pow_l_pow_eq_one_of_mem_muG ψ hψc g hg
    apply Units.ext
    refine eq_one_of_pow hl (hres g) (pow_ne_zero n hlp.ne_zero) ?_
    rw [← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul, hn, one_pow, Units.val_one]
  let φN : (N : ℕ) → G →* (R ⧸ maximalIdeal R ^ N)ˣ := fun N => (powMonoidHom M).comp (ρN N)
  have hφloc : ∀ N, IsLocallyConstant (φN N) := fun N => (hloc N).comp (fun u => u ^ M)
  have hφ : ∀ N g, φN N g = 1 ↔ ((ψ g ^ M : Rˣ) : R) - 1 ∈ maximalIdeal R ^ N := by
    intro N g
    rw [← hq]
    rw [map_pow]
    exact Iff.rfl
  have hφp : ∀ N g, (φN N g) ^ (l ^ N) = 1 := by
    intro N g
    rw [← map_pow, hφ]
    set y := ((ψ g ^ M : Rˣ) : R) - 1 with hy
    have hym : y ∈ maximalIdeal R := hres g
    have : (((ψ g ^ M) ^ (l ^ N) : Rˣ) : R) = 1 + y ^ (l ^ N) := by
      rw [Units.val_pow_eq_pow_val, show ((ψ g ^ M : Rˣ) : R) = 1 + y by rw [hy]; ring,
        add_pow_char_pow, one_pow]
    rw [map_pow, ← pow_mul, mul_comm (l ^ N) M, pow_mul, this, add_sub_cancel_left]
    exact Ideal.pow_le_pow_right (Nat.lt_pow_self hlp.one_lt).le (Ideal.pow_mem_pow hym _)
  have hK : ∀ N, A.a.ker ≤ (φN N).ker := by
    intro N
    haveI : Finite (φN N).range := (hφloc N).range_finite.to_subtype
    have hP : IsPGroup l (φN N).range := by
      rintro ⟨x, g, rfl⟩
      exact ⟨N, Subtype.ext (hφp N g)⟩
    have := A.univ (φN N).range hP (φN N).rangeRestrict
      (by rw [MonoidHom.ker_rangeRestrict]; exact (hφloc N).isOpen_fiber 1)
      (by
        intro g hg
        rw [MonoidHom.ker_rangeRestrict]
        exact (hφ N g).2 (by rw [hmu g hg, Units.val_one, sub_self]; exact zero_mem _))
    rwa [MonoidHom.ker_rangeRestrict] at this
  have hclosed : ∀ N, IsClosed ((Subgroup.map A.a (φN N).ker : Subgroup _) :
      Set (Multiplicative ((Fin d → ℤ_[l]) × ℤ_[l]))) := by
    intro N
    rw [Subgroup.coe_map]
    exact (((hφloc N).isClosed_fiber 1).isCompact.image A.cont).isClosed
  have hmem : ∀ N (x : Fin d → ℤ_[l]),
      Multiplicative.ofAdd (x, (0 : ℤ_[l])) ∈ Subgroup.map A.a (φN N).ker := by
    intro N
    have hint : ∀ z : Fin d → ℤ, Multiplicative.ofAdd ((fun k => (z k : ℤ_[l])), (0 : ℤ_[l])) ∈
        Subgroup.map A.a (φN N).ker := by
      intro z
      have he : ((fun k => (z k : ℤ_[l])), (0 : ℤ_[l])) =
          ∑ k, z k • ((Pi.single k 1 : Fin d → ℤ_[l]), (0 : ℤ_[l])) := by
        refine Prod.ext ?_ ?_
        · funext j
          rw [Prod.fst_sum, Finset.sum_apply]
          simp [Pi.single_apply]
        · rw [Prod.snd_sum]
          simp
      rw [he, ofAdd_sum]
      refine Subgroup.prod_mem _ fun k _ => ?_
      rw [ofAdd_zsmul]
      refine Subgroup.zpow_mem _ ?_ _
      refine ⟨s k, ?_, hsa k⟩
      exact (hφ N (s k)).2 (by rw [hsk, one_pow, Units.val_one, sub_self]; exact zero_mem _)
    have hT : IsClosed {x : Fin d → ℤ_[l] |
        Multiplicative.ofAdd (x, (0 : ℤ_[l])) ∈ Subgroup.map A.a (φN N).ker} :=
      (hclosed N).preimage (continuous_ofAdd.comp (continuous_id.prodMk continuous_const))
    have hD : DenseRange (Pi.map fun (_ : Fin d) (z : ℤ) => (z : ℤ_[l])) :=
      DenseRange.piMap fun _ => PadicInt.denseRange_intCast
    intro x
    have hx : x ∈ closure (Set.range (Pi.map fun (_ : Fin d) (z : ℤ) => (z : ℤ_[l]))) := by
      rw [hD.closure_eq]
      exact Set.mem_univ x
    exact hT.closure_subset_iff.2 (by rintro _ ⟨z, rfl⟩; exact hint z) hx
  have hgN : ∀ N, φN N g = 1 := by
    intro N
    obtain ⟨x, hx⟩ : ∃ x, A.a g = Multiplicative.ofAdd x := ⟨Multiplicative.toAdd (A.a g), rfl⟩
    have hx2 : x.2 = 0 := (A.inertia x).1 ⟨g, hg, hx⟩
    obtain ⟨h, hh, hah⟩ := hmem N x.1
    have hk : h⁻¹ * g ∈ A.a.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hah, hx, inv_mul_eq_one, ← hx2]
    have := hK N hk
    rw [MonoidHom.mem_ker, map_mul, map_inv, MonoidHom.mem_ker.1 hh, inv_one, one_mul] at this
    exact this
  have hzero : ((ψ g ^ M : Rˣ) : R) - 1 = 0 := by
    have : ((ψ g ^ M : Rˣ) : R) - 1 ∈ ⨅ N, maximalIdeal R ^ N :=
      Ideal.mem_iInf.2 fun N => (hφ N g).1 (hgN N)
    rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top,
      Ideal.mem_bot] at this
  apply Units.ext
  refine eq_one_of_pow hl (hψI g hg) hM0 ?_
  rw [← Units.val_pow_eq_pow_val]
  exact sub_eq_zero.1 hzero
end
