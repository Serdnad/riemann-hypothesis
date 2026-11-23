module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.OneVanish
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc
open scoped Pointwise

namespace PositivityTheory.Rg.BcB.CV.SecondVanishing

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.BcB.CV

theorem hcs_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : X × Y → ℂ} (hf : HasCompactSupport f) (g : X) : HasCompactSupport fun y => f (g, y) := by
  refine HasCompactSupport.intro (IsCompact.image hf continuous_snd) fun y hy => ?_
  by_contra h
  exact hy ⟨(g, y), subset_tsupport _ (Function.mem_support.2 h), rfl⟩

theorem hcs_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]
    {f : X × Y → ℂ} (hf : HasCompactSupport f) (g : Y) : HasCompactSupport fun y => f (y, g) := by
  refine HasCompactSupport.intro (IsCompact.image hf continuous_fst) fun y hy => ?_
  by_contra h
  exact hy ⟨(y, g), subset_tsupport _ (Function.mem_support.2 h), rfl⟩

theorem vp_bdd_on {X : Type*} [TopologicalSpace X] {m : ℕ} {V : ((Fin m → SignType) → ℝ) → ℂ} (hV : VP V)
    {q : X → (Fin m → SignType) → ℝ} (hq : Continuous q) {K : Set X} (hK : IsCompact K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ K, ‖V (q x)‖ ≤ B := by
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn hq.continuousOn
  obtain ⟨B, hB⟩ := hV.bdd R
  refine ⟨max B 0, le_max_right _ _, fun x hx => (hB (q x) fun e => ?_).trans (le_max_left _ _)⟩
  rw [← Real.norm_eq_abs]
  exact (norm_le_pi_norm (q x) e).trans (hR x hx)

theorem tor2 {n m : ℕ} {d₁ d₂ : GL (Fin n) ℂ} {V : ((Fin m → SignType) → ℝ) → ℂ}
    {p₁ p₂ : GL (Fin n) ℂ → (Fin m → SignType) → ℝ} (h₁ : LocFam d₁ V p₁) (h₂ : LocFam d₂ V p₂)
    {t₁ t₂ : GL (Fin n) ℂ} (ht₁ : t₁ ∈ twCent (thC n) d₁) (ht₂ : t₂ ∈ twCent (thC n) d₂) (x₁ x₂ : GL (Fin n) ℂ)
    (z : (Fin m → SignType) → ℝ) : V (p₁ (t₁ * x₁) + p₂ (t₂ * x₂) + z) = V (p₁ x₁ + p₂ x₂ + z) := by
  rw [add_assoc, h₁.tor t₁ ht₁, add_left_comm (p₁ x₁), h₂.tor t₂ ht₂, add_left_comm (p₂ x₂), ← add_assoc]

end PositivityTheory.Rg.BcB.CV.SecondVanishing

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.BcB.CV PositivityTheory.Rg.BcB.CV.SecondVanishing in
theorem PositivityTheory.Rg.BcB.CV.pf_TwoVanish : PositivityTheory.Rg.BcB.LocVanish → PositivityTheory.Rg.BcB.D4.LocProper → PositivityTheory.Rg.BcB.CV.LocTor → PositivityTheory.Rg.BcB.CV.QInt → PositivityTheory.Rg.BcB.CV.QAdd → PositivityTheory.Rg.BcB.CV.QProd → PositivityTheory.Rg.BcB.CV.OneVanish → PositivityTheory.Rg.BcB.CV.TwoVanish := by
  intro hLV hLP hLT hQI hQA hQP hOV n m _ _ μ _ d₁ d₂ ν _ _ f V p₁ p₂ z hm hd₁ hd₂ hfc hfs hcu₁ hcu₂ hV hF₁ hF₂ hz
  obtain ⟨hcl₁, hcomm₁, hθ, hlc, hsc⟩ := hLT n d₁ hd₁
  obtain ⟨hcl₂, hcomm₂, -, -, -⟩ := hLT n d₂ hd₂
  have := hlc
  have := hsc
  have hc₁ : Continuous fun x => twConj (thC n) x d₁ := by
    show Continuous fun x => x⁻¹ * d₁ * thC n x
    exact (continuous_inv.mul continuous_const).mul hθ
  have hc₂ : Continuous fun x => twConj (thC n) x d₂ := by
    show Continuous fun x => x⁻¹ * d₂ * thC n x
    exact (continuous_inv.mul continuous_const).mul hθ
  have hΦc : Continuous fun x : GL (Fin n) ℂ × GL (Fin n) ℂ => f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) :=
    hfc.comp ((hc₁.comp continuous_fst).prodMk (hc₂.comp continuous_snd))
  have hΦinv : ∀ t ∈ (twCent (thC n) d₁).prod (twCent (thC n) d₂), ∀ x : GL (Fin n) ℂ × GL (Fin n) ℂ,
      f (twConj (thC n) (t * x).1 d₁, twConj (thC n) (t * x).2 d₂) = f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) := by
    intro t ht x
    rw [Prod.fst_mul, Prod.snd_mul, twConj_mul_left _ _ (Subgroup.mem_prod.1 ht).1,
      twConj_mul_left _ _ (Subgroup.mem_prod.1 ht).2]
  obtain ⟨C₁, hC₁, hsub₁⟩ := hLP n d₁ hd₁ (Prod.fst '' tsupport f) (IsCompact.image hfs continuous_fst)
  obtain ⟨C₂, hC₂, hsub₂⟩ := hLP n d₂ hd₂ (Prod.snd '' tsupport f) (IsCompact.image hfs continuous_snd)
  obtain ⟨Bf, hBf⟩ := hfc.bounded_above_of_compact_support hfs
  have hBf0 : 0 ≤ Bf := (norm_nonneg _).trans (hBf (1, 1))
  have hclosed : IsClosed (((twCent (thC n) d₁).prod (twCent (thC n) d₂) : Subgroup _) :
      Set (GL (Fin n) ℂ × GL (Fin n) ℂ)) := by
    rw [Subgroup.coe_prod]; exact hcl₁.prod hcl₂
  obtain ⟨A₀, -, hA₀⟩ := hQI (GL (Fin n) ℂ × GL (Fin n) ℂ) (μ.prod μ) ((twCent (thC n) d₁).prod (twCent (thC n) d₂)) ν
    (C₁ ×ˢ C₂) hclosed (hC₁.prod hC₂)
  have hint : ∀ h : GL (Fin n) ℂ × GL (Fin n) ℂ → ℂ, Measurable h →
      (∀ t ∈ (twCent (thC n) d₁).prod (twCent (thC n) d₂), ∀ x, h (t * x) = h x) →
      (∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ C₁ ×ˢ C₂, ‖h x‖ ≤ B) →
      quotLIntegral (μ.prod μ) ((twCent (thC n) d₁).prod (twCent (thC n) d₂)) ν
        (fun x => ‖f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) * h x‖ₑ) ≠ ⊤ := by
    intro h hm hinv ⟨B, hB0, hB⟩
    refine (hA₀ (fun x => f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) * h x) (Bf * B) (mul_nonneg hBf0 hB0)
      (hΦc.measurable.mul hm) (fun t ht x => by rw [hΦinv t ht x, hinv t ht x]) ?_ ?_).1
    · intro x hx
      have hfx : f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) ≠ 0 := left_ne_zero_of_mul hx
      have hts : (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) ∈ tsupport f :=
        subset_tsupport _ (Function.mem_support.2 hfx)
      obtain ⟨a₁, ha₁, b₁, hb₁, e₁⟩ := Set.mem_mul.1 (hsub₁ (show twConj (thC n) x.1 d₁ ∈ Prod.fst '' tsupport f from ⟨_, hts, rfl⟩))
      obtain ⟨a₂, ha₂, b₂, hb₂, e₂⟩ := Set.mem_mul.1 (hsub₂ (show twConj (thC n) x.2 d₂ ∈ Prod.snd '' tsupport f from ⟨_, hts, rfl⟩))
      exact Set.mem_mul.2 ⟨(a₁, a₂), Subgroup.mem_prod.2 ⟨ha₁, ha₂⟩, (b₁, b₂), ⟨hb₁, hb₂⟩, Prod.ext e₁ e₂⟩
    · intro x hx
      rw [norm_mul]
      exact mul_le_mul (hBf _) (hB x hx) (norm_nonneg _) hBf0
  have hq : Continuous fun x : GL (Fin n) ℂ × GL (Fin n) ℂ => p₁ x.1 + p₂ x.2 + z :=
    ((hF₁.cont.comp continuous_fst).add (hF₂.cont.comp continuous_snd)).add continuous_const
  have hq' : Continuous fun x : GL (Fin n) ℂ × GL (Fin n) ℂ => p₁ x.1 := hF₁.cont.comp continuous_fst
  have hmF : Measurable fun x : GL (Fin n) ℂ × GL (Fin n) ℂ => V (p₁ x.1 + p₂ x.2 + z) := hV.meas.comp hq.measurable
  have hmB : Measurable fun x : GL (Fin n) ℂ × GL (Fin n) ℂ => V (p₁ x.1) := hV.meas.comp hq'.measurable
  have hiF : ∀ t ∈ (twCent (thC n) d₁).prod (twCent (thC n) d₂), ∀ x : GL (Fin n) ℂ × GL (Fin n) ℂ,
      V (p₁ (t * x).1 + p₂ (t * x).2 + z) = V (p₁ x.1 + p₂ x.2 + z) := fun t ht x =>
    tor2 hF₁ hF₂ (Subgroup.mem_prod.1 ht).1 (Subgroup.mem_prod.1 ht).2 x.1 x.2 z
  have hiB : ∀ t ∈ (twCent (thC n) d₁).prod (twCent (thC n) d₂), ∀ x : GL (Fin n) ℂ × GL (Fin n) ℂ,
      V (p₁ (t * x).1) = V (p₁ x.1) := fun t ht x => by
    simpa using hF₁.tor t.1 (Subgroup.mem_prod.1 ht).1 x.1 0
  have hIF := hint _ hmF hiF (vp_bdd_on hV hq (hC₁.prod hC₂))
  have hIB := hint _ hmB hiB (vp_bdd_on hV hq' (hC₁.prod hC₂))
  have hsplit := (hQA (GL (Fin n) ℂ × GL (Fin n) ℂ) (μ.prod μ) ((twCent (thC n) d₁).prod (twCent (thC n) d₂)) ν).2.1
    (fun x => f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) * V (p₁ x.1 + p₂ x.2 + z))
    (fun x => f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) * V (p₁ x.1))
    (hΦc.measurable.mul hmF) (hΦc.measurable.mul hmB) hIF hIB

  have hA : quotIntegral (μ.prod μ) ((twCent (thC n) d₁).prod (twCent (thC n) d₂)) ν
      (fun x => f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) * V (p₁ x.1 + p₂ x.2 + z) -
        f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) * V (p₁ x.1)) = 0 := by
    refine hQP _ _ μ μ _ _ ν _ hcl₁ hcl₂ hcomm₁ hcomm₂
      ((hΦc.measurable.mul hmF).sub (hΦc.measurable.mul hmB))
      (fun t ht x => by simp only [hΦinv t ht x, hiF t ht x, hiB t ht x]) (Or.inl fun ν₁ _ _ x₂ => ?_)
    have h1 := hOV n m μ d₁ ν₁ (fun y => f (y, twConj (thC n) x₂ d₂)) V p₁ (p₂ x₂ + z) hd₁
      (hfc.comp (continuous_id.prodMk continuous_const)) (hcs_right hfs _) (hcu₁ _) hV hF₁
      (by rw [Pi.add_apply, hF₂.zero, hz, add_zero])
    calc _ = quotIntegral μ (twCent (thC n) d₁) ν₁ (fun x => f (twConj (thC n) x d₁, twConj (thC n) x₂ d₂) *
          (V (p₁ x + (p₂ x₂ + z)) - V (p₁ x))) := by
          congr 1; funext x; dsimp only; rw [add_assoc]; ring
      _ = 0 := h1

  have hB : quotIntegral (μ.prod μ) ((twCent (thC n) d₁).prod (twCent (thC n) d₂)) ν
      (fun x => f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) * V (p₁ x.1)) = 0 := by
    refine hQP _ _ μ μ _ _ ν _ hcl₁ hcl₂ hcomm₁ hcomm₂ (hΦc.measurable.mul hmB)
      (fun t ht x => by simp only [hΦinv t ht x, hiB t ht x]) (Or.inr fun ν₂ _ _ x₁ => ?_)
    have hne : (fun _ : Fin m => (1 : SignType)) ≠ 0 := by
      intro h
      have := congrFun h ⟨0, Nat.pos_of_ne_zero hm⟩
      simp at this
    obtain ⟨W₁, W₂, hW, -⟩ := hF₂.nil _ hne
    have h1 := hLV n μ (fun y => f (twConj (thC n) x₁ d₁, y)) (fun _ => 1) d₂ ν₂ W₁ W₂
      (hfc.comp (continuous_const.prodMk continuous_id)) (hcs_left hfs _) (hcu₂ _) hd₂ hW.1 hW.2.1 hW.2.2.1 hW.2.2.2
      measurable_const (fun _ _ => ⟨1, fun _ _ => by simp⟩) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    calc _ = quotIntegral μ (twCent (thC n) d₂) ν₂ (fun x => V (p₁ x₁) *
          (f (twConj (thC n) x₁ d₁, twConj (thC n) x d₂) * (fun _ => (1 : ℂ)) x)) := by
          congr 1; funext x; dsimp only; ring
      _ = V (p₁ x₁) * quotIntegral μ (twCent (thC n) d₂) ν₂ (fun x =>
          f (twConj (thC n) x₁ d₁, twConj (thC n) x d₂) * (fun _ => (1 : ℂ)) x) := (hQA _ μ _ ν₂).2.2 _ _
      _ = 0 := by rw [h1, mul_zero]
  rw [hA, hB] at hsplit
  linear_combination -hsplit
end
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc
open scoped Pointwise

namespace PositivityTheory.Rg.BcB.CV.ClassVanishing

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4

theorem exists_haar_inv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [LocallyCompactSpace G] (hc : ∀ a b : G, a * b = b * a) :
    ∃ ν : Measure G, ν.IsHaarMeasure ∧ ν.IsInvInvariant := by
  letI : CommGroup G := { (inferInstance : Group G) with mul_comm := hc }
  exact ⟨Measure.haar, inferInstance, Measure.IsHaarMeasure.isInvInvariant_of_regular _⟩

theorem gamma_fin_zero (y : (Fin 0 → SignType) → ℝ) (a : Fin 0 → ℝ) : gam y a = 1 := by
  unfold gam gamOn
  rw [Finset.sum_eq_single (∅ : Finset (Fin 0 → SignType))]
  · simp
  · intro s hs hne
    exfalso
    apply hne
    simp only [Finset.mem_filter] at hs
    exact Finset.subset_empty.mp fun e he => absurd (Subsingleton.elim e 0 ▸ he) hs.2.1
  · intro h
    exfalso
    apply h
    simp [Finset.mem_filter]

theorem quot_congr {G : Type} [Group G] [MeasurableSpace G] (μ : Measure G) {H H' : Subgroup G} (h : H = H')
    (F : G → ℂ) : quotIntegral μ H Measure.count F = quotIntegral μ H' Measure.count F := by
  subst h; rfl

theorem quotL_congr {G : Type} [Group G] [MeasurableSpace G] (μ : Measure G) {H H' : Subgroup G} (h : H = H')
    (F : G → ENNReal) : quotLIntegral μ H Measure.count F = quotLIntegral μ H' Measure.count F := by
  subst h; rfl

end PositivityTheory.Rg.BcB.CV.ClassVanishing

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.BcB.CV

theorem PositivityTheory.Rg.BcB.CV.pf_ClassVanish : PositivityTheory.Rg.BcB.D4.PairParam → PositivityTheory.Rg.BcB.D4.TorusChar → PositivityTheory.Rg.BcB.D4.ChiGam → PositivityTheory.Rg.BcB.D4.QuotStage → PositivityTheory.Rg.BcB.D4.RatDisc → PositivityTheory.Rg.BcB.SizeBasic → PositivityTheory.Rg.BcB.CV.QAdd → PositivityTheory.Rg.BcB.CV.Vfun → PositivityTheory.Rg.BcB.CV.AdTop → PositivityTheory.Rg.BcB.CV.CutInt → PositivityTheory.Rg.BcB.CV.Glob1 → PositivityTheory.Rg.BcB.CV.Glob2 → PositivityTheory.Rg.BcB.ClassVanish := by
  intro hPP hTC hCG hQS hRD hSB hQA hVf hAT hCI hG1 hG2
  intro E _ _ _ _ n
  obtain ⟨C₀, hC₀⟩ := hCG E n
  refine ⟨max 0 C₀, ?_⟩
  intro _ _ μ _ τ r φ d hφ hsz hvc hτ hreg hne
  obtain ⟨hLC, hT2, hSC, -, -, -⟩ := hAT E n
  haveI := hLC
  haveI := hT2
  haveI := hSC
  obtain ⟨m, Wof, hiso, huniq, hzero, hmeet, hmono, hperp⟩ := hPP E n d hreg
  obtain ⟨hcomm, a, hdegT, hadd, hrat0, hcont, hcpt⟩ := hTC E n d m Wof hiso huniq hzero hmeet hmono hreg
  obtain ⟨hle, hdisc, hclosed⟩ := hRD.1 E n d
  haveI : LocallyCompactSpace (adCent d) := hclosed.locallyCompactSpace
  haveI : BorelSpace (adCent d) := Subtype.borelSpace _
  haveI : SecondCountableTopology (adCent d) := TopologicalSpace.Subtype.secondCountableTopology _
  have hcommT : ∀ s t : adCent d, s * t = t * s := fun s t => Subtype.ext (hcomm s s.2 t t.2)
  obtain ⟨ν, hνH, hνI⟩ := ClassVanishing.exists_haar_inv hcommT
  haveI := hνH
  haveI := hνI
  have hmap : (ratIn d).map (adCent d).subtype = ratCent d := by
    rw [ratIn, Subgroup.subgroupOf_map_subtype, inf_of_le_left hle]
  set F : GA E n → ℂ := fun x => chiT τ x * φ (twConj (thetaA E n) x (ratGL E n d)) with hF
  obtain ⟨hFm, hFinv, hFfin⟩ := hCI E n μ τ φ d hφ
  have hstage := hQS (GA E n) μ (adCent d) ν (ratIn d) F hclosed hdisc hFm
    (fun g hg x => hFinv g (Subgroup.mem_subgroupOf.1 hg) x)
    (by rw [ClassVanishing.quotL_congr μ hmap]; exact hFfin)
  rw [ClassVanishing.quot_congr μ hmap] at hstage

  obtain ⟨V, hVdef⟩ : ∃ V : ((Fin m → SignType) → ℝ) → ℂ,
      V = fun y => quotIntegral ν (ratIn d) Measure.count fun t : adCent d => (gam y (a t) : ℂ) := ⟨_, rfl⟩
  have hcptT : ∀ M : ℝ, ∃ K : Set (adCent d), IsCompact K ∧ ∀ t : adCent d, (∀ i, |a t i| ≤ M) →
      t ∈ ((ratIn d : Subgroup (adCent d)) : Set (adCent d)) * K := by
    intro M
    obtain ⟨K, hK, hKt⟩ := hcpt M
    refine ⟨Subtype.val ⁻¹' K, hclosed.isClosedEmbedding_subtypeVal.isCompact_preimage hK, fun t ht => ?_⟩
    obtain ⟨g, hg, k, hk, hgk⟩ := Set.mem_mul.1 (hKt t t.2 ht)
    have hgA : g ∈ adCent d := hle hg
    have hkA : k ∈ adCent d := by
      have : k = g⁻¹ * t := by rw [← hgk]; group
      rw [this]; exact (adCent d).mul_mem ((adCent d).inv_mem hgA) t.2
    exact Set.mem_mul.2 ⟨⟨g, hgA⟩, hg, ⟨k, hkA⟩, hk, Subtype.ext hgk⟩
  obtain ⟨hVP, hVtr⟩ := hVf (adCent d) ν (ratIn d) m (fun t => a t) hcommT hdisc
    (continuousOn_iff_continuous_domRestrict.1 hcont) (fun s t => hadd s s.2 t t.2)
    (fun t ht => hrat0 t (Subgroup.mem_subgroupOf.1 ht)) hcptT
  rw [← hVdef] at hVP
  have hVinv : ∀ t ∈ adCent d, ∀ y, V (fun e => y e - sdot e (a t)) = V y := by
    intro t ht y
    have := hVtr y ⟨t, ht⟩
    rw [hVdef]
    exact this

  have hinner : ∀ x, (quotIntegral ν (ratIn d) Measure.count fun t : adCent d => F ((t : GA E n) * x)) =
      φ (twConj (thetaA E n) x (ratGL E n d)) * V (yOf τ Wof x) := by
    intro x
    have hpt : (fun t : adCent d => F ((t : GA E n) * x)) =
        fun t : adCent d => φ (twConj (thetaA E n) x (ratGL E n d)) * (gam (yOf τ Wof x) (a t) : ℂ) := by
      funext t
      show chiT τ ((t : GA E n) * x) * φ (twConj (thetaA E n) ((t : GA E n) * x) (ratGL E n d)) = _
      rw [twConj_mul_left (thetaA E n) (ratGL E n d) t.2 x]
      by_cases h0 : φ (twConj (thetaA E n) x (ratGL E n d)) = 0
      · simp [h0]
      · have h1 := hsz _ h0
        have h2 := (hSB E n).2.1 (twConj (thetaA E n) x (ratGL E n d))
        have hτ' : C₀ * (1 + logSize (twConj (thetaA E n) x (ratGL E n d))) ≤ τ :=
          calc C₀ * (1 + logSize (twConj (thetaA E n) x (ratGL E n d)))
              ≤ max 0 C₀ * (1 + logSize (twConj (thetaA E n) x (ratGL E n d))) :=
                mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
            _ ≤ max 0 C₀ * (1 + r) := mul_le_mul_of_nonneg_left (by linarith) (le_max_left _ _)
            _ ≤ τ := hτ
        exact (mul_comm _ _).trans
          (congrArg (fun z => φ (twConj (thetaA E n) x (ratGL E n d)) * z)
            (hC₀ d m Wof a hiso huniq hzero hmeet hmono hreg hdegT τ x hτ' t t.2))
    rw [hpt, (hQA (adCent d) ν (ratIn d) Measure.count).2.2 (φ (twConj (thetaA E n) x (ratGL E n d)))
      (fun t : adCent d => (gam (yOf τ Wof x) (a t) : ℂ)), hVdef]
  have hcut : cutTerm μ τ φ d = quotIntegral μ (adCent d) ν
      (fun x => φ (twConj (thetaA E n) x (ratGL E n d)) * V (yOf τ Wof x)) := by
    show quotIntegral μ (ratCent d) Measure.count F = _
    rw [hstage]
    congr 1
    funext x
    exact hinner x
  rw [hcut]
  by_cases hm : m = 0
  · subst hm
    have hV : ∀ y, V y = V 0 := fun y => by
      rw [hVdef]
      simp only [ClassVanishing.gamma_fin_zero]
    rw [show (fun x => φ (twConj (thetaA E n) x (ratGL E n d)) * V (yOf τ Wof x)) =
        fun x => V 0 * φ (twConj (thetaA E n) x (ratGL E n d)) from funext fun x => by rw [hV, mul_comm],
      (hQA (GA E n) μ (adCent d) ν).2.2 (V 0) (fun x => φ (twConj (thetaA E n) x (ratGL E n d))),
      hG1 E n μ d ν φ hreg hne hcomm hclosed hφ hvc, mul_zero]
  · exact hG2 E n m μ d ν Wof a V τ φ hm
      ⟨hreg, hiso, huniq, hzero, hmeet, hmono, hperp, hcomm, hclosed, hdegT⟩ hVP hVinv hφ hvc
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc

namespace PositivityTheory.Rg.BcB.CV.Glob1Aux

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4

theorem emb_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (v : InfinitePlace E) (x : E) :
    v.embedding (conjE E x) = starRingEnd ℂ (v.embedding x) :=
  IsCMField.complexEmbedding_complexConj E v.embedding x

theorem locGL_theta {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (v : InfinitePlace E)
    (d : GL (Fin n) E) : locGL v (thetaE E n d) = thC n (locGL v d) := by
  apply Units.ext
  have h1 : (locGL v (thetaE E n d)).val = ((thetaR (conjE E) n d).val).map v.embedding := rfl
  have h2 : (locGL v d⁻¹).val = (d⁻¹ : GL (Fin n) E).val.map v.embedding := rfl
  rw [h1, thetaR_val, thetaR_val, ← map_inv, h2]
  ext i j
  simp [emb_conj]

theorem locGL_nrm {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (v : InfinitePlace E)
    (d : GL (Fin n) E) : locGL v (nrm d) = locGL v d * thC n (locGL v d) := by
  rw [nrm, map_mul, locGL_theta]

theorem sep {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (v : InfinitePlace E)
    (d : GL (Fin n) E) (hd : IsRegD d) : (locGL v d * thC n (locGL v d)).val.charpoly.Separable := by
  rw [← locGL_nrm]
  have : (locGL v (nrm d)).val = (nrm d).val.map v.embedding := rfl
  rw [this, Matrix.charpoly_map]
  exact hd.map

theorem exists_measure {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
    (e : G ≃ₜ* H) (T : Subgroup G) (T' : Subgroup H) (hT : T.map e.toMonoidHom = T') (ν : Measure T)
    [ν.IsHaarMeasure] [ν.IsInvInvariant] : ∃ ν' : Measure T', ν'.IsHaarMeasure ∧ ν'.IsInvInvariant := by
  have h1 : ∀ t : T, e t ∈ T' := fun t => by
    rw [← hT]; exact Subgroup.mem_map_of_mem _ t.2
  have h2 : ∀ s : T', e.symm s ∈ T := fun s => by
    have hs : (s : H) ∈ T.map e.toMonoidHom := by rw [hT]; exact s.2
    obtain ⟨t, ht, hts⟩ := Subgroup.mem_map.1 hs
    rw [← hts]
    show e.symm (e t) ∈ T
    rw [e.symm_apply_apply]
    exact ht
  let f : T ≃ₜ* T' :=
    { toFun := fun t => ⟨e t, h1 t⟩
      invFun := fun s => ⟨e.symm s, h2 s⟩
      left_inv := fun t => Subtype.ext (e.symm_apply_apply t)
      right_inv := fun s => Subtype.ext (e.apply_symm_apply s)
      map_mul' := fun a b => Subtype.ext (map_mul e (a : G) (b : G))
      continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _ }
  refine ⟨ν.map f, inferInstance, ⟨?_⟩⟩
  have hf : Measurable f := f.continuous.measurable
  have hinv : Measurable (fun t : T => t⁻¹) := continuous_inv.measurable
  have hν : Measure.map (fun t : T => t⁻¹) ν = ν := Measure.IsInvInvariant.inv_eq_self
  show Measure.map (fun s : T' => s⁻¹) (Measure.map f ν) = Measure.map f ν
  rw [Measure.map_map continuous_inv.measurable hf]
  conv_rhs => rw [← hν, Measure.map_map hf hinv]
  congr 1
  funext t
  exact (map_inv f t).symm

end PositivityTheory.Rg.BcB.CV.Glob1Aux

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.BcB.CV.Glob1Aux in
theorem PositivityTheory.Rg.BcB.CV.pf_Glob1 : PositivityTheory.Rg.BcB.D4.SplitAt → PositivityTheory.Rg.BcB.D4.NonEllFlag → PositivityTheory.Rg.BcB.LocVanish → PositivityTheory.Rg.BcB.CV.LocTor → PositivityTheory.Rg.BcB.CV.QMap → PositivityTheory.Rg.BcB.CV.QProd → PositivityTheory.Rg.BcB.CV.Ploc → PositivityTheory.Rg.BcB.CV.AdTop → PositivityTheory.Rg.BcB.CV.Glob1 := by
  intro hSA hNEF hLV hLT hQM hQP hPl hAT E _ _ _ n _ _ μ _ d ν _ _ φ hreg hne hcomm hcl hφ hvc
  obtain ⟨v, W₁, W₂, hW0, hW12, hp1, hp2⟩ := hNEF E n d hreg hne
  obtain ⟨G', _, _, _, _, _, _, _, _, _, e, μ₁, μ₂, θ', hμ₁, hμ₂, -, he1, hemb, hθ, hcent⟩ := hSA E n v μ
  have hsep := sep v d hreg
  obtain ⟨hT1c, hT1m, -, hLC, hSC⟩ := hLT n (locGL v d) hsep
  obtain ⟨hLCA, hT2A, hSCA, hθA, -, -⟩ := hAT E n
  have := hLC; have := hSC; have := hLCA; have := hT2A; have := hSCA; have := hμ₁; have := hμ₂
  have : T2Space (GL (Fin n) ℂ × G') := e.symm.toHomeomorph.isEmbedding.t2Space
  have : T2Space (GL (Fin n) ℂ) :=
    T2Space.of_injective_continuous (f := fun g : GL (Fin n) ℂ => (g, (1 : G')))
      (fun a b h => (Prod.ext_iff.1 h).1) (continuous_id.prodMk continuous_const)
  have : T2Space G' :=
    T2Space.of_injective_continuous (f := fun b : G' => ((1 : GL (Fin n) ℂ), b))
      (fun a b h => (Prod.ext_iff.1 h).2) (continuous_const.prodMk continuous_id)
  have he1' : (e (ratGL E n d)).1 = locGL v d := by
    rw [he1]; exact (hPl E n v ⊥).2.2.2.2.2.2.1 d
  have hmem : ∀ p, p ∈ (twCent (thC n) (locGL v d)).prod (twCent θ' (e (ratGL E n d)).2) ↔
      p ∈ e '' (adCent d : Set (GA E n)) := by
    intro p; rw [← hcent d]; exact Iff.rfl
  have hT2c : IsClosed (twCent θ' (e (ratGL E n d)).2 : Set G') := by
    have hc : IsClosed (e '' (adCent d : Set (GA E n))) := e.toHomeomorph.isClosedMap _ hcl
    have : (twCent θ' (e (ratGL E n d)).2 : Set G') =
        (fun b => ((1 : GL (Fin n) ℂ), b)) ⁻¹' (e '' (adCent d : Set (GA E n))) := by
      ext b
      rw [Set.mem_preimage, ← hmem, Subgroup.mem_prod]
      exact ⟨fun h => ⟨Subgroup.one_mem _, h⟩, fun h => h.2⟩
    rw [this]
    exact hc.preimage (continuous_const.prodMk continuous_id)
  have hT2m : ∀ s ∈ twCent θ' (e (ratGL E n d)).2, ∀ t ∈ twCent θ' (e (ratGL E n d)).2, s * t = t * s := by
    intro s hs t ht
    obtain ⟨x, hx, hxs⟩ := (hmem (1, s)).1 (Subgroup.mem_prod.2 ⟨Subgroup.one_mem _, hs⟩)
    obtain ⟨y, hy, hyt⟩ := (hmem (1, t)).1 (Subgroup.mem_prod.2 ⟨Subgroup.one_mem _, ht⟩)
    have h := congrArg (fun p => (e p).2) (hcomm x hx y hy)
    simp only [map_mul, Prod.snd_mul, hxs, hyt] at h
    exact h
  obtain ⟨ν', hν'1, hν'2⟩ := exists_measure e (adCent d) _ (hcent d) ν
  have := hν'1; have := hν'2
  have hFc : Continuous fun x : GA E n => φ (twConj (thetaA E n) x (ratGL E n d)) :=
    hφ.cont.comp ((continuous_inv.mul continuous_const).mul hθA)
  refine hQM (GA E n) (GL (Fin n) ℂ × G') e μ (μ₁.prod μ₂) (adCent d) _ ν ν' _ hcl (hcent d) hFc.measurable
    (fun t ht x => congrArg φ (twConj_mul_left (thetaA E n) (ratGL E n d) ht x)) ?_
  refine hQP (GL (Fin n) ℂ) G' μ₁ μ₂ _ _ ν' _ hT1c hT2c hT1m hT2m (hFc.comp e.symm.continuous).measurable ?_ (Or.inl ?_)
  · intro t ht x
    obtain ⟨s, hs, rfl⟩ := (hmem t).1 ht
    show φ (twConj (thetaA E n) (e.symm (e s * x)) (ratGL E n d)) = φ (twConj (thetaA E n) (e.symm x) (ratGL E n d))
    rw [map_mul, e.symm_apply_apply]
    exact congrArg φ (twConj_mul_left (thetaA E n) (ratGL E n d) hs _)
  · intro ν₁ _ _ x₂
    have key : ∀ x₁ : GL (Fin n) ℂ, twConj (thetaA E n) (e.symm (x₁, x₂)) (ratGL E n d) =
        e.symm (twConj (thC n) x₁ (locGL v d), twConj θ' x₂ (e (ratGL E n d)).2) := by
      intro x₁
      apply e.injective
      rw [e.apply_symm_apply]
      simp only [twConj, map_mul, map_inv, hθ, e.apply_symm_apply]
      refine Prod.ext ?_ ?_
      · simp [he1']
      · simp
    have hf : VeryCusp fun g => φ (e.symm (g, twConj θ' x₂ (e (ratGL E n d)).2)) := by
      have h := hvc v (e.symm (1, twConj θ' x₂ (e (ratGL E n d)).2)) (by rw [← he1, e.apply_symm_apply])
      have : (fun g => φ (e.symm (g, twConj θ' x₂ (e (ratGL E n d)).2))) =
          fun g => φ (embInf n v g * e.symm (1, twConj θ' x₂ (e (ratGL E n d)).2)) := by
        funext g
        have hg : embInf n v g = e.symm (g, 1) := by rw [← hemb g, e.symm_apply_apply]
        rw [hg, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
      rw [this]; exact h
    have hfc : Continuous fun g => φ (e.symm (g, twConj θ' x₂ (e (ratGL E n d)).2)) :=
      hφ.cont.comp (e.symm.continuous.comp (continuous_id.prodMk continuous_const))
    have hfs : HasCompactSupport fun g => φ (e.symm (g, twConj θ' x₂ (e (ratGL E n d)).2)) := by
      have hK : IsCompact (e '' tsupport φ) := hφ.supp.image e.continuous
      refine IsCompact.of_isClosed_subset (hK.image continuous_fst) (isClosed_tsupport _) ?_
      have hcl' : IsClosed {g : GL (Fin n) ℂ | (g, twConj θ' x₂ (e (ratGL E n d)).2) ∈ e '' tsupport φ} :=
        hK.isClosed.preimage (continuous_id.prodMk continuous_const)
      refine (closure_minimal ?_ hcl').trans ?_
      · intro g hg
        exact ⟨_, subset_tsupport _ hg, e.apply_symm_apply _⟩
      · intro g hg
        exact ⟨_, hg, rfl⟩
    have hLV' := hLV n μ₁ _ (fun _ => 1) (locGL v d) ν₁ W₁ W₂ hfc hfs hf hsep hW0 hW12 hp1 hp2 measurable_const
      (fun _ _ => ⟨1, fun _ _ => by simp⟩) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    refine Eq.trans ?_ hLV'
    congr 1
    funext x₁
    show φ (twConj (thetaA E n) (e.symm (x₁, x₂)) (ratGL E n d)) = _
    rw [key, mul_one]
end
end
