module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.OrthZero
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.TwTrSum
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle005
import Formalism.DoubleCosetMeasures.Statement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle575
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.piFinOf_pf :
    PiAdm → TensType → CvType → CvIn → TypeIn → PiFin := by
  intro hA hT hC hI hY E _ _ _ n hn D π hπ μa μb ha hb Ma Mb κ ka kb va vb R ψ U h1 h2 h3 h4 h5 i j
  obtain ⟨ht, K, W, k1, k2, w1, w2, hl⟩ := hT E n μa μb ha hb Ma Mb κ ka kb va vb R ψ U h1 h2 h3 h4 h5 i j
  obtain ⟨Y, y1, y2, y3⟩ := hA E n hn π hπ K W k1 w1
  refine ⟨Y, y1, y2, fun u hu φ hφ => ?_⟩
  obtain ⟨s0, s1⟩ := hI E n hn D π hπ φ hφ
  obtain ⟨s2, s3, -⟩ := s1 _ u ht hu
  have ty := hC E n D K W _ u φ.1 k2 w1 ht hl hu s0.1
  obtain ⟨φ', m, e⟩ := hY E n hn D π hπ K W k1 k2 w1 w2 _ s2 s3 ty
  refine ⟨φ', y3 φ' m ?_, fun x => congrFun e x⟩
  rw [← e] at ty
  exact ty
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.Zero.ConvolutionTheory.EB
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] borelG borelF borelA borelH

private theorem lev_mono {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (S : Set (Pl E))
    {N N' : ∀ w : Pl E, Subgroup (GLw n w)} (h : ∀ w, N w ≤ N' w) : Lev S N ≤ Lev S N' := by
  intro g hg
  simp only [Lev, Subgroup.mem_iInf] at hg ⊢
  exact fun i => h _ (hg i)

private theorem level_term (h1 : ThetaFixedGlobalWeights) (h3 : LevTop) (h6 : ToYd) (h7 : LevelTr)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (hn : 1 ≤ n) (π : CuspSub E n)
    (hreg : (CG.mk π).IsRegAlg) (hd : GlobalTheory.ContraPair.DualIsConj π) (lamE : (E →+* ℂ) → DomWeight n)
    (hlam : ∀ φ, π.HasInfChar φ (infOfWeight (lamE φ))) {S : Set (Pl E)} (hS : IsSection S)
    {Z : Finset (Pl E)} (hZ : SplitIn S Z) {B : Pl E → Multiset ℂˣ} {τ : ∀ w : Pl E, SmIrr (GLw n w)}
    (hB : ∀ w, Off Z w → (CG.mk π).HasSat w (B w)) (hτ : ∀ w ∈ Z, π.IsLocComp w (τ w))
    {u : GL (Fin n) E} (hu : IsTransl u) (μC : Measure (G n)) (μ : Measure (H E n 0))
    [μC.IsHaarMeasure] [μ.IsHaarMeasure] {N : ∀ w : Pl E, Subgroup (GLw n w)} (hN : Good Z N)
    (hfix : ∃ ψ ∈ π.V, ψ ≠ 0 ∧ ∀ k ∈ Lev S N, finRep E n k ψ = ψ) :
    (∃ φ : ∀ w : Pl E, LF n 0 w, (∀ w ∈ Z, ∀ N' ≤ N w, ∀ b, IsHecke N' (two φ φ w b)) ∧
      (∏ w ∈ Z, trc (τ w).ρ (KGL w (n := n)) fun g => seen φ φ w (g, 1)) ≠ 0) ∧
    ∃ c : ℂ, c ≠ 0 ∧ ∀ φ₁ φ₂ : ∀ w : Pl E, LF n 0 w, (∀ w ∈ Z, ∀ b, IsHecke (N w) (two φ₁ φ₂ w b)) →
      ∀ T : Finset (Pl E), Disjoint T Z → ∀ (e₁ e₂ : Pl E → Ex (Fin (n + 1) × Fin (0 + 1)))
        (k : ∀ v : InfinitePlace E, Mat n → ((lefE n (lamE v.embedding).w).V →L[ℂ] (lefE n (lamE v.embedding).w).V))
        (vl : InfinitePlace E → Inf n → ℂ) (R : ℝ),
        TEv S T e₂ → (∀ v : InfinitePlace E, IsMult μC (lefE n (lamE v.embedding).w) (k v) (vl v) R) →
        IsTwTr μ π (phiProd (fun v => (lamE v.embedding).w) k (finU S u (intersection_update_fsHerm_neg_one Z T φ₁ e₁) (intersection_update_fsHerm_neg_one Z T φ₂ e₂)))
          (c * (∏ v : InfinitePlace E, vl v (infOf (lamE v.embedding).w)) *
            (∏ w ∈ Z, trc (τ w).ρ (KGL w (n := n)) fun g => seen φ₁ φ₂ w (g, 1)) * val T e₁ e₂ B 0) := by
  obtain ⟨hKo, hKc, -, -⟩ := h3 E n S Z N hS hZ hN
  obtain ⟨hKθ, hY⟩ := h6 E n S Z N hS hZ hN π u hu
  let K₀ : TopologicalSpace.PositiveCompacts (GF E n) :=
    ⟨⟨(Lev S N : Set (GF E n)), hKc⟩, by
      show (interior (Lev S N : Set (GF E n))).Nonempty
      rw [hKo.interior_eq]
      exact ⟨1, (Lev S N).one_mem⟩⟩
  let μf : Measure (GF E n) := Measure.haarMeasure K₀
  haveI : μf.IsHaarMeasure := inferInstance
  obtain ⟨Y, ρ, A, cK, hYπ, hfd, hne, hYfix, hact, hsimple, hsq, htw, hcK, htr⟩ :=
    h1 E n hn π hreg hd lamE hlam (Lev S N) hKo hKc hKθ hfix μC μf μ
  obtain ⟨y, v, hv, hyv⟩ := hY μf inferInstance Y ρ A hYπ hfd hne hYfix hact hsimple hsq htw
  obtain ⟨href, d, hd0, hdtr⟩ := h7 E n S Z N hS hZ hN π y B τ hB hτ
  refine ⟨href, cK * v * d, mul_ne_zero (mul_ne_zero hcK hv) hd0, ?_⟩
  intro φ₁ φ₂ hφ T hT e₁ e₂ k vl R hE hM
  obtain ⟨hH, hTr⟩ := hdtr φ₁ φ₂ hφ T hT e₁ e₂ hE
  obtain ⟨hHF, hTrY⟩ := hyv _ hH
  have key := htr k vl (fun _ => R) hM _ hHF
  rw [hTrY, hTr] at key
  have e : cK * (∏ w : InfinitePlace E, vl w (infOf (lamE w.embedding).w)) *
      (v * (d * (∏ w ∈ Z, trc (τ w).ρ (KGL w (n := n)) fun g => seen φ₁ φ₂ w (g, 1)) * val T e₁ e₂ B 0)) =
      cK * v * d * (∏ v : InfinitePlace E, vl v (infOf (lamE v.embedding).w)) *
        (∏ w ∈ Z, trc (τ w).ρ (KGL w (n := n)) fun g => seen φ₁ φ₂ w (g, 1)) * val T e₁ e₂ B 0 := by ring
  rw [e] at key
  exact key

theorem piTerm_of_weights_levels :
    ThetaFixedGlobalWeights → WtEx → LevTop → LevFix → LcLevel → ToYd → LevelTr → TwUniq → PiTerm := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 E _ _ _ _ n hn π hreg hd
  obtain ⟨lamE, hlam⟩ := h2 E n π hreg
  refine ⟨fun v => lamE v.embedding, fun v => hlam _, ?_⟩
  intro S hS Z hZ B τ hB hτ u hu μC μ _ _
  obtain ⟨N₀, hN₀, ψ, hψ, hψ0, hψfix⟩ := h4 E n π S Z hS hZ fun w hw => ⟨B w, hB w hw⟩
  obtain ⟨⟨φr, hr, hrne⟩, c₀, hc₀, hlev₀⟩ := level_term h1 h3 h6 h7 hn π hreg hd lamE hlam hS hZ hB hτ hu μC μ hN₀
    ⟨ψ, hψ, hψ0, hψfix⟩
  refine ⟨c₀, hc₀, ?_⟩
  intro φ₁ φ₂ hφ T hT e₁ e₂ k vl R hE hM
  obtain ⟨N, hN, hle, hHecke⟩ := h5 E n Z N₀ hN₀ φ₁ φ₂ hφ
  obtain ⟨-, c, -, hlev⟩ := level_term h1 h3 h6 h7 hn π hreg hd lamE hlam hS hZ hB hτ hu μC μ hN
    ⟨ψ, hψ, hψ0, fun g hg => hψfix g (lev_mono S hle hg)⟩
  have main := hlev φ₁ φ₂ hHecke T hT e₁ e₂ k vl R hE hM
  by_cases hP : (∏ v : InfinitePlace E, vl v (infOf (lamE v.embedding).w)) = 0
  · rw [hP] at main ⊢
    simpa using main

  have hcc : c = c₀ := by
    let e : Pl E → Ex (Fin (n + 1) × Fin (0 + 1)) := fun _ => Ex.one
    have hEe : TEv S (∅ : Finset (Pl E)) e := ⟨by simp, by simp⟩
    have a₀ := hlev₀ φr φr (fun w hw b => hr w hw (N₀ w) le_rfl b) ∅ (Finset.disjoint_empty_left Z) e e k vl R hEe hM
    have a₁ := hlev φr φr (fun w hw b => hr w hw (N w) (hle w) b) ∅ (Finset.disjoint_empty_left Z) e e k vl R hEe hM
    have heq := h8 E n μ π _ _ _ a₁ a₀
    simp only [val, Finset.prod_empty, mul_one] at heq
    exact mul_right_cancel₀ hP (mul_right_cancel₀ hrne heq)
  rw [hcc] at main
  exact main

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

section

open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F
open PositivityTheory.RgTw (Mat G)

private theorem hecke_comp {G : Type} [Group G] [TopologicalSpace G] {K : Subgroup G} {φ : G → G} (hc : Continuous φ)
    (hi : ∀ g, φ (φ g) = g) (hm : ∀ a b, φ (a * b) = φ a * φ b) (hK : ∀ k ∈ K, φ k ∈ K) {h : G → ℂ}
    (hh : IsHecke K h) : IsHecke K (fun g => h (φ g)) := by
  refine ⟨?_, fun k hk x => ?_⟩
  · let e : G ≃ₜ G :=
      { toFun := φ, invFun := φ, left_inv := hi, right_inv := hi,
        continuous_toFun := hc, continuous_invFun := hc }
    exact hh.1.comp_homeomorph e
  · simp only [hm]
    exact hh.2 _ (hK k hk) _

private theorem core {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (hS : LvShift) (ρ : Representation ℂ G V) (K : Subgroup G) (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G))
    (u : G) (hu : ∀ x, x ∈ K ↔ u * x * u⁻¹ ∈ K) (θ : G → G)
    (hθc : Continuous θ) (hθi : ∀ g, θ (θ g) = g) (hθm : ∀ a b, θ (a * b) = θ a * θ b) (hθK : ∀ k ∈ K, θ k ∈ K)
    (hθu : θ u = u⁻¹) (Y : Submodule ℂ V) (hY : Y ≤ fixed ρ K) (r : (G → ℂ) → Module.End ℂ Y)
    (hact : ∀ h, IsHecke K h → ∀ y : Y, (r h y : V) = Lv ρ K h y)
    (A : Module.End ℂ Y) (hAA : A * A = 1)
    (hA : ∀ h, IsHecke K h → A * r h = r (fun g => h (θ g)) * A) :
    (r (fun g => (K : Set G).indicator 1 (u⁻¹ * g)) * A) * (r (fun g => (K : Set G).indicator 1 (u⁻¹ * g)) * A) = 1 ∧
    (∀ h, IsHecke K h → (r (fun g => (K : Set G).indicator 1 (u⁻¹ * g)) * A) * r h =
      r (fun g => h (u * θ g * u⁻¹)) * (r (fun g => (K : Set G).indicator 1 (u⁻¹ * g)) * A)) ∧
    ∀ h, IsHecke K h → IsHecke K (fun g => h (g * u⁻¹)) ∧
      r (fun g => h (g * u⁻¹)) = r h * r (fun g => (K : Set G).indicator 1 (u⁻¹ * g)) := by
  have h0 : IsHecke K (0 : G → ℂ) := ⟨HasCompactSupport.zero, fun _ _ _ => ⟨rfl, rfl⟩⟩
  have Sh := hS G V ρ K ho hc
  have hI : IsHecke K ((K : Set G).indicator 1) := (Sh u hu 0 h0).2.2.1
  have hu' : ∀ x, x ∈ K ↔ u⁻¹ * x * u⁻¹⁻¹ ∈ K := fun x => by
    rw [hu (u⁻¹ * x * u⁻¹⁻¹)]
    simp [mul_assoc]

  have a1 : ∀ v : G, (∀ x, x ∈ K ↔ v * x * v⁻¹ ∈ K) → ∀ y : Y,
      (r (fun g => (K : Set G).indicator 1 (v⁻¹ * g)) y : V) = ρ v y := fun v hv y => by
    obtain ⟨-, hl, -, -⟩ := Sh v hv _ hI
    obtain ⟨-, -, e1, e2⟩ := (Sh v hv _ hI).2.2.2 y (hY y.2)
    rw [hact _ hl, e1, e2]
  set Ru := r (fun g => (K : Set G).indicator 1 (u⁻¹ * g)) with hRu
  set Ru' := r (fun g => (K : Set G).indicator 1 (u * g)) with hRu'
  have b1 : ∀ y : Y, (Ru y : V) = ρ u y := a1 u hu
  have b2 : ∀ y : Y, (Ru' y : V) = ρ u⁻¹ y := fun y => by
    have := a1 u⁻¹ hu' y
    simpa only [inv_inv] using this
  have hRR : Ru * Ru' = 1 := by
    refine LinearMap.ext fun y => Subtype.ext ?_
    show (Ru (Ru' y) : V) = y
    rw [b1, b2, ← Module.End.mul_apply, ← map_mul]
    simp
  have hAR : A * Ru = Ru' * A := by
    rw [hRu, hA _ (Sh u hu _ hI).2.1, hRu']
    congr 2
    funext g
    have e : u⁻¹ * θ g = θ (u * g) := by rw [hθm, hθu]
    have m : θ (u * g) ∈ K ↔ u * g ∈ K :=
      ⟨fun h => by simpa only [hθi] using hθK _ h, hθK _⟩
    rw [e]
    by_cases c : u * g ∈ K
    · rw [Set.indicator_of_mem (by exact_mod_cast m.2 c), Set.indicator_of_mem (by exact_mod_cast c)]
      rfl
    · rw [Set.indicator_of_notMem (by exact_mod_cast fun d => c (m.1 d)), Set.indicator_of_notMem (by exact_mod_cast c)]
  have hθu' : θ u⁻¹ = u := by rw [← hθu, hθi]
  refine ⟨?_, fun h hh => ?_, fun h hh => ?_⟩
  · calc (Ru * A) * (Ru * A) = Ru * (A * Ru) * A := by simp only [mul_assoc]
      _ = (Ru * Ru') * (A * A) := by rw [hAR]; simp only [mul_assoc]
      _ = 1 := by rw [hRR, hAA, one_mul]
  · have hf : IsHecke K (fun g => h (θ g)) := hecke_comp hθc hθi hθm hθK hh
    have hf' : IsHecke K (fun g => h (u * θ g * u⁻¹)) := by
      refine hecke_comp (φ := fun g => u * θ g * u⁻¹) (by fun_prop) (fun g => ?_) (fun a b => ?_) (fun k hk => ?_) hh
      · show u * θ (u * θ g * u⁻¹) * u⁻¹ = g
        rw [hθm, hθm, hθu, hθu', hθi]
        group
      · show u * θ (a * b) * u⁻¹ = u * θ a * u⁻¹ * (u * θ b * u⁻¹)
        rw [hθm]
        group
      · exact (hu _).1 (hθK k hk)
    have e : Ru * r (fun g => h (θ g)) = r (fun g => h (u * θ g * u⁻¹)) * Ru := by
      refine LinearMap.ext fun y => Subtype.ext ?_
      show (Ru (r (fun g => h (θ g)) y) : V) = (r (fun g => h (u * θ g * u⁻¹)) (Ru y) : V)
      obtain ⟨p1, p2, -⟩ := Sh u hu _ hf
      obtain ⟨q1, q2, -⟩ := Sh u hu _ hf'
      obtain ⟨-, -, e1, -⟩ := (Sh u hu _ hf).2.2.2 y (hY y.2)
      obtain ⟨-, e2, -, -⟩ := (Sh u hu _ hf').2.2.2 y (hY y.2)
      have ef : (fun g => h (θ (u⁻¹ * g))) = fun g => h (u * θ (g * u⁻¹) * u⁻¹) := by
        funext g
        rw [hθm, hθm, hθu']
        congr 1
        group
      rw [b1, hact _ hf, hact _ hf', b1, ← e1, ← e2, ef]
    calc (Ru * A) * r h = Ru * (A * r h) := by rw [mul_assoc]
      _ = (Ru * r (fun g => h (θ g))) * A := by rw [hA h hh, mul_assoc]
      _ = r (fun g => h (u * θ g * u⁻¹)) * (Ru * A) := by rw [e, mul_assoc]
  · obtain ⟨p1, -⟩ := Sh u hu h hh
    refine ⟨p1, LinearMap.ext fun y => Subtype.ext ?_⟩
    show (r (fun g => h (g * u⁻¹)) y : V) = (r h (Ru y) : V)
    obtain ⟨-, e2, -, -⟩ := (Sh u hu h hh).2.2.2 y (hY y.2)
    rw [hact _ p1, hact _ hh, b1, e2]

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.toYd_pf :
    SlotBasic → LevTop → TranslF → HeckeSum → LvShift → ToYd := by
  intro hSl hLT hTF hHS hLS E _ _ _ n S Z N hS hZ hG π u hu
  obtain ⟨hO, hC, -, hNm⟩ := hLT E n S Z N hS hZ hG
  obtain ⟨t1, t2, κ, hκ, t3⟩ := hTF E n u hu
  have hinv := (hSl E n S hS).1
  have hcont := (hSl E n S hS).2.1
  have hthe : ∀ g, thetaF E n g = (ratF E n u)⁻¹ * thF E n g * ratF E n u := by
    intro g
    rw [t1 g]
    group
  have hnorm : ∀ x, x ∈ Lev S N ↔ ratF E n u * x * (ratF E n u)⁻¹ ∈ Lev S N := by
    intro x
    rw [t3 x]
    refine ⟨hNm κ hκ x, fun hx => ?_⟩
    have := hNm κ⁻¹ ((Kf E n).inv_mem hκ) _ hx
    simpa [mul_assoc] using this
  have hθK : ∀ k ∈ Lev S N, thetaF E n k ∈ Lev S N := by
    intro k hk
    refine (hnorm _).2 ?_
    have e : ratF E n u * thetaF E n k * (ratF E n u)⁻¹ = thF E n k := (t1 k).symm
    rw [e]
    exact (hLT E n S Z N hS hZ hG).2.2.1 k hk
  refine ⟨hθK, ?_⟩
  intro μf hμ Y ρ A hYπ hfd hne hfix hAct hsim hAA hAθ
  have hθm : ∀ a b, thetaF E n (a * b) = thetaF E n a * thetaF E n b := by
    intro a b
    simp only [hthe, map_mul]
    group
  have hθi : ∀ g, thetaF E n (thetaF E n g) = g := by
    intro g
    simp only [hthe, map_mul, map_inv, t2, hinv]
    group
  have hθu : thetaF E n (ratF E n u) = (ratF E n u)⁻¹ := by
    rw [hthe, t2]
    group
  have hθc : Continuous (thetaF E n) := by
    have : thetaF E n = fun g => (ratF E n u)⁻¹ * thF E n g * ratF E n u := funext hthe
    rw [this]
    exact (continuous_const.mul hcont).mul continuous_const
  have hv : (μf (Lev S N : Set (GF E n))).toReal ≠ 0 := by
    haveI := hμ
    exact (ENNReal.toReal_pos (hO.measure_pos μf ⟨1, (Lev S N).one_mem⟩).ne' hC.measure_lt_top.ne).ne'
  obtain ⟨v, hvdef⟩ : ∃ v : ℂ, v = (((μf (Lev S N : Set (GF E n))).toReal : ℝ) : ℂ) := ⟨_, rfl⟩
  have hv0 : v ≠ 0 := by
    rw [hvdef]
    exact_mod_cast hv
  have toF : ∀ {h : GF E n → ℂ}, IsHecke (Lev S N) h → IsHeckeF (Lev S N) h := fun hh =>
    ⟨hh.1, fun k₁ h₁ k₂ h₂ g => by rw [(hh.2 _ h₂ _).2, (hh.2 _ h₁ _).1]⟩
  have toH : ∀ {h : GF E n → ℂ}, IsHeckeF (Lev S N) h → IsHecke (Lev S N) h := fun hh =>
    ⟨hh.1, fun k hk x => ⟨by simpa using hh.2 k hk 1 (Lev S N).one_mem x,
      by simpa using hh.2 1 (Lev S N).one_mem k hk x⟩⟩
  have hY : Y ≤ fixed (finRep E n) (Lev S N) := fun y hy k => by
    simpa using hfix y hy k k.2
  have hact : ∀ h, IsHecke (Lev S N) h → ∀ y : Y,
      (((v⁻¹ • ρ h : Module.End ℂ Y) y : Y) : Sm E n) = Lv (finRep E n) (Lev S N) h y := by
    intro h hh y
    have e : ((ρ h y : Y) : Sm E n) = v • Lv (finRep E n) (Lev S N) h y := by
      refine Subtype.ext ?_
      have e1 := hAct h (toF hh) y
      have e2 := hHS E n (Lev S N) hO hC μf hμ h hh y (hY y.2)
      rw [e1, e2, hvdef]
      rfl
    show ((v⁻¹ • (ρ h y) : Y) : Sm E n) = _
    rw [Submodule.coe_smul, e, inv_smul_smul₀ hv0]
  obtain ⟨c1, c2, c3⟩ := core hLS (finRep E n) (Lev S N) hO hC (ratF E n u) hnorm (thetaF E n) hθc hθi hθm hθK hθu
    Y hY (fun h => v⁻¹ • ρ h) hact A hAA (fun h hh => by
      rw [mul_smul_comm, smul_mul_assoc, hAθ h (toF hh)])
  refine ⟨⟨Y, fun h => v⁻¹ • ρ h, _, hYπ, hfd, hne, hY, hact, ?_, c1, ?_⟩, v, hv0, fun h hh =>
    ⟨toF (c3 h hh).1, ?_⟩⟩
  · intro W hW
    refine hsim W fun h hh y hy => ?_
    exact (W.smul_mem_iff (inv_ne_zero hv0)).1 (hW h (toH hh) y hy)
  · intro h hh
    have e : (fun g => h (thF E n g)) = fun g => h (ratF E n u * thetaF E n g * (ratF E n u)⁻¹) :=
      funext fun g => by rw [t1 g]
    show _ * _ = (v⁻¹ • ρ (fun g => h (thF E n g))) * _
    rw [e]
    exact c2 h hh
  · have e2 : v⁻¹ • ρ (fun g => h (g * (ratF E n u)⁻¹)) = (v⁻¹ • ρ h) *
        (v⁻¹ • ρ (fun g => (Lev S N : Set (GF E n)).indicator 1 ((ratF E n u)⁻¹ * g))) := (c3 h hh).2
    have key : ρ (fun g => h (g * (ratF E n u)⁻¹)) * A = v • ((v⁻¹ • ρ h) *
        ((v⁻¹ • ρ (fun g => (Lev S N : Set (GF E n)).indicator 1 ((ratF E n u)⁻¹ * g))) * A)) := by
      rw [← mul_assoc, ← e2, smul_mul_assoc, smul_inv_smul₀ hv0]
    have tr : LinearMap.trace ℂ Y (ρ (fun g => h (g * (ratF E n u)⁻¹)) * A) = v * LinearMap.trace ℂ Y ((v⁻¹ • ρ h) *
        ((v⁻¹ • ρ (fun g => (Lev S N : Set (GF E n)).indicator 1 ((ratF E n u)⁻¹ * g))) * A)) := by
      rw [key, LinearMap.map_smul, smul_eq_mul]
    exact tr
end

section

open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.yLoc_pf :
    PfHecke → ProdOp → YLoc := by
  intro hP hO E _ _ _ n S Z N hS hZ hG π y i hi f hf x hx
  classical
  obtain ⟨w, b⟩ := i
  let F : ∀ w', Bool → _ := fun w' b' =>
    if h : w' = w ∧ b' = b then h.1 ▸ f else ((N w' : Set _).indicator 1)
  have hFi : F w b = f := by simp [F]
  have hFam : Fam S N {(w, b)} F := by
    refine ⟨?_, ?_⟩
    · intro j hj
      obtain rfl := Finset.mem_singleton.mp hj
      exact ⟨hi, by simpa [hFi] using hf⟩
    · rintro ⟨w', b'⟩ _ hj
      have hne : ¬ (w' = w ∧ b' = b) := by
        rintro ⟨rfl, rfl⟩
        exact hj (Finset.mem_singleton_self _)
      simp [F, hne]
  have h1 := hO E n S Z N hS hZ hG {(w, b)} F hFam x (y.fix hx)
  have h2 := y.act _ (hP E n S Z N hS hZ hG {(w, b)} F hFam) ⟨x, hx⟩
  have h3 : Lw N w b f x = ((y.r (pf S F) ⟨x, hx⟩ : y.Y) : _) := by
    rw [h2]
    show _ = Lv _ _ _ x
    rw [h1]
    simp [hFi]
  show Lw N w b f x ∈ y.Y
  rw [h3]
  exact (y.r (pf S F) ⟨x, hx⟩).2
end

section

open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.twUniq_pf :
    TwUniq := by
  intro E _ _ _ n μ π φ t t' h₁ h₂
  obtain ⟨L₁, e₁, -, rfl⟩ := h₁
  obtain ⟨L₂, e₂, -, rfl⟩ := h₂
  obtain rfl : L₁ = L₂ := by
    refine LinearMap.ext fun ψ => Subtype.ext (Subtype.ext (funext fun x => ?_))
    rw [e₁ ψ x, e₂ ψ x]
  rfl
end

section

open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.levTop_pf :
    SlotBasic → LevTop := by
  intro hS E _ _ _ n S Z N hSec hZ hG
  obtain ⟨hinv, -, hloc, -, -, hinert, hK⟩ := hS E n S hSec
  have mem : ∀ (M : ∀ w : GlobalTheory.BCT.Pl E, Subgroup (GlobalTheory.BCT.GLw n w)) (x : GF E n),
      x ∈ Lev S M ↔ ∀ i : GlobalTheory.BCT.Pl E × Bool, Sl S i → qw n i.1 i.2 x ∈ M i.1 := by
    intro M x
    simp only [Lev, Subgroup.mem_iInf, Subgroup.mem_comap, Subtype.forall]
  have hKq : ∀ k ∈ PositivityTheory.Rg.BcB.G8.Kf E n, ∀ i : GlobalTheory.BCT.Pl E × Bool, Sl S i →
      qw n i.1 i.2 k ∈ GlobalTheory.LFun.KGL i.1 (n := n) := fun k hk => (mem _ k).1 ((hK k).2 hk)
  have hsub : (Lev S N : Set (GF E n)) ⊆ (PositivityTheory.Rg.BcB.G8.Kf E n : Set (GF E n)) := by
    intro x hx
    exact (hK x).1 ((mem _ x).2 fun i hi => (hG i.1).2.1 ((mem N x).1 hx i hi))
  have hset : (Lev S N : Set (GF E n)) = (PositivityTheory.Rg.BcB.G8.Kf E n : Set (GF E n)) ∩
      ⋂ i ∈ {i : GlobalTheory.BCT.Pl E × Bool | i.1 ∈ Z ∧ Sl S i},
        (qw n i.1 i.2) ⁻¹' (N i.1 : Set (GlobalTheory.BCT.GLw n i.1)) := by
    ext x
    constructor
    · intro hx
      refine ⟨hsub hx, ?_⟩
      simp only [Set.mem_iInter]
      exact fun i hi => (mem N x).1 hx i hi.2
    · rintro ⟨hx, hx'⟩
      simp only [Set.mem_iInter] at hx'
      refine (mem N x).2 fun i hi => ?_
      by_cases hz : i.1 ∈ Z
      · exact hx' i ⟨hz, hi⟩
      · rw [(hG i.1).2.2.2 hz]
        exact hKq x hx i hi
  have hfinZ : {i : GlobalTheory.BCT.Pl E × Bool | i.1 ∈ Z ∧ Sl S i}.Finite :=
    ((Z.finite_toSet).prod (Set.finite_univ (α := Bool))).subset fun i hi => ⟨hi.1, trivial⟩
  have hopen : IsOpen (Lev S N : Set (GF E n)) := by
    rw [hset]
    refine GlobalTheory.CompanionTheory.EulerV.isOpen_Kf.inter (hfinZ.isOpen_biInter fun i _ => ?_)
    exact ((hG i.1).1).preimage (hloc i.1 i.2).2.1
  refine ⟨hopen, ?_, ?_, ?_⟩
  · exact GlobalTheory.CompanionTheory.EulerV.isCompact_Kf.of_isClosed_subset
      (Subgroup.isClosed_of_isOpen (Lev S N) hopen) hsub
  · intro k hk
    have hq0 : ∀ w, qw n w false (GlobalTheory.BCT.thF E n k) = qw n w true k := fun w => rfl
    have hq1 : ∀ w, qw n w true (GlobalTheory.BCT.thF E n k) = qw n w false k := by
      intro w
      change qw n w false (GlobalTheory.BCT.thF E n (GlobalTheory.BCT.thF E n k)) = _
      rw [hinv]
    refine (mem N _).2 ?_
    rintro ⟨w, b⟩ ⟨hw, hb⟩
    cases b with
    | true =>
      exact (hq1 w).symm ▸ (mem N k).1 hk (w, false) ⟨hw, by simp⟩
    | false =>
      change qw n w false (GlobalTheory.BCT.thF E n k) ∈ N w
      rw [hq0]
      by_cases hs : GlobalTheory.UnitaryBC.IsSplitAt w
      · exact (mem N k).1 hk (w, true) ⟨hw, fun _ => hs⟩
      · have hz : w ∉ Z := fun h => hs (hZ w h).2
        have h0 : qw n w false k ∈ N w := (mem N k).1 hk (w, false) ⟨hw, by simp⟩
        rw [(hG w).2.2.2 hz] at h0 ⊢
        exact (hinert w hs k).2 h0
  · intro k hk x hx
    refine (mem N _).2 fun i hi => ?_
    rw [map_mul, map_mul, map_inv]
    exact (hG i.1).2.2.1 _ (hKq k hk i hi) _ ((mem N x).1 hx i hi)
end
