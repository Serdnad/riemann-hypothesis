module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwOrbUEqZeroOfCusp
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1404
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1615
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1494
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1616
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1618
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1324
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1627
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1413
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1414
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1626
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1553
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr.MpDiv

theorem mem_Bl_of_mul_pow : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ s : X.functionField, s ∈ P.H 0 1 → s ≠ 0 → ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ (N m : ℕ) (f : X.functionField), f ∈ P.H N 0 → f * s ^ m ∈ P.Bl N m 2 → f ∈ P.Bl N 0 (2 * Real.exp (δ * N + C * m)) := by
  intro k _ X _ p D hX P s hs hs0 δ hδ
  obtain ⟨ρ, hρ, H⟩ := GlobalTheory.T.arith_global_maximum_principle_off_divisor k X p D hX P s hs hs0 δ hδ
  refine ⟨max 0 (-Real.log ρ), le_max_left _ _, fun N m f hf hfs => ?_⟩
  set C : ℝ := max 0 (-Real.log ρ) with hC
  have key := H N f (2 * Real.exp (C * m)) hf (fun σ y hy => ?_)
  · have e : Real.exp (δ * N) * (2 * Real.exp (C * m)) = 2 * Real.exp (δ * N + C * m) := by
      rw [Real.exp_add]; ring
    rwa [e] at key
  · obtain ⟨hp1, hp2⟩ := GlobalTheory.T.hermPair_pow_section_mem_and_norm_pow k X p P 0 1 s hs m
    have hm := (GlobalTheory.T.hermLineBundlePair_sections_mul_mem_norm_mul k X p P N 0 _ _ f (s ^ m) hf hp1).2 σ y
    rw [hp2 σ y] at hm
    simp only [mul_zero, add_zero, mul_one, zero_add] at hm
    have h2 := hfs.2 σ y
    rw [hm] at h2
    have hn : 0 ≤ P.nu N 0 σ y f := by unfold Pair.nu; positivity
    have h1 : 1 ≤ Real.exp C * P.nu 0 1 σ y s := by
      have : Real.exp (-Real.log ρ) ≤ Real.exp C := Real.exp_le_exp.2 (le_max_right _ _)
      rw [Real.exp_neg, Real.exp_log hρ] at this
      calc (1 : ℝ) = ρ⁻¹ * ρ := (inv_mul_cancel₀ hρ.ne').symm
        _ ≤ Real.exp C * P.nu 0 1 σ y s :=
          mul_le_mul this hy hρ.le (Real.exp_pos _).le
    have h3 : 1 ≤ Real.exp (C * m) * P.nu 0 1 σ y s ^ m := by
      rw [mul_comm C, Real.exp_nat_mul, ← mul_pow]
      exact one_le_pow₀ h1
    calc P.nu N 0 σ y f ≤ P.nu N 0 σ y f * (Real.exp (C * m) * P.nu 0 1 σ y s ^ m) :=
          le_mul_of_one_le_right hn h3
      _ = Real.exp (C * m) * (P.nu N 0 σ y f * P.nu 0 1 σ y s ^ m) := by ring
      _ ≤ Real.exp (C * m) * 2 := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = 2 * Real.exp (C * m) := mul_comm _ _

end GlobalTheory.VolBr.MpDiv
end

section

noncomputable section

open MeasureTheory Matrix
open scoped Classical

namespace GlobalTheory.OrbDesc

theorem orbK_eq_twOrbU {G : Type} [Group G] (K0 : Subgroup G) (γ : G) (f : G → ℂ)
    (hbi : ∀ k ∈ K0, ∀ k' ∈ K0, ∀ g, f (k * g * k') = f g) :
    GlobalTheory.LKCount.orbK (MonoidHom.id G) K0 γ f =
      GlobalTheory.LKLoc.twOrbU (MonoidHom.id G) K0 γ (GlobalTheory.BCT.twCent (MonoidHom.id G) γ ⊓ K0) f := by
  unfold GlobalTheory.LKCount.orbK GlobalTheory.LKCount.orbC GlobalTheory.LKLoc.twOrbU GlobalTheory.LKLoc.orbSum
  refine finsum_congr fun q => ?_
  have hc : (fun k : K0 => f ((Quotient.out q * k)⁻¹ * γ * (MonoidHom.id G) (Quotient.out q * k))) =
      fun _ => f ((Quotient.out q)⁻¹ * γ * Quotient.out q) := by
    funext k
    have := hbi (k : G)⁻¹ (K0.inv_mem k.2) k k.2 ((Quotient.out q)⁻¹ * γ * Quotient.out q)
    rw [← this]
    simp only [MonoidHom.id_apply, _root_.mul_inv_rev, mul_assoc]
  rw [hc, avg_const']
  simp only [MonoidHom.id_apply, GlobalTheory.LKCount.vol, GlobalTheory.LKLoc.volRat, GlobalTheory.LKLoc.locPart]
  congr 1
  push_cast
  rw [inv_div]

end GlobalTheory.OrbDesc

namespace GlobalTheory.LKCount

theorem orbK_eq_zero_of_cusp : ∀ (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (f : GL ι K → ℂ), IsLocallyConstant f → HasCompactSupport f →
  (∀ (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ (μ : Measure (Fin a → Fin b → K)), μ.IsAddHaarMeasure →
    ∀ u : (Fin a → Fin b → K) → GL ι K,
      (∀ X, (u X : Matrix ι ι K) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) →
      ∀ g h : GL ι K, ∫ X, f (g * (h⁻¹ * u X * h)) ∂μ = 0) →
  ∀ γ : GL ι K, (γ : Matrix ι ι K).charpoly.Separable → ¬ Irreducible (γ : Matrix ι ι K).charpoly →
  ∀ (K0 : Subgroup (GL ι K)), IsOpen (K0 : Set (GL ι K)) → IsCompact (K0 : Set (GL ι K)) →
    (∀ k ∈ K0, ∀ k' ∈ K0, ∀ g, f (k * g * k') = f g) →
    GlobalTheory.LKCount.orbK (MonoidHom.id (GL ι K)) K0 γ f = 0 := by
  intro K _ _ _ _ _ _ ι _ _ _ f hlc hcs hyp γ hsep hirr K0 hK0o hK0c hbi
  rw [GlobalTheory.OrbDesc.orbK_eq_twOrbU K0 γ f hbi]
  exact GlobalTheory.OrbDesc.twOrbU_eq_zero_of_cusp K ι f hlc hcs hyp γ hsep hirr K0 K0 hK0o hK0c hK0o hK0c hbi

end GlobalTheory.LKCount
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem ampleHS_pair : AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p) (a b a' b' : ℤ) (M : HermLB p) (α : ℝ), P.Rep a b M → IsAmpleLB M.B →
    M.SemiPos D → M.IsSelfInter α → ∃ t₀ : ℝ, ∀ t, t₀ ≤ t →
      Tendsto (fun m : ℕ => P.lc (m * a + a') (m * b + b') (Real.exp (t * m)) / (m : ℝ) ^ (D + 1)) atTop
        (𝓝 (α / (D + 1).factorial + (((D : ℝ) + 1) * gdeg M D / (D + 1).factorial) * t)) := by
  intro hHS k _ X _ p D hX P a b a' b' M α hM hamp hsemi hself
  obtain ⟨N, hN⟩ := GlobalTheory.T.exists_hermitianRepresentative_integerCombination k X p P a' b'
  obtain ⟨Q, hQL, hQA, hQB⟩ := GlobalTheory.T.exists_hermPairSections_change_of_isometric_combinations k X p P a b a' b' M N hM hN
  have hamp' : IsAmpleLB Q.L.B := by rw [hQL]; exact hamp
  have hsemi' : Q.L.SemiPos D := by rw [hQL]; exact hsemi
  have hself' : Q.L.IsSelfInter α := by rw [hQL]; exact hself
  obtain ⟨t₀, ht⟩ := hHS k X p D hX Q α hamp' hsemi' hself'
  refine ⟨t₀, fun t htt => ?_⟩
  have hlc : ∀ m : ℕ, Q.lc m 1 (Real.exp (t * m)) = P.lc (m * a + a') (m * b + b') (Real.exp (t * m)) := by
    intro m
    simp only [Pair.lc]
    rw [hQB, one_mul, one_mul]
  have e : (α + ((D : ℝ) + 1) * t * gdeg Q.L D) / ((D + 1).factorial : ℝ) =
      α / (D + 1).factorial + (((D : ℝ) + 1) * gdeg M D / (D + 1).factorial) * t := by
    rw [hQL]; ring
  have h := ht t htt
  rw [e] at h
  simpa only [hlc] using h

end GlobalTheory.HSNef
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HSNef.GenLow

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem exists_pos_bounds {Y : Type} [TopologicalSpace Y] [CompactSpace Y] (G : Y → ℝ) (hG : Continuous G)
    (hpos : ∀ y, 0 < G y) : ∃ m U : ℝ, 0 < m ∧ 0 < U ∧ ∀ y, m ≤ G y ∧ G y ≤ U := by
  rcases isEmpty_or_nonempty Y with h | h
  · exact ⟨1, 1, one_pos, one_pos, fun y => (h.false y).elim⟩
  · obtain ⟨a, -, ha⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hG.continuousOn
    obtain ⟨b, -, hb⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hG.continuousOn
    exact ⟨G a, G b, hpos a, hpos b, fun y => ⟨ha (Set.mem_univ y), hb (Set.mem_univ y)⟩⟩

theorem nu_nonneg (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    0 ≤ P.nu a b σ y f :=
  mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

theorem continuous_nu (P : Pair p) (a b : ℤ) (M : HermLB p) (hM : P.Rep a b M) (σ : k →+* ℂ)
    (f : X.functionField) (hf : f ∈ P.H a b) : Continuous fun y : CxPts p σ => P.nu a b σ y f := by
  obtain ⟨e, -, hr, hn, -⟩ := GlobalTheory.VolBr.RepDict.rep_dict k X p P a b M hM
  obtain ⟨u, rfl⟩ : f ∈ Set.range e := hr ▸ hf
  have h : (fun y : CxPts p σ => P.nu a b σ y (e u)) = fun y => Real.sqrt ((M.φ σ).nsq (secVal p σ u) y) := by
    funext y
    rw [← hn u σ y, Real.sqrt_sq (nu_nonneg P a b σ y _)]
  rw [h]
  exact ((M.cInf σ).continuous_nsq u).sqrt

theorem gen_low : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (P : Pair p) (c : ℕ), GenAt P c → ∃ (n : ℕ) (v : Fin n → X.functionField) (ρ : ℝ), 0 < ρ ∧
      (∀ i, v i ∈ P.Bl 0 c ρ⁻¹) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ i, ρ ≤ P.nu 0 c σ y (v i) := by
  intro k _ X _ p D hX P c ⟨n, v, hvH, hnz⟩
  classical
  haveI : Finite (k →+* ℂ) := hX.finite_emb
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_hermitianRepresentative_integerCombination k X p P 0 c
  have hb : ∀ σ : k →+* ℂ, ∃ m U : ℝ, 0 < m ∧ 0 < U ∧ ∀ y : CxPts p σ,
      m ≤ ∑ i, P.nu 0 c σ y (v i) ∧ ∑ i, P.nu 0 c σ y (v i) ≤ U := by
    intro σ
    haveI : CompactSpace (CxPts p σ) := hX.compactSpace σ
    refine exists_pos_bounds _ (continuous_finsetSum _ fun i _ => continuous_nu P 0 c M hM σ (v i) (hvH i))
      fun y => ?_
    obtain ⟨i, hi⟩ := hnz σ y
    exact lt_of_lt_of_le ((nu_nonneg P 0 c σ y _).lt_of_ne' hi)
      (Finset.single_le_sum (fun j _ => nu_nonneg P 0 c σ y (v j)) (Finset.mem_univ i))
  choose m U hm hU hmU using hb
  have hlow : ∃ m₀ : ℝ, 0 < m₀ ∧ ∀ σ, m₀ ≤ m σ := by
    rcases isEmpty_or_nonempty (k →+* ℂ) with h | h
    · exact ⟨1, one_pos, fun σ => (h.false σ).elim⟩
    · obtain ⟨σ, hσ⟩ := Finite.exists_min m
      exact ⟨m σ, hm σ, hσ⟩
  have hup : ∃ U₀ : ℝ, 0 < U₀ ∧ ∀ σ, U σ ≤ U₀ := by
    rcases isEmpty_or_nonempty (k →+* ℂ) with h | h
    · exact ⟨1, one_pos, fun σ => (h.false σ).elim⟩
    · obtain ⟨σ, hσ⟩ := Finite.exists_max U
      exact ⟨U σ, hU σ, hσ⟩
  obtain ⟨m₀, hm₀, hm₀le⟩ := hlow
  obtain ⟨U₀, hU₀, hU₀le⟩ := hup
  have hn1 : (0 : ℝ) < ((max n 1 : ℕ) : ℝ) := by exact_mod_cast lt_max_of_lt_right one_pos
  refine ⟨n, v, min (m₀ / (max n 1 : ℕ)) U₀⁻¹, lt_min (div_pos hm₀ hn1) (inv_pos.2 hU₀), fun i => ⟨hvH i, fun σ y => ?_⟩,
    fun σ y => ?_⟩
  · calc P.nu 0 c σ y (v i) ≤ ∑ j, P.nu 0 c σ y (v j) :=
          Finset.single_le_sum (fun j _ => nu_nonneg P 0 c σ y (v j)) (Finset.mem_univ i)
      _ ≤ U σ := (hmU σ y).2
      _ ≤ U₀ := hU₀le σ
      _ = U₀⁻¹⁻¹ := (inv_inv U₀).symm
      _ ≤ (min (m₀ / (max n 1 : ℕ)) U₀⁻¹)⁻¹ :=
          inv_anti₀ (lt_min (div_pos hm₀ hn1) (inv_pos.2 hU₀)) (min_le_right _ _)
  · obtain ⟨i₀, -⟩ := hnz σ y
    have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 fun h => by subst h; exact i₀.elim0
    have hmax : (max n 1 : ℕ) = n := max_eq_left hn
    have hsum : ∑ _j : Fin n, m₀ / (max n 1 : ℕ) ≤ ∑ j, P.nu 0 c σ y (v j) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hmax, mul_div_cancel₀ _
        (by exact_mod_cast (show n ≠ 0 by omega))]
      exact (hm₀le σ).trans (hmU σ y).1
    obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le ⟨i₀, Finset.mem_univ _⟩ hsum
    exact ⟨i, (min_le_left _ _).trans hi⟩

end GlobalTheory.HSNef.GenLow
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

theorem _root_.GlobalTheory.T.exists_doubleSpace_of_genericFunctionFieldPair : ∀ (F : Type) [Field F] (Y : Var F) (K : Type) [Field K] (ψ₁ ψ₂ : Y.Fn →+* K), GenPair Y ψ₁ ψ₂ → ∃ (W : Dbl Y) (j : W.Z.functionField →+* K), j.comp W.α₁ = ψ₁ ∧ j.comp W.α₂ = ψ₂ := by
  first | exact @GlobalTheory.FlagPush.exists_dbl_of_genPair | exact GlobalTheory.FlagPush.exists_dbl_of_genPair | (intros; apply GlobalTheory.FlagPush.exists_dbl_of_genPair <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.nonKlt_locus_dim_lt_after_perturbation : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ D B : X → ℚ) (δ c : ℚ) (x z : X) (j : ℕ), KltAt p n Δ x → IsQCart D → IsQCart B → LcAt p n (Δ + D) x → 0 < δ → δ ≤ 1 → c ≤ 1 → Off B z → (∀ y, ¬ z ⤳ y → ∀ a : ℚ, 0 ≤ a → KltAt p n (Δ + a • D) y → KltAt p n (Δ + a • D + B) y) → topologicalKrullDim (closure ({z} : Set X)) = (j + 1 : ℕ) → LcAt p n (Δ + (1 - δ) • D + c • B) x → ¬ KltAt p n (Δ + (1 - δ) • D + c • B) x → LcCut p n (Δ + (1 - δ) • D + c • B) x j := by
  first | exact @GlobalTheory.PairStep.logCanonicalCut_of_step | exact GlobalTheory.PairStep.logCanonicalCut_of_step | (intros; apply GlobalTheory.PairStep.logCanonicalCut_of_step <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

theorem _root_.GlobalTheory.T.exists_generic_pair_flags_differing_one_step : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ B ∈ E'.S (genericPoint Y.X), ∀ (τ : ι) (a b : Fin (m τ)), a < b → ∃ ψ₂ : Y.Fn →+* RatFunc Y.Fn, GenPair Y (algebraMap Y.Fn (RatFunc Y.Fn)) ψ₂ ∧ (∀ u : X.Fn, algebraMap Y.Fn (RatFunc Y.Fn) (φ u) = ψ₂ (φ u)) ∧ Par m ⊤ (shear τ a b (RatFunc.X : RatFunc Y.Fn) * (B.map (algebraMap Y.Fn (RatFunc Y.Fn)) * (B.map ψ₂)⁻¹)) := by
  first | exact @GlobalTheory.FlagPush.Gen.exists_genPair | exact GlobalTheory.FlagPush.Gen.exists_genPair | (intros; apply GlobalTheory.FlagPush.Gen.exists_genPair <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef


open MvPolynomial in
theorem mixed_diff_nonneg : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (A B : HermLB p) (Φ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ), IsArFun ![A, B] D Φ → Le B A → ∀ x y : ℕ, HtNef ((A.pow x).tens (B.pow y)) D → 0 ≤ Φ ((MvPolynomial.X 0 - MvPolynomial.X 1) * (MvPolynomial.C (x : ℝ) * MvPolynomial.X 0 + MvPolynomial.C (y : ℝ) * MvPolynomial.X 1) ^ D) := by
  intro hC k _ X _ p D hX A B Φ hΦ hle x y hN
  classical
  haveI := hX.isLocallyNoetherian
  obtain ⟨s, hs, hs0⟩ := (GlobalTheory.T.hermLBLeBySmallSection_iff_exists_smallSection_difference k X p A B).1 hle
  have hg :=  (sec_ne_zero_iff s).1 hs0
  let L : Fin 2 → HermLB p := ![A, B]
  let F : Option (Fin 2) → HermLB p := fun o => o.elim (A.tens B.dual) L
  let E : Option (Fin 2) → Fin 2 → ℤ := fun o => o.elim ![1, -1] (fun i => Pi.single i 1)
  have hiso : ∀ j, (comb L (E j)).Isometric (F j) := by
    rintro (_ | i)
    · apply HermLB.icls_eq_iff.1
      simp [icls_comb, Fin.sum_univ_two, L, E, F, HermLB.icls_tens, HermLB.icls_dual, sub_eq_add_neg]
    · exact isometric_comb_single L i
  have hΦ' := ((hC.arIso k X p D hX).2 (Fin 2) L Φ hΦ).2.2 (Option (Fin 2)) F E hiso
  let n : Fin 2 → ℤ := ![(x : ℤ), (y : ℤ)]
  obtain ⟨h, hh⟩ := (hC.arExists k X p D hX).1 (comb L n)
  have hNiso : (comb L n).Isometric ((A.pow x).tens (B.pow y)) := by
    apply HermLB.icls_eq_iff.1
    simp [icls_comb, Fin.sum_univ_two, L, n, HermLB.icls_tens, HermLB.icls_pow]
  have hr := isRatSec_ratOfSec s hg
  obtain ⟨-, hmix⟩ := hC.arMix k X p D hX (Fin 2) (A.tens B.dual) L _ hΦ' n h hh (ratOfSec s hg) hr
  have hpoly : aeval (fun j => lin fun i => ((E j i : ℤ) : ℝ))
      (MvPolynomial.X none * rename some (lin fun i => ((n i : ℤ) : ℝ)) ^ D) =
      (MvPolynomial.X 0 - MvPolynomial.X 1) * (C (x : ℝ) * MvPolynomial.X 0 + C (y : ℝ) * MvPolynomial.X 1) ^ D := by
    simp [aeval_rename, lin, Fin.sum_univ_two, E, n, Function.comp_def, Pi.single_apply]
    left
    ring
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, hpoly] at hmix
  rw [hmix]
  have h1 : 0 ≤ ∑ᶠ z, (((A.tens B.dual).div hr).mult z : ℝ) * h z :=
    finsum_nonneg fun z => mul_nonneg (Int.cast_nonneg (mult_divOfSec_nonneg (hL := (A.tens B.dual).isLB) z))
      (hN.2 h (hNiso.isArithHeight hX hh) z)
  have h2 : ∀ σ, ((comb L n).φ σ).chernInt D (offSupp p σ ((A.tens B.dual).div hr))
      (logNorm ((A.tens B.dual).φ σ) (ratOfSec s hg)) ≤ 0 := by
    intro σ
    have hneg : ((comb L n).φ σ).chernPart D (-1) = 0 := by
      rw [hNiso.chernPart_eq]
      exact Weight.chernPart_neg_eq_zero (((A.pow x).tens (B.pow y)).cInf σ) (hN.1 σ)
    rw [Weight.chernInt, hneg, MeasureTheory.Measure.restrict_zero, MeasureTheory.integral_zero_measure, sub_zero]
    refine MeasureTheory.setIntegral_nonpos (isOpen_offSupp _).measurableSet fun z hz => ?_
    have hz' : z ∈ ptsIn p σ (Out.nonzeroLocus s) := by
      rw [← offSupp_divOfSec (hL := (A.tens B.dual).isLB)]
      exact hz
    rw [logNorm_ratOfSec _ hz']
    have h0 : 0 ≤ ((A.tens B.dual).φ σ).nsq (secVal p σ s) z := by
      unfold Weight.nsq
      positivity
    have := Real.log_nonpos h0 (hs σ z)
    linarith
  have h3 : (comb L n).archInt (A.tens B.dual) D hr ≤ 0 := by
    have := finsum_nonneg fun σ => neg_nonneg.2 (h2 σ)
    rw [finsum_neg_distrib] at this
    unfold HermLB.archInt
    linarith
  linarith

end GlobalTheory.HSNef
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

theorem adjKlt_of_klt_restrict : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (n : ℕ) (T : Subring L) (S : Place cL) (hS : S.Contains T) (ψ : S.ring →+* K) (f : S.ring) (w : Fin n → S.ring) (θ : S.ring →₀ ℚ) (R : Subring K), Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) → Irreducible f → TrBasis cK (fun i => ψ (w i)) → (∀ g ∈ θ.support, ψ g ≠ 0) → (∀ a ∈ R, ∃ t : T, ψ ⟨t, hS t t.2⟩ = a) → Klt cK n R (dForm cK (fun i => ψ (w i))) (Finsupp.mapDomain ψ θ) → AdjKlt cL (n + 1) T S (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L)) (Finsupp.mapDomain (fun g : S.ring => (g : L)) θ + Finsupp.single (f : L) 1) := by
  intro L K _ _ cL cK n T S hS ψ f w θ R hψ hc hf hw hθ hR hK
  refine ⟨?_, ?_, ?_⟩
  · have htr := (trBasis_uniformiser_cons cL cK n S ψ f w hψ hc hf hw).1
    have hfree := (formOrd_api cL (n + 1) _ htr).1
    exact fun h0 => one_ne_zero (hfree.1 (a₁ := 1) (a₂ := 0) (by simp [h0]))
  · have hf0 : (0 : L) ≠ (f : L) := fun h => hf.ne_zero (Subtype.ext h.symm)
    have hθ0 : θ 0 = 0 := by
      by_contra h
      exact hθ 0 (Finsupp.mem_support_iff.2 h) (map_zero ψ)
    have h1 : Finsupp.mapDomain (fun g : S.ring => (g : L)) θ ((0 : S.ring) : L) = θ 0 :=
      Finsupp.mapDomain_apply_of_injective Subtype.val_injective θ 0
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hf0, add_zero]
    exact h1.trans hθ0
  intro Q hQ t u E hTQ hspan hdim hSQ hEQ hSt hEu hP
  obtain ⟨F, hF, hdisc⟩ := GlobalTheory.AdjCodimTwo.disc_residue_eq cL cK n Q hQ t u S E ψ f w θ hspan hdim
    hSQ hEQ hSt hEu hψ hc hf hw hθ hP
  rw [← hdisc]
  apply hK.lt_disc
  intro a ha
  obtain ⟨x, hx⟩ := hR a ha
  exact (hF a).2 ⟨⟨x, hS x x.2⟩, hTQ x.2, hx⟩

end GlobalTheory.FieldPair
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem exists_pow_section_nonvanishing_on_closed : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ T : Set X, IsClosed T → (∀ ℓ : ℕ, (T ∩ fib X ℓ).Finite) → ∃ e : ℕ, 0 < e ∧ ∃ f ∈ P.H e 0, T ⊆ NV P e 0 f := by
  intro k _ X _ p D hX P hA T hT hfin
  let Z : Closeds X := ⟨T, hT⟩
  obtain ⟨hAff, hFin⟩ := GlobalTheory.T.closedSubset_finiteFibres_isAffine_finite_int k X p D hX Z hfin
  haveI := hAff
  haveI := ReducedSubgroup.isReduced_subscheme_vanishingIdeal Z
  let i := (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι
  obtain ⟨n, s, hn, hs⟩ := GlobalTheory.T.exists_nowhereZero_section_lineBundle_pow_finite_int _ hFin (P.L.B.pull i) (LB.isLB_pull hA.isLB i)
  obtain ⟨N, u, hN, hu⟩ := GlobalTheory.T.exists_ample_power_lift_of_nonvanishing_on_closed k X p D hX P.L.B hA _ i n s hn hs
  obtain ⟨f, hf, hfu⟩ := (GlobalTheory.T.lineBundlePow_sections_rationalFunctions_loci k X p P N).1 u
  refine ⟨N, hN, f, hf, ?_⟩
  rw [hfu]
  intro x hx
  apply hu
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  exact hx

end GlobalTheory.HSAmp
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.fubiniStudy_log_sum_weight_uniformly_bounded : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, 1 ≤ n → ∀ (σ : k →+* ℂ) (y : CxPts p σ), |((e : ℝ) * n)⁻¹ * Real.log (∑ l, P.nu e 0 σ y (x l) ^ (2 * n))| ≤ B := by
  first | exact @GlobalTheory.HSAmp.can_bound | exact GlobalTheory.HSAmp.can_bound | (intros; apply GlobalTheory.HSAmp.can_bound <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isFreeGen_topForm_etaleTower_transcendenceBasis : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (n r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (x : Fin n → R),
  IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) →
  IsFreeGen L (dForm cL (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)))) := by
  first | exact @GlobalTheory.FieldPair.isFreeGen_dForm_tower | exact GlobalTheory.FieldPair.isFreeGen_dForm_tower | (intros; apply GlobalTheory.FieldPair.isFreeGen_dForm_tower <;> assumption)
end
