module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle017
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThickLetterWordLatticeSurjectionHypotheses
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle089
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle084
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle085
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle114
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle144
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle020
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle173
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle033
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle174
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle028
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle040
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle133
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle171
public import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle178
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
import Formalism.LocalToGlobal.InertKernelTheory.Bundle008
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle001
import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting

@[expose] public section

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

theorem _root_.GlobalTheory.T.hilbert90_normOne_oneOff_at_split_place_forall : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)) (spl : E ⊗[F] w.adicCompletion F ≃+* w.adicCompletion F × w.adicCompletion F), (∀ x, spl (sigR σ (w.adicCompletion F) x) = swapR (w.adicCompletion F) (spl x)) → ∀ (π : (AfE F E)ˣ), π ∈ U1 σ → OneOff w π → ∃ x : (AfE F E)ˣ, h90 σ x = π ∧ OneOff w x := by
  first | exact @GlobalTheory.TwV.Xc.Unif.exists_h90_eq_oneOff_of_normOne_at_split_place | exact GlobalTheory.TwV.Xc.Unif.exists_h90_eq_oneOff_of_normOne_at_split_place | (intros; apply GlobalTheory.TwV.Xc.Unif.exists_h90_eq_oneOff_of_normOne_at_split_place <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.RecS

theorem jointCD_of_large : ∀ eps ez A : ℝ, 0 < eps → 0 < ez → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L)
    (HW : HWOf D.loc), L.sc.eps = eps → L.sc.ez = ez → Pm.CLw ≤ A → x0 ≤ L.sc.x → LocalSituation.adm7 D →
    (∀ i, TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → LJ.ConclusionJa D → RecS.JointCD L HW := by
  intro eps ez A heps hez
  obtain ⟨x1, h1⟩ := GlobalTheory.T.roomy_of_large_scale eps 100 A heps le_rfl
  obtain ⟨x2, h2⟩ := GlobalTheory.T.eleven_le_inertOddPrimeImagQuadratic_large_scale ez hez
  refine ⟨max x1 x2, ?_⟩
  intro D L Pm HW he hZ hA hx hadm hfont hja i hin r ρ π hpt w hw
  have hR : Roomy L 100 := h1 D L Pm he hA (le_trans (le_max_left _ _) hx)
  have h11 : 11 ≤ D.nd.l i := h2 D L _ hZ (le_trans (le_max_right _ _) hx) Fact.out hin
  have hn2 := hin.ne_two
  have hj := hin.2.2.2
  refine ⟨GlobalTheory.T.placeCompletion_le_maxUnramified_away_2qd D.nbr i w hw hin.1 hin.2.1 hin.2.2.1, ?_⟩
  intro Cx hG
  obtain ⟨ε, g, hg, hB⟩ := GlobalTheory.T.wordConditions_common_natural_representation L 100 HW i r ρ π w hw Cx hG hR hadm hfont hja hpt hin.1 hin.2.1 hin.2.2.1
  have hs := (GlobalTheory.T.frobG_isArithFrobAt_and_sign_eq_jacobiSym D (D.nd.l i) hin.1 hin.2.1 hin.2.2.1).2
  have hm : (DV.frobG D (D.nd.l i)).1.2 = -1 := by
    refine (Int.units_eq_one_or _).resolve_left fun h => hj ?_
    rw [← hs, h]; rfl
  have hm' : ((DV.frobG D (D.nd.l i))⁻¹).1.2 = -1 := by
    change ((DV.frobG D (D.nd.l i)).1.2)⁻¹ = -1
    rw [hm]; rfl
  refine ⟨_, hB, GlobalTheory.T.thickLetterWord_hypotheses_of_common_conditions L HW i r ρ π w hw Cx hG _ hn2 hB, h11,
    GlobalTheory.T.twistedDualSizeWord_boxesAndSizes L 100 _ ε g _ hR hg, ?_⟩
  rcases GlobalTheory.T.twistedDualSizeWord_inert_dichotomy L 100 _ ε g _ _ hR hg h11 hm' with h | ⟨d, hd⟩
  · exact Or.inl h
  · exact Or.inr ⟨d, hd, GlobalTheory.T.alternatingWord_hypotheses_every_lattice_surjection L HW i r ρ π w hw Cx hG _ d h11 hB hd⟩

end GlobalTheory.HTW.RecS
end

section

open Matrix

namespace GlobalTheory.Hk3.IntWitt

theorem hensel_step : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ (ι : Type) [Fintype ι] (z z' : ι → Fin n' → L) (k : ℕ), 1 ≤ k →
    (∀ i r, z i r ∈ Formalism.UG.intL L) → (∀ i r, z' i r ∈ Formalism.UG.intL L) → GlobalTheory.Hk3.IntWitt.IndepMod ϖ z →
    (∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ k (z' i r - z i r)) →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z' i) (z' j) - Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z i) (z j))) →
    ∃ g : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (g : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      (∀ r s, GlobalTheory.Hk3.IntWitt.DvdPow ϖ k ((((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L)) r s - (1 : Matrix (Fin n') (Fin n') L) r s)) ∧
      ∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) ((((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i) r - z' i r) := by
  intro L _ _ ϖ σ q hU hq n' JT hJT hherm ι _ z z' k hk hz hz' hind hdiff hgram
  classical
  have hv := hU.2.2.2.1
  have hσϖ : σ ϖ = ϖ := hU.2.2.1
  have hσv := hU.2.1
  have hϖI : ϖ ∈ Formalism.UG.intL L := by
    show Valued.v ϖ ≤ 1
    rw [hv]; exact_mod_cast (show Multiplicative.ofAdd (-1 : ℤ) ≤ 1 from by decide)
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hv; exact WithZero.zero_ne_coe hv
  set J : Matrix (Fin n') (Fin n') L := (JT : Matrix (Fin n') (Fin n') L) with hJdef
  set Ji : Matrix (Fin n') (Fin n') L := ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) with hJidef
  have hJI : ∀ r s, J r s ∈ Formalism.UG.intL L := GlobalTheory.Hk3.HoweDuality.entry_mem_of_mem_GLint hJT
  have hJiI : ∀ r s, Ji r s ∈ Formalism.UG.intL L := GlobalTheory.Hk3.HoweDuality.entry_mem_of_mem_GLint (inv_mem hJT)
  have hJiJ : Ji * J = 1 := by rw [hJidef, hJdef, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  choose w hwI hwe using hdiff
  have hz'e : ∀ i r, z' i r = z i r + ϖ ^ k * w i r := fun i r => by rw [← hwe]; ring
  have hz'v : ∀ i, z' i = z i + ϖ ^ k • w i := fun i => funext fun r => by simp [hz'e]

  have hformI : ∀ x y : Fin n' → L, (∀ r, x r ∈ Formalism.UG.intL L) → (∀ r, y r ∈ Formalism.UG.intL L) →
      Formalism.UG.hform σ J x y ∈ Formalism.UG.intL L := by
    intro x y hx hy
    refine sum_mem fun r _ => sum_mem fun s _ => mul_mem (mul_mem ?_ (hJI r s)) (hy s)
    show Valued.v (σ (x r)) ≤ 1
    rw [hσv]; exact hx r
  have key : ∀ i j, Formalism.UG.hform σ J (z' i) (z' j) - Formalism.UG.hform σ J (z i) (z j) =
      ϖ ^ k * (Formalism.UG.hform σ J (z i) (w j) + Formalism.UG.hform σ J (w i) (z j) + ϖ ^ k * Formalism.UG.hform σ J (w i) (w j)) := by
    intro i j
    simp only [Formalism.UG.hform, hz'e, map_add (f := _), map_mul, map_pow, hσϖ, mul_add, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => by ring
  have hgram1 : ∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (Formalism.UG.hform σ J (z i) (w j) + Formalism.UG.hform σ J (w i) (z j)) := by
    intro i j
    have h1 : GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (Formalism.UG.hform σ J (z i) (w j) + Formalism.UG.hform σ J (w i) (z j) +
        ϖ ^ k * Formalism.UG.hform σ J (w i) (w j)) := by
      obtain ⟨b, hb, hbe⟩ := hgram i j
      refine ⟨b, hb, ?_⟩
      have := (key i j).symm.trans hbe
      rw [pow_succ, mul_assoc] at this
      rw [pow_one]
      exact mul_left_cancel₀ (pow_ne_zero k hϖ0) this
    have h2 : GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (ϖ ^ k * Formalism.UG.hform σ J (w i) (w j)) := by
      refine ⟨ϖ ^ (k - 1) * Formalism.UG.hform σ J (w i) (w j),
        mul_mem (pow_mem hϖI _) (hformI _ _ (hwI i) (hwI j)), ?_⟩
      rw [← mul_assoc, ← pow_add]; congr 2; omega
    have := GlobalTheory.Hk3.IntWitt.dvdPow_sub h1 h2
    simpa using this
  obtain ⟨a, haI, ha⟩ := GlobalTheory.T.exists_integral_dual_of_independentModUniformizer L ϖ hv n' ι z hz hind
  obtain ⟨C, hCs, hCI, hCz⟩ := GlobalTheory.T.exists_integral_skew_hermitian_lift_mod_uniformizer L ϖ σ q hU hq n' JT hJT hherm ι z w a hz hwI haI ha hgram1
  obtain ⟨g, hgI, hg1, hg2⟩ := GlobalTheory.T.cayley_transform_integral_unitary_congruent_one L ϖ σ q hU hq n' JT hJT hherm C hCs hCI k hk
  refine ⟨g, hgI, hg1, fun i r => ?_⟩
  set G : Matrix (Fin n') (Fin n') L := ((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) with hGdef
  have e : G *ᵥ z i - z' i = (G - 1 - ϖ ^ k • (Ji * C)) *ᵥ z i + ϖ ^ k • (Ji *ᵥ (C *ᵥ z i - J *ᵥ w i)) := by
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.mulVec_sub, Matrix.mulVec_mulVec (w i) Ji J, hJiJ, Matrix.one_mulVec, hz'v, smul_sub]
    abel
  have e' := congrFun e r
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e'
  rw [e']
  have t1 : GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) (((G - 1 - ϖ ^ k • (Ji * C)) *ᵥ z i) r) := by
    show GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) (∑ s, (G - 1 - ϖ ^ k • (Ji * C)) r s * z i s)
    refine GlobalTheory.Hk3.IntWitt.dvdPow_sum _ _ fun s _ => ?_
    rw [mul_comm]
    exact GlobalTheory.Hk3.IntWitt.dvdPow_mul_int (hg2 r s) (hz i s)
  have t2 : GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 ((Ji *ᵥ (C *ᵥ z i - J *ᵥ w i)) r) := by
    show GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (∑ s, Ji r s * (C *ᵥ z i - J *ᵥ w i) s)
    exact GlobalTheory.Hk3.IntWitt.dvdPow_sum _ _ fun s _ => GlobalTheory.Hk3.IntWitt.dvdPow_mul_int (hCz i s) (hJiI r s)
  refine GlobalTheory.Hk3.IntWitt.dvdPow_add t1 ?_
  obtain ⟨b, hb, hbe⟩ := t2
  exact ⟨b, hb, by rw [hbe, pow_succ]; ring⟩

end GlobalTheory.Hk3.IntWitt
end

section

open Matrix

theorem GlobalTheory.Hk3.HoweG.selfDual_lattice_of_gram_int : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ x : Matrix (Fin n') (Fin n) L, (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    ∃ a : GL (Fin n) L, GlobalTheory.Hk3.HoweG.SelfDual σ JS a ∧
      (∀ y : Matrix (Fin n') (Fin n) L, GlobalTheory.Hk3.HoweG.HomA σ JS JT x y ↔
        ∀ i j, (y * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) ∧
      (∀ v : Fin n → L, (∀ i, v i ∈ Formalism.UG.intL L) →
        ((∃ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ v = (a : Matrix (Fin n) (Fin n) L) *ᵥ u) ↔
          ∀ i, (x *ᵥ v) i ∈ Formalism.UG.intL L)) ∧
      (∀ w : Fin n → L, (∃ u v : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, v i ∈ Formalism.UG.intL L) ∧
          w = (a : Matrix (Fin n) (Fin n) L) *ᵥ u + v) ↔
        ∃ v : Fin n → L, ∃ w' : Fin n' → L, (∀ i, v i ∈ Formalism.UG.intL L) ∧ (∀ i, w' i ∈ Formalism.UG.intL L) ∧
          w = v + GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w') := by
  intro L _ _ ϖ σ q n n' JS JT hU _hq hJS hJT hS hT x hx
  have hσσ : ∀ z, σ (σ z) = z := hU.1
  have hσv : ∀ z, Valued.v (σ z) = Valued.v z := hU.2.1
  have hσO : ∀ z ∈ Formalism.UG.intL L, σ z ∈ Formalism.UG.intL L := by
    intro z hz
    change Valued.v (σ z) ≤ 1
    rw [hσv]; exact hz
  have iMV : ∀ {k l : ℕ} (M : Matrix (Fin k) (Fin l) L) (t : Fin l → L), (∀ i j, M i j ∈ Formalism.UG.intL L) →
      (∀ j, t j ∈ Formalism.UG.intL L) → ∀ i, (M *ᵥ t) i ∈ Formalism.UG.intL L := by
    intro k l M t hM ht i
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hM i j) (ht j)
  have iMM : ∀ {k l r : ℕ} (M : Matrix (Fin k) (Fin l) L) (M' : Matrix (Fin l) (Fin r) L), (∀ i j, M i j ∈ Formalism.UG.intL L) →
      (∀ i j, M' i j ∈ Formalism.UG.intL L) → ∀ i j, (M * M') i j ∈ Formalism.UG.intL L := by
    intro k l r M M' hM hM' i j
    simp only [Matrix.mul_apply]
    exact Subring.sum_mem _ fun m _ => Subring.mul_mem _ (hM i m) (hM' m j)
  have eJT : ∀ i j, (JT : Matrix (Fin n') (Fin n') L) i j ∈ Formalism.UG.intL L := by
    obtain ⟨g0, hg0⟩ := hJT
    intro i j; rw [← hg0]; exact ((g0 : Matrix (Fin n') (Fin n') (Formalism.UG.intL L)) i j).2
  set y := GlobalTheory.Hk3.HoweG.adj σ JS JT x with hy
  have hxy : ∀ i j, (x * y) i j ∈ Formalism.UG.intL L := by
    have : x * y = (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) *
        (JT : Matrix (Fin n') (Fin n') L) := by
      simp only [hy, GlobalTheory.Hk3.HoweG.adj, Formalism.UG.cT, Matrix.mul_assoc]
    rw [this]; exact iMM _ _ hx eJT
  have T4 := GlobalTheory.T.integral_preimage_add_image_eq_lattice
  have T5 := GlobalTheory.T.hermitianDual_subset_of_integral_gram
  have FreeQuotientRank := GlobalTheory.T.hermitianForm_integral_preimage_lattice
  obtain ⟨a, ha⟩ := T4 L n n' x y
  have hcol : ∀ j, ∃ u : Fin n → L, ∃ w : Fin n' → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) ∧
      (∀ i, w i ∈ Formalism.UG.intL L) ∧ (fun k => (a : Matrix (Fin n) (Fin n) L) k j) = u + y *ᵥ w := by
    intro j
    refine (ha _).mpr ⟨Pi.single j 1, fun i => ?_, ?_⟩
    · by_cases h : i = j
      · subst h; simp [Subring.one_mem]
      · simp [h, Subring.zero_mem]
    · funext k; simp [Matrix.mulVec_single_one]
  have hN : ∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) →
      ∃ t : Fin n → L, (∀ i, t i ∈ Formalism.UG.intL L) ∧ u = (a : Matrix (Fin n) (Fin n) L) *ᵥ t := by
    intro u hu hxu
    exact (ha u).mp ⟨u, 0, hu, hxu, fun _ => Subring.zero_mem _, by simp⟩
  have hY : ∀ w : Fin n' → L, (∀ i, w i ∈ Formalism.UG.intL L) →
      ∃ t : Fin n → L, (∀ i, t i ∈ Formalism.UG.intL L) ∧ y *ᵥ w = (a : Matrix (Fin n) (Fin n) L) *ᵥ t := by
    intro w hw
    exact (ha _).mp ⟨0, w, fun _ => Subring.zero_mem _, by simp [Subring.zero_mem], hw, by simp⟩
  have hformM : ∀ (M : Matrix (Fin n) (Fin n) L) (t : Fin n → L) (V : Matrix (Fin n) (Fin n) L) (j : Fin n),
      Formalism.UG.hform σ (JS : Matrix (Fin n) (Fin n) L) (M *ᵥ t) (fun l => V l j) =
        ∑ k, σ (t k) * (Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L) * V) k j := by
    intro M t V j

    simp only [Formalism.UG.hform, Formalism.UG.cT, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Eq.trans (Finset.sum_congr rfl fun x1 _ => Finset.sum_comm) ?_
    symm; rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hformC : ∀ (M : Matrix (Fin n) (Fin n) L) (i j : Fin n),
      (Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L) * M) i j =
        Formalism.UG.hform σ (JS : Matrix (Fin n) (Fin n) L) (fun k => M k i) (fun k => M k j) := by
    intro M i j
    simp only [Formalism.UG.hform, Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  refine ⟨a, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i j
    obtain ⟨u, w, hu, hxu, hw, he⟩ := hcol i
    obtain ⟨u', w', hu', hxu', hw', he'⟩ := hcol j
    rw [hformC, he, he']
    exact FreeQuotientRank L σ n n' JS JT hσσ hσv hJS hJT hS hT x hx u u' w w' hu hxu hw hu' hxu' hw'
  · intro i j
    set V : Matrix (Fin n) (Fin n) L := ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      Formalism.UG.cT σ ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hV
    have hG : Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) * V = 1 := by
      rw [hV, Matrix.mul_assoc, ← Matrix.mul_assoc (JS : Matrix (Fin n) (Fin n) L), Units.mul_inv, Matrix.one_mul,
        ← Formalism.UG.cT_mul, Units.inv_mul, Formalism.UG.cT_one]
    have hAm : ∀ m : Fin n → L, (∃ t : Fin n → L, (∀ i, t i ∈ Formalism.UG.intL L) ∧ m = (a : Matrix (Fin n) (Fin n) L) *ᵥ t) →
        Formalism.UG.hform σ (JS : Matrix (Fin n) (Fin n) L) m (fun l => V l j) ∈ Formalism.UG.intL L := by
      rintro m ⟨t, ht, rfl⟩
      rw [hformM, hG, Finset.sum_eq_single j]
      · simp only [Matrix.one_apply_eq, mul_one]; exact hσO _ (ht j)
      · intro k _ hk; simp [Matrix.one_apply_ne hk]
      · intro h; exact absurd (Finset.mem_univ j) h
    obtain ⟨u, w, hu, hxu, hw, he⟩ := T5 L σ n n' JS JT hσσ hσv hJS hJT hS hT x hx (fun l => V l j)
      (fun u hu hxu => hAm u (hN u hu hxu)) (fun w hw => hAm _ (hY w hw))
    obtain ⟨t, ht, het⟩ := (ha _).mp ⟨u, w, hu, hxu, hw, he⟩
    have : (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * V) i j = t i := by
      have h2 : ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ (fun l => V l j) = t := by
        rw [het, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      rw [← h2]; simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    rw [Matrix.mul_assoc, ← hV, this]; exact ht i
  · intro y'
    constructor
    · rintro ⟨h1, h2⟩ i j
      obtain ⟨u, w, hu, hxu, hw, he⟩ := hcol j
      have : (y' * (a : Matrix (Fin n) (Fin n) L)) i j = (y' *ᵥ (fun k => (a : Matrix (Fin n) (Fin n) L) k j)) i := by
        simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
      rw [this, he, Matrix.mulVec_add]
      exact Subring.add_mem _ (h1 u hu hxu i) (h2 w hw i)
    · intro h
      refine ⟨fun u hu hxu i => ?_, fun w hw i => ?_⟩
      · obtain ⟨t, ht, rfl⟩ := hN u hu hxu
        rw [Matrix.mulVec_mulVec]; exact iMV _ _ h ht i
      · obtain ⟨t, ht, het⟩ := hY w hw
        rw [het, Matrix.mulVec_mulVec]; exact iMV _ _ h ht i
  · intro v hv
    constructor
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨u, w, hu, hxu, hw, he⟩ := (ha _).mpr ⟨t, ht, rfl⟩
      intro i
      rw [he, Matrix.mulVec_add, Matrix.mulVec_mulVec]
      exact Subring.add_mem _ (hxu i) (iMV _ _ hxy hw i)
    · intro hxv
      exact hN v hv hxv
  · intro z
    constructor
    · rintro ⟨t, v, ht, hv, rfl⟩
      obtain ⟨u, w, hu, hxu, hw, he⟩ := (ha _).mpr ⟨t, ht, rfl⟩
      refine ⟨u + v, w, fun i => Subring.add_mem _ (hu i) (hv i), hw, ?_⟩
      rw [he]; abel
    · rintro ⟨v, w, hv, hw, rfl⟩
      obtain ⟨t, ht, het⟩ := hY w hw
      exact ⟨t, v, ht, hv, by rw [het, add_comm]⟩
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitDualLat

variable {D : D7}

theorem ringHom_sum {A B ι : Type} [Semiring A] [Semiring B] [Fintype ι] (f : A →+* B) (g : ι → A) :
    f (∑ i, g i) = ∑ i, f (g i) := map_sum f g _

theorem cA_cA (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), hx, hy]
  | tmul a x =>
    change a ⊗ₜ[D.host.F] star (star x) = _
    rw [star_star]

theorem cA_incA (x : D.host.E) : cA D (incA D x) = incA D (star x) := rfl

theorem finPart_cA (x : AE D) : finPart D (cA D x) = sigR (Af D.host.F) D.sp.cm.sig (finPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add x y hx hy => simp only [RingHom.map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem finPart_surjective : Function.Surjective (finPart D) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, RingHom.map_add _ _ _⟩
  | tmul a x => exact ⟨pairA D.host.F 0 a ⊗ₜ[D.host.F] x, rfl⟩

theorem sigR_mem_intAE {z : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) :
    sigR (Af D.host.F) D.sp.cm.sig z ∈ intAE D := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, o, rfl⟩ := hw
    exact AddSubgroup.subset_closure ⟨a, ha, ⟨D.sp.cm.sig (o : D.host.E),
      (show IsIntegral ℤ (o : D.host.E) from o.2).map (D.sp.cm.sig : D.host.E →+* D.host.E).toIntAlgHom⟩, rfl⟩
  | zero => rw [RingHom.map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [RingHom.map_add (f := _)]; exact add_mem hx hy
  | neg x _ hx => rw [RingHom.map_neg]; exact neg_mem hx

def form (V : HSp D) (x z : Fin V.rank → AE D) : AE D := ∑ i, ∑ j, cA D (x i) * incA D (V.gram i j) * z j

theorem finPart_form (V : HSp D) (x z : Fin V.rank → AE D) :
    finPart D (form V x z) =
      hR (Af D.host.F) D.sp.cm.sig V.gram (fun i => finPart D (x i)) fun i => finPart D (z i) := by
  simp only [form, ringHom_sum, RingHom.map_mul, finPart_cA]
  rfl

theorem cA_form (V : HSp D) (x z : Fin V.rank → AE D) : cA D (form V x z) = form V z x := by

  simp only [form, map_sum, RingHom.map_mul, cA_cA, cA_incA, GlobalTheory.LatVac.gram_star]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem form_mul (V : HSp D) (a b : AE D) (x z : Fin V.rank → AE D) :
    form V (fun i => a * x i) (fun i => b * z i) = cA D a * b * form V x z := by
  simp only [form, RingHom.map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem mem_iff (V : HSp D) (x : Fin V.rank → AE D) :
    (fun i => finPart D (x i)) ∈ LamHat V ↔
      ∀ z : Fin V.rank → AE D, (fun i => finPart D (z i)) ∈ LamHat V → finPart D (form V x z) ∈ intAE D := by
  rw [(GlobalTheory.LatDual.lamHat_selfDual_and_module V).1]
  constructor
  · intro h z hz
    rw [← cA_form, finPart_cA, finPart_form]
    exact sigR_mem_intAE (h _ hz)
  · intro h z hz
    obtain ⟨w, rfl⟩ : ∃ w : Fin V.rank → AE D, (fun i => finPart D (w i)) = z := by
      choose s hs using finPart_surjective (D := D)
      exact ⟨fun i => s (z i), funext fun i => hs _⟩
    rw [← finPart_form, ← cA_form, finPart_cA]
    exact sigR_mem_intAE (h _ hz)

theorem map_form (V : HSp D) {K : Type} [CommRing K] (π : AE D →+* K) (x z : Fin V.rank → AE D) :
    π (form V x z) =
      ((fun i => π (cA D (x i))) ᵥ* (V.gram.map fun a => π (incA D a))) ⬝ᵥ fun k => π (z k) := by

  simp only [form, map_sum, RingHom.map_mul, dotProduct, vecMul, Finset.sum_mul, Matrix.map_apply]
  exact Finset.sum_comm

theorem conj_mem_lamHat_iff : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ (V : HSp D) (β : GL (Fin V.rank) (Fv D.host.F v)), Frame V e π β → ∀ y : Fin V.rank → AE D, (fun i => finPart D (cA D e * y i)) ∈ LamHat V ↔ ∀ j, IsInt (Ov D v) (((fun i => π (cA D (y i))) ᵥ* ((V.gram.map fun a => π (incA D a)) * β.1)) j) := by
  intro D e v π he hπ V β hβ y
  rw [mem_iff]
  constructor
  · intro h j
    choose s hs using hπ.1
    have h1 : (fun k => π (s (β.1 k j))) = β.1 *ᵥ Pi.single j 1 := by
      funext k
      rw [hs, Matrix.mulVec_single_one]
      rfl
    have h2 := h _ ((hβ fun k => s (β.1 k j)).2 fun i => by
      rw [h1, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      by_cases hi : i = j
      · subst hi; rw [Pi.single_eq_same]; exact ⟨1, map_one _⟩
      · rw [Pi.single_eq_of_ne hi]; exact ⟨0, map_zero _⟩)
    rw [form_mul, cA_cA, he.1, hπ.2.2.2, map_form, h1, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      dotProduct_single, mul_one] at h2
    exact h2
  · intro h z hz
    have h1 := (GlobalTheory.LatDual.lamHat_selfDual_and_module V).2 _
      (GlobalTheory.AdIdem.idempotent_mem_intAE D (finPart D e) (by rw [← RingHom.map_mul, he.1])) _ hz
    simp only [← RingHom.map_mul] at h1
    have h2 := (hβ z).1 h1
    have h3 := form_mul V (cA D e) 1 y z
    simp only [one_mul, mul_one, cA_cA] at h3
    have h4 : (fun k => π (z k)) = β.1 *ᵥ ((β⁻¹).1 *ᵥ fun k => π (z k)) := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    rw [h3, hπ.2.2.2, map_form, h4, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, isInt_iff]
    exact sum_mem fun i _ => mul_mem (isInt_iff.1 (h i)) (isInt_iff.1 (h2 i))

end GlobalTheory.SplitDualLat

end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct
open Formalism.L2.Th1.H Formalism.L2.KerInert.RepComb

theorem _root_.GlobalTheory.T.common_representatives_period_lattice_halves : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι κ : Type) [Fintype ι] [Nonempty ι] [Fintype κ] (a b : ℕ) (emb : ι → E →+* ℂ) (δ : ℂ) (AA0 : Submodule (𝓞 E) E) (SS : Finset (HeightOneSpectrum (𝓞 E))) (cl : ℕ) (N₀ : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N₀' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (N : κ → Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N' : κ → Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (g : 𝓞 E), δ ≠ 0 → (∃ k : 𝓞 E, g = 1 + (cl : 𝓞 E) * k) → (∀ i, (∀ x ∈ perO AA0 (N i) (N' i), g • x ∈ perO AA0 N₀ N₀') ∧ ∀ x ∈ perO AA0 N₀ N₀', g • x ∈ perO AA0 (N i) (N' i)) → relIdx (LamC emb δ AA0 N₀ N₀') (AC emb δ AA0 SS N₀ N₀' cl) ≠ 0 → relIdx (BC emb δ AA0 SS N₀ N₀' cl) (LamC emb δ AA0 N₀ N₀' ⊓ AC emb δ AA0 SS N₀ N₀' cl) ≠ 0 → relIdx (LamC emb δ AA0 N₀ N₀') (BC emb δ AA0 SS N₀ N₀' cl) ≠ 0 → ∃ SX SA SB : Finset (VV ι a b), ∀ i, IsReps (LamC emb δ AA0 (N i) (N' i)) (AC emb δ AA0 SS (N i) (N' i) cl) SX ∧ IsReps (BC emb δ AA0 SS (N i) (N' i) cl) (LamC emb δ AA0 (N i) (N' i) ⊓ AC emb δ AA0 SS (N i) (N' i) cl) SA ∧ IsReps (LamC emb δ AA0 (N i) (N' i)) (BC emb δ AA0 SS (N i) (N' i) cl) SB := by
  first | exact @GlobalTheory.CommonReps.common_reps_halves | exact GlobalTheory.CommonReps.common_reps_halves | (intros; apply GlobalTheory.CommonReps.common_reps_halves <;> assumption)
end
