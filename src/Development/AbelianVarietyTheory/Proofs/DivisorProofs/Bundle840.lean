module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle440
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle525
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle811
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle763
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle780
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle807
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle809
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle810
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle817
public import Formalism.LocalToGlobal.Divisibility.Bundle002
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle387

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

noncomputable section
namespace GlobalTheory.SUVolBound
theorem countable_numberField (E : Type) [Field E] [NumberField E] : Countable E :=
  (Module.finBasis ℚ E).equivFun.injective.countable

theorem countable_inReal {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (Ψ : Finset (E →+* ℂ))
    (G : Matrix (Fin r) (Fin r) E) (Γ : Subgroup (GL (Fin r) E)) : Countable (inReal Ψ G Γ) := by
  haveI := countable_numberField E
  haveI : Countable (Matrix (Fin r) (Fin r) E) := inferInstanceAs (Countable (Fin r → Fin r → E))
  haveI : Countable (GL (Fin r) E) := Function.Injective.countable (f := fun u : GL (Fin r) E => (u : Matrix (Fin r) (Fin r) E)) (fun a b h => Units.ext h)
  have hsub : ∀ y : inReal Ψ G Γ, ∃ γ : GL (Fin r) E, embGL Ψ r γ = (y : realSU Ψ G).1 := by
    rintro ⟨y, hy⟩
    obtain ⟨γ, -, hγ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hy)
    exact ⟨γ, hγ⟩
  choose f hf using hsub
  refine Function.Injective.countable (f := f) fun a b hab => ?_
  apply Subtype.ext; apply Subtype.ext
  rw [← hf a, ← hf b, hab]

theorem tangentHaar_smul {ι : Type} [Fintype ι] {r : ℕ} (H : Subgroup (ι → GL (Fin r) ℂ)) [LocallyCompactSpace H]
    [MeasurableSpace H] [BorelSpace H] (c : ℝ≥0∞) (hc : c ≠ ⊤) (ν : Measure (ι → Fin r → Fin r → ℂ)) :
    tangentHaar H (c • ν) = c • tangentHaar H ν := by
  unfold tangentHaar
  rw [smul_smul]
  congr 1
  simp only [Measure.smul_apply, smul_eq_mul, mul_div_assoc]
  exact ENNReal.limsup_const_mul_of_ne_top hc

theorem covolume_smul {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace α] [Countable G]
    [MeasurableConstSMul G α] (ν : Measure α) [SMulInvariantMeasure G α ν] (c : ℝ≥0∞) (hc : c ≠ 0) :
    covolume G α (c • ν) = c * covolume G α ν := by
  by_cases h : HasFundamentalDomain G α ν
  · obtain ⟨s, hs⟩ := h.ExistsIsFundamentalDomain
    have hs' : IsFundamentalDomain G s (c • ν) := hs.mono (Measure.smul_absolutelyContinuous)
    rw [hs'.covolume_eq_volume, hs.covolume_eq_volume, Measure.smul_apply, smul_eq_mul]
  · have h' : ¬ HasFundamentalDomain G α (c • ν) := by
      rintro ⟨⟨s, hs⟩⟩
      exact h ⟨⟨s, hs.mono (Measure.absolutelyContinuous_smul hc)⟩⟩
    simp [covolume, h, h']

theorem abs_discr_real_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) :
    |(discr (maximalRealSubfield E) : ℝ)| = rdE E ^ fdeg E := by
  have hdiff : differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) = ⊤ :=
    (GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top _ E).1 (by
      haveI : Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) := hU; infer_instance)
  have h := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow (maximalRealSubfield E)
    (𝓞 (maximalRealSubfield E)) E (𝓞 E)
  rw [hdiff, Algebra.IsQuadraticExtension.finrank_eq_two] at h
  simp only [Ideal.absNorm_top, one_mul] at h
  have hd : dE E = |(discr (maximalRealSubfield E) : ℝ)| ^ 2 := by
    unfold dE
    rw [← Int.cast_abs, ← Int.cast_abs, Int.abs_eq_natAbs, Int.abs_eq_natAbs, h]
    push_cast; ring
  have hf : 1 ≤ (fdeg E : ℝ) := one_le_field_half_degree
  rw [rootDiscriminant_eq_rpow, hd, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _),
    ← Real.rpow_mul (abs_nonneg _)]
  have : (((2 : ℕ) : ℝ) * (1 / (2 * (fdeg E : ℝ))) * (fdeg E : ℝ)) = 1 := by
    field_simp; norm_num
  rw [this, Real.rpow_one]

theorem exists_lie_basis {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (hΛ : SelfDualLat G Λ) :
    ∃ e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E,
      (∀ i, e i ∈ lieLat G Λ) ∧ LinearIndependent (maximalRealSubfield E) e := by
  obtain ⟨e, he, hli⟩ := GlobalTheory.T.exists_unitary_lie_basis G hΛ.1 hΛ.2.1
  choose N hN hmem using fun i => GlobalTheory.T.integral_multiple_in_lie_lattice G Λ hΛ.2.2.1 hΛ.2.2.2.1 (e i) (he i).1 (he i).2
  refine ⟨fun i => (N i : E) • e i, hmem, ?_⟩
  let w : Fin (r ^ 2 - 1) → (maximalRealSubfield E)ˣ :=
    fun i => Units.mk0 (N i : maximalRealSubfield E) (by exact_mod_cast (hN i).ne')
  have hw : (fun i => (N i : E) • e i) = w • e := by
    funext i
    ext a b
    simp [w, Algebra.smul_def]
  rw [hw]
  exact hli.units_smul w

theorem sum_covolume_le : GlobalTheory.Published.TamagawaSpecialUnitary → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Λ : Submodule (𝓞 E) (Fin r → E)) (x : Frame X.Ψ r) [MeasurableSpace (realSU X.Ψ X.Gm)] [BorelSpace (realSU X.Ψ X.Gm)] (J : Type) (s : J → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), 2 ≤ r → Unr E → SelfDualLat X.Gm Λ → IsOrth X x → IsSReps X.Gm (Λ : Set (Fin r → E)) 1 s → ∑' j, covolume (inReal X.Ψ X.Gm (ratStab X.Gm (Λ : Set (Fin r → E)) (s j))) (realSU X.Ψ X.Gm) (riemHaar X.Ψ X.Gm x) ≤ ENNReal.ofReal (rdE E ^ ((fdeg E : ℝ) * ((r : ℝ) ^ 2 - 1) / 2) * (Real.sqrt r * ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i) ^ fdeg E) := by
  intro hP E _ _ _ r X Λ x _ _ J s hr hU hΛ hx hs
  obtain ⟨e, he, hli⟩ := exists_lie_basis X.Gm Λ hΛ
  obtain ⟨hmult, hP1⟩ := hP E r X.Gm Λ X.Ψ e J s hr hU hΛ X.cmType he hli hs
  have hlie := GlobalTheory.T.riemannian_lie_volume_formula E r X Λ x e hr hU hΛ hx he hli
  obtain ⟨hPpos, hPinv⟩ := GlobalTheory.T.local_factor_product_bound E r hr hmult
  set m : ℝ := ((Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex
    (lieLat X.Gm Λ) : ℝ) with hm
  set P : ℝ := ∏' v, locFactor E r v with hPdef
  set D : ℝ := |(discr (maximalRealSubfield E) : ℝ)| with hD
  set Z : ℝ := ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i with hZ
  set n : ℝ := (r : ℝ) ^ 2 - 1 with hn
  set μ := tangentHaar (realSU X.Ψ X.Gm) (formLie X.Ψ e) with hμ
  set c : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt r ^ fdeg E * m) with hc
  have hDpos : 0 < D := abs_pos.2 (by exact_mod_cast discr_ne_zero _)
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hmpos : 0 < m := by
    rcases hm0.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, mul_zero, zero_mul, ENNReal.ofReal_zero, mul_zero] at hP1
      exact zero_ne_one hP1
  have hr0 : 0 < Real.sqrt r := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < r))
  have hcpos : c ≠ 0 := by
    rw [hc, ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hriem : riemHaar X.Ψ X.Gm x = c • μ := by
    unfold riemHaar
    rw [hlie, tangentHaar_smul _ _ ENNReal.ofReal_ne_top]
  have hcov : ∀ j, covolume (inReal X.Ψ X.Gm (ratStab X.Gm (Λ : Set (Fin r → E)) (s j))) (realSU X.Ψ X.Gm)
      (riemHaar X.Ψ X.Gm x) = c * covolume (inReal X.Ψ X.Gm (ratStab X.Gm (Λ : Set (Fin r → E)) (s j)))
      (realSU X.Ψ X.Gm) μ := by
    intro j
    haveI := countable_inReal X.Ψ X.Gm (ratStab X.Gm (Λ : Set (Fin r → E)) (s j))
    rw [hriem, covolume_smul _ _ hcpos]
  simp_rw [hcov]
  rw [ENNReal.tsum_mul_left]
  set S := ∑' j, covolume (inReal X.Ψ X.Gm (ratStab X.Gm (Λ : Set (Fin r → E)) (s j))) (realSU X.Ψ X.Gm) μ
    with hS
  have ha : 0 < D ^ (-n / 2) * m * P := by positivity
  have hS1 : S = ENNReal.ofReal ((D ^ (-n / 2) * m * P)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos ha]
    exact (ENNReal.eq_inv_of_mul_eq_one_left hP1)
  rw [hS1, hc, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hDr : D = rdE E ^ fdeg E := abs_discr_real_eq hU
  have hrd0 : 0 ≤ rdE E := by
    unfold rdE; exact Real.rpow_nonneg (abs_nonneg _) _
  have hDn : D ^ (n / 2) = rdE E ^ ((fdeg E : ℝ) * n / 2) := by
    rw [hDr, ← Real.rpow_natCast, ← Real.rpow_mul hrd0, mul_div_assoc]
  have key : Real.sqrt r ^ fdeg E * m * (D ^ (-n / 2) * m * P)⁻¹ = D ^ (n / 2) * Real.sqrt r ^ fdeg E * P⁻¹ := by
    rw [neg_div, Real.rpow_neg hDpos.le]
    have : D ^ (n / 2) ≠ 0 := (Real.rpow_pos_of_pos hDpos _).ne'
    field_simp
  rw [key, hDn, mul_pow, mul_assoc]
  gcongr

end GlobalTheory.SUVolBound
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

set_option autoImplicit false

namespace GlobalTheory.ChartCob

theorem resG_appLE {Y Z : Scheme.{0}} (f : Y ⟶ Z) {O : Z.Opens} {V V' : Y.Opens} (h : V ≤ f ⁻¹ᵁ O) (h' : V' ≤ V)
    (s : Γ(Z, O)) : resG Y h' ((f.appLE O V h).hom s) = (f.appLE O V' (h'.trans h)).hom s := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem appLE_resG {Y Z : Scheme.{0}} (f : Y ⟶ Z) {O O' : Z.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ O') (h' : O' ≤ O)
    (s : Γ(Z, O)) :
    (f.appLE O' V h).hom (resG Z h' s) = (f.appLE O V (fun _ hx => h' (h hx))).hom s := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem isCoc_pullback {Y Z : Scheme.{0}} (f : Y ⟶ Z) {J : Type} (W : J → Z.Opens)
    (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')) (hc : GlobalTheory.CechFin.IsCoc W c) :
    GlobalTheory.CechFin.IsCoc (fun i => f ⁻¹ᵁ W i)
      (fun i i' => (f.appLE (W i ⊓ W i') (f ⁻¹ᵁ W i ⊓ f ⁻¹ᵁ W i') (fun _ hx => hx)).hom (c i i')) := by
  intro i i' i''
  have h3 : f ⁻¹ᵁ W i ⊓ f ⁻¹ᵁ W i' ⊓ f ⁻¹ᵁ W i'' ≤ f ⁻¹ᵁ (W i ⊓ W i' ⊓ W i'') := fun _ hx => hx
  have e := congrArg (f.appLE (W i ⊓ W i' ⊓ W i'') (f ⁻¹ᵁ W i ⊓ f ⁻¹ᵁ W i' ⊓ f ⁻¹ᵁ W i'') h3).hom
    (hc i i' i'')
  rw [map_add (f := _), appLE_resG, appLE_resG, appLE_resG] at e
  exact (congrArg₂ (· + ·) (resG_appLE f _ _ _) (resG_appLE f _ _ _)).trans (e.trans (resG_appLE f _ _ _).symm)

theorem isCoc_sum {Z X : Scheme.{0}} (p : Z ⟶ X) (U : X.Opens) (L : LB Z) (hL : L.IsLB) {n : ℕ}
    (δ : Fin n → ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)) (hδ : ∀ a, IsField (p ⁻¹ᵁ U) (δ a))
    {J : Type} (W : J → Z.Opens) (j : J → L.ι) (hWU : ∀ i, W i ≤ p ⁻¹ᵁ U) (hj : ∀ i, W i ≤ L.U (j i))
    (r : Fin n → Γ(X, U)) :
    GlobalTheory.CechFin.IsCoc W (fun i i' => ∑ b, (p.appLE U (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r b) *
      (δ b (W i ⊓ W i') (resG Z (inf_le_inf (hj i) (hj i')) (L.g (j i) (j i')).val) *
        resG Z (inf_le_inf (hj i) (hj i')) (L.g (j i) (j i'))⁻¹.val)) := by
  intro i i' i''

  simp only [map_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  have e := GlobalTheory.DlogCocycle.dlog_cocycle Z L hL _ (δ b) (hδ b) J W j hWU hj i i' i''
  rw [map_mul (resG Z _) ((p.appLE _ _ _).hom _), map_mul (resG Z _) ((p.appLE _ _ _).hom _),
    map_mul (resG Z _) ((p.appLE _ _ _).hom _), resG_appLE, resG_appLE, resG_appLE, ← e, mul_add]

theorem isCob_pbT {Y Z : Scheme.{0}} (f : Y ⟶ Z) {I : Type} (V Ω : I → Z.Opens)
    (hle : ∀ a, f ⁻¹ᵁ V a ≤ f ⁻¹ᵁ Ω a) (c : ∀ a b : I, Γ(Z, Ω a ⊓ Ω b)) (h : ∀ a, Γ(Y, f ⁻¹ᵁ Ω a))
    (hh : ∀ a b, (f.appLE (Ω a ⊓ Ω b) (f ⁻¹ᵁ Ω a ⊓ f ⁻¹ᵁ Ω b) (fun _ hx => hx)).hom (c a b) =
      resG Y inf_le_left (h a) - resG Y inf_le_right (h b)) :
    GlobalTheory.KS.IsCob (fun a => f ⁻¹ᵁ V a) (fun a b => GlobalTheory.KS.pbT f (c a b) (f ⁻¹ᵁ V a ⊓ f ⁻¹ᵁ V b)) := by
  refine ⟨fun a => -resG Y (hle a) (h a), fun a b => ?_⟩
  have e := (resG_appLE f _ (inf_le_inf (hle a) (hle b)) _).symm.trans
    (congrArg (resG Y (inf_le_inf (hle a) (hle b))) (hh a b))
  rw [map_sub, GlobalTheory.DlogCocycle.resG_resG, GlobalTheory.DlogCocycle.resG_resG] at e
  have hab : f ⁻¹ᵁ V a ⊓ f ⁻¹ᵁ V b ≤ f ⁻¹ᵁ (Ω a ⊓ Ω b) := fun x hx => ⟨hle a hx.1, hle b hx.2⟩
  simp only [GlobalTheory.KS.pbT, GlobalTheory.KS.rsT]
  rw [dite_eq_left hab, dite_eq_left inf_le_left, dite_eq_left inf_le_right, map_neg, map_neg,
    GlobalTheory.DlogCocycle.resG_resG, GlobalTheory.DlogCocycle.resG_resG]
  refine e.trans ?_
  ring

theorem chart_isCob : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (m : Ideal Γ(X, U.1)) (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ι : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ι → ∀ (r : Fin n → Γ(X, U.1)) (h' : ∀ i, Γ(A.left, ι ⁻¹ᵁ W i)), (∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (∑ b, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r b) * (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val)) = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i')) → GlobalTheory.KS.IsCob (fun a => ι ⁻¹ᵁ t.PP.L.U a) (fun a b => GlobalTheory.KS.pbT ι (∑ c, (t.G.hom.appLE U.1 ((t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1)) (inf_le_left.trans inf_le_right)).hom (r c) * (δ c ((t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1)) (resG t.G.left (inf_le_inf inf_le_left inf_le_left) (t.PP.L.g a b).val) * resG t.G.left (inf_le_inf inf_le_left inf_le_left) (t.PP.L.g a b)⁻¹.val)) (ι ⁻¹ᵁ t.PP.L.U a ⊓ ι ⁻¹ᵁ t.PP.L.U b)) := by
  intro E _ _ _ H X t U n δ hδ J W j _ hsup hWU hj m A _ ι hι r h' hh'
  have htop : ∀ x : A.left, x ∈ ι ⁻¹ᵁ (t.G.hom ⁻¹ᵁ U.1) := by
    intro x
    have hw := hι.1.w
    have : x ∈ (ι ≫ t.G.hom) ⁻¹ᵁ U.1 := by
      rw [hw]
      show (A.hom ≫ spMap (Ideal.Quotient.mk m) ≫ chart U) x ∈ (U.1 : Set X)
      rw [← U.2.range_fromSpec]
      exact ⟨(A.hom ≫ spMap (Ideal.Quotient.mk m)) x, rfl⟩
    exact this
  let Ω : J ⊕ t.PP.L.ι → t.G.left.Opens := Sum.elim W (fun a => t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1)
  let jj : J ⊕ t.PP.L.ι → t.PP.L.ι := Sum.elim j id
  have hΩU : ∀ q, Ω q ≤ t.G.hom ⁻¹ᵁ U.1 := by
    rintro (i | a)
    · exact hWU i
    · exact inf_le_right
  have hΩj : ∀ q, Ω q ≤ t.PP.L.U (jj q) := by
    rintro (i | a)
    · exact hj i
    · exact inf_le_left
  have hc := isCoc_pullback ι Ω _ (isCoc_sum t.G.hom U.1 t.PP.L t.PP.isLB δ hδ Ω jj hΩU hΩj r)
  obtain ⟨h, hh⟩ := GlobalTheory.CechFin.isCob_of_isCob_subcover A.left (J ⊕ t.PP.L.ι) (fun q => ι ⁻¹ᵁ Ω q)
    (Set.range Sum.inl) (by
      intro q x _
      have hx : ι x ∈ ⨆ i, W i := by rw [hsup]; exact htop x
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨Sum.inl i, TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, rfl⟩, hi⟩⟩)
    _ hc (fun q => match q with | Sum.inl i => h' i | Sum.inr _ => 0) (by
      rintro _ ⟨i, rfl⟩ _ ⟨i', rfl⟩
      exact hh' i i')
  exact isCob_pbT ι t.PP.L.U (fun a => t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) (fun a x hx => ⟨hx, htop x⟩) _
    (fun a => h (Sum.inr a)) (fun a b => hh (Sum.inr a) (Sum.inr b))

end GlobalTheory.ChartCob
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory.KSLift

def twist {R A : Type} [CommRing R] [CommRing A] (ρ : R →+* A) (D : Derivation ℤ R R) : R →+* DualNumber A where
  toFun r := TrivSqZeroExt.inl (ρ r) + TrivSqZeroExt.inr (ρ (D r))
  map_one' := by ext <;> simp
  map_mul' x y := by
    ext <;> simp [Derivation.leibniz, smul_eq_mul] <;> ring
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

def epsIdeal (A : Type) [CommRing A] : Ideal (DualNumber A) := RingHom.ker (TrivSqZeroExt.fstHom A A A).toRingHom

theorem mem_epsIdeal {A : Type} [CommRing A] (x : DualNumber A) : x ∈ epsIdeal A ↔ x.fst = 0 := Iff.rfl

theorem isNilpotent_epsIdeal (A : Type) [CommRing A] : IsNilpotent (epsIdeal A) := by
  refine ⟨2, ?_⟩
  rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff]
  refine Ideal.mul_le.2 fun x hx y hy => ?_
  rw [mem_epsIdeal] at hx hy
  rw [Ideal.mem_bot]
  ext <;> simp [hx, hy]

theorem exists_lift {R A : Type} [CommRing R] [CommRing A] (ρ : R →+* A) (hρ : ρ.FormallySmooth)
    (D : Derivation ℤ R R) : ∃ σ : A →+* DualNumber A, (∀ a, (σ a).fst = a) ∧ ∀ r, (σ (ρ r)).snd = ρ (D r) := by
  have hg : ((Ideal.Quotient.mk (epsIdeal A)).comp (algebraMap A (DualNumber A))).comp ρ =
      (Ideal.Quotient.mk (epsIdeal A)).comp (twist ρ D) := by
    ext r
    simp only [RingHom.comp_apply]
    rw [Ideal.Quotient.eq, mem_epsIdeal]
    simp [twist, TrivSqZeroExt.algebraMap_eq_inl]
  obtain ⟨F, hF1, hF2⟩ := GlobalTheory.DI.exists_ringHom_lift_of_formallySmooth ρ hρ (twist ρ D) (epsIdeal A)
    (isNilpotent_epsIdeal A) _ hg
  refine ⟨F, fun a => ?_, fun r => ?_⟩
  · have h := hF1 a
    simp only [RingHom.comp_apply] at h
    rw [Ideal.Quotient.eq, mem_epsIdeal] at h
    simpa [sub_eq_zero, TrivSqZeroExt.algebraMap_eq_inl] using h
  · rw [hF2]; simp [twist]

theorem main (LA : ∀ (A : Type) [CommRing A] (σ : A →+* DualNumber A), (∀ a, (σ a).fst = a) → ∃ d : ∀ O : (Sp A).Opens, Γ(Sp A, O) → Γ(Sp A, O), IsField ⊤ d ∧ ∀ a : A, d ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) = (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (σ a).snd) (LB : ∀ (Z : Scheme.{0}) (W : Z.Opens) (hW : IsAffineOpen W) (δ : Γ(Z, W) → Γ(Z, W)) (d' : ∀ O : (Spec Γ(Z, W)).Opens, Γ(Spec Γ(Z, W), O) → Γ(Spec Γ(Z, W), O)), IsField ⊤ d' → (∀ a, d' ⊤ ((Scheme.ΓSpecIso Γ(Z, W)).inv.hom a) = (Scheme.ΓSpecIso Γ(Z, W)).inv.hom (δ a)) → ∃ d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O), IsField W d ∧ ∀ a, d W a = δ a) : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (D : Derivation ℤ Γ(X, U.1) Γ(X, U.1)), ∃ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (d : J → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ i, IsAffineOpen (W i)) ∧ ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 ∧ (∀ i, W i ≤ t.PP.L.U (j i)) ∧ (∀ i, IsField (W i) (d i)) ∧ ∀ i (h : W i ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), d i (W i) ((t.G.hom.appLE U.1 (W i) h).hom r) = (t.G.hom.appLE U.1 (W i) h).hom (D r) := by
  intro E _ _ _ H X t U D
  have key : ∀ (V : t.G.left.affineOpens) (h : V.1 ≤ t.G.hom ⁻¹ᵁ U.1),
      ∃ d : ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O), IsField V.1 d ∧
        ∀ r, d V.1 ((t.G.hom.appLE U.1 V.1 h).hom r) = (t.G.hom.appLE U.1 V.1 h).hom (D r) := by
    intro V h
    have hsm : (t.G.hom.appLE U.1 V.1 h).hom.Smooth := t.semi.smooth.smooth_appLE U.2 V.2 h
    obtain ⟨σ, hσ1, hσ2⟩ := exists_lift _ hsm.formallySmooth D
    obtain ⟨d', hd'1, hd'2⟩ := LA _ σ hσ1
    obtain ⟨d, hd1, hd2⟩ := LB t.G.left V.1 V.2 (fun a => (σ a).snd) d' hd'1 hd'2
    exact ⟨d, hd1, fun r => by rw [hd2, hσ2]⟩
  choose dd hdd1 hdd2 using key
  let J := {p : t.G.left.affineOpens × t.PP.L.ι // p.1.1 ≤ t.G.hom ⁻¹ᵁ U.1 ⊓ t.PP.L.U p.2}
  refine ⟨J, fun i => i.1.1.1, fun i => i.1.2, fun i => dd i.1.1 (i.2.trans inf_le_left),
    fun i => i.1.1.2, ?_, fun i => i.2.trans inf_le_right, fun i => hdd1 _ _, fun i h r => hdd2 _ _ r⟩
  refine le_antisymm (iSup_le fun i => i.2.trans inf_le_left) fun x hx => ?_
  have hx' : x ∈ (⨆ k, t.PP.L.U k) := by rw [t.PP.isLB.cover]; trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVle⟩ := t.G.left.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ t.G.hom ⁻¹ᵁ U.1 ⊓ t.PP.L.U k from ⟨hx, hk⟩) (t.G.hom ⁻¹ᵁ U.1 ⊓ t.PP.L.U k).2
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(⟨V, hV⟩, k), hVle⟩, hxV⟩

theorem exists_lifts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (D : Derivation ℤ Γ(X, U.1) Γ(X, U.1)), ∃ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (d : J → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ i, IsAffineOpen (W i)) ∧ ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 ∧ (∀ i, W i ≤ t.PP.L.U (j i)) ∧ (∀ i, IsField (W i) (d i)) ∧ ∀ i (h : W i ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), d i (W i) ((t.G.hom.appLE U.1 (W i) h).hom r) = (t.G.hom.appLE U.1 (W i) h).hom (D r) :=
  main GlobalTheory.T.exists_spec_vectorField_of_dualNumber_section GlobalTheory.T.exists_vectorField_affineOpen_transport

end GlobalTheory.KSLift
end

section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

noncomputable section

namespace GlobalTheory.SUChartSection

theorem conj_mem_realLie : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r}, IsOrth X x → ∀ (Y : X.Ψ → Matrix (Fin r) (Fin r) ℂ), (∀ τ a b, Y τ b a * ((sgn X.p0 (b : ℕ) : ℝ) : ℂ) + ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * conj (Y τ a b) = 0) → (∀ τ a, Y τ a a = 0) → (fun τ => ((mat x τ * Y τ * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Fin r → Fin r → ℂ)) ∈ realLie X.Ψ X.Gm := by
  intro E _ _ _ r X x hx Y hY hd
  intro τ
  set A : Matrix (Fin r) (Fin r) ℂ := mat x τ with hAdef
  have hA : IsUnit A.det := isUnit_iff_ne_zero.2 (det_ne_of_orth X hx τ)
  set D : Matrix (Fin r) (Fin r) ℂ := A * Y τ * A⁻¹ with hDdef
  have hDA : D * A = A * Y τ := by
    rw [hDdef, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA, Matrix.mul_one]
  refine ⟨?_, ?_⟩
  · change (A * Y τ * A⁻¹).trace = 0
    rw [Matrix.trace_mul_cycle, Matrix.nonsing_inv_mul _ hA, Matrix.one_mul]
    simp only [Matrix.trace, Matrix.diag, hd, Finset.sum_const_zero]
  · intro u w
    change hermC τ.1 X.Gm (D *ᵥ u) w + hermC τ.1 X.Gm u (D *ᵥ w) = 0
    clear_value D
    set Gt : Matrix (Fin r) (Fin r) ℂ := X.Gm.map τ.1 with hGt
    have hform : ∀ u v : Fin r → ℂ, hermC τ.1 X.Gm u v = u ⬝ᵥ (Gt *ᵥ (fun b => conj (v b))) := by
      intro u v
      simp only [hermC, dotProduct, mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [hGt, Matrix.map_apply]
      ring
    have hconj : ∀ v : Fin r → ℂ, (fun b => conj ((D *ᵥ v) b)) = D.map (starRingEnd ℂ) *ᵥ (fun b => conj (v b)) := by
      intro v
      funext b

      simp only [mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
    set M : Matrix (Fin r) (Fin r) ℂ := Dᵀ * Gt + Gt * D.map (starRingEnd ℂ) with hMdef
    have hsum : hermC τ.1 X.Gm (D *ᵥ u) w + hermC τ.1 X.Gm u (D *ᵥ w) =
        u ⬝ᵥ (M *ᵥ (fun b => conj (w b))) := by
      rw [hform, hform, hconj, hMdef, Matrix.add_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, Matrix.mulVec_transpose]
      congr 1
      rw [dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm]
    have hJ : Aᵀ * Gt * A.map (starRingEnd ℂ) = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) := by
      rw [hGt, ← FrameDegreeData.gram_eq]
      exact hx τ
    have hkey : Aᵀ * M * A.map (starRingEnd ℂ) = 0 := by
      have e1 : Aᵀ * M * A.map (starRingEnd ℂ) =
          (D * A)ᵀ * Gt * A.map (starRingEnd ℂ) + Aᵀ * Gt * (D * A).map (starRingEnd ℂ) := by
        rw [hMdef, Matrix.transpose_mul, Matrix.map_mul]
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      have e2 : (D * A)ᵀ * Gt * A.map (starRingEnd ℂ) + Aᵀ * Gt * (D * A).map (starRingEnd ℂ) =
          (Y τ)ᵀ * (Aᵀ * Gt * A.map (starRingEnd ℂ)) + (Aᵀ * Gt * A.map (starRingEnd ℂ)) * (Y τ).map (starRingEnd ℂ) := by
        rw [hDA, Matrix.transpose_mul, Matrix.map_mul]
        simp only [Matrix.mul_assoc]
      rw [e1, e2, hJ]
      ext a b
      simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply,
        Matrix.map_apply, Matrix.zero_apply]
      exact hY τ a b
    have hAt : IsUnit Aᵀ.det := by rwa [Matrix.det_transpose]
    have hAc : IsUnit (A.map (starRingEnd ℂ)).det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact hA.map _
    have hM : M = 0 := by
      calc M = Aᵀ⁻¹ * (Aᵀ * M * A.map (starRingEnd ℂ)) * (A.map (starRingEnd ℂ))⁻¹ := by
            rw [Matrix.mul_assoc Aᵀ, Matrix.nonsing_inv_mul_cancel_left _ _ hAt,
              Matrix.mul_nonsing_inv_cancel_right _ _ hAc]
        _ = 0 := by rw [hkey, Matrix.mul_zero, Matrix.zero_mul]
    rw [hsum, hM, Matrix.zero_mulVec, dotProduct_zero]

end GlobalTheory.SUChartSection
end
end

section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Matrix
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory

theorem hv_map_embedding : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0) (ℓ : Lvl K G) (v0 : InfinitePlace K) (s : ℕ), BlockHyp B ℓ v0 s → ∀ v : InfinitePlace K, (B.HV ℓ).map v.embedding = ((Nat.card ℓ.P : ℂ)⁻¹) • (((B.vE ℓ).map v.embedding).conjTranspose * B.S.H.map v.embedding * (B.vE ℓ).map v.embedding) := by
  intro K _ _ _ G _ _ Pl0 B ℓ v0 s h v
  have hE : ∀ i j, B.vE ℓ i j ∈ Formalism.DivisionValues.cmMax K :=
    (Formalism.L2.DIV.good_part_hermitian_spec K v0 h.conj B.S h.ok.hrat h.ok.hpos G B.r h.ok.actRat ℓ.X h.irr ℓ.P ℓ.ψ).1
  have hct : ((B.vE ℓ)ᴴ).map v.embedding = ((B.vE ℓ).map v.embedding)ᴴ := by
    ext i j
    simp only [Matrix.map_apply, Matrix.conjTranspose_apply]
    exact hE j i v.embedding
  have hdef : B.HV ℓ = (Nat.card ℓ.P : K)⁻¹ • ((B.vE ℓ)ᴴ * B.S.H * B.vE ℓ) := rfl
  rw [hdef, ← hct, ← Matrix.map_mul, ← Matrix.map_mul]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, map_natCast]

end GlobalTheory
end
end
