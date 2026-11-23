module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle010
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameThetaConstPos
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle029
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle011
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle053
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivityHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle003
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps GlobalTheory.Shares

namespace GlobalTheory.Shares.PolyDict

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j}

theorem ofWt_C {ι : Type} (u : WeightFamilies.Wt D j) (F : B.Cusp j u) :
    OfWt X u (MvPolynomial.C (X.inc u F) : MvPolynomial ι X.Forms) := by
  classical
  intro m
  rw [MvPolynomial.coeff_C]
  split_ifs
  · exact LinearMap.mem_range.mpr ⟨F, rfl⟩
  · exact Submodule.zero_mem _

theorem ofWt_sum {ι κ : Type} (u : WeightFamilies.Wt D j) (s : Finset κ) (p : κ → MvPolynomial ι X.Forms)
    (h : ∀ k ∈ s, OfWt X u (p k)) : OfWt X u (∑ k ∈ s, p k) := by
  intro m
  rw [MvPolynomial.coeff_sum]
  exact Submodule.sum_mem _ fun k hk => h k hk m

theorem ofWt_X_mul {ι : Type} (u : WeightFamilies.Wt D j) (i : ι) (p : MvPolynomial ι X.Forms) (h : OfWt X u p) :
    OfWt X u (MvPolynomial.X i * p) := by
  classical
  intro m
  rw [MvPolynomial.coeff_X_mul']
  split_ifs
  · exact h _
  · exact Submodule.zero_mem _

theorem ofWt_mul {ι : Type} (u u' : WeightFamilies.Wt D j) (p q : MvPolynomial ι X.Forms) (hp : OfWt X u p)
    (hq : OfWt X u' q) : OfWt X (wadd u u') (p * q) := by
  classical
  intro m
  rw [MvPolynomial.coeff_mul]
  refine Submodule.sum_mem _ fun x _ => ?_
  obtain ⟨F, hF⟩ := LinearMap.mem_range.mp (hp x.1)
  obtain ⟨G, hG⟩ := LinearMap.mem_range.mp (hq x.2)
  obtain ⟨H, hH⟩ := X.inc_mul u u' F G
  rw [← hF, ← hG, hH]
  exact LinearMap.mem_range_self _ _

theorem toRp_C (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (F : X.Forms) :
    toRp X la N (MvPolynomial.C F) = emb X la N F := MvPolynomial.eval₂Hom_C _ _ _

theorem toRp_X (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (p : Idx D j N) :
    toRp X la N (MvPolynomial.X p) = algebraMap (Op X la N) (Rp X la N) (Tv X la N p) := MvPolynomial.eval₂Hom_X' _ _ _

theorem toFn_C (R : Rdg X) {N : ℕ} (t : Idx D j N → ℂ) (F : X.Forms) :
    R.toFn t (MvPolynomial.C F) = R.ev F := MvPolynomial.eval₂Hom_C _ _ _

theorem toFn_X (R : Rdg X) {N : ℕ} (t : Idx D j N → ℂ) (p : Idx D j N) :
    R.toFn t (MvPolynomial.X p) = fun _ => t p := MvPolynomial.eval₂Hom_X' _ _ _

private lemma algebraMap_mul_mem_Vw (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (u : WeightFamilies.Wt D j)
    (x : Op X la N) {v : Rp X la N} (hv : v ∈ Vw X la N u) :
    algebraMap (Op X la N) (Rp X la N) x * v ∈ Vw X la N u := by
  rw [IsScalarTower.algebraMap_apply (Op X la N) (Kp X la N) (Rp X la N), ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ hv

theorem toRp_mem (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (u : WeightFamilies.Wt D j)
    (p : MvPolynomial (Idx D j N) X.Forms) (hp : OfWt X u p) : toRp X la N p ∈ Vw X la N u := by

  rw [p.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m _ => ?_
  obtain ⟨F, hF⟩ := LinearMap.mem_range.mp (hp m)
  have key : toRp X la N (MvPolynomial.monomial m (p.coeff m)) = emb X la N (p.coeff m) *
      m.prod fun n e => (algebraMap (Op X la N) (Rp X la N) (Tv X la N n)) ^ e := by
    rw [toRp, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial]
  rw [key, ← hF, mul_comm]
  have hbase : emb X la N (X.inc u F) ∈ Vw X la N u := Submodule.subset_span ⟨F, rfl⟩
  suffices H : ∀ v ∈ Vw X la N u,
      (m.prod fun n e => (algebraMap (Op X la N) (Rp X la N) (Tv X la N n)) ^ e) * v ∈ Vw X la N u from
    H _ hbase
  unfold Finsupp.prod
  refine Finset.prod_induction _ (fun x => ∀ v ∈ Vw X la N u, x * v ∈ Vw X la N u) ?_ ?_ ?_
  · intro a b ha hb v hv
    rw [mul_assoc]
    exact ha _ (hb v hv)
  · intro v hv
    rwa [one_mul]
  · intro n _ v hv
    show algebraMap (Op X la N) (Rp X la N) (Tv X la N n) ^ (m n) * v ∈ _
    rw [← map_pow]
    exact algebraMap_mul_mem_Vw la N u _ hv

theorem toFn_mem (R : Rdg X) {N : ℕ} (t : Idx D j N → ℂ) (u : WeightFamilies.Wt D j)
    (p : MvPolynomial (Idx D j N) X.Forms) (hp : OfWt X u p) : R.toFn t p ∈ R.sp u Set.univ := by

  rw [p.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m _ => ?_
  obtain ⟨F, hF⟩ := LinearMap.mem_range.mp (hp m)
  have key : R.toFn t (MvPolynomial.monomial m (p.coeff m)) = R.ev (p.coeff m) *
      m.prod fun n e => (fun _ : R.Y => t n) ^ e := by
    rw [Rdg.toFn, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial]
  rw [key, ← hF, mul_comm]
  have hbase : R.ev (X.inc u F) ∈ R.sp u Set.univ := Submodule.subset_span ⟨F, Set.mem_univ _, rfl⟩
  suffices H : ∀ v ∈ R.sp u Set.univ,
      (m.prod fun n e => (fun _ : R.Y => t n) ^ e) * v ∈ R.sp u Set.univ from H _ hbase
  unfold Finsupp.prod
  refine Finset.prod_induction _ (fun x => ∀ v ∈ R.sp u Set.univ, x * v ∈ R.sp u Set.univ) ?_ ?_ ?_
  · intro a b ha hb v hv
    rw [mul_assoc]
    exact ha _ (hb v hv)
  · intro v hv
    rwa [one_mul]
  · intro n _ v hv
    show (fun _ : R.Y => t n) ^ (m n) * v ∈ _
    have hc : (fun _ : R.Y => t n) ^ (m n) * v = (t n ^ m n) • v := by
      funext y
      simp [Pi.pow_apply, Pi.mul_apply, Pi.smul_apply]
    rw [hc]
    exact Submodule.smul_mem _ _ hv

theorem sp_mul (R : Rdg X) (u u' : WeightFamilies.Wt D j) (f : R.Y → ℂ) (hf : f ∈ R.sp u Set.univ) (g : R.Y → ℂ)
    (hg : g ∈ R.sp u' Set.univ) : f * g ∈ R.sp (wadd u u') Set.univ := by
  have hfg := Submodule.mul_mem_mul hf hg
  simp only [Rdg.sp, Submodule.span_mul_span] at hfg ⊢
  refine Submodule.span_le.mpr ?_ hfg
  rintro _ ⟨_, ⟨F, -, rfl⟩, _, ⟨G, -, rfl⟩, rfl⟩
  obtain ⟨H, hH⟩ := X.inc_mul u u' F G
  show R.ev (X.inc u F) * R.ev (X.inc u' G) ∈ _
  rw [← map_mul R.ev, hH]
  exact Submodule.subset_span ⟨H, Set.mem_univ _, rfl⟩

theorem sp_span (R : Rdg X) (u : WeightFamilies.Wt D j) (s : Set (B.Cusp j u)) :
    R.sp u (Submodule.span B.KO s) = R.sp u s := by
  unfold Rdg.sp
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨F, hF, rfl⟩
    have hF' : F ∈ Submodule.span B.KO s := hF
    clear hF
    induction hF' using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero =>
      simp only [map_zero]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      simp only [map_add (f := _)]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      simp only [map_smul, R.ev_smul]
      exact Submodule.smul_mem _ _ hx
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem sp_finrank (R : Rdg X) (u : WeightFamilies.Wt D j) (M : Submodule B.KO (B.Cusp j u)) :
    FiniteDimensional ℂ (R.sp u M) ∧ Module.finrank ℂ (R.sp u M) = Module.finrank B.KO M := by
  let b := Module.finBasis B.KO M
  have hli : LinearIndependent B.KO (fun i => (b i : B.Cusp j u)) :=
    b.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hli' := R.indep u _ _ hli
  have hspan : Submodule.span B.KO (Set.range fun i => (b i : B.Cusp j u)) = M := by
    rw [show (Set.range fun i => (b i : B.Cusp j u)) = M.subtype '' Set.range b from Set.range_comp _ _,
      Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have hs := sp_span R u (Set.range fun i => (b i : B.Cusp j u))
  rw [hspan] at hs
  have e : R.sp u (M : Set (B.Cusp j u)) =
      Submodule.span ℂ (Set.range fun i => R.ev (X.inc u (b i : B.Cusp j u))) := by
    rw [hs]
    unfold Rdg.sp
    rw [← Set.range_comp]
    rfl
  rw [e]
  exact ⟨FiniteDimensional.span_of_finite ℂ (Set.finite_range _),
    (finrank_span_eq_card hli').trans (Fintype.card_fin _)⟩

end GlobalTheory.Shares.PolyDict

namespace GlobalTheory.Shares


open PolyDict in
theorem polyDictionary : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (R : Rdg X) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (wL : WeightFamilies.Wt D j) (w : Fin N → B.Cusp j wL) (t : Idx D j N → ℂ), (∀ i, toRp X la N (∑ k, MvPolynomial.X (i, k) * MvPolynomial.C (X.inc wL (w k))) = sec X la w i ∧ R.toFn t (∑ k, MvPolynomial.X (i, k) * MvPolynomial.C (X.inc wL (w k))) = R.s w t i ∧ OfWt X wL (∑ k, MvPolynomial.X (i, k) * MvPolynomial.C (X.inc wL (w k)) : MvPolynomial (Idx D j N) X.Forms)) ∧ (∀ F, toRp X la N (MvPolynomial.C F) = emb X la N F ∧ R.toFn t (MvPolynomial.C F) = R.ev F) ∧ (∀ u (F : B.Cusp j u), OfWt X u (MvPolynomial.C (X.inc u F) : MvPolynomial (Idx D j N) X.Forms)) ∧ (∀ u u' (p q : MvPolynomial (Idx D j N) X.Forms), OfWt X u p → OfWt X u' q → OfWt X (wadd u u') (p * q)) ∧ (∀ u (p : MvPolynomial (Idx D j N) X.Forms), OfWt X u p → toRp X la N p ∈ Vw X la N u ∧ R.toFn t p ∈ R.sp u Set.univ) ∧ (∀ u u', ∀ f ∈ R.sp u Set.univ, ∀ g ∈ R.sp u' Set.univ, f * g ∈ R.sp (wadd u u') Set.univ) ∧ (∀ u (s : Set (B.Cusp j u)), R.sp u (Submodule.span B.KO s) = R.sp u s) ∧ (∀ u (M : Submodule B.KO (B.Cusp j u)), FiniteDimensional ℂ (R.sp u M) ∧ Module.finrank ℂ (R.sp u M) = Module.finrank B.KO M) := by
  intro D B P j X R la N wL w t
  refine ⟨fun i => ⟨?_, ?_, ?_⟩, fun F => ⟨PolyDict.toRp_C la N F, PolyDict.toFn_C R t F⟩,
    fun u F => PolyDict.ofWt_C u F, fun u u' p q hp hq => PolyDict.ofWt_mul u u' p q hp hq,
    fun u p hp => ⟨PolyDict.toRp_mem la N u p hp, PolyDict.toFn_mem R t u p hp⟩,
    fun u u' f hf g hg => PolyDict.sp_mul R u u' f hf g hg,
    fun u s => PolyDict.sp_span R u s, fun u M => PolyDict.sp_finrank R u M⟩

  · rw [map_sum]
    unfold Formalism.MainNotions.Gaps.EtaleWeightGaps.sec
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, PolyDict.toRp_X, PolyDict.toRp_C, Algebra.smul_def,
      IsScalarTower.algebraMap_apply (Op X la N) (Kp X la N) (Rp X la N)]

  · rw [map_sum]
    unfold Rdg.s
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, PolyDict.toFn_X, PolyDict.toFn_C]
    funext y
    simp [Pi.mul_apply, Pi.smul_apply]
  · exact PolyDict.ofWt_sum wL _ _ fun k _ => PolyDict.ofWt_X_mul wL _ _ (PolyDict.ofWt_C wL (w k))

end GlobalTheory.Shares
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

namespace GlobalTheory.Shares

theorem spanMem_ssgt_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) {P : Frame X.Ψ r → ℂ} (hP : P ∈ X.SS la) : P ∈ X.SSgt la 0 := by
  refine ⟨hP, fun ξ hξ ν hν x hx => ?_⟩
  by_contra hne
  obtain ⟨⟨hsec, C, hC⟩, h0⟩ := hP
  have hpos := (moderateCoefficientPositivity_holds r X la P C 0 hsec (fun y hy => by simpa using hC y hy)).1 ξ hξ ν x hx hne
  have hsum : ∑ τ, ν τ = 0 := le_antisymm hν (Finset.sum_nonneg fun τ _ => hpos τ)
  have hz : ν = 0 := by
    funext τ
    exact (Finset.sum_eq_zero_iff_of_nonneg fun τ _ => hpos τ).1 hsum τ (Finset.mem_univ τ)
  subst hz
  exact hne (h0 ξ hξ x hx)

theorem spanMem_rdR {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (u : WeightFamilies.Wt D j)
    (F : (recB h.toLawsCore).Cusp j u) (k : (T.U j T.σ₀).Comp) :
    rdR h j F k ∈ ((T.U j T.σ₀).X k).SSgt (laR T j u k) 0 := by
  have hF : F.1 ∈ T.C j u := by
    rw [← cutR_eq T.C hj]; exact F.2
  exact spanMem_ssgt_zero _ _
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.readings_holomorphic_cuspForms (U := T.U j) siegelSpaceAlgebra_holds T.good_σ₀ (wtA u) u.n ⟨F.1, hF⟩ k)

theorem span_readings_components : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ u : WeightFamilies.Wt D j, (∀ g ∈ R.sp u Set.univ, ∃ f : ∀ k : (T.U j T.σ₀).Comp, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ, (∀ k, f k ∈ ((T.U j T.σ₀).X k).SSgt (laR T j u k) 0) ∧ ∀ y, g y = f (e y).1 (e y).2.1) ∧ (∀ (A : ∀ k : (T.U j T.σ₀).Comp, Set (Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ)) (s : Set ((recB h.toLawsCore).Cusp j u)), OntoBy h j u A s → ∀ f : ∀ k : (T.U j T.σ₀).Comp, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ, (∀ k, f k ∈ A k) → (fun y => f (e y).1 (e y).2.1) ∈ R.sp u s) ∧ ∀ (F : (recB h.toLawsCore).Cusp j u) (k : (T.U j T.σ₀).Comp), rdR h j F k ∈ ((T.U j T.σ₀).X k).SSgt (laR T j u k) 0 := by
  intro D T h j hj n R e hR u
  refine ⟨fun g hg => ?_, fun A s hA f hf => ?_, fun F k => spanMem_rdR h j hj u F k⟩
  · unfold Rdg.sp at hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨F, -, rfl⟩ := hg
      exact ⟨fun k => rdR h j F k, fun k => spanMem_rdR h j hj u F k, fun y => hR.2 u F y⟩
    | zero =>
      exact ⟨fun _ => 0, fun k => (siegelSpaceAlgebra_holds _ _ (laR T j u k) (laR T j u k) 0).2.2.1.1, fun _ => rfl⟩
    | add g g' _ _ hg hg' =>
      obtain ⟨f, hf, e1⟩ := hg
      obtain ⟨f', hf', e2⟩ := hg'
      refine ⟨fun k => f k + f' k,
        fun k => (siegelSpaceAlgebra_holds _ _ (laR T j u k) (laR T j u k) 0).2.2.1.2.1 _ (hf k) _ (hf' k), fun y => ?_⟩
      simp only [Pi.add_apply, e1, e2]
    | smul a g _ hg =>
      obtain ⟨f, hf, e1⟩ := hg
      refine ⟨fun k => a • f k,
        fun k => (siegelSpaceAlgebra_holds _ _ (laR T j u k) (laR T j u k) 0).2.2.1.2.2 a _ (hf k), fun y => ?_⟩
      simp only [Pi.smul_apply, e1]
  · obtain ⟨m, a, F, hF, hsum⟩ := hA f hf
    have : (fun y => f (e y).1 (e y).2.1) = ∑ i, a i • R.ev ((recPlusN h j hj n).inc u (F i)) := by
      funext y
      rw [hsum _ _ (e y).2.2, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, hR.2 u (F i) y, smul_eq_mul]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨F i, hF i, rfl⟩)

end GlobalTheory.Shares
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Shares

theorem cone_sum_sq_le {m N : ℕ} (t : Fin m × Fin N → ℂ) (Z : Set (Fin N → ℂ)) (hZ : IsClosed Z)
    (hc : ∀ (c : ℂ), ∀ ζ ∈ Z, c • ζ ∈ Z) (h0 : ∀ ζ ∈ Z, (∀ i, ∑ j, t (i, j) * ζ j = 0) → ζ = 0) :
    ∃ C : ℝ, ∀ ζ ∈ Z, ∑ k, ‖ζ k‖ ^ 2 ≤ C * ∑ i, ‖∑ j, t (i, j) * ζ j‖ ^ 2 := by
  set f : (Fin N → ℂ) → ℝ := fun ζ => ∑ i, ‖∑ j, t (i, j) * ζ j‖ ^ 2 with hf
  set g : (Fin N → ℂ) → ℝ := fun ζ => ∑ k, ‖ζ k‖ ^ 2 with hg
  have hfc : Continuous f := by simp only [hf]; fun_prop
  have hgc : Continuous g := by simp only [hg]; fun_prop
  have hS : IsCompact (Metric.sphere (0 : Fin N → ℂ) 1 ∩ Z) := (isCompact_sphere _ _).inter_right hZ
  have hfnn : ∀ ζ, 0 ≤ f ζ := fun ζ => Finset.sum_nonneg fun i _ => by positivity
  have hpos : ∀ ζ ∈ Metric.sphere (0 : Fin N → ℂ) 1 ∩ Z, 0 < f ζ := by
    rintro ζ ⟨h1, h2⟩
    refine lt_of_le_of_ne (hfnn ζ) fun h => ?_
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1 h.symm
    have h4 : ζ = 0 := h0 ζ h2 fun i => by simpa using h3 i (Finset.mem_univ i)
    simp [h4] at h1
  obtain ⟨C, hC⟩ := hS.bddAbove_image (f := fun ζ => g ζ / f ζ)
    (hgc.continuousOn.div hfc.continuousOn fun ζ hζ => (hpos ζ hζ).ne')
  refine ⟨C, fun ζ hζ => ?_⟩
  by_cases hz : ζ = 0
  · simp [hz]
  have hn : 0 < ‖ζ‖ := norm_pos_iff.2 hz
  set c : ℂ := ((‖ζ‖⁻¹ : ℝ) : ℂ) with hcdef
  have hcn : ‖c‖ = ‖ζ‖⁻¹ := by simp [hcdef]
  have hmem : c • ζ ∈ Metric.sphere (0 : Fin N → ℂ) 1 ∩ Z :=
    ⟨by rw [mem_sphere_zero_iff_norm, norm_smul, hcn, inv_mul_cancel₀ hn.ne'], hc c ζ hζ⟩
  have h1 : g (c • ζ) ≤ C * f (c • ζ) := (div_le_iff₀ (hpos _ hmem)).1 (hC ⟨_, hmem, rfl⟩)
  have h2 : g (c • ζ) = ‖c‖ ^ 2 * g ζ := by
    simp only [hg, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  have h3 : f (c • ζ) = ‖c‖ ^ 2 * f ζ := by
    simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_pow, ← norm_mul, Finset.mul_sum]
    congr 2
    exact Finset.sum_congr rfl fun j _ => by ring
  have h4 : 0 < ‖c‖ ^ 2 := by rw [hcn]; positivity
  rw [h2, h3, mul_left_comm] at h1
  exact le_of_mul_le_mul_left h1 h4

theorem eval₂_smul_of_isHomogeneous {K : Type} [Field K] (σ : K →+* ℂ) {n d : ℕ} {Q : MvPolynomial (Fin n) K}
    (hQ : Q.IsHomogeneous d) (c : ℂ) (z : Fin n → ℂ) :
    MvPolynomial.eval₂ σ (fun a => c * z a) Q = c ^ d * MvPolynomial.eval₂ σ z Q := by
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have h := hQ (MvPolynomial.mem_support_iff.1 hs)
  have h' : ∑ a, s a = d := by
    rw [← h, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, h']
  ring

theorem forms_le_generic_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (K : Type) [Field K] (σ : K →+* ℂ) (t : Fin (nd X + 1) × Fin Xa.N → ℂ), (∀ Q : MvPolynomial (Fin (nd X + 1) × Fin Xa.N) K, Q ≠ 0 → MvPolynomial.eval₂ σ t Q ≠ 0) → RelIn σ X Xa → let sf : Fin (nd X + 1) → Frame X.Ψ r → ℂ := fun i x => ∑ j, t (i, j) * Xa.w j x; ∃ C : ℝ, ∀ x ∈ X.dom, ∑ k, ‖Xa.w k x‖ ^ 2 ≤ C * ∑ i, ‖sf i x‖ ^ 2 := by
  intro E _ _ _ r X Xa K _ σ t ht hrel sf
  choose Q d hQ0 hQd hQ using hrel.1
  let Z : Set (Fin Xa.N → ℂ) := {ζ | ∀ jj, MvPolynomial.eval₂ σ (fun a => ζ (jj a)) (Q jj) = 0}
  have hZ : IsClosed Z := by
    simp only [Z, Set.setOf_forall]
    refine isClosed_iInter fun jj => isClosed_eq ?_ continuous_const
    simp only [MvPolynomial.eval₂_eq']
    fun_prop
  obtain ⟨C, hC⟩ := cone_sum_sq_le t Z hZ
    (fun c ζ hζ jj => by
      have := eval₂_smul_of_isHomogeneous σ (hQd jj) c fun a => ζ (jj a)
      rw [hζ jj, mul_zero] at this
      exact this)
    (fun ζ hζ h => by
      by_contra hz
      obtain ⟨jj, hjj⟩ := GlobalTheory.T.exists_coords_no_homogeneous_relation_generic_hyperplanes K σ _ _ t ζ ht hz h
      exact hjj _ _ (hQ0 jj) (hQd jj) (hζ jj))
  exact ⟨C, fun x hx => hC (fun k => Xa.w k x) fun jj => hQ jj x hx⟩

end GlobalTheory.Shares
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Shares

theorem margins_of_gaps : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X), 0 < X.p0 → X.p0 < r → Nonempty X.Ψ → Xa.de = de2W X → IsStrictDom X Xa.L → (∀ τ (a b : Fin r), a ≤ b → ((b : ℕ) < X.p0 ∨ X.p0 ≤ (a : ℕ)) → (Xa.Fp - kapW X - nd X • Xa.L) τ b ≤ (Xa.Fp - kapW X - nd X • Xa.L) τ a) → ∀ bb m mL : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb → (∀ τ (a b : Fin r), (a : ℕ) < X.p0 → X.p0 ≤ (b : ℕ) → m ≤ (((Xa.Fp - kapW X - nd X • Xa.L) τ b : ℤ) : ℝ) - (((Xa.Fp - kapW X - nd X • Xa.L) τ a : ℤ) : ℝ) ∧ mL ≤ ((Xa.L τ b : ℤ) : ℝ) - ((Xa.L τ a : ℤ) : ℝ)) → bb + 2 * Xa.T < m → bb ^ 2 * ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) + bb < m + nd X * mL → 2 * (r : ℝ) < m → Margins X Xa := by
  intro E _ _ _ r X Xa h0 hr _ hde hL hgap bb m mL hbb hpair hm1 hm2 _
  obtain ⟨g1, g2, g3, g4⟩ := GlobalTheory.ThetaRecordCompare.arch_gaps Xa h0 hr
  have hT : (0 : ℝ) ≤ Xa.T := Nat.cast_nonneg _
  have hde2 : GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.IsTwoDelta X Xa.de := by
    rw [hde]
    intro τ i j
    refine ⟨fun h => ?_, fun a b => ?_⟩
    · simp only [de2W]
      split_ifs <;> omega
    · simp only [de2W]
      split_ifs <;> omega
  have hA : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
        (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ := fun x0 ho z hz ξ => by
    rw [← IW.leviM_comb X x0 ho hz]
    exact (GlobalTheory.CurvMarginClosed.curv_and_margin_closed (E := E)).2 r X _ m
      (fun τ i j a b => hgap τ i j a (Or.inl b)) (fun τ i j a b => hgap τ i j b (Or.inr a))
      (fun τ i j a b => (hpair τ i j a b).1) x0 ho z hz ξ
  have hB : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      mL * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.L) z ξ :=
    (GlobalTheory.CurvMarginClosed.curv_and_margin_closed (E := E)).2 r X _ mL
      (fun τ i j a b => by
        rcases a.eq_or_lt with h | h
        · rw [h]
        · exact ((hL τ).1 i j h b).le)
      (fun τ i j a b => by
        rcases b.eq_or_lt with h | h
        · rw [h]
        · exact ((hL τ).2.1 i j a h).le)
      (fun τ i j a b => (hpair τ i j a b).2)
  refine ⟨⟨bb, m - 2 * Xa.T, hbb, by linarith, fun t ht x0 ho z hz ξ => ?_⟩,
    ⟨bb, m + nd X * mL, hbb, hm2, fun x0 ho z hz ξ => ?_⟩, fun x0 ho z hz ξ => ?_,
    (GlobalTheory.ThetaRecordCompare.arch_extra Xa).2.2.2.1,
    fun k P => GlobalTheory.ThetaRecordCompare.cusp_of_gaps Xa.n_ge h0 hr
      (GlobalTheory.ThetaRecordCompare.gaps_add g3 (GlobalTheory.ThetaRecordCompare.gapsGe_mono g1 zero_le_one) k)
      (GlobalTheory.ThetaRecordCompare.pair_add g4 g2 k)⟩
  · have a := hA x0 ho z hz ξ
    have hrh := GlobalTheory.ThetaRecordCompare.leviRh_nonneg X ho hz ξ
    rcases ht with rfl | ht
    · have := mul_nonneg hT hrh
      nlinarith
    · rw [Set.mem_singleton_iff] at ht
      subst ht
      have b := Xa.base_psi_levi_lower_bound x0 (IW.orth_mem_dom X x0 ho) z hz ξ
      have c : leviM X (phla X Xa.de) x0 z ξ = 2 * leviRh X x0 z ξ :=
        GlobalTheory.ThetaRecordCompare.levi_twoDelta hde2 ho hz ξ
      have ht : 0 ≤ 1 + Xa.c1 / Xa.a1 := by have := Xa.frame_theta_const_pos; have := Xa.frame_theta_weight_pos; positivity
      have d := mul_le_mul_of_nonneg_left b ht
      have e := mul_le_mul_of_nonneg_right Xa.rr_le hrh
      rw [c] at d
      unfold leviO at *
      nlinarith
  · have a := hA x0 ho z hz ξ
    have b := mul_le_mul_of_nonneg_left (hB x0 ho z hz ξ) (Nat.cast_nonneg (α := ℝ) (nd X))
    nlinarith
  · by_cases hξ : ξ = 0
    · subst hξ; simp [leviO, leviM, leviV]
    · exact (Xa.posL x0 (IW.orth_mem_dom X x0 ho) z hz ξ hξ).le

end GlobalTheory.Shares
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

theorem _root_.GlobalTheory.T.exists_rankOne_cuspData_log_bounds : ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∃ (e : ∀ k : (T.U j σ).Comp, XExt ((T.U j σ).X k)) (M wg : ℝ), 1 ≤ M ∧ Real.log M ≤ 30 * large₂.sc.L ∧ 0 < wg ∧ Real.log wg ≤ 3 * large₂.sc.L ∧ Real.log ((fdeg D.host.E : ℝ) * wg + 2) ≤ 5 * large₂.sc.L ∧ ∀ k, (∑ τ, ((T.U j σ).X k).spread (laU (T.U j σ) (wtA w) w.n k) τ) ≤ wg ∧ (∀ v ∈ (e k).L', herm ((T.U j σ).X k).Gm v v = 0 → ∀ b : D.host.E, ReciprocityTheory.ChartRestriction.G.FD.cc b = b → IsIntegral ℤ b → ∃ γ ∈ ((T.U j σ).X k).Γ, ((T.U j σ).X k).χ (laU (T.U j σ) (wtA w) w.n k) γ = 1 ∧ ∀ τ : ((T.U j σ).X k).Ψ, (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 = ((T.U j σ).X k).flowMat v τ ((M : ℂ) * τ.1 b)) ∧ Real.log (1 + ∑ τ, ∑ i, |((laU (T.U j σ) (wtA w) w.n k τ i : ℤ) : ℝ)|) ≤ 3 * large₂.sc.L ∧ Real.log (e k).NA ≤ 4 * large₂.sc.L ∧ Real.log (e k).NC ≤ 2 * large₂.sc.L ∧ Real.log (e k).g ≤ 19 * large₂.sc.L ∧ Real.log (1 / (e k).k0) ≤ 3 * large₂.sc.L := by
  first | exact @GlobalTheory.CuspDataBounds.cusp_data_bounds | exact GlobalTheory.CuspDataBounds.cusp_data_bounds | (intros; apply GlobalTheory.CuspDataBounds.cusp_data_bounds <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

theorem _root_.GlobalTheory.T.thetaLatticeWeightScalar_ne_zero_and_log_bounds : ∀ (D : D7) (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (j : ℕ) (w : WeightFamilies.Wt D j), sOf B hinj EX w ≠ 0 ∧ ∀ σ : B.KO →+* ℂ, 0 ≤ Real.log ‖σ (sOf B hinj EX w : B.KO)‖ ∧ (WeightAlgebra.DF w : ℝ) / 2 * Real.log (qq D) ≤ Real.log ‖σ (sOf B hinj EX w : B.KO)‖ ∧ (WeightAlgebra.DF w : ℝ) / 2 * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ≤ Real.log ‖σ (sOf B hinj EX w : B.KO)‖ ∧ Real.log ‖σ (sOf B hinj EX w : B.KO)‖ ≤ lamStar D * w.size := by
  first | exact @GlobalTheory.RunIn.sOf_ne_zero_and_log_bounds | exact GlobalTheory.RunIn.sOf_ne_zero_and_log_bounds | (intros; apply GlobalTheory.RunIn.sOf_ne_zero_and_log_bounds <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.harmonicValue_canonicalConnection_eq_polyDeriv : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (k n : ℕ) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (θ : Fin n → (Fin g → ℂ) → ℂ), (∀ b, Φ.toAnFr.Rd k (F b) (θ b)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∑ m ∈ P.support, algebraMap c.F ℂ (P.coeff m) * ∏ b, nab y k (F b) (colOf m b) = I2.polyDeriv (MvPolynomial.map (algebraMap c.F ℂ) P) (letDir el) (fun z => ∏ b, θ b (z b)) 0 := by
  first | exact @GlobalTheory.AnVal.harm_nab_eq_polyDeriv | exact GlobalTheory.AnVal.harm_nab_eq_polyDeriv | (intros; apply GlobalTheory.AnVal.harm_nab_eq_polyDeriv <;> assumption)
end
