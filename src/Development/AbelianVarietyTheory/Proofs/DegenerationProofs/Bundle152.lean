module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle123
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle007
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SemicharacterSqEqOneOfSymmetric
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescOfPoints
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPelUnifPull
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Convex.Contractible
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle130

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

namespace GlobalTheory.Ex.Arch


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField in
open scoped CategoryTheory.Obj BigOperators in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.Ex.Arch.towerSt_of : _root_.GlobalTheory.Ex.BrGtSt → _root_.GlobalTheory.Ex.BrWpSt → _root_.GlobalTheory.Ex.Arch.PtSt → _root_.GlobalTheory.Ex.Arch.QkSt → _root_.GlobalTheory.Ex.Arch.WpSt → _root_.GlobalTheory.Ex.Arch.TowerSt := by
  intro hGt hWp hPt hQk hWA
  unfold _root_.GlobalTheory.Ex.BrGtSt _root_.GlobalTheory.Ex.AllN at hGt
  unfold _root_.GlobalTheory.Ex.BrWpSt _root_.GlobalTheory.Ex.AllN at hWp
  unfold _root_.GlobalTheory.Ex.Arch.PtSt _root_.GlobalTheory.Ex.Arch.AllDict at hPt
  unfold _root_.GlobalTheory.Ex.Arch.QkSt _root_.GlobalTheory.Ex.Arch.AllDict at hQk
  unfold _root_.GlobalTheory.Ex.Arch.WpSt _root_.GlobalTheory.Ex.Arch.AllDict at hWA
  beta_reduce at hGt hWp hPt hQk hWA
  unfold _root_.GlobalTheory.Ex.Arch.TowerSt _root_.GlobalTheory.Ex.AllD
  intro E _ _ _ H D R _ _ _ A B dd hl
  letI := H.starRing
  have hG := hGt R A.D₀ A.even A.bimult ℂ A.N A.ν
  have hW := hWp R A.D₀ A.even A.bimult ℂ A.N A.ν
  have hV := hPt (𝓞 E) A.N _ dd
  have hL := hQk (𝓞 E) A.N _ dd
  have hE := hWA (𝓞 E) A.N _ dd
  have hq := A.hq
  have hT := _root_.GlobalTheory.NestQVal.qval_add_tower E H D R A.D₀ A.oa A.even A.bimult ℂ A.I A.N A.ν A.q
    hG.1 hG.2.2.1 (fun k => ⟨(hG.2.2.2.2 k).1, (hG.2.2.2.2 k).2.2⟩) hq
  choose! f hf using fun n (hn : 0 < n) (a : D.La) => (hL n hn).1 (A.q n a)
  have hpow : ∀ (m : ℕ) v g, dd.IsPt v g → dd.IsPt (m • v) (g ^ m) := by
    obtain ⟨g₀, hg₀, hu⟩ := hV.1 0
    have h00 := hV.2.2.1 0 0 g₀ g₀ hg₀ hg₀
    rw [add_zero] at h00
    have hg₁ : g₀ = 1 := mul_eq_left.1 (hu _ h00)
    intro m v g hg
    induction m with
    | zero => simpa [hg₁] using hg₀
    | succ k ih => simpa [succ_nsmul, pow_succ] using hV.2.2.1 _ _ _ _ ih hg
  refine ⟨f, ?_, hf⟩
  unfold _root_.GlobalTheory.Ex.Arch.IsTower
  intro n hn
  obtain ⟨-, hRep, hmul, hmod⟩ := hL n hn
  have hQn := (hG.2.2.2.2 n).2.2
  have hadd : ∀ a b, ∃ e, f n (a + b) = f n a + f n b + n • e := fun a b =>
    (hmod _ _ _ _ (hmul _ _ _ _ (hf n hn a) (hf n hn b)) (hf n hn (a + b))).1 (hT.1 n hn a b)
  refine ⟨hadd, ?_, ?_, ?_, ?_, ?_⟩
  · intro c a
    obtain ⟨Q, hQy, hQg, hQe⟩ := A.I.lin n hn c a
    obtain ⟨p', hp', -⟩ := hRep (c • f n a)
    obtain ⟨hya, hga⟩ := hq n a
    obtain ⟨c'', hc'', -⟩ := hG.1 Q.g
    have hRa := hf n hn a
    have hv := hl.2 c _ _ _ _ _ hga hc'' hQg hRa.2
    rw [map_smul, ← _root_.GlobalTheory.AnArc.degeneratingTori_basePeriodMap_smul] at hv
    have hc : c'' = (p' : Multiplicative A.N.X × A.N.Gt).2 := (hV.1 _).unique hv hp'.2
    have hQp : A.ν.QPt Q p' := by
      refine ⟨?_, hc ▸ hc''⟩
      rw [hp'.1, _root_.GlobalTheory.AnArc.La.smul_y, hl.1, hQy, ← hya, hRa.1]
      unfold _root_.GlobalTheory.Ex.ArcF.act
      simp
    exact (hmod _ _ _ _ hp' (hf n hn (c • a))).1 ((hQn _ _ _ _ hQp (hq n (c • a))).1 hQe)
  · intro a
    obtain ⟨e₀, he₀⟩ : ∃ e, f n 0 = n • e := by
      obtain ⟨e, he⟩ := hadd 0 0
      rw [add_zero] at he
      refine ⟨-e, ?_⟩
      rw [smul_neg, eq_neg_iff_add_eq_zero]
      calc f n 0 + n • e = (f n 0 + f n 0 + n • e) - f n 0 := by abel
        _ = 0 := by rw [← he, sub_self]
    have key : (∃ e, f n 0 = f n a + n • e) ↔ ∃ b, a = n • b := by
      rw [← hmod _ _ _ _ (hf n hn a) (hf n hn 0), ← hQn _ _ _ _ (hq n a) (hq n 0), A.I.ker n hn a 0]
      simp
    rw [← key]
    constructor
    · rintro ⟨e, he⟩
      exact ⟨e₀ - e, by rw [he₀, he, smul_sub]; abel⟩
    · rintro ⟨e, he⟩
      exact ⟨e₀ - e, by rw [smul_sub, ← he₀, he]; abel⟩
  · intro x
    obtain ⟨p, hp, -⟩ := hRep x
    obtain ⟨P, hP⟩ := (hG.2.2.2.2 n).2.1 p
    obtain ⟨a, ha⟩ := A.I.onto n hn P
    obtain ⟨e, he⟩ := (hmod _ _ _ _ (hf n hn a) hp).1 ((hQn _ _ _ _ (hq n a) hP).1 ha)
    exact ⟨a, e, he⟩
  · intro m hm a
    have hnm : 0 < n * m := Nat.mul_pos hn hm
    obtain ⟨p, hp, -⟩ := hRep (f (n * m) a)
    have hR := hf (n * m) hnm a
    have h1 : (p : Multiplicative A.N.X × A.N.Gt).1 = (A.q (n * m) a : Multiplicative A.N.X × A.N.Gt).1 := by
      apply Multiplicative.toAdd.injective
      rw [hp.1, hR.1]
    have h2 : (p : Multiplicative A.N.X × A.N.Gt).2 = (A.q (n * m) a : Multiplicative A.N.X × A.N.Gt).2 ^ m := by
      apply (hV.1 _).unique hp.2
      convert hpow m _ _ hR.2 using 1
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
      congr 1
      have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      have : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
      push_cast
      field_simp
    obtain ⟨e, he⟩ := (hmod _ _ _ _ hp (hf n hn a)).1 (hT.2 n m hn hm a p h1 h2)
    exact ⟨-e, by rw [he, smul_neg]; abel⟩
  · intro a b
    rw [(hW n hn _ _ _ _ _ (hq n a) (hq n b)).1 (A.I.isom n hn a b)]
    exact hE n hn _ _ _ _ (hf n hn a) (hf n hn b)

end GlobalTheory.Ex.Arch
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.Ex.Arch

variable {E : Type} [Field E] [NumberField E]

theorem exists_types (m : (E →+* ℂ) → ℕ) : ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)),
    (∀ φ, Nat.card {i // ty i = φ} = m φ) ∧ ∀ a : E, ∑ i, ty i a = ∑ φ : E →+* ℂ, (m φ : ℂ) * φ a := by
  classical
  let e := (Fintype.equivFin (Σ φ : E →+* ℂ, Fin (m φ))).symm
  refine ⟨_, fun i => (e i).1, fun φ => ?_, fun a => ?_⟩
  · rw [Nat.card_congr (e.subtypeEquiv (q := fun k => k.1 = φ) fun _ => Iff.rfl),
      Nat.card_congr (Equiv.sigmaSubtype φ)]
    simp
  · rw [e.sum_comp fun k => k.1 a, Fintype.sum_sigma]
    simp

theorem trace_eq_sum_finrank {g : ℕ} (ρ : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (a : 𝓞 E) :
    LinearMap.trace ℂ _ (ρ a) = ∑ φ : E →+* ℂ,
      (Module.finrank ℂ (EigenSplit.eigenSub ρ (φ.comp (algebraMap (𝓞 E) E))) : ℂ) * φ (a : E) := by
  obtain ⟨g', ty, hc, hs⟩ :=
    exists_types fun φ : E →+* ℂ => Module.finrank ℂ (EigenSplit.eigenSub ρ (φ.comp (algebraMap (𝓞 E) E)))
  obtain ⟨h, hh⟩ := PointUnif.exists_equiv_of_finrank_eq (PointUnif.isSplitting_embeddings (E := E))
    (PointUnif.diagRep ty) ρ fun φ => by rw [PointUnif.finrank_eigenSub_diagRep, hc]
  have h1 : ρ a = h.conj (PointUnif.diagRep ty a) := LinearMap.ext fun v => by simp [LinearEquiv.conj_apply, hh]
  have h2 : PointUnif.diagRep ty a = Matrix.toLin' (Matrix.diagonal fun i => ty i (a : E)) :=
    LinearMap.ext fun z => funext fun i => by simp [PointUnif.diagRep_apply, Matrix.mulVec_diagonal]
  rw [h1, LinearMap.trace_conj', h2, ← hs]
  simp

theorem typeSt : TypeSt := by
  intro E _ _ _ H D
  let _ := H.starRing
  intro B hB
  classical
  obtain ⟨g, ty, hc, hs⟩ := exists_types fun φ : E →+* ℂ => if φ (H.rt : E) = H.rt0 then D.p else D.q
  have hbar : ∀ a : 𝓞 E, ∑ τ : E →+* ℂ, τ (H.bar a : E) = ∑ τ : E →+* ℂ, τ (a : E) := fun a => by
    refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
    · intro τ _; exact Finset.mem_univ _
    · intro τ _; exact Finset.mem_univ _
    · intro τ _; ext x; simp
    · intro τ _; ext x; simp
    · intro τ _
      rw [H.bar_eq, IsCMField.complexEmbedding_complexConj, ComplexEmbedding.conjugate_coe_eq]
  have := HomTrace.finite_hom B.X
  obtain ⟨h, hh⟩ := PeriodNonempty.exists_diag B.actV ty fun a => by
    let f : (B.X →+ ℂ) →ₗ[ℂ] (B.X →+ ℂ) := LinearMap.fst ℂ _ _ ∘ₗ B.actV a ∘ₗ LinearMap.inl ℂ _ _
    have h1 : B.actV a = f.prodMap (B.F a) := LinearMap.ext fun v => rfl
    rw [h1, LinearMap.trace_prodMap', HomTrace.trace_eq_finrank_mul_sum E B.X (H.bar a) f fun _ _ => rfl, hbar,
      trace_eq_sum_finrank, hs, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun φ _ => ?_
    have h2 : Module.finrank ℂ (EigenSplit.eigenSub B.F (φ.comp (algebraMap (𝓞 E) E))) + Module.finrank (𝓞 E) B.X =
        if φ (H.rt : E) = H.rt0 then D.p else D.q := by
      have h3 := hB (φ.comp (algebraMap (𝓞 E) E))
      by_cases hφ : φ (H.rt : E) = H.rt0
      · rw [if_pos hφ]; exact h3.trans (if_pos hφ)
      · rw [if_neg hφ]; exact h3.trans (if_neg hφ)
    rw [← h2]
    push_cast
    ring
  exact ⟨g, ty, h, fun φ => ⟨fun hφ => (hc φ).trans (if_pos hφ), fun hφ => (hc φ).trans (if_neg hφ)⟩, hh⟩

end GlobalTheory.Ex.Arch

end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

noncomputable section

namespace GlobalTheory.Ex.Arch

theorem exists_pull_endo {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {b : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (hg : IsGrpPullback G' G b φ) (f : G ⟶ G) (hf : IsMonHom f) :
    ∃ f' : G' ⟶ G', IsMonHom f' ∧ f'.left ≫ φ = φ ≫ f.left := by
  have inj : ∀ {T : Over S'} {x y : T ⟶ G'}, pushPt hg.1.w x = pushPt hg.1.w y → x = y := fun {T x y} h =>
    Over.OverMorphism.ext (hg.1.hom_ext (congrArg (fun q => q.left) h) (by rw [Over.w, Over.w]))
  let f' : G' ⟶ G' := Over.homMk (hg.1.lift (φ ≫ f.left) G'.hom
    (by rw [Category.assoc, Over.w, hg.1.w])) (hg.1.lift_snd _ _ _)
  have ha : f'.left ≫ φ = φ ≫ f.left := hg.1.lift_fst _ _ _
  have pa : ∀ {T : Over S'} (x : T ⟶ G'), pushPt hg.1.w (x ≫ f') = pushPt hg.1.w x ≫ f := fun x =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, ha, Category.assoc])
  have pm : ∀ {T : Over S'} (x y : T ⟶ G'), pushPt hg.1.w (x * y) = pushPt hg.1.w x * pushPt hg.1.w y := fun x y =>
    map_mul (pushHom hg _) x y
  refine ⟨f', isMonHom_of_mul _ fun T x y => inj ?_, ha⟩
  rw [pa, pm, pm, pa, pa, MonObj.mul_comp]

theorem fibGrp : FibGrpSt := by
  intro R _ _ _ D J g Λ Hm χ ex fr hF
  obtain ⟨-, P', φ, w, u, hΛ, hg, -, hAH, -, -, hlift, hex, hfr⟩ := hF
  subst hΛ
  obtain ⟨e, he⟩ := LiePull.exists_pushEquiv hg (𝟙_ (Over (Sp ℂ))) (TF (R := R) ℂ).hom (Category.id_comp _).symm
  have hee : ∀ z, ex z = e (u.ex z) := fun z => Over.OverMorphism.ext ((hex z).trans (he _).symm)
  have hadd : ∀ z w, ex (z + w) = ex z * ex w := fun z w => by
    rw [hee, hee, hee, u.ex_add]
    exact map_mul e _ _
  have hker : ∀ z, ex z = 1 ↔ z ∈ u.Λ := fun z => by
    rw [hee, ← u.ker]
    exact e.map_eq_one_iff
  refine ⟨u.discrete, u.full, hAH.1, hAH.2.1, hAH.2.2.1, fun l m => FrameValue.chi_add P'.isLB hAH l m, hadd,
    fun y => ?_, hker, fun l z => ?_, fun f hf => ?_⟩
  · obtain ⟨x, hx⟩ := e.surjective y
    obtain ⟨z, rfl⟩ := u.ex_onto x
    exact ⟨z, (hee z).trans hx⟩
  · have hi := FrameValue.le_chartAt P'.isLB (u.ex z).left
    set i := FrameValue.chartAt P'.isLB (u.ex z).left
    have h₁ : u.ex (z + l) = u.ex z := by rw [u.ex_add, (u.ker _).2 l.2, _root_.mul_one]
    have h₂ : ex (z + l) = ex z := by rw [hee, hee, h₁]
    have a := hfr z i hi
    have b := hfr (z + l) i (by rw [h₁]; exact hi)
    rw [h₁, h₂] at b
    rw [a, b, hAH.2.2.2 l i z hi]
    simp only [hermForm]
    ring
  · obtain ⟨f', hf', hc⟩ := exists_pull_endo hg f hf
    obtain ⟨F, hF⟩ := hlift f' hf'
    have hF' : ∀ z, ex (F z) = ex z ≫ f := fun z => Over.OverMorphism.ext (by
      rw [Over.comp_left, hex, hex, hF, Over.comp_left, Category.assoc, hc, Category.assoc])
    refine ⟨F, hF', fun G hG => ?_⟩
    have hm : ∀ z, (G - F) z ∈ u.Λ := fun z => by
      rw [← hker]
      have h := hadd ((G - F) z) (F z)
      rw [LinearMap.sub_apply, sub_add_cancel, hG, hF'] at h
      exact mul_eq_right.1 h.symm
    haveI := u.discrete
    have hc : Continuous fun w => (⟨(G - F) w, hm w⟩ : u.Λ) :=
      (G - F).continuous_of_finiteDimensional.subtype_mk _
    refine sub_eq_zero.1 (LinearMap.ext fun z => ?_)
    have := PreconnectedSpace.constant inferInstance hc (x := z) (y := 0)
    simpa using congrArg Subtype.val this

end GlobalTheory.Ex.Arch

end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

noncomputable section
namespace GlobalTheory.Ex.Arch.FibSym
open GlobalTheory.FrameValue GlobalTheory.TorusExt GlobalTheory.DegPull

theorem vF_down {A : Over (Sp ℂ)} [GrpObj A] {L' : LB A.left} {g : ℕ} {u : HolUnif A L' g} (hL' : L'.IsLB)
    {X Y Y' : Scheme.{0}} {L : LB X} {Φ : A.left ⟶ X} {K : Type} [Fintype K] {w : LB.Iso L' (L.pull Φ)}
    {φ' : K → (Y' ⟶ A.left)} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y} (hψ : ∀ k, φ' k ≫ Φ = h ≫ φ k)
    {a : LB.Gen (LB.LinComb L' φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)} (ha : a.IsGen) (H : PMaps w φ' φ ε a t h)
    {J : (Sp ℂ ⟶ X) → L.ι} (hJ : ∀ ψ : Sp ℂ ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) {fr : (Fin g → ℂ) → ℂˣ}
    (hfr : ∀ z i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L'.U i →
      (fr z : ℂ) = valAt' (u.ex z).left _ (w.s (fun _ => J ((u.ex z).left ≫ Φ), i)).val * u.fr i z)
    {y : Sp ℂ ⟶ Y'} {z : K → Fin g → ℂ} (hz : IsLift u φ' y z) :
    vF t (y ≫ h) J = genVal u hL' a y z * ∏ k, (fr (z k) : ℂ) ^ ε k := by
  let p : Sp ℂ := IsLocalRing.closedPoint ℂ
  have gJ : ∀ q : Sp ℂ, Good L q J := fun q ψ => hJ ψ trivial
  have gJ' : ∀ q : Sp ℂ, Good L' q (chartAt hL') := fun q ψ => le_chartAt hL' ψ trivial
  have key : ∀ {Z : Scheme.{0}} (x : Sp ℂ ⟶ Z) (U : Z.Opens) (f : Γ(Z, U)ˣ), ⊤ ≤ x ⁻¹ᵁ U →
      (gm x p U f).val = stalkConst p (valAt' x U f.val) := fun x U f hU =>
    (gs_unit x p U (hU trivial) f).symm.trans (gs_eq_stalkConst x p hU _)
  have e := congrArg Units.val (pmaps_val hψ H y p (gJ p) (gJ' p))
  have e₁ : (val t (y ≫ h) p J).val = stalkConst p (vF t (y ≫ h) J) :=
    key _ _ _ (fun q _ => (gJ q).mem φ (y ≫ h))
  have e₂ : (val a y p (chartAt hL')).val = stalkConst p (genVal u hL' a y z *
      GlobalTheory.FrameValue.frameProd u ε z fun k => GlobalTheory.FrameValue.chartAt hL' (y ≫ φ' k)) :=
    (key _ _ _ (le_wchart_chartAt hL' φ' y)).trans (congrArg _ (valAt'_gen hL' ha hz (le_wchart_chartAt hL' φ' y)))
  have hm : ∀ x : Sp ℂ ⟶ A.left, ⊤ ≤ x ⁻¹ᵁ ((L.pull Φ).U (fun _ => J (x ≫ Φ)) ⊓ L'.U (chartAt hL' x)) :=
    fun x q _ => ⟨mem_pull.2 (gJ q (x ≫ Φ)), gJ' q x⟩
  have e₃ : ∀ x : Sp ℂ ⟶ A.left, Geo.Tor.gw w x p (J (x ≫ Φ)) (chartAt hL' x) = stalkUnits p
      (Units.mk0 (valAt' x _ (w.s (fun _ => J (x ≫ Φ), chartAt hL' x)).val)
        (CubeValues.val_unit_ne_zero x SymmetricSemicharacter.valueRules (hm x) _)) := fun x =>
    Units.ext (key x _ _ (hm x))
  rw [Units.val_mul, e₁, e₂] at e
  simp only [e₃, ← map_zpow, ← map_prod] at e
  rw [stalkUnits_val, ← map_mul] at e
  rw [(stalkConst p).injective e, mul_left_comm, GlobalTheory.FrameValue.frameProd, Units.coe_prod, ← Finset.prod_mul_distrib]
  refine congrArg _ (Finset.prod_congr rfl fun k _ => ?_)
  rw [Units.val_zpow_eq_zpow_val, ← mul_zpow, hz k, hfr (z k) _ (le_chartAt hL' _)]
  rfl

theorem exists_sym_pmaps {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] [IsCommMonObj G]
    [IsCommMonObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left} (gp : IsGrpPullback G' G f F) {L : LB G.left}
    {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB) {w : LB.Iso L' (L.pull F)} (hw : PGen w)
    (s : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])) (hs : s.IsGen)
    (hr : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ s (eSec G)) (LB.oneGen L)) :
    ∃ s' : LB.Gen (LB.LinComb L' (K := Fin 2) ![(ι[G']).left, 𝟙 G'.left] ![1, -1]), s'.IsGen ∧
      LB.Gen.Corr L' _ _ _ _ (LB.pullGen L' _ _ s' (eSec G')) (LB.oneGen L') ∧
      (∀ k : Fin 2, ![(ι[G']).left, 𝟙 G'.left] k ≫ F = F ≫ ![(ι[G]).left, 𝟙 G.left] k) ∧ PMaps w _ _ _ s' s F := by
  have hι : (ι[G']).left ≫ F = F ≫ (ι[G]).left := by
    have e := congrArg (fun q => q.left) (map_inv (pushHom gp G') (𝟙 G'))
    simp only [Hom.inv_def, Category.id_comp] at e
    refine Eq.trans e ?_
    show (𝟙 _ ≫ F) ≫ _ = _
    rw [Category.id_comp]
  have hψ : ∀ k : Fin 2, ![(ι[G']).left, 𝟙 G'.left] k ≫ F = F ≫ ![(ι[G]).left, 𝟙 G.left] k := fun k => by
    fin_cases k
    · exact hι
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨s', hs', H⟩ := exists_pmaps hw hL hL' F hψ s hs
  refine ⟨s', hs', corr_of_val hL' fun y J' hJ' => ?_, hψ, H⟩
  obtain ⟨J, hJ⟩ := exists_good' hL y
  have e := pmaps_val hψ H (eSec G') y hJ hJ'
  have e₀ : eSec G' ≫ (ι[G']).left = eSec G' := by
    rw [eSec, ← Over.comp_left]; simp
  have he : eSec G' ≫ F = f ≫ eSec G := (cubeMapOf gp).e_comm
  rw [Fin.prod_univ_two] at e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e₀, Category.comp_id, zpow_one, zpow_neg,
    mul_inv_cancel, _root_.one_mul] at e
  refine (val_pull hJ' _ _ _).trans (Eq.trans ?_ (val_one _).symm)
  rw [Category.id_comp, ← e, he]
  exact (val_pull hJ s (eSec G) f).symm.trans ((val_corr hJ hr f).trans (val_one _))

theorem fibSymSt : Laws → FibSymSt := by
  intro _ R _ _ _ D J g Λ Hm χ ex fr hF
  obtain ⟨hJ, P', φ, w, u, rfl, gp, hw, hAH, -, -, -, hex, hfr⟩ := hF
  obtain ⟨s, hs, hr, hψ, H⟩ := exists_sym_pmaps gp D.P.isLB P'.isLB ((isGen_iff w).1 hw) D.sym D.sym_gen D.sym_rig
  obtain ⟨h₁, h₂⟩ := genVal_sym P'.isLB hAH s hs hr
  refine ⟨fun x => ?_, h₂⟩
  have e := vF_down P'.isLB hψ hs H hJ (fr := fr) (fun z i hi => hex z ▸ hfr z i hi) (isLift_sym u x)
  rw [h₁, Fin.prod_univ_two] at e
  rw [hex x]
  refine (congrArg (· * (fr x : ℂ)) e).trans ?_
  simp

end GlobalTheory.Ex.Arch.FibSym
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

namespace GlobalTheory

theorem exists_desc_of_smooth_of_geometricPoints :
    ∀ (K C : Type) [Field K] [CharZero K] [Field C] [Algebra K C] (X Y : Over (Sp K)), Smooth X.hom → IsSeparated Y.hom → ∀ f : pullback X.hom (spMap (algebraMap K C)) ⟶ Y.left, f ≫ Y.hom = pullback.fst X.hom (spMap (algebraMap K C)) ≫ X.hom → (∀ (F : Type) [Field F] [IsAlgClosed F] (x x' : Sp F ⟶ pullback X.hom (spMap (algebraMap K C))), x ≫ pullback.fst _ _ = x' ≫ pullback.fst _ _ → x ≫ f = x' ≫ f) → ∃ f₀ : X ⟶ Y, pullback.fst X.hom (spMap (algebraMap K C)) ≫ f₀.left = f := by
  intro K C _ _ _ _ X Y hX hY f hf H
  have : IsReduced (pullback X.hom (spMap (algebraMap K C))) :=
    isReduced_of_smooth_of_isReduced (pullback.snd X.hom (spMap (algebraMap K C)))
  obtain ⟨ψ, hψ⟩ := ArcDataDescent.exists_desc_of_points (algebraMap K C)
    (IsPullback.of_hasPullback X.hom (spMap (algebraMap K C))) Y.hom f X.hom hf H
  have f₁ : Flat (spMap (algebraMap K C)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.Flat.of_isField (Field.toIsField K) _
  have f₂ : Surjective (spMap (algebraMap K C)) :=
    ⟨fun y => ⟨(default : PrimeSpectrum C), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  have : Epi (pullback.fst X.hom (spMap (algebraMap K C))) := Flat.epi_of_flat_of_surjective _
  refine ⟨Over.homMk ψ ?_, hψ⟩
  rw [← cancel_epi (pullback.fst X.hom (spMap (algebraMap K C))), ← Category.assoc, hψ]
  exact hf

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

namespace GlobalTheory.Ex.Trait

theorem exists_pelUnif_baseChange : Laws → Laws3 → Laws4 → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R'), AdmBase R I → AdmBase R' I' → ∀ g : R →+* R', Function.Injective g → I.map g ≤ I' → ∀ (t : SAB H (Sp R)) (P : PELUnif I t), ∃ (t' : SAB H (Sp R')) (_ : SABMap t' t (spMap g)) (P' : PELUnif I' t') (ψ : P'.D.toPre.P.A.left ⟶ P.D.toPre.P.A.left), IsGrpPullback P'.D.toPre.P.A P.D.toPre.P.A (spMap g) ψ := by
  intro h1 h3 h4 h5 E _ _ _ H R R' _ _ _ _ I I' hR hR' g hg hI t P
  obtain ⟨t', m₀, P', hD, -⟩ := GlobalTheory.ArcDataDescent.exists_pelUnif_pull h3.cubePull h1.polBaseChange h4.unifBaseChange h5
    hR hR' t P g hg hI
  have := hD.e_hom
  exact ⟨t', m₀, P', hD.e.hom.left ≫ pullback.fst P.D.toPre.P.A.hom (specOf g),
    ((isGrpPullback_of_iso hD.e).comp (isGrpPullback_pullback P.D.toPre.P.A (specOf g))).congr
      (Category.id_comp _) rfl⟩

end GlobalTheory.Ex.Trait
end
