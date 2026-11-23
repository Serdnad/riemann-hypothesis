module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle047
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle033
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsPullCubicalOfIso
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle042
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle034
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle002
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle024
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle006
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle015
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle029
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle002
public import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.NumberField.Discriminant.Different
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle009
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle002
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.CM.TripleModel

section Tensor

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {X Y : Over S} {X' Y' : Over S'}

theorem isPullback_tensor {a : X'.left ⟶ X.left} {b : Y'.left ⟶ Y.left} (ha : IsPullback a X'.hom X.hom f)
    (hb : IsPullback b Y'.hom Y.hom f) {c : (X' ⊗ Y').left ⟶ (X ⊗ Y).left}
    (h₁ : c ≫ (fst X Y).left = (fst X' Y').left ≫ a) (h₂ : c ≫ (snd X Y).left = (snd X' Y').left ≫ b) :
    IsPullback c (X' ⊗ Y').hom (X ⊗ Y).hom f := by
  have h : IsPullback (fst X' Y').left (snd X' Y').left X'.hom Y'.hom := .of_hasPullback _ _
  have h₀ : IsPullback (fst X Y).left (snd X Y).left X.hom Y.hom := .of_hasPullback _ _
  have h₃ : IsPullback c (snd X' Y').left (snd X Y).left b := by
    refine IsPullback.of_right ?_ h₂ h₀
    rw [h₁, hb.w]
    exact h.paste_horiz ha
  rw [← Over.w (snd X' Y'), ← Over.w (snd X Y)]
  exact h₃.paste_vert hb

end Tensor

section Cube

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
  [IsCommMonObj G'] {φ : G'.left ⟶ G.left} {M : LB G.left} {M' : LB G'.left}

theorem lbIso_cube_pull (h : IsGrpPullback G' G f φ) (hM : M.IsLB) (hM' : M'.IsLB) (e : LBIso (M.pull φ) M')
    {T' : Over S'} {T : Over S} {n : ℕ} (x' : Fin n → (T' ⟶ G')) (x : Fin n → (T ⟶ G))
    (U : Over.mk (T'.hom ≫ f) ⟶ T) (hx : ∀ i, pushPt h.1.w (x' i) = U ≫ x i) :
    LBIso ((cubeLB G x M).pull U.left) (cubeLB G' x' M') := by
  have hc : (cubeLB G x M).IsLB := DVR.linComb_isLB _ hM _ _
  have h₁ : LBIso ((cubeLB G x M).pull U.left) (cubeLB G' x' (M.pull φ)) :=
    LBIso.chartPull (Geo.Tor.chartPullPull _ _ U.left rfl)
      (chartPullLinComb M _ _ _ _ U.left fun I => psum_push h _ _ U hx I.down) (PolBaseChange.lbIso_refl hc)
  exact LBIso.trans (pull_isLB hc _) (DVR.linComb_isLB _ (pull_isLB hM _) _ _) (DVR.linComb_isLB _ hM' _ _) h₁
    (PowPrimitive.lbIso_linComb e _ _)

theorem lbIso_cube_of_eq (hM : M.IsLB) {T T' : Over S} (ρ : T' ⟶ T) {n : ℕ} (x y : Fin n → (T ⟶ G))
    (h : ∀ i, ρ ≫ x i = ρ ≫ y i) : LBIso ((cubeLB G x M).pull ρ.left) ((cubeLB G y M).pull ρ.left) :=
  LBIso.chartPull (chartPullOut M _ _ ρ.left _ fun I => PrimNorm.psum_pre ρ x (fun i => ρ ≫ x i) (fun _ => rfl) I.down)
    (chartPullOut M _ _ ρ.left _ fun I => PrimNorm.psum_pre ρ y (fun i => ρ ≫ x i) h I.down)
    (PolBaseChange.lbIso_refl (L := cubeLB G (fun i => ρ ≫ x i) M) (DVR.linComb_isLB _ hM _ _))

theorem exists_gen_theta_zero (hM : M.IsLB) :
    ∃ t : LB.Gen ((Theta G M).pull (eSec (G ⊗ G ⊗ G))), t.IsGen := by
  have e : η[G ⊗ G ⊗ G] = lift (1 : 𝟙_ _ ⟶ G) (lift (1 : 𝟙_ _ ⟶ G) (1 : 𝟙_ _ ⟶ G)) := by
    ext <;> simp [Hom.one_def]
  obtain ⟨t, ht⟩ := (PrimNorm.hasGen_iff hM
    (fun I : thK => (lift (1 : 𝟙_ _ ⟶ G) (lift (1 : 𝟙_ _ ⟶ G) (1 : 𝟙_ _ ⟶ G))).left ≫ thφ G (x3 G) I) thε).2
    ((prod_cub _ _ _ (PrimNorm.cls M)).trans (by simp))
  exact gen_chartPull (chartPullOut M (thφ G (x3 G)) thε (eSec (G ⊗ G ⊗ G)) _ fun I => by rw [eSec, e]) t ht

end Cube

theorem exists_gen_of_lbIso {X : Scheme.{0}} {L N : LB X} (hL : L.IsLB) (hN : N.IsLB) (H : LBIso L N)
    (h : ∃ t : L.Gen, t.IsGen) : ∃ t : N.Gen, t.IsGen :=
  (CechPic.iso_triv_iff N).1 (LBIso.trans (LB.isLB_triv X) hL hN ((CechPic.iso_triv_iff L).2 h) H)

theorem exists_triple_of_abelian_model : Out.Laws → (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (t₀ : SAB H (Sp K)) (B : Over (Sp R)) [GrpObj B] (φ : t₀.G.left ⟶ B.left), IsAbelianScheme B → IsGrpPullback t₀.G B (spMap (algebraMap R K)) φ → ∃ (t : SAB H (Sp R)) (m : SABMap t₀ t (spMap (algebraMap R K))) (e : t.G ≅ B), IsMonHom e.hom ∧ m.φ ≫ e.hom.left = φ := by
  intro hL hext E _ _ _ H R K _ _ _ _ _ t₀ B _ φ hB h
  have := hB.comm
  have hB₂ := AbelianSchemeGerms.isAbelianScheme_tensor B B hB hB
  have hB₃ := AbelianSchemeGerms.isAbelianScheme_tensor B _ hB hB₂
  obtain ⟨act, hact⟩ := exists_oAct_extend_dedekind hext R K (𝓞 E) B t₀.G φ hB h t₀.act
  obtain ⟨M, hM⟩ := exists_rigLB_extension_dedekind R K B hB _ φ t₀.G.hom h.1 t₀.PP.L t₀.PP.isLB
  have lb : ∀ {T : Over (Sp R)} {n : ℕ} (x : Fin n → (T ⟶ B)) {L : LB B.left}, L.IsLB → (cubeLB B x L).IsLB :=
    fun x L hL => DVR.linComb_isLB _ hL _ _
  have lb₀ : ∀ {T : Over (Sp K)} {n : ℕ} (x : Fin n → (T ⟶ t₀.G)), (cubeLB t₀.G x t₀.PP.L).IsLB :=
    fun x => DVR.linComb_isLB _ t₀.PP.isLB _ _
  have pa : ∀ {T : Over (Sp K)} (x : T ⟶ t₀.G) a,
      pushPt h.1.w (x ≫ t₀.act.act a) = pushPt h.1.w x ≫ act.act a := fun x a =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hact, Category.assoc])
  let U₂ := lift (pushPt h.1.w (fst t₀.G t₀.G)) (pushPt h.1.w (snd t₀.G t₀.G))
  have p₂ : IsPullback U₂.left (t₀.G ⊗ t₀.G).hom (B ⊗ B).hom (spMap (algebraMap R K)) :=
    isPullback_tensor h.1 h.1
      (congrArg (fun q => q.left) (lift_fst (pushPt h.1.w (fst t₀.G t₀.G)) (pushPt h.1.w (snd t₀.G t₀.G))))
      (congrArg (fun q => q.left) (lift_snd (pushPt h.1.w (fst t₀.G t₀.G)) (pushPt h.1.w (snd t₀.G t₀.G))))
  let U₃ := lift (pushPt h.1.w (x3 t₀.G 0)) (lift (pushPt h.1.w (x3 t₀.G 1)) (pushPt h.1.w (x3 t₀.G 2)))
  have p₃ : IsPullback U₃.left (t₀.G ⊗ t₀.G ⊗ t₀.G).hom (B ⊗ B ⊗ B).hom (spMap (algebraMap R K)) := by
    refine isPullback_tensor h.1 p₂ (congrArg (fun q => q.left) (lift_fst (pushPt h.1.w (x3 t₀.G 0))
        (lift (pushPt h.1.w (x3 t₀.G 1)) (pushPt h.1.w (x3 t₀.G 2)))))
      ((congrArg (fun q => q.left) (lift_snd (pushPt h.1.w (x3 t₀.G 0))
        (lift (pushPt h.1.w (x3 t₀.G 1)) (pushPt h.1.w (x3 t₀.G 2))))).trans ?_)
    apply pullback.hom_ext
    · refine (congrArg (fun q => q.left) (lift_fst (pushPt h.1.w (x3 t₀.G 1)) (pushPt h.1.w (x3 t₀.G 2)))).trans ?_
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (congrArg (fun q => q.left) (lift_fst
        (pushPt h.1.w (fst t₀.G t₀.G)) (pushPt h.1.w (snd t₀.G t₀.G)))).symm)
    · refine (congrArg (fun q => q.left) (lift_snd (pushPt h.1.w (x3 t₀.G 1)) (pushPt h.1.w (x3 t₀.G 2)))).trans ?_
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (congrArg (fun q => q.left) (lift_snd
        (pushPt h.1.w (fst t₀.G t₀.G)) (pushPt h.1.w (snd t₀.G t₀.G)))).symm)
  have hT : ∃ t : LB.Gen (Theta B M.L), t.IsGen :=
    TrivDedekind.exists_gen_of_generic R K (B ⊗ B ⊗ B) hB₃ _ U₃.left _ p₃ (Theta B M.L) (lb _ M.isLB) (exists_gen_theta_zero M.isLB)
      (exists_gen_of_lbIso (lb₀ _) (pull_isLB (lb _ M.isLB) _)
        (lbIso_cube_pull h M.isLB t₀.PP.isLB hM (x3 t₀.G) (x3 B) U₃
          (fun i => by fin_cases i <;> simp [U₃, x3])).symm ⟨t₀.cub.t, t₀.cub.isGen⟩)
  have ha : ∀ a, LBIso (cubeLB B ![fst B B ≫ act.act a, snd B B] M.L)
      (cubeLB B ![fst B B, snd B B ≫ act.act (H.bar a)] M.L) := by
    intro a
    have := act.hom a
    have := act.hom (H.bar a)
    refine IsoDescent.lbIso_of_field R K (algebraMap R K) (IsFractionRing.injective R K) (B ⊗ B) hB₂ _ U₂.left _ p₂ _ _
      (lb _ M.isLB) (lb _ M.isLB) (lbIso_cube_of_eq M.isLB η[B ⊗ B] _ _ fun i => ?_) ?_
    · fin_cases i <;> simp
    · refine LBIso.trans (pull_isLB (lb _ M.isLB) _) (lb₀ _) (pull_isLB (lb _ M.isLB) _)
        (lbIso_cube_pull h M.isLB t₀.PP.isLB hM _ _ U₂ fun i => ?_)
        (LBIso.trans (lb₀ _) (lb₀ _) (pull_isLB (lb _ M.isLB) _) (t₀.adj a)
          (lbIso_cube_pull h M.isLB t₀.PP.isLB hM _ _ U₂ fun i => ?_).symm)
      · fin_cases i
        · exact (pa _ a).trans (by simp [U₂])
        · simp [U₂]
      · fin_cases i
        · simp [U₂]
        · exact (pa _ _).trans (by simp [U₂])
  obtain ⟨PP, cub, sym, hPP, -, prim, adj⟩ :=
    PrimNorm.exists_primitive_normalisation hL.globalFns E H _ B act M.L hB M.isLB hT ha
  let t : SAB H (Sp R) := ⟨B, isSemiAbelian_of_isAbelianScheme B hB, act, PP, cub, sym, adj, prim⟩
  have hφ : LBIso t₀.PP.L (PP.L.pull φ) := by
    let U := pushPt h.1.w (𝟙 t₀.G)
    have eU : U.left = φ := Category.id_comp _
    have h₁ : LBIso ((cubeLB B ![𝟙 B, act.act H.w0] M.L).pull U.left)
        (cubeLB t₀.G ![𝟙 t₀.G, t₀.act.act H.w0] t₀.PP.L) := by
      refine lbIso_cube_pull h M.isLB t₀.PP.isLB hM _ _ U fun i => ?_
      fin_cases i
      · simp [U]
      · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)
    rw [eU] at h₁
    exact LBIso.trans t₀.PP.isLB (lb₀ _) (pull_isLB PP.isLB _) t₀.prim
      (LBIso.trans (lb₀ _) (pull_isLB (lb _ M.isLB) _) (pull_isLB PP.isLB _) h₁.symm
        (PowPrimitive.lbIso_linComb hPP.symm _ _))
  obtain ⟨m, hm⟩ := CartTriple.exists_tripleMap hL.globalFns E H _ _ _ t₀ t φ (PolPull.isAbelianScheme_of_isGrpPullback hB h) h hact hφ
  exact ⟨t, m, Iso.refl B, inferInstanceAs (IsMonHom (𝟙 B)), (Category.comp_id _).trans hm⟩

end GlobalTheory.CM.TripleModel
end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions
open GlobalTheory GlobalTheory.RunIn

noncomputable section

namespace GlobalTheory.WtSizes

theorem extendByZero_le_sum {p : ℕ} (f : Fin p → ℕ) (i : ℕ) : Formalism.L2.Pj.ext0 f i ≤ ∑ k, f k := by
  unfold Formalism.L2.Pj.ext0
  split_ifs with hi
  · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨i, hi⟩ : Fin p))
  · exact Nat.zero_le _

theorem sum_extendByZero_le_sum {p : ℕ} (f : Fin p → ℕ) (m : ℕ) : ∑ i : Fin m, Formalism.L2.Pj.ext0 f i ≤ ∑ k, f k := by
  have h1 : ∑ k, f k = ∑ i : Fin p, Formalism.L2.Pj.ext0 f i :=
    Finset.sum_congr rfl fun i _ => by simp [Formalism.L2.Pj.ext0, i.isLt]
  rw [h1, Fin.sum_univ_eq_sum_range (fun i => Formalism.L2.Pj.ext0 f i) m,
    Fin.sum_univ_eq_sum_range (fun i => Formalism.L2.Pj.ext0 f i) p]
  refine Finset.sum_le_sum_of_ne_zero fun i _ hi => ?_
  rw [Finset.mem_range]
  by_contra hp
  exact hi (by simp [Formalism.L2.Pj.ext0, hp])

variable {D : D7} {j : ℕ}


open Classical in
def tot (w : WeightFamilies.Wt D j) (b : D.host.E →+* ℂ) : ℕ :=
  ∑ t : D.what₂.Tau, ((if b = DV.tauEmb D t then ∑ i, w.aP t i else 0) +
    if b = conjEmb (DV.tauEmb D t) then ∑ i, w.aM t i else 0)

theorem wtA_le_tot (w : WeightFamilies.Wt D j) (b : D.host.E →+* ℂ) (i : ℕ) : wtA w (b, i) ≤ tot w b := by
  unfold wtA tot
  refine Finset.sum_le_sum fun t _ => add_le_add ?_ ?_
  · dsimp only
    split_ifs
    · exact extendByZero_le_sum _ _
    · exact le_rfl
  · dsimp only
    split_ifs
    · exact extendByZero_le_sum _ _
    · exact le_rfl

theorem sum_wtA_le_tot (w : WeightFamilies.Wt D j) (b : D.host.E →+* ℂ) (m : ℕ) :
    ∑ i : Fin m, wtA w (b, i) ≤ tot w b := by
  unfold wtA tot
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun t _ => ?_
  rw [Finset.sum_add_distrib]
  refine add_le_add ?_ ?_
  · dsimp only
    split_ifs
    · exact sum_extendByZero_le_sum _ _
    · simp
  · dsimp only
    split_ifs
    · exact sum_extendByZero_le_sum _ _
    · simp

theorem sum_tot (w : WeightFamilies.Wt D j) :
    ∑ b, tot w b = ∑ t, ((∑ i, w.aP t i) + ∑ i, w.aM t i) := by
  classical
  unfold tot
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

theorem tot_le_size (w : WeightFamilies.Wt D j) :
    ((∑ b, tot w b : ℕ) : ℝ) + ((D.R.f * D.R.r : ℕ) : ℝ) * w.n ≤ w.size := by
  rw [sum_tot]
  unfold WeightFamilies.Wt.size
  push_cast
  have h1 : (1 : ℝ) ≤ max ((D.R.sigW j).2 : ℝ) 1 := le_max_right _ _
  have h2 : (0 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * w.n := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h1 h2]

theorem spread_le {r : ℕ} (hr : 0 < r) (x : Fin r → ℝ) (A B : ℝ) (h1 : ∀ i, x i ≤ A) (h2 : ∀ i, -B ≤ x i) :
    (⨆ i, x i) - ⨅ i, x i ≤ A + B := by
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have := ciSup_le h1
  have := le_ciInf h2
  linarith

theorem invFun_relab (T : Core D) (τ : D.host.E →+* ℂ) : Function.invFun (relab T.Q.c T.σ₀) τ = τ := by
  have h : ∀ τ : D.host.E →+* ℂ, relab T.Q.c T.σ₀ τ = τ := fun τ => RingHom.ext fun _ => rfl
  have h2 : relab T.Q.c T.σ₀ (Function.invFun (relab T.Q.c T.σ₀) τ) = τ := Function.invFun_eq ⟨τ, h τ⟩
  rwa [h] at h2

theorem spread_laU_le (T : Core D) (hr : 0 < D.R.r) (w : WeightFamilies.Wt D j) (k : (T.U j T.σ₀).Comp)
    (τ : ((T.U j T.σ₀).X k).Ψ) :
    ((T.U j T.σ₀).X k).spread (laU (T.U j T.σ₀) (wtA w) w.n k) τ ≤
      (tot w τ.1 : ℝ) + tot w (conjEmb τ.1) + w.n := by
  have hn : ((w.n / 2 : ℕ) : ℝ) + ((w.n / 2 : ℕ) : ℝ) ≤ w.n := by
    have : w.n / 2 + w.n / 2 ≤ w.n := by omega
    exact_mod_cast this
  have key : ∀ i, -((tot w (conjEmb τ.1) : ℤ) + ((w.n / 2 : ℕ) : ℤ)) ≤ laU (T.U j T.σ₀) (wtA w) w.n k τ i ∧
      laU (T.U j T.σ₀) (wtA w) w.n k τ i ≤ (tot w τ.1 : ℤ) + ((w.n / 2 : ℕ) : ℤ) := by
    intro i
    unfold laU
    rw [invFun_relab, invFun_relab]
    have a1 := wtA_le_tot w τ.1 ((i : ℕ) - ((T.U j T.σ₀).X k).p0)
    have a2 := wtA_le_tot w (conjEmb τ.1) (((T.U j T.σ₀).X k).p0 - 1 - (i : ℕ))
    split_ifs <;> constructor <;> omega
  refine (spread_le hr _ ((tot w τ.1 : ℝ) + ((w.n / 2 : ℕ) : ℝ))
    ((tot w (conjEmb τ.1) : ℝ) + ((w.n / 2 : ℕ) : ℝ)) (fun i => ?_) (fun i => ?_)).trans (by linarith)
  · have h1 := (Int.cast_le (R := ℝ)).2 (key i).2
    rwa [Int.cast_add, Int.cast_natCast, Int.cast_natCast] at h1
  · exact_mod_cast (key i).1

theorem sum_cm_le {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (B : (E →+* ℂ) → ℕ) : ∑ τ : X.Ψ, (B τ.1 + B (conjEmb τ.1)) ≤ ∑ b, B b := by
  classical
  have hcc : ∀ τ : E →+* ℂ, conjEmb (conjEmb τ) = τ := fun τ => RingHom.ext fun x => by simp [conjEmb]
  have hinj : Function.Injective (conjEmb : (E →+* ℂ) → (E →+* ℂ)) := Function.LeftInverse.injective hcc
  rw [Finset.sum_add_distrib, Finset.sum_coe_sort X.Ψ B, Finset.sum_coe_sort X.Ψ (fun τ => B (conjEmb τ)),
    ← Finset.sum_image (f := B) (g := conjEmb) (s := X.Ψ) hinj.injOn, ← Finset.sum_add_sum_compl X.Ψ B]
  refine Nat.add_le_add_left (Finset.sum_le_sum_of_subset fun b hb => ?_) _
  obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.1 hb
  rw [Finset.mem_compl]
  exact (X.cmType τ).1 hτ

theorem fdeg_eq (D : D7) : fdeg D.host.E = D.R.f := by
  unfold fdeg
  rw [hostSize_finrank]
  omega

theorem one_le_dE (D : D7) : 1 ≤ dE D.host.E := by
  unfold dE
  have h : (1 : ℤ) ≤ |NumberField.discr D.host.E| := Int.one_le_abs (NumberField.discr_ne_zero _)
  exact_mod_cast h

theorem sqrt_le_dE (D : D7) : Real.sqrt D.host.d ≤ dE D.host.E := by
  have h1 : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ D.host.rdE :=
    (UpperTheory.KR.log_qd_le_rd D.host.toHostAx D.host.flPS).2.2.1
  have hq : (1 : ℝ) ≤ D.host.q := by exact_mod_cast D.host.hyp.1.one_lt.le
  have h2 : Real.sqrt D.host.d ≤ Real.sqrt ((D.host.q : ℝ) * D.host.d) :=
    Real.sqrt_le_sqrt (le_mul_of_one_le_left (Nat.cast_nonneg _) hq)
  have h4 : D.host.rdE ≤ dE D.host.E := by
    have h5 : (1 : ℝ) ≤ (Module.finrank ℚ D.host.E : ℝ) := by
      have : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
      exact_mod_cast this
    exact Real.rpow_le_self_of_one_le (one_le_dE D) ((div_le_one (by linarith)).2 h5)
  linarith

theorem sizes : ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ), InR D j → ∀ w : WeightFamilies.Wt D j, 0 < D.R.r ∧ (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r ∧ fdeg D.host.E = D.R.f ∧ Real.sqrt D.host.d ≤ dE D.host.E ∧ 1 ≤ dE D.host.E ∧ Real.log (dE D.host.E) = logdE D ∧ (∀ k, (∑ τ, ((T.U j T.σ₀).X k).spread (laU (T.U j T.σ₀) (wtA w) w.n k) τ) ≤ w.size) ∧ ((∑ b : D.host.E →+* ℂ, ∑ i : Fin ((T.Q.Dw j).mult b), wtA w (b, i) : ℕ) : ℝ) + ((D.R.f * D.R.r : ℕ) : ℝ) * w.n ≤ w.size := by
  intro D T h j hj w
  have hr : 0 < D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Ranks.r
    omega
  have hts := tot_le_size w
  refine ⟨hr, (h.unf j hj T.σ₀ T.good_σ₀).1.symm, fdeg_eq D, sqrt_le_dE D, one_le_dE D, rfl, fun k => ?_, ?_⟩
  · refine (Finset.sum_le_sum fun τ _ => spread_laU_le T hr w k τ).trans (le_trans ?_ hts)
    rw [Finset.sum_add_distrib]
    refine add_le_add ?_ ?_
    · exact_mod_cast sum_cm_le ((T.U j T.σ₀).X k) (tot w)
    · rw [Finset.sum_const, Finset.card_univ, QuadraticCoefficientForms.card_Psi (X := (T.U j T.σ₀).X k), fdeg_eq, nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
      exact_mod_cast Nat.le_mul_of_pos_right _ hr
  · refine le_trans (add_le_add ?_ le_rfl) hts
    exact_mod_cast Finset.sum_le_sum fun b _ => sum_wtA_le_tot w b _

end GlobalTheory.WtSizes
end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory.LatticeData

theorem cc_eq_conj (D : D7) (x : D.host.E) : ReciprocityTheory.ChartRestriction.G.FD.cc x = D.host.conj x :=
  bridge_star_holds D.R D.host x

theorem flagDomainConj_hostXi_eq_neg (D : D7) : ReciprocityTheory.ChartRestriction.G.FD.cc D.host.xi0 = -D.host.xi0 :=
  conj_xi0_alt D

theorem halfDifferent_ne_bot (D : D7) : D.host.𝔟 ≠ ⊥ := by
  intro h
  exact (bB_ne D).1 (by rw [h]; simp)

theorem absNorm_halfDifferent_le (D : D7) :
    (Ideal.absNorm D.host.𝔟 : ℝ) ≤ |(NumberField.discr D.host.E : ℝ)| := by
  have ht : differentIdeal ℤ (𝓞 D.host.E) = differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) *
      (differentIdeal ℤ (𝓞 D.host.K)).map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) :=
    differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 D.host.K) (𝓞 D.host.E)
  have hdvd : D.host.𝔟 ∣ differentIdeal ℤ (𝓞 D.host.E) := by
    rw [ht, D.host.𝔟_spec.1, mul_assoc]
    exact dvd_mul_right _ _
  have h1 := map_dvd Ideal.absNorm hdvd
  rw [NumberField.absNorm_differentIdeal D.host.E (𝓞 D.host.E)] at h1
  have h2 := Nat.le_of_dvd (Int.natAbs_pos.2 (NumberField.discr_ne_zero D.host.E)) h1
  rw [← Int.cast_abs, ← Nat.cast_natAbs]
  exact_mod_cast h2

theorem absNorm_mul_mem_one (D : D7) {a : D.host.E} (ha : a ∈ D.host.AA) :
    ∃ z : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E z = (Ideal.absNorm D.host.𝔟 : D.host.E) * a := by
  unfold Formalism.BasicNotions.Host.AA Formalism.BasicNotions.Host.AA0 at ha
  rw [← div_eq_mul_inv, FractionalIdeal.mem_div_iff_of_ne_zero (bB_ne D).1] at ha
  obtain ⟨w, -, hw⟩ := (FractionalIdeal.mem_coeIdeal _).1
    (ha _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, Ideal.absNorm_mem D.host.𝔟, rfl⟩))
  exact ⟨w, by rw [hw, map_natCast, mul_comm]⟩

theorem absNorm_ccK_mem (D : D7) : (Ideal.absNorm D.host.ccK : D.host.E) ∈ D.host.AA := by
  unfold Formalism.BasicNotions.Host.AA Formalism.BasicNotions.Host.AA0
  rw [← div_eq_mul_inv, FractionalIdeal.mem_div_iff_of_ne_zero (bB_ne D).1]
  intro y hy
  obtain ⟨z, -, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
  have h : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∈ D.host.ccE := by
    have := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) (Ideal.absNorm_mem D.host.ccK)
    rwa [map_natCast] at this
  exact (FractionalIdeal.mem_coeIdeal _).2 ⟨_, Ideal.mul_mem_right z _ h, by rw [map_mul, map_natCast]⟩

theorem exists_dataX_of_hasPrinc : ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (hj : InR D j), ∀ σ, GoodEmb T.Q.c σ → GlobalTheory.FrameNorm.HasPrinc (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) T.Q.l.M → ∀ k : (T.U j σ).Comp, ∃ Xx : ReciprocityTheory.ChartRestriction.G.FD.DataX D.host.E D.R.r, Xx.toData = (T.U j σ).X k ∧ Xx.g = T.Q.l.M ∧ Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ Xx.L', v = a • u} ∧ Xx.k0 = 2 * xiR D ∧ (Xx.NA : ℝ) ≤ |(NumberField.discr D.host.E : ℝ)| ∧ Xx.NC ≤ Ideal.absNorm D.host.ccK := by
  intro D T h j hj σ hσ hP k
  obtain ⟨-, -, -, hx0, hx1, -⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  have habs := h.xiAbs j hj σ hσ k
  have hperf := GlobalTheory.traceForm_integral_perfect_of_isUnf _ _ _ _ _ _ σ _ (Formalism.L2.PjFree.Unf.ofPj (T.U j σ))
    ((Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf j hj σ hσ)) k
  have hξ := GlobalTheory.eq_or_eq_neg_of_purelyImaginary_of_norm_eq _ D.host.xi0 ((T.U j σ).X k).ξ0 D.host.φ₀
    (flagDomainConj_hostXi_eq_neg D) ((T.U j σ).X k).ξ0_im (habs _).symm
  have hone : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) ((T.U j σ).X k).ξ0 * D.host.AA *
      D.host.AAbar * (differentIdeal ℤ (𝓞 D.host.E) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) = 1 := by
    have h1 := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
    rcases hξ with e | e
    · rw [e]; exact h1
    · rw [e, show -D.host.xi0 = (-1 : (𝓞 D.host.E)ˣ) • D.host.xi0 by simp,
        ← (FractionalIdeal.spanSingleton_eq_spanSingleton.2 ⟨-1, rfl⟩)]
      exact h1
  have hM : 0 < T.Q.l.M := by have := T.Q.l.three_le; omega
  obtain ⟨Xx, h1, h2, h3⟩ := GlobalTheory.exists_dataX_of_perfect_traceForm _ _ ((T.U j σ).X k) D.host.AA D.host.AAbar
    (xiR D) T.Q.l.M
    (fun a => by
      rw [cc_eq_conj]
      exact ⟨conj_mem_AA D, fun ha => by simpa only [conj_conj] using conj_mem_AAbar D ha⟩)
    hone habs hx1 hperf.1 hperf.2 hM (hP k)
  refine ⟨{ Xx with
    k0 := 2 * xiR D
    minWeight_pos := by positivity
    k0_le := by linarith
    ξ0_abs := fun τ => by rw [show Xx.ξ0 = ((T.U j σ).X k).ξ0 from congrArg _ h1, habs]; ring
    NA := Ideal.absNorm D.host.𝔟
    NC := Ideal.absNorm D.host.ccK
    NA_pos := Nat.pos_of_ne_zero fun e => halfDifferent_ne_bot D (Ideal.absNorm_eq_zero_iff.1 e)
    NC_pos := Nat.pos_of_ne_zero fun e => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 e)
    NA_sub := fun x hx => ?_
    NC_sub := fun x hx => ?_ }, h1, h2, h3, rfl, absNorm_halfDifferent_le D, le_rfl⟩
  · rw [h3] at hx
    induction hx using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, ha, u, hu, rfl⟩ := hv
      obtain ⟨z, hz⟩ := absNorm_mul_mem_one D ha
      rw [smul_smul, ← hz, algebraMap_smul]
      exact Xx.L'.smul_mem z hu
    | zero => simp
    | add v w _ _ hv hw => rw [smul_add]; exact add_mem hv hw
    | smul c v _ hv => rw [smul_comm]; exact Xx.L'.smul_mem c hv
  · rw [h3]
    exact Submodule.subset_span ⟨_, absNorm_ccK_mem D, x, hx, rfl⟩

end GlobalTheory.LatticeData
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.exists_triple_of_abelian_model_dedekind : Out.Laws → (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (t₀ : SAB H (Sp K)) (B : Over (Sp R)) [GrpObj B] (φ : t₀.G.left ⟶ B.left), IsAbelianScheme B → IsGrpPullback t₀.G B (spMap (algebraMap R K)) φ → ∃ (t : SAB H (Sp R)) (m : SABMap t₀ t (spMap (algebraMap R K))) (e : t.G ≅ B), IsMonHom e.hom ∧ m.φ ≫ e.hom.left = φ := by
  first | exact @GlobalTheory.CM.TripleModel.exists_triple_of_abelian_model | exact GlobalTheory.CM.TripleModel.exists_triple_of_abelian_model | (intros; apply GlobalTheory.CM.TripleModel.exists_triple_of_abelian_model <;> assumption)

end
end
