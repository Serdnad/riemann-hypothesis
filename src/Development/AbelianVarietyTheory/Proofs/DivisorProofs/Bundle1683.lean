module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle359
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle391
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle090
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionOfBasicOpenCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1640
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1257
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1363
import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNbhdLieMatrixSmoothCommGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle599
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle644
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1641
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle675
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CharChPartZero
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
import Mathlib.NumberTheory.SelbergSieve
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546

@[expose] public section

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.FinClsLoc

open IsDedekindDomain

theorem eventually_rat_mem_adicCompletionIntegers (q : ℚ) :
    ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite,
      algebraMap ℚ (v.adicCompletion ℚ) q ∈ v.adicCompletionIntegers ℚ := by
  have h := (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q).2
  filter_upwards [h] with v hv
  exact hv

theorem intC_isIntegral : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), ∀ᶠ w : AwayP p in Filter.cofinite,
    ∀ x : w.1.adicCompletion ℚ ⊗[ℚ] G.C, IntC G w x → (∃ f : Polynomial (w.1.adicCompletion ℚ), f.Monic ∧
      (∀ i, f.coeff i ∈ w.1.adicCompletionIntegers ℚ) ∧ Polynomial.aeval x f = 0) := by
  intro p _ G
  set b := Module.finBasis ℚ G.C with hb
  have hev : ∀ᶠ w : AwayP p in Filter.cofinite, ∀ k j l,
      algebraMap ℚ (w.1.adicCompletion ℚ) (b.repr (b k * b j) l) ∈ w.1.adicCompletionIntegers ℚ := by
    rw [Filter.eventually_all]; intro k
    rw [Filter.eventually_all]; intro j
    rw [Filter.eventually_all]; intro l
    exact Subtype.val_injective.tendsto_cofinite.eventually (eventually_rat_mem_adicCompletionIntegers _)
  filter_upwards [hev] with w hw
  intro x hx
  set B := Algebra.TensorProduct.basis (w.1.adicCompletion ℚ) b with hB
  have hent : ∀ i j, Algebra.leftMulMatrix B x i j ∈ w.1.adicCompletionIntegers ℚ := by
    intro i j
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    rw [← B.sum_repr x]

    rw [Finset.sum_mul, map_sum, Finsupp.finsetSum_apply]
    refine sum_mem fun k _ => ?_
    rw [smul_mul_assoc, map_smul, Finsupp.smul_apply, smul_eq_mul]
    have e : B k * B j = (1 : w.1.adicCompletion ℚ) ⊗ₜ[ℚ] (b k * b j) := by
      simp [hB, Algebra.TensorProduct.basis_apply]
    rw [e, Algebra.TensorProduct.basis_repr_tmul]
    simp only [one_smul, Finsupp.mapRange_apply]
    exact mul_mem (hx k) (hw k j i)
  refine ⟨(Algebra.leftMulMatrix B x).charpoly, Matrix.charpoly_monic _, ?_, ?_⟩
  · intro n
    let M : Matrix (Fin (Module.finrank ℚ G.C)) (Fin (Module.finrank ℚ G.C)) (w.1.adicCompletionIntegers ℚ) :=
      fun i j => ⟨_, hent i j⟩
    have hM : Algebra.leftMulMatrix B x = M.map (algebraMap (w.1.adicCompletionIntegers ℚ) (w.1.adicCompletion ℚ)) := by
      ext i j; rfl
    rw [hM, Matrix.charpoly_map, Polynomial.coeff_map]
    exact (M.charpoly.coeff n).2
  · apply Algebra.leftMulMatrix_injective B
    rw [← Polynomial.aeval_algHom_apply, Matrix.aeval_self_charpoly, map_zero]

end GlobalTheory.FinClsLoc
end
end

section

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.CxUnfold

theorem finite_orbits_of_finite_pts : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ), (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g) → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), Set.Finite {q : Pts G v β x t hx Kf K' | ∃ y : grp G β, FixL G v β y (Quot.out q).2.1 ∧ f ((Quot.out q).1.1⁻¹ * toAfF G β x t hx y * (Quot.out q).1.1) * f' ((Quot.out q).1.2⁻¹ * toP1 G β y * (Quot.out q).1.2) ≠ 0} → {o : MulAction.orbitRel.Quotient (grp G β) (GlobalTheory.CxUnfold.Ys G v β x t hx Kf K') | ∃ y, GlobalTheory.CxUnfold.cxF G v wt β x t hx Kf f K' f' (Quotient.out o) y ≠ 0}.Finite := by
  intro p _ G v wt Kf f hfi K' f' hfi' β x t hx hT
  let F : Pts G v β x t hx Kf K' → MulAction.orbitRel.Quotient (grp G β) (Ys G v β x t hx Kf K') :=
    Quot.lift (orbOfDat G v β x t hx Kf K') (fun a b h => orbOfDat_eq_of_same G v β x t hx _ _ h)
  let PL : Pts G v β x t hx Kf K' → Prop :=
    Quot.lift (DatWt G v β x t hx f f') (fun a b h => propext (datWt_iff_of_same G v β x t hx _ _ hfi hfi' h))
  refine (hT.image F).subset ?_
  rintro o ⟨y, hy⟩
  unfold cxF at hy
  split_ifs at hy with hc
  on_goal 2 => exact absurd rfl hy
  let d : Dat G v β := (LeftCosets.rep _ _ (Quotient.out o).1,
    ⟨Projectivization.rep ((Quotient.out o).2 : Projectivization ℂ (Fin G.n → ℂ)), hc.1⟩)
  have hd : DatWt G v β x t hx f f' d := ⟨y, hc.2, left_ne_zero_of_mul hy⟩
  refine ⟨Quot.mk _ d, ?_, ?_⟩
  · have e : PL (Quot.mk _ (Quot.out (Quot.mk (Same G v β x t hx Kf K') d))) = PL (Quot.mk _ d) :=
      congrArg PL (Quot.out_eq _)
    exact (e : DatWt G v β x t hx f f' _ = DatWt G v β x t hx f f' d).mpr hd
  · show orbOfDat G v β x t hx Kf K' d = o
    simp only [orbOfDat, d, LeftCosets.mk_rep]
    convert Quotient.out_eq' o using 2
    exact Prod.ext rfl (Projectivization.mk_rep _)

end GlobalTheory.CxUnfold
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section
open MeasureTheory

namespace GlobalTheory.WeilL2Words

theorem dS_om_eq : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), GlobalTheory.WeilL2Words.IsStdInf F ψ →
    ∀ {G : Type} [Group G] (om : G →* Module.End ℂ ((κ → AdeleRing (𝓞 F) F) → ℂ)),
      (∀ p, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, om p φ ∈ GlobalTheory.WeilM.schA F κ) →
      ∀ (M : G → ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))),
      (∀ p h, ∀ φ ∈ GlobalTheory.WeilM.schA F κ,
        om p (GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F (M p h)) φ) = GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F h) (om p φ)) →
      ∀ (μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _)), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      (∀ p, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, GlobalTheory.WeilL2Words.l2A F μ (om p φ) = GlobalTheory.WeilL2Words.l2A F μ φ) →
      ∀ p h, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, GlobalTheory.WeilL2Words.dS F ψ h (om p φ) = om p (GlobalTheory.WeilL2Words.dS F ψ (M p h) φ) := by
  intro F _ _ _ κ _ ψ hψ G _ om hpres M himpl μ hμ hiso p h φ hφ
  set h' := M p h with hh'
  have hOm : om p φ ∈ GlobalTheory.WeilM.schA F κ := hpres p φ hφ
  have hD1 : GlobalTheory.WeilL2Words.dS F ψ h' φ ∈ GlobalTheory.WeilM.schA F κ := GlobalTheory.WeilL2Words.dS_mem_schA F hψ h' hφ

  set Qr : ℕ → (κ → AdeleRing (𝓞 F) F) → ℂ := fun n => ((n : ℂ) + 1) •
      (GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F (((n : ℝ) + 1)⁻¹ • h')) φ - φ) - GlobalTheory.WeilL2Words.dS F ψ h' φ with hQr
  have hQr_mem : ∀ n, Qr n ∈ GlobalTheory.WeilM.schA F κ := fun n =>
    Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.sub_mem _ (GlobalTheory.T.schroedingerOperator_archimedean_mem_adelicSchwartz F κ ψ hψ _ φ hφ) hφ)) hD1
  set Gn : ℕ → (κ → AdeleRing (𝓞 F) F) → ℂ := fun n a => ((n : ℂ) + 1) *
      (GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F (((n : ℝ) + 1)⁻¹ • h)) (om p φ) a - om p φ a) -
        om p (GlobalTheory.WeilL2Words.dS F ψ h' φ) a with hGn
  have hGQ : ∀ n, Gn n = om p (Qr n) := by
    intro n
    have e := himpl p (((n : ℝ) + 1)⁻¹ • h) φ hφ
    rw [map_smul] at e
    rw [hQr, map_sub, map_smul, map_sub, e]
    funext a
    simp [hGn, smul_eq_mul]
  have hGmem : ∀ n, Gn n ∈ GlobalTheory.WeilM.schA F κ := fun n => by rw [hGQ]; exact hpres p _ (hQr_mem n)
  have hGl2 : Filter.Tendsto (fun n => GlobalTheory.WeilL2Words.l2A F μ (Gn n)) Filter.atTop (nhds 0) := by
    have e : (fun n => GlobalTheory.WeilL2Words.l2A F μ (Gn n)) = fun n => GlobalTheory.WeilL2Words.l2A F μ (Qr n) := by
      funext n; rw [hGQ, hiso p _ (hQr_mem n)]
    rw [e]
    have := GlobalTheory.T.adelic_schwartz_haar_weil F κ ψ hψ μ hμ h' φ hφ
    refine this.congr fun n => ?_
    congr 1
  set D : (κ → AdeleRing (𝓞 F) F) → ℂ := GlobalTheory.WeilL2Words.dS F ψ h (om p φ) - om p (GlobalTheory.WeilL2Words.dS F ψ h' φ) with hD
  have hDmem : D ∈ GlobalTheory.WeilM.schA F κ :=
    Submodule.sub_mem _ (GlobalTheory.WeilL2Words.dS_mem_schA F hψ h hOm) (hpres p _ hD1)
  have hpt : ∀ a, Filter.Tendsto (fun n => Gn n a) Filter.atTop (nhds (D a)) := by
    intro a
    have hd := (GlobalTheory.WeilL2Words.differentiableAt_schr F hψ h hOm a).hasDerivAt
    rw [hasDerivAt_iff_tendsto_slope_zero] at hd
    have ht : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) Filter.atTop (nhdsWithin 0 {0}ᶜ) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Filter.Eventually.of_forall fun n => ?_⟩
      · have h1 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        simpa only [one_div] using h1
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, inv_eq_zero]; positivity
    have h0 : ∀ Ψ : (κ → AdeleRing (𝓞 F) F) → ℂ, GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F ((0 : ℝ) • h)) Ψ a = Ψ a := by
      intro Ψ
      have : GlobalTheory.WeilL2Words.archPair F ((0 : ℝ) • h) = (0, 0) := by
        rw [zero_smul]
        refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> exact GlobalTheory.WeilL2Words.adeleOfMixedSpaceComponent_zero F
      rw [this]
      simp [GlobalTheory.WeilM.schr]
    have := (hd.comp ht).sub_const (om p (GlobalTheory.WeilL2Words.dS F ψ h' φ) a)
    refine this.congr fun n => ?_
    simp only [Function.comp, zero_add, h0, hGn, inv_inv, Complex.real_smul]
    push_cast
    ring
  have hl := GlobalTheory.T.adelic_l2_limit_zero F κ μ D Gn hGmem hpt hGl2
  have hz := GlobalTheory.T.adelic_l2_eq_zero_imp_eq_zero F κ μ hμ D hDmem hl
  exact sub_eq_zero.mp hz

end GlobalTheory.WeilL2Words
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.TrivLocus
open scoped CategoryTheory.Obj

namespace GlobalTheory.TrivLocusLocal


open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison in
theorem exists_gen_pull_pull_iff {X Y Z : Scheme.{0}} (N : LB X) (a : Y ⟶ X) (b : Z ⟶ Y) :
    (∃ s : ((N.pull a).pull b).Gen, s.IsGen) ↔ ∃ s : (N.pull (b ≫ a)).Gen, s.IsGen := by
  have hb : ∀ z : Z, (b ≫ a).base z = a.base (b.base z) := fun z => rfl
  have m1 : ∀ (j : PUnit.{1} → N.ι) (z : Z), z ∈ (N.pull (b ≫ a)).U j →
      z ∈ ((N.pull a).pull b).U (fun _ _ => j PUnit.unit) := by
    intro j z hz
    have h1 : (b ≫ a).base z ∈ N.U (j PUnit.unit) := (mem_wchart_pu N (b ≫ a) j z).1 hz
    have h2 : b.base z ∈ (N.pull a).U (fun _ => j PUnit.unit) :=
      (mem_wchart_pu N a (fun _ => j PUnit.unit) (b.base z)).2 (by rw [← hb]; exact h1)
    exact (mem_wchart_pu (N.pull a) b (fun _ _ => j PUnit.unit) z).2 h2
  have m2 : ∀ (j : PUnit.{1} → PUnit.{1} → N.ι) (z : Z), z ∈ ((N.pull a).pull b).U j →
      z ∈ (N.pull (b ≫ a)).U (fun _ => j PUnit.unit PUnit.unit) := by
    intro j z hz
    have h2 : b.base z ∈ (N.pull a).U (j PUnit.unit) := (mem_wchart_pu (N.pull a) b j z).1 hz
    have h1 : a.base (b.base z) ∈ N.U (j PUnit.unit PUnit.unit) :=
      (mem_wchart_pu N a (j PUnit.unit) (b.base z)).1 h2
    exact (mem_wchart_pu N (b ≫ a) (fun _ => j PUnit.unit PUnit.unit) z).2 (by rw [hb]; exact h1)
  constructor
  · intro h
    refine exists_gen_transfer (L := (N.pull a).pull b) (L' := N.pull (b ≫ a))
      (fun j _ _ => j PUnit.unit) m1 ?_ h
    intro i j y hy
    have hy' := pull_inf_le N (b ≫ a) i j hy
    exact (germ_pull N (b ≫ a) i j y hy hy').trans
      (germ_pull_pull N a b (fun _ _ => i PUnit.unit) (fun _ _ => j PUnit.unit) y ⟨m1 i y hy.1, m1 j y hy.2⟩ hy').symm
  · intro h
    refine exists_gen_transfer (L := N.pull (b ≫ a)) (L' := (N.pull a).pull b)
      (fun j _ => j PUnit.unit PUnit.unit) m2 ?_ h
    intro i j y hy
    have hy2 : y ∈ (N.pull (b ≫ a)).U (fun _ => i PUnit.unit PUnit.unit) ⊓
        (N.pull (b ≫ a)).U (fun _ => j PUnit.unit PUnit.unit) := ⟨m2 i y hy.1, m2 j y hy.2⟩
    have hy' := pull_inf_le N (b ≫ a) _ _ hy2
    exact (germ_pull_pull N a b i j y hy hy').trans (germ_pull N (b ≫ a) _ _ y hy2 hy').symm

end GlobalTheory.TrivLocusLocal

namespace GlobalTheory.TrivLocusLocal

theorem exists_closed_triv_local : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] (L₀ N : LB A.left), IsAbelianScheme A → L₀.IsLB → Out.RelAmple A L₀ → N.IsLB → Out.Rigidified A N → ∀ x : S, ∃ (U : S.Opens) (Z : Scheme.{0}) (i : Z ⟶ U), x ∈ U ∧ IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ U), TrivCond A N T (t ≫ U.ι) ↔ ∃ z : T ⟶ Z, z ≫ i = t := by
  intro S _ A _ L₀ N hA hL₀ ha hN hr x
  obtain ⟨R, j, _, hx, -⟩ := Scheme.exists_affine_mem_range_and_range_subset (x := x) (U := ⊤) trivial
  let j' : Sp R ⟶ S := j
  haveI : IsOpenImmersion j' := inferInstanceAs (IsOpenImmersion j)
  letI : GrpObj ((Over.pullback j').obj A) := Functor.grpObjObj
  let φ₀ := pullback.fst A.hom j'
  have hp := isGrpPullback_pullback A j'
  have hB : IsAbelianScheme ((Over.pullback j').obj A) := Out.TLinPf.isAb_pullback j' A hA
  have hL₀' := pull_isLB hL₀ φ₀
  have haB : Out.RelAmple ((Over.pullback j').obj A) (L₀.pull φ₀) := by
    have := GlobalTheory.KTrivSpread.relAmple_chart j' (𝟙 _) hL₀ ha
    rwa [Category.id_comp] at this
  have hN' := pull_isLB hN φ₀
  have hrB : Out.Rigidified ((Over.pullback j').obj A) (N.pull φ₀) := by
    obtain ⟨s, hs⟩ := hr
    have h1 := exists_gen_pull_comp N (eSec A) j' ⟨s, hs⟩
    rw [← GlobalTheory.RigidBundleGlue.eSec_comm hp] at h1
    exact (exists_gen_pull_pull_iff N φ₀ (eSec ((Over.pullback j').obj A))).2 h1
  obtain ⟨Z, i₀, hi₀, H⟩ := GlobalTheory.T.exists_closed_subscheme_trivial_locus_rigidified R ((Over.pullback j').obj A) (L₀.pull φ₀) (N.pull φ₀) hB hL₀' haB hN' hrB
  refine ⟨j'.opensRange, Z, i₀ ≫ j'.isoOpensRange.hom, hx, inferInstance, fun T t => ?_⟩
  let t' : T ⟶ Sp R := t ≫ j'.isoOpensRange.inv
  have ht : t' ≫ j' = t ≫ j'.opensRange.ι := by
    simp only [t', Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]
  letI : GrpObj ((Over.pullback t').obj ((Over.pullback j').obj A)) := Functor.grpObjObj
  have hq := isGrpPullback_pullback ((Over.pullback j').obj A) t'
  have H1 := H T t' _ _ hq
  have hP : IsPullback (pullback.fst ((Over.pullback j').obj A).hom t' ≫ φ₀)
      (pullback.snd ((Over.pullback j').obj A).hom t') A.hom (t ≫ j'.opensRange.ι) := by
    rw [← ht]
    exact (IsPullback.of_hasPullback ((Over.pullback j').obj A).hom t').paste_horiz
      (IsPullback.of_hasPullback A.hom j')
  rw [← trivCond_iff A N T (t ≫ j'.opensRange.ι) _ _ _ hP, ← exists_gen_pull_pull_iff]
  refine H1.trans ⟨fun ⟨z, hz⟩ => ⟨z, ?_⟩, fun ⟨z, hz⟩ => ⟨z, ?_⟩⟩
  · rw [← Category.assoc, hz]
    simp only [t', Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · simp only [t', ← hz, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end GlobalTheory.TrivLocusLocal
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin

namespace GlobalTheory.UPel.HT.LieLin

theorem decomp_iff_kill : ∀ (O T V : Type) [CommRing O] [CommRing T] [AddCommGroup V] [Module T V]
  (ψ : O →+* Module.End T V) (a : ℕ)
  (τ : Fin a → (O →+* T)), (∀ i j, i ≠ j → Ideal.span (Set.range fun x => τ i x - τ j x) = ⊤) → ∀ v : V,
    ((∃ w : Fin a → V, (∀ i, w i ∈ eigSub ψ (τ i)) ∧ v = ∑ i, w i) ↔
      ∀ c : Fin a → O, (List.ofFn fun i => ψ (c i) - algebraMap T (Module.End T V) (τ i (c i))).prod v = 0) := by
  intro O T V _ _ _ _ ψ a τ hτ v
  constructor
  · rintro ⟨w, hw, hv⟩ c
    exact GlobalTheory.UPel.HT.LieLoc.kill_of_decomp ψ τ v w (fun i c => mem_eigSub.1 (hw i) c) hv c
  · intro h
    obtain ⟨w, hw, hv⟩ := GlobalTheory.UPel.HT.LieLoc.decomp_of_kill ψ τ hτ v h
    exact ⟨w, fun i => mem_eigSub.2 (hw i), hv⟩

end GlobalTheory.UPel.HT.LieLin
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin

theorem _root_.GlobalTheory.T.lieMult_iff_finrank_simultaneousEigenSubmodule : ∀ (O : Type) [CommRing O] (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G]
  (act : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G) (k : Type) [Field k] (t : Sp k ⟶ S) (τ : O →+* k) (m : ℕ),
    Module.Finite k (ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM t G) →
      (LieMult act t τ m ↔ Module.finrank k (eigSub (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR (x0 := t) (S := k) act) τ) = m) := by
  first | exact @GlobalTheory.UPel.HT.LieLin.lieMult_iff_finrank | exact GlobalTheory.UPel.HT.LieLin.lieMult_iff_finrank | (intros; apply GlobalTheory.UPel.HT.LieLin.lieMult_iff_finrank <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin

theorem _root_.GlobalTheory.T.harrisTaylorLieConditionAt_iff_kottwitzModuleCondition : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (S : Scheme.{0})
  (A : Over S) [GrpObj A] [IsCommMonObj A] (act : OActN D.O A) (R' : Type) [CommRing R'] (β : R →+* R')
  (x : Sp R' ⟶ S),
    LieAt b act β x ↔
      LieMod (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR (x0 := x) (S := R') (act.toF D)) D.ω (β b.ρ) (fun i => β.comp (b.t i)) := by
  first | exact @GlobalTheory.UPel.HT.LieLin.lieAt_iff_lieMod | exact GlobalTheory.UPel.HT.LieLin.lieAt_iff_lieMod | (intros; apply GlobalTheory.UPel.HT.LieLin.lieAt_iff_lieMod <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin

theorem _root_.GlobalTheory.T.exists_affine_nbhd_lie_matrix_smooth_comm_group : ∀ (O : Type) [CommRing O] (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], Smooth A.hom →
  ∀ (act : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O A) (z : S),
    ∃ (U : S.Opens) (hU : IsAffineOpen U), z ∈ U ∧ ∃ (n : ℕ) (M : O →+* Matrix (Fin n) (Fin n) Γ(S, U)),
      ∀ (R' : Type) [CommRing R'] (f : Γ(S, U) →+* R'),
        ∃ e : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (spMap f ≫ hU.fromSpec) A ≃ₗ[R'] (Fin n → R'),
          ∀ (c : O) (v : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (spMap f ≫ hU.fromSpec) A),
            e (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR (x0 := spMap f ≫ hU.fromSpec) (S := R') act c v) = matAct M f c (e v) := by
  first | (exact @GlobalTheory.exists_affine_lieMatrix) | (exact GlobalTheory.exists_affine_lieMatrix) | (intros; apply GlobalTheory.exists_affine_lieMatrix  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

theorem _root_.GlobalTheory.T.exists_finiteEtaleScheme_representing_etaleLevels : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), N.Coprime p → IsEtPlace b w0 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s), ∃ (Y : Scheme.{0}) (π : Y ⟶ S) (lu : D.La → (Over.mk π ⟶ o.A)), IsFinite π ∧ Etale π ∧ IsEtLevOver o w0 r lu ∧ ∀ (T : Over S) (l : D.La → (T ⟶ o.A)), IsEtLevOver o w0 r l → ∃! f : T ⟶ Over.mk π, ∀ y, f ≫ lu y = l y := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.exists_etLevScheme) | (exact GlobalTheory.UPel.HT.EtLev.exists_etLevScheme) | (intros; apply GlobalTheory.UPel.HT.EtLev.exists_etLevScheme <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES


theorem _root_.GlobalTheory.T.exists_orderAction_descent_along_isogeny : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → KerStableAt o ψ (𝟙 Y) → ∃ act' : OActN D.O B, ∀ a : D.O, o.act.act a ≫ ψ = ψ ≫ act'.act a := by
  first | (exact @GlobalTheory.UPel.HT.ES.exists_oAct_desc) | (exact GlobalTheory.UPel.HT.ES.exists_oAct_desc) | (intros; apply GlobalTheory.UPel.HT.ES.exists_oAct_desc  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES


theorem _root_.GlobalTheory.T.harrisTaylor_lie_of_quasiInverseIsogeny : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∀ act' : OActN D.O B, (∀ a : D.O, o.act.act a ≫ ψ = ψ ≫ act'.act a) → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Y), x ≫ s = spMap β → ∀ v : epsPtR x ⟶ B, IsTanScal act' x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v → ∃ w : Fin D.a → (epsPtR x ⟶ B), (∀ i, ∀ a : 𝓞 D.F, IsTanScal act' x (algebraMap (𝓞 D.F) D.O a) (β (b.t i a)) (w i)) ∧ v = (List.ofFn w).prod) ∧ (∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ Y) (β : R →+* κ), x ≫ s = spMap β → ∀ i, LieMult (act'.toF D) x (β.comp (b.t i)) D.m) := by
  first | (exact @GlobalTheory.UPel.HT.ES.lie_of_isQuasiInv) | (exact GlobalTheory.UPel.HT.ES.lie_of_isQuasiInv) | (intros; apply GlobalTheory.UPel.HT.ES.lie_of_isQuasiInv  <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
open scoped CategoryTheory.Obj

namespace GlobalTheory.AmpleGen

theorem isRelAcyclic_of_not_NV : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (P : LB A.left),
    (∀ j : ℕ, ¬ NV A P (j + 1)) → GlobalTheory.CxForm.IsRelAcyclic A.hom A.hom P := by
  intro K _ A _ P hP U _ κ _ _ W hW hWU n
  by_cases hU : U = ⊤
  · subst hU
    have hWU' : ⨆ i, W i = ⊤ := by rw [hWU]; simp
    by_contra h
    exact hP n ⟨κ, inferInstance, inferInstance, W, hW, hWU', h⟩
  · have hb : U = ⊥ := by
      refine eq_bot_iff.2 fun x hx => (hU (eq_top_iff.2 fun y _ => ?_)).elim
      have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
      rwa [Subsingleton.elim y x]
    subst hb
    refine HomologicalComplex.ExactAt.of_isZero ?_
    rw [GlobalTheory.AbLaw.cechLB_X, ModuleCat.isZero_iff_subsingleton]
    refine ⟨fun a b => funext fun s => ?_⟩
    refine GlobalTheory.AbLaw.SecOnR.ext_of_cover _ (I := PEmpty) (fun i => i.elim) (fun i => i.elim) ?_ fun i => i.elim
    obtain ⟨i, hi⟩ := Finset.card_pos.1 (by rw [s.2]; exact Nat.succ_pos _ : 0 < s.1.card)
    refine (biInf_le W hi).trans (((le_iSup W i).trans hWU.le).trans ?_)
    simp

end GlobalTheory.AmpleGen
end
end
