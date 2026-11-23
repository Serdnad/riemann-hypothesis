module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle418
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalLetter
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle423
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle201
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.PullRep

def plU {X Y : Scheme.{0}} (f : Y ⟶ X) {U : X.Opens} {W : Y.Opens} (h : W ≤ f ⁻¹ᵁ U) :
    Γ(X, U)ˣ →* Γ(Y, W)ˣ := (res h).comp (pullU f U)

theorem res_plU {X Y : Scheme.{0}} (f : Y ⟶ X) {U : X.Opens} {W V : Y.Opens} (h : W ≤ f ⁻¹ᵁ U)
    (l : V ≤ W) (x : Γ(X, U)ˣ) : res l (plU f h x) = plU f (l.trans h) x :=
  Units.ext (resG_appLE f h l (x : Γ(X, U)))

theorem plU_res {X Y : Scheme.{0}} (f : Y ⟶ X) {U U' : X.Opens} {W : Y.Opens} (l : U' ≤ U)
    (h : W ≤ f ⁻¹ᵁ U') (x : Γ(X, U)ˣ) : plU f h (res l x) = plU f (h.trans (f.preimage_mono l)) x :=
  Units.ext (appLE_resG f l h (x : Γ(X, U)))

theorem plU_plU {X Y Z : Scheme.{0}} (g : Z ⟶ Y) (f : Y ⟶ X) {U : X.Opens} {V : Y.Opens} {W : Z.Opens}
    (h : V ≤ f ⁻¹ᵁ U) (h' : W ≤ g ⁻¹ᵁ V) (x : Γ(X, U)ˣ) :
    plU g h' (plU f h x) = plU (g ≫ f) (h'.trans (g.preimage_mono h)) x :=
  Units.ext (appLE_appLE g f h h' (x : Γ(X, U)))

theorem lbPull_g {X Y : Scheme.{0}} (B : LB X) (f : Y ⟶ X) (i j : PUnit → B.ι) :
    (B.pull f).g i j = plU f (le_inf (inf_le_left.trans (LB.wchart_le B (fun _ => f) i PUnit.unit))
      (inf_le_right.trans (LB.wchart_le B (fun _ => f) j PUnit.unit)) :
        (B.pull f).U i ⊓ (B.pull f).U j ≤ f ⁻¹ᵁ (B.U (i PUnit.unit) ⊓ B.U (j PUnit.unit)))
      (B.g (i PUnit.unit) (j PUnit.unit)) := by
  show ∏ k : PUnit, (plU f _ (B.g (i k) (j k))) ^ ((fun _ => (1 : ℤ)) k) = _
  rw [Fintype.prod_unique]
  exact zpow_one _

variable {n' m : ℕ} {n : Fin (m + 1) → ℕ}

abbrev qq (n' m : ℕ) (n : Fin (m + 1) → ℕ) : MP ℤ (m + 1) (consN n' n) ⟶ MP ℤ m n := qpSnd n' m n

theorem qq_str (n' m : ℕ) (n : Fin (m + 1) → ℕ) : qq n' m n ≫ mpStr ℤ m n = mpStr ℤ (m + 1) (consN n' n) :=
  qpSnd_str n' m n

def tl (c : ∀ k, Bk (consN n' n) k) : ∀ k, Bk n k := fun k => c k.succ

theorem mchart_le_pull (c : ∀ k, Bk (consN n' n) k) :
    mchart c ≤ qq n' m n ⁻¹ᵁ mchart (tl c) :=
  fun _ hx => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k.succ

theorem pullDeg_zero (a : Fin (m + 1) → ℤ) : pullDeg (Fin.succ : Fin (m + 1) → Fin (m + 2)) a 0 = 0 := by
  unfold pullDeg
  rw [Function.extend_apply']
  · rfl
  · rintro ⟨k, hk⟩
    exact Fin.succ_ne_zero k hk

theorem pullDeg_succ (a : Fin (m + 1) → ℤ) (k : Fin (m + 1)) :
    pullDeg (Fin.succ : Fin (m + 1) → Fin (m + 2)) a k.succ = a k :=
  (Fin.succ_injective _).extend_apply _ _ _

theorem blockUnit_succ {k : Fin (m + 1)} (i j : Bk n k) {W : (MP ℤ (m + 1) (consN n' n)).Opens}
    {W₀ : (MP ℤ m n).Opens} (h : W ≤ prB (consN n' n) k.succ ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j))
    (H : W ≤ qq n' m n ⁻¹ᵁ W₀) (h₀ : W₀ ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j)) :
    blockUnit (n := consN n' n) (k := k.succ) i j h = plU (qq n' m n) H (blockUnit i j h₀) :=
  (plU_plU (qq n' m n) (prB n k) h₀ H _).symm

theorem prod_blockUnit (c c' : ∀ k, Bk (consN n' n) k) {W : (MP ℤ (m + 1) (consN n' n)).Opens}
    {V : (MP ℤ m n).Opens} (HV : W ≤ qq n' m n ⁻¹ᵁ V) (hW : W ≤ mchart c ⊓ mchart c')
    (hV : V ≤ mchart (tl c) ⊓ mchart (tl c')) (a : Fin (m + 1) → ℤ) :
    ∏ k, blockUnit (c k) (c' k) (fun _ hx => ⟨mchart_le c k (hW hx).1, mchart_le c' k (hW hx).2⟩ :
        W ≤ prB (consN n' n) k ⁻¹ᵁ (chart ℤ (consN n' n k) (c k) ⊓ chart ℤ (consN n' n k) (c' k))) ^
          pullDeg (Fin.succ : Fin (m + 1) → Fin (m + 2)) a k =
      plU (qq n' m n) HV (∏ k, blockUnit (tl c k) (tl c' k)
        (fun _ hx => ⟨mchart_le (tl c) k (hV hx).1, mchart_le (tl c') k (hV hx).2⟩ :
          V ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (tl c k) ⊓ chart ℤ (n k) (tl c' k))) ^ a k) := by
  rw [map_prod, Fin.prod_univ_succ, pullDeg_zero, zpow_zero, one_mul]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow, pullDeg_succ]
  exact congrArg (· ^ a k) (blockUnit_succ _ _ _ HV _)

theorem prod_norm_pull (z : (Σ k, Bk (consN n' n) k) → ℂ) (c : ∀ k, Bk (consN n' n) k) (a : Fin (m + 1) → ℤ) :
    ∏ k, ‖z ⟨k, c k⟩‖ ^ pullDeg (Fin.succ : Fin (m + 1) → Fin (m + 2)) a k =
      ∏ k, ‖z (sv n' n ⟨k, tl c k⟩)‖ ^ a k := by
  rw [Fin.prod_univ_succ, pullDeg_zero, zpow_zero, one_mul]
  simp only [pullDeg_succ]
  rfl

theorem isUnder_map {y' : CxPts (mpStr ℤ (m + 1) (consN n' n)) σ₀} {z' : (Σ k, Bk (consN n' n) k) → ℂ}
    (h : IsUnder y' z') :
    IsUnder (Points.PtsOver.map (qq n' m n) (qq_str n' m n) _ y') (fun p => z' (sv n' n p)) := by
  intro k i
  refine ⟨(h k.succ i).1, fun j hy => ?_⟩
  have e := (h k.succ i).2 j hy
  calc CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k i) (pullRatio (prB n k) _ i le_rfl j)
        (Points.PtsOver.map (qq n' m n) (qq_str n' m n) _ y')
      = CxPts.ev (mpStr ℤ (m + 1) (consN n' n)) σ₀ (qq n' m n ⁻¹ᵁ blockChart n k i)
          ((qq n' m n).app _ (pullRatio (prB n k) _ i le_rfl j)) y' :=
        (ev_app (qq n' m n) (qq_str n' m n) _ _ y').symm
    _ = CxPts.ev (mpStr ℤ (m + 1) (consN n' n)) σ₀ (qq n' m n ⁻¹ᵁ blockChart n k i)
          (pullRatio (qq n' m n ≫ prB n k) _ i le_rfl j) y' := by
        rw [Scheme.Hom.app_eq_appLE, appLE_pullRatio]
    _ = _ := e

theorem ev_plU {y' : CxPts (mpStr ℤ (m + 1) (consN n' n)) σ₀} {U : (MP ℤ m n).Opens}
    {W : (MP ℤ (m + 1) (consN n' n)).Opens} (H : W ≤ qq n' m n ⁻¹ᵁ U)
    (hy : y' ∈ ptsIn (mpStr ℤ (m + 1) (consN n' n)) σ₀ W) (x : Γ(MP ℤ m n, U)ˣ) :
    CxPts.ev (mpStr ℤ (m + 1) (consN n' n)) σ₀ W (plU (qq n' m n) H x : Γ(MP ℤ (m + 1) (consN n' n), W)) y' =
      CxPts.ev (mpStr ℤ m n) σ₀ U (x : Γ(MP ℤ m n, U)) (Points.PtsOver.map (qq n' m n) (qq_str n' m n) _ y') :=
  (ev_res H hy _).trans (ev_app (qq n' m n) (qq_str n' m n) U _ y')

end GlobalTheory.CompanionTheory.MPDict.PullRep

namespace GlobalTheory.CompanionTheory.MPDict

open GlobalTheory.CompanionTheory.MPDict.PullRep

theorem isHermRep_pull (n' m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)) (A : Geo.HermLine (Bk n))
    (hM : IsHermRep M A) :
    IsHermRep (m := m + 1) (n := consN n' n) (M.pull (qpSnd n' m n) (qpSnd_str n' m n)) (pullLine n' A) := by
  show IsHermRep (M.pull (qq n' m n) (qq_str n' m n)) (pullLine n' A)
  obtain ⟨u, h1, h2, h3⟩ := hM
  have Hu : ∀ (i : PUnit → M.B.ι) (c : ∀ k, Bk (consN n' n) k),
      (M.pull (qq n' m n) (qq_str n' m n)).B.U i ⊓ mchart c ≤
        qq n' m n ⁻¹ᵁ (M.B.U (i PUnit.unit) ⊓ mchart (tl c)) := fun i c x hx =>
    ⟨LB.wchart_le M.B (fun _ => qq n' m n) i PUnit.unit hx.1, mchart_le_pull c hx.2⟩
  refine ⟨fun i c => plU (qq n' m n) (Hu i c) (u (i PUnit.unit) (tl c)), ?_, ?_, ?_⟩
  · intro i j c
    have HV : (M.pull (qq n' m n) (qq_str n' m n)).B.U i ⊓
        (M.pull (qq n' m n) (qq_str n' m n)).B.U j ⊓ mchart c ≤
          qq n' m n ⁻¹ᵁ (M.B.U (i PUnit.unit) ⊓ M.B.U (j PUnit.unit) ⊓ mchart (tl c)) := fun x hx =>
      ⟨⟨LB.wchart_le M.B (fun _ => qq n' m n) i PUnit.unit hx.1.1,
        LB.wchart_le M.B (fun _ => qq n' m n) j PUnit.unit hx.1.2⟩, mchart_le_pull c hx.2⟩
    have e := congrArg (plU (qq n' m n) HV) (h1 (i PUnit.unit) (j PUnit.unit) (tl c))
    rw [map_mul, plU_res, plU_res, plU_res] at e
    exact (res_plU _ _ _ _).trans (e.trans (congrArg₂ (· * ·)
      ((congrArg (Semi.res _) (lbPull_g M.B (qq n' m n) i j)).trans (res_plU _ _ _ _)).symm
      (res_plU _ _ _ _).symm))
  · intro i c c'
    have HV : (M.pull (qq n' m n) (qq_str n' m n)).B.U i ⊓
        (mchart c ⊓ mchart c') ≤ qq n' m n ⁻¹ᵁ (M.B.U (i PUnit.unit) ⊓ (mchart (tl c) ⊓ mchart (tl c'))) :=
      fun x hx => ⟨LB.wchart_le M.B (fun _ => qq n' m n) i PUnit.unit hx.1, mchart_le_pull c hx.2.1,
        mchart_le_pull c' hx.2.2⟩
    have e := congrArg (plU (qq n' m n) HV) (h2 (i PUnit.unit) (tl c) (tl c'))
    rw [map_mul, plU_res, plU_res] at e
    rw [res_plU, res_plU]
    refine e.trans (congrArg₂ (· * ·) rfl ?_)
    exact (prod_blockUnit c c' HV (fun _ hx => hx.2) (fun _ hx => hx.2) A.a).symm
  · intro i c y z hz hy
    have hy0 : Points.PtsOver.map (qq n' m n) (qq_str n' m n) _ y ∈
        ptsIn (mpStr ℤ m n) σ₀ (M.B.U (i PUnit.unit) ⊓ mchart (tl c)) :=
      Points.le_preimage_comp y.1 (qq n' m n) (Hu i c) hy
    have e := h3 (i PUnit.unit) (tl c) _ _ (isUnder_map hz) hy0
    have ev_e := ev_plU (Hu i c) hy (u (i PUnit.unit) (tl c))
    have φ_e := (M.φ σ₀).pull_φ (qq n' m n) (qq_str n' m n) i y
    show A.h (fun p => z (sv n' n p)) = _
    rw [e]
    refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (prod_norm_pull z c A.a).symm ?_) ?_
    · exact congrArg (‖·‖) ev_e.symm
    · exact congrArg (fun t => Real.exp (t / 2)) φ_e.symm

end GlobalTheory.CompanionTheory.MPDict
end
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical

theorem _root_.GlobalTheory.T.local_character_induced_tied : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), Formalism.ConjugateSelfDual.IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (ReciprocityTheory.Gal.Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw →
    ∀ (LL' : FinExt l), Bw.LL.1 ≤ LL'.1 → ∀ (ψ₁ ψ₂ : ↥(ReciprocityTheory.Gal.Dec (F := E) A) →* (↥LL'.1)ˣ)
      (J₁ J₂ : (↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) → ℤ),
      PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' ψ₁ J₁ → PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' ψ₂ J₂ →
      PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' (ψ₁ * ψ₂) (J₁ + J₂) := by
  exact @GlobalTheory.CompanionTheory.HLCMul.isdRJ_mul
end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

noncomputable section

namespace GlobalTheory.CompanionTheory.BZMir

section Groups

variable {k : Type} [Field k]

theorem blk_stdBlocks_two {n N : ℕ} (h : ∑ c, ![n, N - n] c = N) (i : Fin N) :
    blk (stdBlocks ![n, N - n] h) i = if (i : ℕ) < n then 0 else 1 := by
  obtain ⟨⟨c, i'⟩, rfl⟩ := (stdBlocks ![n, N - n] h).surjective i
  rw [blk_apply]
  have := stdBlocks_val ![n, N - n] h c i'
  fin_cases c
  · have hi := i'.2
    simp at this hi ⊢
    omega
  · have hi := i'.2
    simp at this hi ⊢
    omega

theorem mem_unipRad_two_iff {n N : ℕ} (h : ∑ c, ![n, N - n] c = N) {g : GL (Fin N) k} :
    g ∈ unipRad k (stdBlocks ![n, N - n] h) ↔
      ∀ i j : Fin N, ¬ ((i : ℕ) < n ∧ n ≤ (j : ℕ)) →
        (g : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j := by
  rw [GlobalTheory.RadRev.mem_unipRad_entries]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [blk_stdBlocks_two, blk_stdBlocks_two]
  have : ((if (i : ℕ) < n then (0 : Fin 2) else 1) < if (j : ℕ) < n then 0 else 1) ↔
      ((i : ℕ) < n ∧ n ≤ (j : ℕ)) := by
    by_cases hi : (i : ℕ) < n <;> by_cases hj : (j : ℕ) < n <;> simp [hi, hj] <;> omega
  rw [this]

theorem unipRad_two_le_derUnip {n N : ℕ} (h : ∑ c, ![n, N - n] c = N) :
    unipRad k (stdBlocks ![n, N - n] h) ≤ derUnip k N n := by
  intro g hg
  have hE := (mem_unipRad_two_iff h).1 hg
  refine Subgroup.mem_inf.2 ⟨(mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩, ?_⟩
  · have := Fin.lt_def.1 hji
    rw [hE i j (by omega), one_apply_ne (ne_of_gt hji)]
  · rw [hE i i (by omega), one_apply_eq]
  · intro i hi
    ext r
    have hc : ((g : Matrix (Fin N) (Fin N) k) *ᵥ Pi.single i 1) r = (g : Matrix (Fin N) (Fin N) k) r i := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hc, hE r i (by omega)]
    by_cases hri : r = i
    · subst hri; simp
    · rw [one_apply_ne hri, Pi.single_apply, if_neg hri]

theorem unipRad_two_ne_bot {n N : ℕ} (h : ∑ c, ![n, N - n] c = N) (h1 : 1 ≤ n) (h2 : n < N) :
    unipRad k (stdBlocks ![n, N - n] h) ≠ ⊥ := by
  set i : Fin N := ⟨0, by omega⟩
  set j : Fin N := ⟨n, h2⟩
  have hne : i ≠ j := by
    intro e
    have := congrArg Fin.val e
    simp [i, j] at this
    omega
  let t : GL (Fin N) k := ⟨transvection i j 1, transvection i j (-1),
    by rw [transvection_mul_transvection_same i j hne]; simp,
    by rw [transvection_mul_transvection_same i j hne]; simp⟩
  have ht : t ∈ unipRad k (stdBlocks ![n, N - n] h) := by
    refine (mem_unipRad_two_iff h).2 fun r s hrs => ?_
    show transvection i j (1 : k) r s = _
    have : ¬ (r = i ∧ s = j) := by
      rintro ⟨rfl, rfl⟩
      exact hrs ⟨by simp [i]; omega, le_refl _⟩
    simp only [transvection, Matrix.add_apply]
    rw [Matrix.single_apply, if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    exact this ⟨rfl, rfl⟩
  intro hb
  rw [hb, Subgroup.mem_bot] at ht
  have := congrArg (fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) i j) ht
  simp [t, transvection, one_apply_ne hne] at this

end Groups

section Chars

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem derChar_eq_one_of_mem_unipRad_two {n N : ℕ} (ψ : AddChar k Circle) (h : ∑ c, ![n, N - n] c = N)
    (u : derUnip k N n) (hu : (u : GL (Fin N) k) ∈ unipRad k (stdBlocks ![n, N - n] h)) :
    derChar k ψ N n u = 1 := by
  have hE := (mem_unipRad_two_iff h).1 hu
  show Circle.toUnits _ = 1
  rw [Finset.sum_eq_zero, AddChar.map_zero_eq_one, map_one]
  intro p hp
  obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
  refine (hE p.1 p.2 (by omega)).trans (one_apply_ne fun e => ?_)
  rw [e] at h1
  omega

theorem twKer_unipRad_two_le {n N : ℕ} (ψ : AddChar k Circle) (h : ∑ c, ![n, N - n] c = N)
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) :
    twKer π (unipRad k (stdBlocks ![n, N - n] h)) 1 ≤ twKer π (derUnip k N n) (derChar k ψ N n) := by
  refine Submodule.span_mono ?_
  rintro _ ⟨u, v, rfl⟩
  refine ⟨⟨u, unipRad_two_le_derUnip h u.2⟩, v, ?_⟩
  rw [derChar_eq_one_of_mem_unipRad_two ψ h _ u.2]
  simp

end Chars

theorem twKer_derUnip_eq_top_of_isCuspidal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (N n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsCuspidal π → 1 ≤ n → n < N →
      twKer π (derUnip k N n) (derChar k ψ N n) = ⊤ := by
  intro k _ _ _ _ ψ N n V _ _ π hπ h1 h2
  have h : ∑ c, ![n, N - n] c = N := by
    simp [Fin.sum_univ_two]
    omega
  have hs := hπ.2 2 ![n, N - n] (stdBlocks ![n, N - n] h) (unipRad_two_ne_bot h h1 h2)
  have htop : twKer π (unipRad k (stdBlocks ![n, N - n] h)) 1 = ⊤ :=
    Submodule.Quotient.subsingleton_iff.1 hs
  exact eq_top_iff.2 (htop ▸ twKer_unipRad_two_le ψ h π)

end GlobalTheory.CompanionTheory.BZMir
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Path

variable {F : Type} [Field F] [NumberField F]

def invInf (F : Type) [Field F] [NumberField F] (n : ℕ) : Ainf F :=
  fun w => ((n : w.Completion) + 1)⁻¹

omit [NumberField F] in
theorem norm_natCast_add_one (w : NumberField.InfinitePlace F) (n : ℕ) :
    ‖((n : w.Completion) + 1)‖ = (n : ℝ) + 1 := by
  have h := (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
    (map_zero _) ((n : w.Completion) + 1)
  rw [← h, map_add (f := _), map_natCast, map_one]
  have : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_natCast]
  push_cast; ring

theorem natCast_add_one_ne_zero (w : NumberField.InfinitePlace F) (n : ℕ) :
    ((n : w.Completion) + 1) ≠ 0 := by
  intro h
  have := norm_natCast_add_one w n
  rw [h, norm_zero] at this
  have h2 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem mul_invInf (n : ℕ) : ((n : Ainf F) + 1) * invInf F n = 1 := by
  have key : ((n : ∀ w : NumberField.InfinitePlace F, w.Completion) + 1) *
      (fun w : NumberField.InfinitePlace F => ((n : w.Completion) + 1)⁻¹) = 1 := by
    funext w
    simp only [Pi.mul_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply]
    exact mul_inv_cancel₀ (natCast_add_one_ne_zero w n)
  exact key

theorem tendsto_invInf : Filter.Tendsto (invInf F) Filter.atTop (nhds 0) := by
  refine tendsto_pi_nhds.2 fun w => ?_
  have key : Filter.Tendsto (fun n : ℕ => ((n : w.Completion) + 1)⁻¹) Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have e : ∀ n : ℕ, ‖((n : w.Completion) + 1)⁻¹‖ = 1 / ((n : ℝ) + 1) := fun n => by
      rw [norm_inv, norm_natCast_add_one, one_div]
    simp only [e]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  exact key

def seqA (F : Type) [Field F] [NumberField F] (n : ℕ) : AF F := pairA F (invInf F n) 0

theorem tendsto_seqA : Filter.Tendsto (seqA F) Filter.atTop (nhds 0) := by
  have : Filter.Tendsto (fun n => (invInf F n, (0 : Af F))) Filter.atTop (nhds ((0 : Ainf F), (0 : Af F))) :=
    tendsto_invInf.prodMk_nhds tendsto_const_nhds
  exact this

def seqE (D : D7) (r n : ℕ) : Mx D r r :=
  Matrix.diagonal fun _ => seqA D.host.F n ⊗ₜ[D.host.F] (1 : D.host.E)

theorem seqE_mem (D : D7) (r n : ℕ) : seqE D r n ∈ hermA D r := by
  show GlobalTheory.MixModel.adj (seqE D r n) = seqE D r n
  ext i j
  by_cases h : i = j
  · subst h
    simp [GlobalTheory.MixModel.adj, seqE, sigR]
  · simp [GlobalTheory.MixModel.adj, seqE, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]

theorem tendsto_seqE (D : D7) (r : ℕ) : Filter.Tendsto (seqE D r) Filter.atTop (nhds 0) := by
  have hc : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul _ _
  have h1 : Filter.Tendsto (fun n => seqA D.host.F n ⊗ₜ[D.host.F] (1 : D.host.E)) Filter.atTop (nhds (0 : AE D)) := by
    have h2 : Filter.Tendsto (fun n => seqA D.host.F n • (1 : AE D)) Filter.atTop (nhds ((0 : AF D.host.F) • (1 : AE D))) :=
      tendsto_seqA.smul_const _
    rw [zero_smul] at h2
    refine h2.congr fun n => ?_
    rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  show Filter.Tendsto (fun n => seqE D r n i j) Filter.atTop (nhds (0 : AE D))
  by_cases h : i = j
  · subst h
    refine h1.congr fun n => ?_
    exact (Matrix.diagonal_apply_eq (fun _ => seqA D.host.F n ⊗ₜ[D.host.F] (1 : D.host.E)) i).symm
  · refine (tendsto_const_nhds (x := (0 : AE D))).congr fun n => ?_
    exact (Matrix.diagonal_apply_ne (fun _ => seqA D.host.F n ⊗ₜ[D.host.F] (1 : D.host.E)) h).symm

theorem theta_seqE (D : D7) (θ : InfFam D) (ρ : D.what₂.Tau) (n : ℕ) :
    θ ρ (infPart D (seqA D.host.F n ⊗ₜ[D.host.F] (1 : D.host.E))) = (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ) := by
  have e1 : infPart D (seqA D.host.F n ⊗ₜ[D.host.F] (1 : D.host.E)) = invInf D.host.F n ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  rw [e1]
  have e2 : (((n : Ainf D.host.F) + 1) ⊗ₜ[D.host.F] (1 : D.host.E)) * (invInf D.host.F n ⊗ₜ[D.host.F] (1 : D.host.E)) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_invInf, mul_one]; rfl
  have e3 : (((n : Ainf D.host.F) + 1) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      ((n : Ainf D.host.F ⊗[D.host.F] D.host.E) + 1) := by
    rw [TensorProduct.add_tmul, ← Algebra.TensorProduct.one_def]
    congr 1
  have e4 := congrArg (θ ρ) e2
  rw [e3, map_mul, map_add (f := _), map_natCast, map_one] at e4
  have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  field_simp
  linear_combination e4

theorem exists_herm_seq : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ r : ℕ, ∃ e : ℕ → Mx D r r, (∀ n, e n ∈ hermA D r) ∧ Filter.Tendsto e Filter.atTop (nhds 0) ∧ ∀ (n : ℕ) (ρ : D.what₂.Tau), compAt θ ρ (e n) = (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) := by
  intro D θ _ r
  refine ⟨seqE D r, seqE_mem D r, tendsto_seqE D r, fun n ρ => ?_⟩
  ext i j
  by_cases h : i = j
  · subst h
    simp only [compAt, seqE, Matrix.map_apply, Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq]
    rw [theta_seqE]; simp
  · simp [compAt, seqE, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Path
end
end
