module

public import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoDuality
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle357
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle352
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowPlacesSatisfyRowHypothesisAtQAndD
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle346
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod

@[expose] public section

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

noncomputable section

namespace GlobalTheory.LetterWindows

theorem wj_eq_sz (D : D7) (j : ℕ) (ρ : D.what₂.Tau) :
    Formalism.BasicNotions.wj D j ρ = ((Formalism.MainNotions.AdmissibleParameterJ.sz D j ρ : ℚ) : ℝ) := by
  unfold Formalism.BasicNotions.wj Formalism.MainNotions.AdmissibleParameterJ.sz
  split_ifs <;> simp

theorem sz_eq (D : D7) (j : ℕ) (ρ : D.what₂.Tau) (h : j - 1 < D.R.m) :
    Formalism.MainNotions.AdmissibleParameterJ.sz D j ρ = (D.hc ρ).e ⟨j - 1, h⟩ := by
  unfold Formalism.MainNotions.AdmissibleParameterJ.sz
  rw [dite_eq_left h]

theorem low_abs (D : D7) (j : ℕ) (h : j - 1 < D.R.m) (up : Bool) (ρ : D.what₂.Tau) (z : ℤ)
    (hz : (z : ℚ) ∈ Formalism.MainNotions.AdmissibleParameterJ.lowT D up j ρ) :
    ∃ a : Fin D.R.m, |(z : ℝ) - ((D.R.t : ℝ) - 1) / 2| =
      |((((D.hc ρ).b a - (D.hc ρ).e ⟨j - 1, h⟩ : ℚ)) : ℝ)| := by
  cases up
  · simp only [Formalism.MainNotions.AdmissibleParameterJ.lowT, Formalism.MainNotions.AdmissibleParameterJ.reflS, Formalism.MainNotions.AdmissibleParameterJ.lowJ, Formalism.MainNotions.AdmissibleParameterJ.refl,
      Formalism.MainNotions.AdmissibleParameterJ.c0, sz_eq D j ρ h, Set.mem_setOf_eq] at hz
    simp only [Bool.false_eq_true, if_false, Set.mem_setOf_eq] at hz
    obtain ⟨a, ha⟩ := hz
    refine ⟨a, ?_⟩
    have ha' := congrArg (fun q : ℚ => (q : ℝ)) ha
    push_cast at ha' ⊢
    congr 1
    linarith
  · simp only [Formalism.MainNotions.AdmissibleParameterJ.lowT, Formalism.MainNotions.AdmissibleParameterJ.lowJ,
      Formalism.MainNotions.AdmissibleParameterJ.c0, sz_eq D j ρ h, Set.mem_setOf_eq, if_true] at hz
    obtain ⟨a, ha⟩ := hz
    refine ⟨a, ?_⟩
    have ha' := congrArg (fun q : ℚ => (q : ℝ)) ha
    push_cast at ha' ⊢
    rw [abs_sub_comm ((((D.hc ρ).b a : ℚ)) : ℝ)]
    congr 1
    linarith

theorem cloud_val (D : D7) (j : ℕ) (up : Bool) (ρ : D.what₂.Tau) (z : ℤ)
    (hz : (z : ℚ) ∈ Formalism.MainNotions.AdmissibleParameterJ.cloudT D up j ρ) :
    ∃ a : Fin (D.R.k - 1),
      (if up then (z : ℝ) - ((D.R.t : ℝ) - 1) / 2 else ((D.R.t : ℝ) - 1) / 2 - z) =
        Formalism.BasicNotions.wj D j ρ + ((((D.hc ρ).v a : ℚ)) : ℝ) := by
  rw [wj_eq_sz]
  cases up
  · simp only [Formalism.MainNotions.AdmissibleParameterJ.cloudT, Formalism.MainNotions.AdmissibleParameterJ.reflS, Formalism.MainNotions.AdmissibleParameterJ.cloudJ, Formalism.MainNotions.AdmissibleParameterJ.refl,
      Formalism.MainNotions.AdmissibleParameterJ.c0, Set.mem_setOf_eq] at hz
    simp only [Bool.false_eq_true, if_false, Set.mem_setOf_eq] at hz ⊢
    obtain ⟨a, ha⟩ := hz
    refine ⟨a, ?_⟩
    have ha' := congrArg (fun q : ℚ => (q : ℝ)) ha
    push_cast at ha' ⊢
    linarith
  · simp only [Formalism.MainNotions.AdmissibleParameterJ.cloudT, Formalism.MainNotions.AdmissibleParameterJ.cloudJ,
      Formalism.MainNotions.AdmissibleParameterJ.c0, Set.mem_setOf_eq, if_true] at hz ⊢
    obtain ⟨a, ha⟩ := hz
    refine ⟨a, ?_⟩
    have ha' := congrArg (fun q : ℚ => (q : ℝ)) ha
    push_cast at ha' ⊢
    linarith

theorem base_window (D : D7) (L : SizeData₂ D) (j : ℕ) (hj1 : 1 ≤ j) (hjm : j ≤ D.R.m)
    (ρ : D.what₂.Tau) :
    ∃ W0 ∈ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.baseSizes L,
      W0 ≤ Formalism.BasicNotions.wj D j ρ ∧ Formalism.BasicNotions.wj D j ρ ≤ W0 + L.etaSz + 1 := by
  by_cases htop : (D.eTau ρ : D.R.GG) ∈ D.host.topPlaces
  · have htop' := htop
    simp only [Formalism.BasicNotions.Host.topPlaces, Finset.mem_image] at htop'
    obtain ⟨t, ht, hte⟩ := htop'
    have hw := L.win_top j hj1 hjm ρ ⟨t, ht⟩ hte.symm
    refine ⟨(L.bT ⟨t, ht⟩ : ℝ) + ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ), ?_, ?_, ?_⟩
    · exact Or.inr (Or.inr ⟨⟨t, ht⟩, rfl⟩)
    · have := Int.floor_le (L.sc.b' / L.sc.x)
      linarith [hw.1]
    · have := Int.lt_floor_add_one (L.sc.b' / L.sc.x)
      linarith [hw.2]
  · by_cases hthick : (D.eTau ρ : D.R.GG) ∈ D.host.thickPlaces
    · have hw := L.win_thick j hj1 hjm ρ hthick
      exact ⟨L.sc.b, Or.inl rfl, hw.1, hw.2⟩
    · have hthin : D.host.IsThin (D.eTau ρ : D.R.GG) :=
        ⟨(D.eTau ρ).2, htop, hthick⟩
      have hw := L.win_thin j hj1 hjm ρ hthin
      exact ⟨L.sc.w'' D.R.n, Or.inr (Or.inl rfl), hw.1, by linarith [hw.2]⟩

end GlobalTheory.LetterWindows

namespace GlobalTheory.LetterWindows

theorem lows_cloud_windows : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ), Fm.x1 < x → ∀ (a : Fm.Ix x) (j : ℕ), 1 ≤ j → j ≤ (Fm.D x a).R.m →
    ∀ (up : Bool) (ρ : (Fm.D x a).what₂.Tau),
    (∀ z : ℤ, (z : ℚ) ∈ AdmissibleParameterJ.lowT (Fm.D x a) up j ρ →
      |(z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2| ≤ (Fm.L x a).etaSz ∧
      2 * ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) + ((Fm.D x a).R.t : ℝ) / 2 + 3 ≤
        |(z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2|) ∧
    ∃ W0 ∈ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.baseSizes (Fm.L x a), ∀ z : ℤ, (z : ℚ) ∈ AdmissibleParameterJ.cloudT (Fm.D x a) up j ρ →
      W0 ≤ (if up then (z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2 else (((Fm.D x a).R.t : ℝ) - 1) / 2 - z) ∧
      (if up then (z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2 else (((Fm.D x a).R.t : ℝ) - 1) / 2 - z) ≤
        W0 + (Fm.L x a).Sc + (Fm.L x a).etaSz + 1 := by
  intro eps Fm x hx a j hj1 hjm up ρ
  have h : j - 1 < (Fm.D x a).R.m := by omega
  refine ⟨fun z hz => ?_, ?_⟩
  · obtain ⟨i, hi⟩ := low_abs (Fm.D x a) j h up ρ z hz
    rw [hi]
    refine ⟨(Fm.L x a).be_close ρ i ⟨j - 1, h⟩, ?_⟩
    have := (Fm.params x hx a).lows_far ρ i ⟨j - 1, h⟩
    have e : 2 * ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) = 2 * (Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a) := by
      ring
    rw [e]
    exact this
  · obtain ⟨W0, hW0, hlo, hhi⟩ := base_window (Fm.D x a) (Fm.L x a) j hj1 hjm ρ
    refine ⟨W0, hW0, fun z hz => ?_⟩
    obtain ⟨i, hi⟩ := cloud_val (Fm.D x a) j up ρ z hz
    rw [hi]
    have hv := (Fm.L x a).cloud_v ρ i
    constructor <;> linarith [hv.1, hv.2]

end GlobalTheory.LetterWindows
end
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual

namespace GlobalTheory.Pass.LocDual

theorem lenMod_eq_height_map {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (S H : Submodule O M) : BlochKatoDuality.lenMod S H = Order.height (S.map H.mkQ) := by
  show Module.length O (↥(S ⊔ H) ⧸ H.comap (S ⊔ H).subtype) = _
  have hker : LinearMap.ker (H.mkQ ∘ₗ (S ⊔ H).subtype) = H.comap (S ⊔ H).subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hrange : LinearMap.range (H.mkQ ∘ₗ (S ⊔ H).subtype) = S.map H.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype, Submodule.map_sup, Submodule.mkQ_map_self,
      sup_bot_eq]
  rw [← Module.length_submodule]
  exact ((Submodule.quotEquivOfEq _ _ hker.symm).trans
    ((H.mkQ ∘ₗ (S ⊔ H).subtype).quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hrange))).length_eq

theorem height_map_span_le_of_finset {O M N : Type} [CommRing O] [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] (f : M →ₗ[O] N) (S : Set M) (b : ℕ∞)
    (h : ∀ F : Finset M, (↑F : Set M) ⊆ S →
      Order.height ((Submodule.span O (↑F : Set M)).map f) ≤ b) :
    Order.height ((Submodule.span O S).map f) ≤ b := by
  classical
  rw [Order.height_le_iff]
  intro p hp

  have hx : ∀ i : Fin p.length, ∃ x ∈ p i.succ, x ∉ p i.castSucc :=
    fun i => SetLike.exists_of_lt (p.step i)
  choose x hxin hxout using hx

  have hfin : ∀ i : Fin p.length, ∃ F : Finset M, (↑F : Set M) ⊆ S ∧
      x i ∈ (Submodule.span O (↑F : Set M)).map f := by
    intro i
    have hxi : x i ∈ (Submodule.span O S).map f := hp (p.monotone (Fin.le_last i.succ) (hxin i))
    obtain ⟨y, hyS, hyx⟩ := Submodule.mem_map.mp hxi
    obtain ⟨T, hTS, hyT⟩ := Submodule.mem_span_finite_of_mem_span hyS
    exact ⟨T, hTS, Submodule.mem_map.mpr ⟨y, hyT, hyx⟩⟩
  choose F hFS hxF using hfin
  let G : Finset M := Finset.univ.biUnion F
  have hGS : (↑G : Set M) ⊆ S := by
    intro z hz
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hz
    exact hFS i hi
  have hFG : ∀ i, Submodule.span O (↑(F i) : Set M) ≤ Submodule.span O (↑G : Set M) := fun i =>
    Submodule.span_mono (fun z hz => Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hz⟩)

  let Q := (Submodule.span O (↑G : Set M)).map f
  let q : LTSeries (Submodule O N) := LTSeries.mk p.length (fun j => p j ⊓ Q) (by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    dsimp only
    refine lt_of_le_of_ne (inf_le_inf_right _ (p.monotone (Fin.castSucc_le_succ i))) ?_
    intro heq
    have h1 : x i ∈ p i.succ ⊓ Q :=
      Submodule.mem_inf.mpr ⟨hxin i, Submodule.map_mono (hFG i) (hxF i)⟩
    rw [← heq] at h1
    exact hxout i (Submodule.mem_inf.mp h1).1)
  calc (p.length : ℕ∞) = q.length := rfl
    _ ≤ Order.height Q := Order.length_le_height inf_le_right
    _ ≤ b := h G hGS

theorem lenMod_span_le_of_finset : ∀ {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (S : Set M) (H : Submodule O M) (b : ℕ∞),
    (∀ F : Finset M, (↑F : Set M) ⊆ S → BlochKatoDuality.lenMod (Submodule.span O (↑F : Set M)) H ≤ b) →
    BlochKatoDuality.lenMod (Submodule.span O S) H ≤ b := by
  intro O M _ _ _ S H b h
  rw [lenMod_eq_height_map]
  apply height_map_span_le_of_finset H.mkQ S b
  intro F hF
  rw [← lenMod_eq_height_map]
  exact h F hF

end GlobalTheory.Pass.LocDual
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo

namespace GlobalTheory.MatKerCokernel

section
variable {R : Type} [CommRing R] {a : ℕ}

abbrev Cok (Φ : Matrix (Fin a) (Fin a) R) : Type :=
  (Fin a → R) ⧸ LinearMap.range Φ.transpose.mulVecLin

def univ (Φ : Matrix (Fin a) (Fin a) R) (c : Fin a) : Cok Φ :=
  (LinearMap.range Φ.transpose.mulVecLin).mkQ (Pi.single c 1)

theorem matAct_apply' {B : Type} [AddCommGroup B] [Module R B] (Φ : Matrix (Fin a) (Fin a) R)
    (u : Fin a → B) (i : Fin a) : matAct Φ u i = ∑ j, Φ i j • u j := rfl

theorem mk_eq_sum (Φ : Matrix (Fin a) (Fin a) R) (y : Fin a → R) :
    (LinearMap.range Φ.transpose.mulVecLin).mkQ y = ∑ c, y c • univ Φ c := by
  have hy : y = ∑ c, y c • (Pi.single c 1 : Fin a → R) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hy]

  simp only [map_sum, map_smul, univ]

theorem univ_ker (Φ : Matrix (Fin a) (Fin a) R) : matAct Φ (univ Φ) = 0 := by
  funext i
  rw [matAct_apply', Pi.zero_apply]
  have h := mk_eq_sum Φ (fun j => Φ i j)
  beta_reduce at h
  rw [← h, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  refine ⟨Pi.single i 1, ?_⟩
  ext j
  simp

theorem map_ker {B B' : Type} [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R B']
    (Φ : Matrix (Fin a) (Fin a) R) (f : B →ₗ[R] B') (u : Fin a → B) (hu : matAct Φ u = 0) :
    matAct Φ (fun c => f (u c)) = 0 := by
  funext i
  have h := congrFun hu i
  rw [matAct_apply', Pi.zero_apply] at h
  rw [matAct_apply', Pi.zero_apply]
  calc ∑ j, Φ i j • f (u j) = f (∑ j, Φ i j • u j) := by

        rw [map_sum]
        simp only [map_smul]
    _ = 0 := by rw [h, map_zero]

theorem exists_lift {B : Type} [AddCommGroup B] [Module R B]
    (Φ : Matrix (Fin a) (Fin a) R) (b : Fin a → B) (hb : matAct Φ b = 0) :
    ∃ f : Cok Φ →ₗ[R] B, ∀ c, f (univ Φ c) = b c := by
  obtain ⟨g, hg⟩ : ∃ g : (Fin a → R) →ₗ[R] B, ∀ y, g y = ∑ c, y c • b c :=
    ⟨∑ c, (LinearMap.proj c).smulRight (b c), fun y => by simp [LinearMap.sum_apply]⟩
  have key : ∀ j, ∑ c, Φ j c • b c = 0 := fun j => by
    have h := congrFun hb j
    rw [matAct_apply', Pi.zero_apply] at h
    exact h
  have hle : LinearMap.range Φ.transpose.mulVecLin ≤ LinearMap.ker g := by
    rintro _ ⟨z, rfl⟩
    rw [LinearMap.mem_ker, hg]
    calc ∑ c, (Φ.transpose.mulVecLin z) c • b c
        = ∑ c, ∑ j, z j • Φ j c • b c := by
          refine Finset.sum_congr rfl fun c _ => ?_
          simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
            Finset.sum_smul]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [mul_comm, mul_smul]
      _ = ∑ j, z j • ∑ c, Φ j c • b c := by
          rw [Finset.sum_comm]
          simp only [Finset.smul_sum]
      _ = 0 := by simp [key]
  refine ⟨(LinearMap.range Φ.transpose.mulVecLin).liftQ g hle, fun c => ?_⟩
  rw [univ, Submodule.mkQ_apply, Submodule.liftQ_apply, hg]
  simp [Pi.single_apply]

theorem hom_ext {B : Type} [AddCommGroup B] [Module R B]
    (Φ : Matrix (Fin a) (Fin a) R) (f g : Cok Φ →ₗ[R] B)
    (h : ∀ c, f (univ Φ c) = g (univ Φ c)) : f = g := by
  apply Submodule.linearMap_qext
  refine LinearMap.ext fun y => ?_

  simp only [LinearMap.comp_apply, mk_eq_sum, map_sum, map_smul, h]

end

theorem cok_equiv_of_exact : ∀ (R : Type) [CommRing R] (a a' k : ℕ) (Φ : Matrix (Fin a) (Fin a) R) (Φ' : Matrix (Fin a') (Fin a') R) (x : R) (rel : ∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B], (Fin a → B) → (Fin a' → B) → Prop) (t : ∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B], (Fin a' → B) → Fin k → B), (∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B] (u u' : Fin a → B) (w : Fin a' → B), matAct Φ u = 0 → matAct Φ u' = 0 → rel B u w → rel B u' w → u = u') → (∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B] (u : Fin a → B) (w w' : Fin a' → B), matAct Φ' w = 0 → matAct Φ' w' = 0 → rel B u w → rel B u w' → w = w') → (∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B] (u : Fin a → B), matAct Φ u = 0 → ∃ w : Fin a' → B, matAct Φ' w = 0 ∧ rel B u w ∧ t B w = 0) → (∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B] (w : Fin a' → B), matAct Φ' w = 0 → t B w = 0 → ∃ u : Fin a → B, matAct Φ u = 0 ∧ rel B u w) → (∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B] (w : Fin a' → B), matAct Φ' w = 0 → ∀ j, x • t B w j = 0) → (∀ (B B' : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B] [AddCommGroup B'] [Module R B'] [TopologicalSpace B'] [DiscreteTopology B'] (f : B →ₗ[R] B') (u : Fin a → B) (w : Fin a' → B), matAct Φ u = 0 → matAct Φ' w = 0 → rel B u w → rel B' (fun c => f (u c)) (fun c => f (w c))) → (∀ (B B' : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B] [AddCommGroup B'] [Module R B'] [TopologicalSpace B'] [DiscreteTopology B'] (f : B →ₗ[R] B') (w : Fin a' → B), matAct Φ' w = 0 → t B' (fun c => f (w c)) = fun j => f (t B w j)) → ∃ v : Fin k → ((Fin a' → R) ⧸ LinearMap.range Φ'.transpose.mulVecLin), (∀ j, x • v j = 0) ∧ Nonempty ((((Fin a' → R) ⧸ LinearMap.range Φ'.transpose.mulVecLin) ⧸ Submodule.span R (Set.range v)) ≃ₗ[R] ((Fin a → R) ⧸ LinearMap.range Φ.transpose.mulVecLin)) := by
  intro R _ a a' k Φ Φ' x rel t H1 H2 H3 H4 H5 H6 H7

  let _ : TopologicalSpace (Cok Φ) := ⊥
  have : DiscreteTopology (Cok Φ) := ⟨rfl⟩
  let _ : TopologicalSpace (Cok Φ') := ⊥
  have : DiscreteTopology (Cok Φ') := ⟨rfl⟩

  obtain ⟨v, hv⟩ : ∃ v : Fin k → Cok Φ', v = t (Cok Φ') (univ Φ') := ⟨_, rfl⟩
  refine ⟨v, fun j => by rw [hv]; exact H5 _ _ (univ_ker Φ') j, ?_⟩
  obtain ⟨S, hS⟩ : ∃ S : Submodule R (Cok Φ'), S = Submodule.span R (Set.range v) := ⟨_, rfl⟩
  rw [← hS]
  let _ : TopologicalSpace (Cok Φ' ⧸ S) := ⊥
  have : DiscreteTopology (Cok Φ' ⧸ S) := ⟨rfl⟩

  have hw0 : matAct Φ' (fun c => S.mkQ (univ Φ' c)) = 0 := map_ker Φ' S.mkQ (univ Φ') (univ_ker Φ')
  have ht0 : t (Cok Φ' ⧸ S) (fun c => S.mkQ (univ Φ' c)) = 0 := by
    rw [H7 (Cok Φ') (Cok Φ' ⧸ S) S.mkQ (univ Φ') (univ_ker Φ'), ← hv]
    funext j
    simp only [Submodule.mkQ_apply, Pi.zero_apply, Submodule.Quotient.mk_eq_zero]
    rw [hS]
    exact Submodule.subset_span ⟨j, rfl⟩
  obtain ⟨u0, hu0, hr0⟩ := H4 _ _ hw0 ht0
  obtain ⟨φ, hφ⟩ := exists_lift Φ u0 hu0

  obtain ⟨w1, hw1, hr1, ht1⟩ := H3 (Cok Φ) (univ Φ) (univ_ker Φ)
  obtain ⟨ψ0, hψ0⟩ := exists_lift Φ' w1 hw1
  have hψ0v : S ≤ LinearMap.ker ψ0 := by
    rw [hS, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, hv]
    have h := H7 (Cok Φ') (Cok Φ) ψ0 (univ Φ') (univ_ker Φ')
    rw [show (fun c => ψ0 (univ Φ' c)) = w1 from funext hψ0, ht1] at h
    exact (congrFun h j).symm
  obtain ⟨ψ, hψ⟩ : ∃ ψ : (Cok Φ' ⧸ S) →ₗ[R] Cok Φ, ∀ c, ψ (S.mkQ (univ Φ' c)) = w1 c :=
    ⟨S.liftQ ψ0 hψ0v, fun c => by rw [Submodule.mkQ_apply, Submodule.liftQ_apply, hψ0]⟩

  have e1 : ψ.comp φ = LinearMap.id := by
    apply hom_ext Φ
    intro c
    simp only [LinearMap.comp_apply, LinearMap.id_apply, hφ]
    have hk : matAct Φ (fun c => ψ (u0 c)) = 0 := map_ker Φ ψ u0 hu0
    have hr := H6 (Cok Φ' ⧸ S) (Cok Φ) ψ u0 (fun c => S.mkQ (univ Φ' c)) hu0 hw0 hr0
    simp only [hψ] at hr
    exact congrFun (H1 (Cok Φ) _ _ w1 hk (univ_ker Φ) hr hr1) c
  have e2 : φ.comp ψ = LinearMap.id := by
    apply Submodule.linearMap_qext
    apply hom_ext Φ'
    intro c
    simp only [LinearMap.comp_apply, LinearMap.id_apply, hψ]
    have hk : matAct Φ' (fun c => φ (w1 c)) = 0 := map_ker Φ' φ w1 hw1
    have hr := H6 (Cok Φ) (Cok Φ' ⧸ S) φ (univ Φ) w1 (univ_ker Φ) hw1 hr1
    simp only [hφ] at hr
    exact congrFun (H2 _ u0 _ _ hk hw0 hr hr0) c
  exact ⟨LinearEquiv.ofLinearMap ψ φ e1 e2⟩

end GlobalTheory.MatKerCokernel
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

noncomputable section
namespace GlobalTheory.InertiaDecomp
open Pointwise

theorem iner_decomp : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' : FinExt l) (h : K.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c') (g : ↥(GK K)), g ∈ (pc P h hN hF hS).Iner → ∃ s : ↥(GK K), s ∈ IK K ∧ s⁻¹ * g ∈ GKin h := by
  intro l _ P K K' h hN hF hS g hg
  haveI : Nontrivial P.R.B := by
    by_contra hB
    have : Subsingleton P.R.B := not_nontrivial_iff_subsingleton.mp hB
    apply (P.PD K).not_mem_filtration_two
    rw [Subsingleton.elim (P.PD K).t 0, map_zero]
    exact Submodule.zero_mem _

  have hfix : ∀ x ∈ K0 K', (g : GQ l) x = x := by
    intro x hx
    have h1 : (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B ⟨x, hx⟩) = algebraMap ↥(K0 K') P.R.B ⟨x, hx⟩ :=
      hg ⟨x, hx⟩
    rw [P.PD_actB] at h1
    have h2 := P.actQ_Kur ((g : ↥(GK K)) : GQ l) ⟨x, hx.2⟩ ⟨_, GlobalTheory.TameInertiaCyclic.map_mem_Kur _ hx.2⟩ rfl
    have h3 := (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B).injective (h2.symm.trans h1)
    exact congrArg Subtype.val h3
  haveI := K'.2

  let S : Subgroup (GQ l) := (MaximalUnramifiedExtension l).fixingSubgroup ⊔ (K'.1).fixingSubgroup
  have hSo : IsOpen (S : Set (GQ l)) :=
    Subgroup.isOpen_mono le_sup_right (IntermediateField.fixingSubgroup_isOpen K'.1)
  let SC : ClosedSubgroup (GQ l) := ⟨S, Subgroup.isClosed_of_isOpen S hSo⟩
  have hfe : IntermediateField.fixedField (SC : Subgroup (GQ l)) ≤ K0 K' := by
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    refine IntermediateField.mem_inf.2 ⟨?_, ?_⟩
    · exact (InfiniteGalois.fixedField_fixingSubgroup K'.1).le
        ((IntermediateField.mem_fixedField_iff _ _).2 fun f hf => hx f (Subgroup.mem_sup_right hf))
    · exact (InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension l)).le
        ((IntermediateField.mem_fixedField_iff _ _).2 fun f hf => hx f (Subgroup.mem_sup_left hf))
  have hgS : (g : GQ l) ∈ S := by
    have e := InfiniteGalois.fixingSubgroup_fixedField SC
    have : (g : GQ l) ∈ (IntermediateField.fixedField (SC : Subgroup (GQ l))).fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact hfix x (hfe hx)
    rw [e] at this
    exact this
  haveI := GlobalTheory.FrobGen.normal_fix (l := l)
  have hgS' : (g : GQ l) ∈ ((MaximalUnramifiedExtension l).fixingSubgroup : Set (GQ l)) * ((K'.1).fixingSubgroup : Set (GQ l)) := by
    rw [← Subgroup.normal_mul]; exact hgS
  obtain ⟨b, hb, a, ha, hba⟩ := hgS'
  have haK : a ∈ GK K := GK_le h ha
  have hbK : b ∈ GK K := by
    have : b = (g : GQ l) * a⁻¹ := by rw [← hba, mul_inv_cancel_right]
    rw [this]; exact mul_mem g.2 (inv_mem haK)
  refine ⟨⟨b, hbK⟩, Subgroup.subset_closure fun x hx => GlobalTheory.FrobGen.norm_sub_lt hb x hx, ?_⟩
  rw [GKin, Subgroup.mem_subgroupOf]
  have : (((⟨b, hbK⟩ : ↥(GK K))⁻¹ * g : ↥(GK K)) : GQ l) = a := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, ← hba]; simp
  rw [this]; exact ha

end GlobalTheory.InertiaDecomp
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.aux_statement : ∀ D : D7, EmbeddingTypeJumps.Conclusion1 D := by
  first | exact @GlobalTheory.PrimesQD.ramification_two_and_conjugation_at_q_and_d | exact GlobalTheory.PrimesQD.ramification_two_and_conjugation_at_q_and_d | (intros; apply GlobalTheory.PrimesQD.ramification_two_and_conjugation_at_q_and_d <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.rowPlaces_satisfy_rowHypothesis_at_q_and_d : ∀ (D : D7) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool) (CA : ℝ), EmbeddingTypeJumps.Conclusion0 D → EmbeddingTypeJumps.Conclusion1 D → EmbeddingTypeJumps.admA (D := D) CA → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ → EmbeddingTypeJumps.admG2 r ρ → EmbeddingTypeJumps.iwahoriAdmissibleSet r ρ → EmbeddingTypeJumps.LiteratureHypotheses (D := D) → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → ∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → ∀ π ∈ D.nd.Zgood i, ∀ dc : TruncatedSeriesCountingIdentities.Decl D i, ∃ lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ, TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i (r i) (ρ i) π dc lenRow ∧ ∀ w ∈ dc.row, (lenRow w : ℝ) ≤ max CA 0 * (((locDeg D.host.E w : ℕ) + 1 : ℝ) * (D.R.r : ℝ) * (4 * large₂.sc.b / (D.nd.l i : ℝ) + 2 * large₂.Sc + 2 * Real.logb (D.nd.l i : ℝ) (2 * large₂.sc.b) + 1 + large₂.etaSz + (D.R.t : ℝ)) + 3 * ((locDeg D.host.E w : ℕ) : ℝ) * (D.R.m : ℝ) * (2 * large₂.sc.b + 1)) + 1 := by
  first | exact @GlobalTheory.RowBoundB.row_bound | exact GlobalTheory.RowBoundB.row_bound | (intros; apply GlobalTheory.RowBoundB.row_bound <;> assumption)
end
