module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle133
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle466
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle018
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle463
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle053
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateNoTwistedInvariantsComplexPadic
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ApplyLayers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle467
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachFunctorRingPsiOperatorExistsOfGood
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

namespace GlobalTheory.SplitHecke

open Matrix

section

variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {r : ℕ}

theorem isInt_of_mem_span_basisFun {w : Fin r → K}
    (hw : w ∈ Submodule.span O (Set.range (Pi.basisFun K (Fin r)))) (i : Fin r) :
    IsInt O (w i) := by
  show ∃ o : O, algebraMap O K o = w i
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    by_cases hij : i = j
    · subst hij
      exact ⟨1, by simp⟩
    · exact ⟨0, by simp [Pi.basisFun_apply, Pi.single_apply, hij]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by simp [ha, hb]⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨c * a, by simp [ha, Algebra.smul_def]⟩

theorem intM_inv_mul_of_map_le {a b : GL (Fin r) K}
    (hle : (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map
        (((a : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) ≤
      (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map
        (((b : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O)) :
    IntM O (b⁻¹ * a).1 := by
  intro i j
  have hmem := Submodule.mem_map_of_mem
    (f := ((a : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O)
    (Submodule.subset_span ⟨j, rfl⟩ :
      Pi.basisFun K (Fin r) j ∈ Submodule.span O (Set.range (Pi.basisFun K (Fin r))))
  obtain ⟨w, hw, hwe⟩ := hle hmem
  simp only [LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply] at hwe
  have hcol : ((b⁻¹ * a : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *ᵥ Pi.basisFun K (Fin r) j = w := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← hwe, Matrix.mulVec_mulVec, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hentry : (b⁻¹ * a).1 i j = w i := by
    rw [← hcol]
    simp [Pi.basisFun_apply]
  rw [hentry]
  exact isInt_of_mem_span_basisFun hw i

end

theorem gInt_inv_mul_of_map_eq : ∀ (O K : Type) [CommRing O] [Field K] [Algebra O K] (r : ℕ)
    (h h' : GL (Fin r) K),
    (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map
        (((h : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) =
      (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map
        (((h' : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) →
    GInt O (h⁻¹ * h') := by
  intro O K _ _ _ r h h' heq
  show IntM O (h⁻¹ * h').1 ∧ IntM O ((h⁻¹ * h')⁻¹).1
  refine ⟨intM_inv_mul_of_map_le heq.ge, ?_⟩
  rw [_root_.mul_inv_rev, inv_inv]
  exact intM_inv_mul_of_map_le heq.le

end GlobalTheory.SplitHecke
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.weilDeligneParam_dual_listSum_absTwist_special : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), (∀ l : List (WD h), (sumList l).lpDual = sumList (l.map WD.lpDual)) ∧ (∀ (y : WD h) (s : ℝ), (y.lpTw s).lpDual = y.lpDual.lpTw (-s)) ∧ ∀ (y : WD h) (n : ℕ), (y.lpChar (WD.lpSp (h := h) n)).lpDual = y.lpDual.lpChar (WD.lpSp (h := h) n) := by
  intro E Ω _ _ _ _ _ A w h
  have dual_sp (y : WD h) (n : ℕ) :
      (y.lpChar (WD.lpSp (h := h) n)).lpDual = y.lpDual.lpChar (WD.lpSp (h := h) n) := by
    induction y using WD.ind with
    | hP m a =>
      rw [WD.lpSp, WD.lpChar_mk, WD.lpDual_mk, WD.lpDual_mk, WD.lpChar_mk]
      exact WD.sound ((GlobalTheory.WDDual.iso_tensor_dual a (WDRep.sp (h := h) n)).symm.trans
        ((WDRep.Iso.refl a.dual).tensor (GlobalTheory.WDDual.iso_sp_dual (h := h) n)))
  exact ⟨GlobalTheory.WDDual.WDClass.lpDual_sumList, GlobalTheory.WDDual.WDClass.lpDual_lpTw,
    dual_sp⟩
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.weil_deligne_sum_twist_compat : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), (∀ l l' : List (WD h), l.Perm l' → sumList l = sumList l') ∧ (∀ (l : List (WD h)) (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ), (sumList l).lpTwist ξ hξ = sumList (l.map fun y => y.lpTwist ξ hξ)) ∧ (∀ (x y : WD h) (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ), (x.lpSum y).lpTwist ξ hξ = (x.lpTwist ξ hξ).lpSum (y.lpTwist ξ hξ) ∧ (x.lpChar y).lpTwist ξ hξ = (x.lpTwist ξ hξ).lpChar y) ∧ (∀ (x : WD h) (l : List (WD h)), x.lpChar (sumList l) = sumList (l.map x.lpChar)) ∧ (∀ l : List (WD h), (sumList l).lpDim = (l.map WD.lpDim).sum ∧ ∀ σ, (sumList l).charPol σ = (l.map fun y => y.charPol σ).prod) := by
  exact @GlobalTheory.sumList_laws
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocGL.SumProd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ}

theorem sum_fst_of_lFactors {𝔪 : Multiset (Segment k)} {h : ℕ} {x : Fin h → IrrGL (k := k)} (hx : LFactors 𝔪 x) :
    ∑ a, (x a).1 = (𝔪.map Segment.deg).sum := by
  obtain ⟨Δ, ⟨rfl, -⟩, hΔ⟩ := hx
  rw [Multiset.map_map, ← Finset.sum_eq_multiset_sum]
  exact Finset.sum_congr rfl fun a _ => (hΔ a).deg_eq.symm

theorem deg_of_isL {𝔪 : Multiset (Segment k)} {π : Representation ℂ (GL (Fin N) k) V} (h : IsL 𝔪 π) :
    (𝔪.map Segment.deg).sum = N := by
  obtain ⟨_, x, hd, hx, -⟩ := h
  exact (sum_fst_of_lFactors hx).symm.trans hd

theorem exists_isLSeg_of_isL {𝔪 : Multiset (Segment k)} {π : Representation ℂ (GL (Fin N) k) V} (h : IsL 𝔪 π)
    {Δ : Segment k} (hΔ : Δ ∈ 𝔪) : ∃ y : IrrGL (k := k), IsLSeg Δ y.rep := by
  obtain ⟨_, x, -, ⟨D, ⟨rfl, -⟩, hD⟩, -⟩ := h
  obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hΔ
  exact ⟨x a, hD a⟩

theorem exists_isL [CharZero k] (hS : StandardCosocleGL) {𝔪 : Multiset (Segment k)}
    (h : ∀ Δ ∈ 𝔪, ∃ y : IrrGL (k := k), IsLSeg Δ y.rep) (hN : (𝔪.map Segment.deg).sum = N) :
    ∃ π : IrrRep (GL (Fin N) k), IsL 𝔪 π.ρ := by
  obtain ⟨D, hD⟩ := exists_isOrderedForm 𝔪
  have hm : ∀ i, D i ∈ 𝔪 := fun i => hD.1 ▸ Multiset.mem_map_of_mem D (Finset.mem_univ i)
  choose x hx using fun i => h _ (hm i)
  have hF : LFactors 𝔪 x := ⟨D, hD, hx⟩
  have hd : ∑ a, (x a).1 = N := (sum_fst_of_lFactors hF).trans hN
  obtain ⟨π, hπ⟩ := hS k 𝔪 _ _ x hd hF
  exact ⟨π, _, x, hd, hF, hπ⟩

theorem isL_add_of_equiv_prod₂ : LanglandsMultisegments → StandardCosocleGL → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (r t : ℕ) (σ : IrrRep (GL (Fin r) k)) (τ : IrrRep (GL (Fin t) k)) (π : IrrRep (GL (Fin (r + t)) k)) (𝔪 𝔫 : Multiset (Segment k)), IsL 𝔪 σ.ρ → IsL 𝔫 τ.ρ → Nonempty (π.ρ.Equiv (prod₂ σ.ρ τ.ρ)) → IsL (𝔪 + 𝔫) π.ρ := by
  rintro hM hS k _ _ _ _ _ r t σ τ π 𝔪 𝔫 h1 h2 ⟨e⟩
  obtain ⟨y, hy⟩ := exists_isL (N := r + t) hS (𝔪 := 𝔪 + 𝔫)
    (fun Δ hΔ => (Multiset.mem_add.1 hΔ).elim (exists_isLSeg_of_isL h1) (exists_isLSeg_of_isL h2))
    (by rw [Multiset.map_add (f := _), Multiset.sum_add, deg_of_isL h1, deg_of_isL h2])
  have hd : ∑ a, (![IrrGL.of σ.ρ σ.smooth σ.irr, IrrGL.of τ.ρ τ.smooth τ.irr] a).1 = r + t := Fin.sum_univ_two _
  obtain ⟨φ⟩ := nonempty_prod₂_equiv_prodIrr σ.ρ σ.smooth σ.irr τ.ρ τ.smooth τ.irr hd
  have ψ := IrrGL.equivOf y.ρ y.smooth y.irr
  have a1 : IsL 𝔪 (IrrGL.of σ.ρ σ.smooth σ.irr).rep := h1.of_equiv (IrrGL.equivOf _ _ _)
  have a2 : IsL 𝔫 (IrrGL.of τ.ρ τ.smooth τ.irr).rep := h2.of_equiv (IrrGL.equivOf _ _ _)
  have a3 : IsL (𝔪 + 𝔫) (IrrGL.of y.ρ y.smooth y.irr).rep := hy.of_equiv ψ
  have hs := (hM k).2 𝔪 𝔫 ![IrrGL.of σ.ρ σ.smooth σ.irr, IrrGL.of τ.ρ τ.smooth τ.irr]
    (IrrGL.of y.ρ y.smooth y.irr) hd a1 a2 a3
  have E := (e.trans φ).symm
  obtain ⟨θ⟩ := IsSubquotient.nonempty_equiv
    (hs.trans (.of_injective E.toIntertwiningMap E.toLinearEquiv.injective)) (IrrRep.irr _) π.irr
  exact a3.of_equiv θ.symm

end GlobalTheory.LocGL.SumProd
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

theorem _root_.GlobalTheory.T.langlandsQuotient_of_speh_type_product_isL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
    GlobalTheory.Published.StandardCosocleGL → (∀ (δ δ' : IrrGL (k := k)) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
    IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y) → (∀ (d h : ℕ) (y : Fin d → Fin h → IrrGL (k := k)) (N : Fin d → ℕ) (M : ℕ) (hN : ∀ i, ∑ j, (y i j).1 = N i)
    (hM : ∑ i, N i = M)
    (hM' : ∑ p : Fin (d * h), (y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).1 = M),
    Nonempty ((multiProd (stdBlocks N hM) fun i => prodIrr (y i) (hN i)).Equiv
      (prodIrr (fun p => y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2) hM'))) →
    ∀ (a : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin a) k) V)
    (m : ℕ) (δ : Fin m → IrrGL (k := k)) (Δ : Fin m → Segment k) (s : Fin m → ℝ), (∀ j, IsLSeg (Δ j) (δ j).rep) →
      (∀ j, IsUnitarisable (δ j).rep) → (∀ j, |s j| < 1 / 2) → ∀ hd : ∑ j, ((δ j).nu (s j)).1 = a,
      Nonempty (σ.Equiv (prodIrr (fun j => (δ j).nu (s j)) hd)) →
    ∀ (d n : ℕ) (hdn : ∑ _ : Fin d, a = n) (W : Type) [AddCommGroup W] [Module ℂ W]
      (σ' : Representation ℂ (GL (Fin n) k) W), σ'.IsIrreducible →
      (∃ f : (multiProd (stdBlocks (fun _ : Fin d => a) hdn) fun i : Fin d =>
        twist σ (detChar (Fin a) (absPow k (((d : ℂ) - 1) / 2 - (i : ℕ))))).IntertwiningMap σ',
        Function.Surjective f) →
      IsL ↑((List.range d).flatMap fun i : ℕ =>
        (List.ofFn fun j => (Δ j).nu (s j)).map fun Γ => Γ.nu ((((d : ℝ) - 1) / 2 - i : ℝ) : ℂ)) σ' := by
  first | exact @GlobalTheory.speh_quotient_isL | exact GlobalTheory.speh_quotient_isL | (intros; apply GlobalTheory.speh_quotient_isL <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

theorem _root_.GlobalTheory.T.langlands_classification_unitary : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], GlobalTheory.Published.StandardCosocleGL → (∀ (δ δ' : IrrGL (k := k)) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
      IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y) →
    ∀ 𝔫 : Multiset (Segment k), (∀ Δ ∈ 𝔫, ∃ (δ : IrrGL (k := k)) (Γ : Segment k) (t : ℝ), IsLSeg Γ δ.rep ∧
      IsUnitarisable δ.rep ∧ Δ = Γ.nu (t : ℂ)) → ∃ y : IrrGL (k := k), IsL 𝔫 y.rep := by
  first | exact @GlobalTheory.LocGL.exists_isL_of_unitary_twists | exact GlobalTheory.LocGL.exists_isL_of_unitary_twists | (intros; apply GlobalTheory.LocGL.exists_isL_of_unitary_twists <;> assumption)
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocLanglands.LExtInj

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_irreducible_GL_zero : ∃ t : IrrGL (k := k), t.1 = 0 ∧ IsL (0 : Multiset (Segment k)) t.rep :=
  ⟨IrrGL.of (detRep (Fin 0) (1 : kˣ →* ℂˣ)) ((isSmooth_ofChar_iff _).2 isSmoothChar_one.detChar)
    (isIrreducible_ofChar _), rfl, (Tests.empty_spec (k := k)).2.of_equiv (IrrGL.equivOf _ _ _)⟩

theorem sum_fst_of_lFactors' {𝔪 : Multiset (Segment k)} {c : ℕ} {x : Fin c → IrrGL (k := k)} (hx : LFactors 𝔪 x) :
    ∑ a, (x a).1 = (𝔪.map Segment.deg).sum := by
  obtain ⟨Δ, ⟨rfl, -⟩, hΔ⟩ := hx
  rw [Multiset.map_map, ← Finset.sum_eq_multiset_sum]
  exact Finset.sum_congr rfl fun a _ => (hΔ a).deg_eq.symm

theorem deg_of_isL' {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ} {𝔪 : Multiset (Segment k)}
    {π : Representation ℂ (GL (Fin N) k) V} (h : IsL 𝔪 π) : (𝔪.map Segment.deg).sum = N := by
  obtain ⟨_, x, hd, hx, -⟩ := h
  exact (sum_fst_of_lFactors' hx).symm.trans hd

theorem eq_of_isL (hM : LanglandsMultisegments) [CharZero k] (𝔪 : Multiset (Segment k)) (x y : IrrGL (k := k))
    (hx : IsL 𝔪 x.rep) (hy : IsL 𝔪 y.rep) : x = y := by
  obtain ⟨t, ht0, ht⟩ := exists_irreducible_GL_zero (k := k)
  have hdeg : x.1 = y.1 := (deg_of_isL' hx).symm.trans (deg_of_isL' hy)
  obtain ⟨nx, cx⟩ := x
  obtain ⟨ny, cy⟩ := y
  obtain rfl : nx = ny := hdeg
  have hd : ∑ a, (![(⟨nx, cx⟩ : IrrGL (k := k)), t] a).1 = nx := by simp [Fin.sum_univ_two, ht0]
  have hs := (hM k).2 𝔪 0 ![⟨nx, cx⟩, t] ⟨nx, cy⟩ hd hx ht (by rwa [add_zero])
  obtain ⟨φ⟩ := GlobalTheory.T.nonempty_equiv_prodChosenIrrGL_pair_degreeZero k (⟨nx, cx⟩ : IrrGL (k := k)) t ht0 hd
  have hs2 : IsSubquotient (IrrGL.rep (⟨nx, cy⟩ : IrrGL (k := k))) (IrrGL.rep (⟨nx, cx⟩ : IrrGL (k := k))) :=
    hs.trans (.of_injective φ.symm.toIntertwiningMap φ.symm.toLinearEquiv.injective)
  obtain ⟨ψ⟩ := hs2.nonempty_equiv cy.rep.irr cx.rep.irr
  congr 1
  rw [← cx.cl_rep, ← cy.cl_rep]
  exact IrrRep.cl_eq_iff.2 ⟨ψ⟩

end Local

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem isIrrWD_lpTw {y : WD h} (hy : IsIrrWD y) (s : ℝ) : IsIrrWD (y.lpTw s) := by
  obtain ⟨n, a, rfl, ha⟩ := hy
  exact ⟨n, a.tw s, (WD.lpTw_mk a s).symm, isIrreducible_twist ha _⟩

theorem lpTw_injective {y y' : WD h} {s : ℝ} (e : y.lpTw s = y'.lpTw s) : y = y' := by
  have := congrArg (fun z : WD h => z.lpTw (-s)) e
  simpa only [WD.lpTw_add, add_neg_cancel, WD.lpTw_zero] using this

end GlobalTheory.LocLanglands.LExtInj

end
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.centralCharacter_eq_prod_supercuspidalSupport : BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL (k := k)) (s : Multiset (IrrGL (k := k))) (ω : kˣ →* ℂˣ), HasSupport x.rep s → HasCentralChar x.rep ω → ∃ f : IrrGL (k := k) → kˣ →* ℂˣ, (∀ y ∈ s, HasCentralChar y.rep (f y)) ∧ ∀ z, ω z = (s.map fun y => f y z).prod := by
  first | exact @GlobalTheory.CentralSupport.centralChar_eq_prod_support | exact GlobalTheory.CentralSupport.centralChar_eq_prod_support | (intros; apply GlobalTheory.CentralSupport.centralChar_eq_prod_support <;> assumption)
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocGL.SupportPerm

theorem isSubquotient_prodIrr_of_hasSupport : ZelevinskyPolynomialRing → BernsteinZelevinskyFiniteness →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
      (n t : ℕ) (τ : IrrRep (GL (Fin n) k)) (x : Fin t → IrrGL (k := k)) (hd : ∑ i, (x i).1 = n),
      HasSupport τ.ρ (Finset.univ.val.map x) → IsSubquotient τ.ρ (prodIrr x hd) := by
  intro hZ _ k _ _ _ _ _ n t τ x hd hs
  obtain ⟨Z, Ψ, -, hΨ, -⟩ := hZ k
  have h1 := SupportRing.pos_pc_sub hΨ hs τ.smooth τ.irr
  obtain ⟨hp, ep⟩ := SupportRing.prodIrr_cls hΨ x hd
  refine SupportRing.isSubquotient_of_clsGL_ne hp τ.smooth τ.irr ?_
  have h2 := h1 (IrrGL.of τ.ρ τ.smooth τ.irr)
  rw [SupportRing.pc_map, ← ep] at h2
  have e1 : ∀ (A : GrothGL k) (y : IrrGL (k := k)), Ψ.symm (Ψ A - SupportRing.bas Ψ y) y = A y - 1 := by
    intro A y
    rw [SupportRing.bas, ← map_sub, Ψ.symm_apply_apply, Finsupp.sub_apply, Finsupp.single_eq_same]
  rw [e1] at h2
  intro h3
  rw [h3] at h2
  exact absurd h2 (by norm_num)

end GlobalTheory.LocGL.SupportPerm
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.tate_no_twisted_invariants_complexPadic : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (m : ℤ), m ≠ 0 → ∀ x : ℂ_[l], (∀ g : ↥(GK K), Per.σC (g : GQ l) x = ((((P.χQ (g : GQ l)) ^ m : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) * x) → x = 0 := by
  first | exact @GlobalTheory.TateChiQ.tate_chiQ | exact GlobalTheory.TateChiQ.tate_chiQ | (intros; apply GlobalTheory.TateChiQ.tate_chiQ <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

theorem _root_.GlobalTheory.T.wach_functor_three_layer_properties_every_place : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; Laws (HW l) (F l) h := by
  first | exact @GlobalTheory.NL.AllLaws.laws | exact GlobalTheory.NL.AllLaws.laws | (intros; apply GlobalTheory.NL.AllLaws.laws <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.wachFunctorRing_psiOperator_exists_of_good : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∃ ψ : W.EE →ₗ[↥(OL LL)] W.EE, (∀ a x, ψ (W.φE a * x) = a * ψ x) ∧ (∀ g x, ψ (W.γE g x) = W.γE g (ψ x)) ∧ ∀ j < l, ∀ a, ψ (algebraMap (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) W.EE ((1 : (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)))) + (letπ : (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))))) ^ j * W.φE a) = if j = 0 then a else 0 := by
  first | exact @GlobalTheory.psiE_exists | exact GlobalTheory.psiE_exists | (intros; apply GlobalTheory.psiE_exists <;> assumption)
end
