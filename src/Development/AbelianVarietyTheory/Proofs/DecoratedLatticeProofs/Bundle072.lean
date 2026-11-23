module

public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBoundLatLoc
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixMeasureTopBlockIntegralGLMaxIdeal
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle028
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle296
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1047
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle097
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle101
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Formalism.LocalToGlobal.Columns.ChainTw
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle067
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle068
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdentityCosetEntryProportionalColumnDatum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019

@[expose] public section

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory

theorem absFin_latLoc_le : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (v : HeightOneSpectrum (𝓞 F)),
    ∃ C : ℝ≥0, ∀ y ∈ latLoc F L v, ∀ i, absFin F v (y i) ≤ C := by
  first
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact @_root_.GlobalTheory.LocalLatticeBound.exists_bound_latLoc
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact _root_.GlobalTheory.LocalLatticeBound.exists_bound_latLoc
  | exact @_root_.GlobalTheory.LocalLatticeBound.exists_bound_latLoc
  | exact _root_.GlobalTheory.LocalLatticeBound.exists_bound_latLoc
  | (apply _root_.GlobalTheory.LocalLatticeBound.exists_bound_latLoc <;> assumption)
  | (intros; apply _root_.GlobalTheory.LocalLatticeBound.exists_bound_latLoc <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LocalLatticeBound.exists_bound_latLoc <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LocalLatticeBound.exists_bound_latLoc ..)

end GlobalTheory
end

section

open MeasureTheory Matrix Formalism.IndefR.Datum

theorem _root_.GlobalTheory.T.matrixMeasure_topBlock_integralGL_maxIdeal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (a b r : ℕ), r ≤ a → r ≤ b → (GlobalTheory.SplitWeil.volM ν (Fin b) (Fin a) {x | topL r x ∈ Units.val '' (GlobalTheory.SplitWeil.KO k (Fin r) : Set (GL (Fin r) k)) ∧ (∀ i j, ValuativeRel.valuation k (x i j) ≤ 1) ∧ ∀ i j, r ≤ i.val → j.val < r → ValuativeRel.valuation k (x i j) < 1}).toReal = (GlobalTheory.SplitWeil.volM ν (Fin b) (Fin a) {x | ∀ i j, ValuativeRel.valuation k (x i j) ≤ 1}).toReal * ((∏ n ∈ Finset.Ioc 0 r, (1 - ((GlobalTheory.SplitWeil.resCard k : ℝ) ^ n)⁻¹)) * ((GlobalTheory.SplitWeil.resCard k : ℝ) ^ (r * (b - r)))⁻¹) := by
  first | exact @GlobalTheory.RectBlockVolume.vol_topBlock_KO | exact GlobalTheory.RectBlockVolume.vol_topBlock_KO | (intros; apply GlobalTheory.RectBlockVolume.vol_topBlock_KO <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.SymChain

theorem allPositions_holds : AllPositions := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _
  have hpat : S.Pattern t := GlobalTheory.T.symmetricLevelChain_pattern_iterated k s κ S t
  have hsupp : S.SupportAt t := GlobalTheory.T.symmetricLevelChain_supportAt_of_pattern k s κ S t hpat
  have hclass : S.ClassAt t ν := GlobalTheory.T.symmetricLevelChain_classAt_every_position k ν hν s κ S t
  exact ⟨GlobalTheory.T.symmetricLevelChain_oneIndexAt_of_class_support k ν hν s κ S t hclass hsupp, GlobalTheory.T.symmetricLevelChain_unfolded_position_exchange k ν hν s κ S t hpat⟩

end GlobalTheory.SymChain
end

section

open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.KJInf

theorem lft_rename_unit {a : ℕ} (u : Matrix (Fin a) (Fin a) ℂ) (f : MvPolynomial (Fin a × Fin a) ℂ) :
    lft (fun _ : Unit => u) (rename (Prod.mk ()) f) = rename (Prod.mk ()) (Formalism.GradedWeylDivisibility.rowAct ℂ u f) := by
  have : (lft (fun _ : Unit => u)).comp (rename (Prod.mk ())) = (rename (Prod.mk ())).comp (Formalism.GradedWeylDivisibility.rowAct ℂ (n := a) u) := by
    apply MvPolynomial.algHom_ext
    intro v

    simp [lft, Formalism.GradedWeylDivisibility.rowAct, rename_X, aeval_X, map_sum]
  exact congrArg (fun φ => φ f) this

theorem lft_frDet_unit {a : ℕ} (u : Matrix (Fin a) (Fin a) ℂ) :
    lft (fun _ : Unit => u) (frDet ℂ a ()) = C u.det * frDet ℂ a () := by
  unfold frDet
  rw [AlgHom.map_det]
  have : (lft (fun _ : Unit => u)).mapMatrix (Matrix.of fun α s : Fin a => (X ((), α, s) : PY Unit a)) =
      u.map C * Matrix.of fun α s : Fin a => (X ((), α, s) : PY Unit a) := by
    ext i j
    simp [lft, aeval_X, Matrix.mul_apply]
  rw [this, Matrix.det_mul, RingHom.map_det]
  rfl

theorem frDet_unit_ne_zero (a : ℕ) : frDet ℂ a () ≠ 0 := by
  have h : frDet ℂ a () = rename (Prod.mk ()) (Matrix.mvPolynomialX (Fin a) (Fin a) ℂ).det := by
    unfold frDet
    rw [AlgHom.map_det]
    congr 1
    ext i j
    simp [Matrix.mvPolynomialX]
  rw [h]
  intro e
  apply Matrix.det_mvPolynomialX_ne_zero (Fin a) ℂ
  exact rename_injective _ (Prod.mk_right_injective ()) (e.trans (map_zero _).symm)

theorem CSpan_unit {a : ℕ} (lam : Unit → DomWeight a) :
    CSpan lam = (delSq ℂ a (lam ())).map (rename (R := ℂ) (Prod.mk ())).toLinearMap := by
  apply le_antisymm
  · unfold CSpan
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    refine ⟨f (), hf (), ?_⟩
    simp [ten]
  · rintro _ ⟨f, hf, rfl⟩
    apply Submodule.subset_span
    refine ⟨fun _ => f, fun _ => hf, ?_⟩
    simp [ten]

theorem Vn_unit_irreducible : ∀ (a : ℕ), 0 < a → ∀ (lam : Unit → DomWeight a) (n : Unit → ℕ), Vn lam n ≠ ⊥ ∧
    ∀ U : Submodule ℂ (PY Unit a), U ≤ Vn lam n → (∀ k, IsUni k → ∀ F ∈ U, lft k F ∈ U) → U = ⊥ ∨ U = Vn lam n := by
  intro a _ lam n
  set D : PY Unit a := ∏ τ, frDet ℂ a τ ^ n τ with hDdef
  have hD : D = frDet ℂ a () ^ n () := by simp [D]
  have hD0 : D ≠ 0 := hD ▸ pow_ne_zero _ (frDet_unit_ne_zero a)
  let φ : MvPolynomial (Fin a × Fin a) ℂ →ₗ[ℂ] PY Unit a :=
    LinearMap.mulRight ℂ D ∘ₗ (rename (R := ℂ) (Prod.mk ())).toLinearMap
  have hφ : ∀ f, φ f = rename (Prod.mk ()) f * D := fun f => rfl
  have hVn : Vn lam n = (delSq ℂ a (lam ())).map φ := by
    rw [Vn, CSpan_unit, ← Submodule.map_comp]
  have hinj : Function.Injective φ := by
    intro f g e
    rw [hφ, hφ] at e
    exact rename_injective _ (Prod.mk_right_injective ()) (mul_right_cancel₀ hD0 e)
  have hdel : delSq ℂ a (lam ()) = Formalism.GradedWeylDivisibility.dualWeyl ℂ a a (lam ()).natW := by
    rw [← Formalism.L2.Col.nablaSq_eq_delSq]; rfl
  have hanti : Antitone (lam ()).natW := fun i j hij => by
    have := (lam ()).anti hij
    simp only [DomWeight.natW]
    omega
  constructor
  · intro h
    rw [hVn] at h
    have h2 : delSq ℂ a (lam ()) = ⊥ :=
      Submodule.map_injective_of_injective hinj (h.trans (Submodule.map_bot _).symm)
    have hne : nablaSq ℂ a (lam ()) ≠ ⊥ := Submodule.nontrivial_iff_ne_bot.mp inferInstance
    exact hne (by rw [Formalism.L2.Col.nablaSq_eq_delSq]; exact h2)
  · intro U hU hst
    let M : Submodule ℂ (MvPolynomial (Fin a × Fin a) ℂ) := U.comap φ
    have hMU : M.map φ = U := by
      apply Submodule.map_comap_eq_self
      refine hU.trans ?_
      rw [hVn]
      exact LinearMap.map_le_range
    have hMd : M ≤ delSq ℂ a (lam ()) := by
      intro f hf
      have h1 : φ f ∈ (delSq ℂ a (lam ())).map φ := hVn ▸ hU hf
      obtain ⟨g, hg, e⟩ := h1
      exact hinj e ▸ hg
    have hrow : ∀ u ∈ Matrix.unitaryGroup (Fin a) ℂ, ∀ f ∈ M, Formalism.GradedWeylDivisibility.rowAct ℂ u f ∈ M := by
      intro u hu f hf
      have h1 := hst (fun _ => u) (fun _ => hu) (φ f) hf
      have hdet : u.det ≠ 0 := by
        have h := (Matrix.mem_unitaryGroup_iff.mp hu)
        have h' := congrArg Matrix.det h
        rw [Matrix.det_mul, Matrix.det_one] at h'
        exact left_ne_zero_of_mul_eq_one h'
      have e : lft (fun _ : Unit => u) (φ f) = (u.det ^ n ()) • φ (Formalism.GradedWeylDivisibility.rowAct ℂ u f) := by
        rw [hφ, hφ, map_mul, lft_rename_unit, hD, map_pow, lft_frDet_unit, smul_eq_C_mul, map_pow, mul_pow]
        ring
      rw [e] at h1
      exact (U.smul_mem_iff (pow_ne_zero _ hdet)).1 h1
    by_cases hM : M = ⊥
    · left
      rw [← hMU, hM, Submodule.map_bot]
    · right
      apply le_antisymm hU
      rw [hVn, ← hMU]
      apply Submodule.map_mono
      rw [hdel]
      exact GlobalTheory.Branching.dualWeyl_le_of_rowDivClosed le_rfl _ hanti M (hdel ▸ hMd)
        (GlobalTheory.Branching.rowDivClosed_of_rowAct_stable M (GlobalTheory.Branching.rowAct_mem_of_unitary_stable M hrow)) hM
end GlobalTheory.KJInf
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.Core.Ht2
open scoped ComplexOrder

namespace GlobalTheory.Core.Ht2.BadPrimesS

open GlobalTheory.ColNorms.BadPrimes

theorem bad_primes_sharp : ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → (∀ P ∈ rowSG Pr sel mu, P ∈ Pr.vGs) ∧ (∀ P ∈ Pr.vGs, ∃ i, P ∈ Pr.vG i ∧ Formalism.L2.Col.qOf P = Pr.g i ∧ ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal ∧ ((Pr.g i : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2 ∧ ((Pr.g (1 - i) : ℕ) : 𝓞 X.E) ∉ P.asIdeal ∧ ((Pr.T u : ℕ) : 𝓞 X.E) ∉ P.asIdeal ∧ Pr.piT u ∉ P.asIdeal) ∧ (∀ P ∈ Pr.vT u, ((Pr.T u : ℕ) : 𝓞 X.E) ∈ P.asIdeal) ∧ (∏ P : rowSG Pr sel mu, Formalism.L2.Col.qOf P.1) = (Pr.g 0 * Pr.g 1) ^ N.R.f ∧ Odd (Pr.T u) ∧ (∀ i, Odd (Pr.g i)) ∧ ∀ P ∈ Sall sel mu u, conjPrime₂ P ∉ Sall sel mu u ∧ (2 : 𝓞 X.E) ∉ P.asIdeal := by
  classical
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ h
  obtain ⟨⟨-, -, -, -, -, -, hX1, -, -, hPr, -, hc, -, -⟩, -, -, -, hmu, -⟩ := h
  subst hmu
  have hX := hX1.ok
  have h2 : 2 ∣ Pr.cond := by
    rw [hc, NumDatum.cond]
    exact N.H.toHostRaw.two_dvd_condN
  have hS : ∀ P, P ∈ Sall sel (1 : Tup X.F X.E X.K Sg) u ↔ P ∈ Pr.vT u ∨ P ∈ Pr.vGs := fun P => by
    rw [← rowSG_one sel Sg]
    exact Finset.mem_union
  refine ⟨fun P hP => rowSG_one sel Sg ▸ hP, fun P hP => ?_, fun P hP => T_mem hPr hP, ?_, odd_typePrime_of_two_dvd_cond hX hPr h2 u,
    odd_g hPr h2, fun P hP => ⟨fun h' => conjP_notMem hPr u ((hS _).1 hP) ((hS _).1 h'), ?_⟩⟩
  · obtain ⟨i, hi⟩ := exists_vG hP
    have hT : ((Pr.T u : ℕ) : 𝓞 X.E) ∉ P.asIdeal := fun hT =>
      hPr.T_ne_g u i (eq_of_natCast_mem P (hPr.T_prime u) (hPr.g_prime i) hT (g_mem hPr hi))
    refine ⟨i, hi, hPr.vG_norm i P hi, g_mem hPr hi,
      (GlobalTheory.TypePrimeUnif.typePrime_mem_and_notMem_sq hX hPr i P hi).2, fun hg => ?_, hT,
      fun hπ => hT (hPr.piT_norm u ▸ Ideal.mul_mem_right _ _ hπ)⟩
    have := g_injective hPr (eq_of_natCast_mem P (hPr.g_prime _) (hPr.g_prime _) hg (g_mem hPr hi))
    fin_cases i <;> simp at this
  · rw [Finset.prod_coe_sort _ (fun P => Formalism.L2.Col.qOf P), rowSG_one, prod_qOf_vGs hPr,
      GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.card_eq_f N X pl.symm]
  · rcases (hS _).1 hP with h | h
    · exact two_notMem_vT hPr h2 h
    · obtain ⟨i, hi⟩ := exists_vG h
      intro hP2
      have := eq_of_natCast_mem P (hPr.g_prime i) Nat.prime_two (g_mem hPr hi) (by exact_mod_cast hP2)
      have ho := odd_g hPr h2 i
      rw [this] at ho
      exact absurd ho (by decide)

end GlobalTheory.Core.Ht2.BadPrimesS
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.Core.Ht2
open scoped ComplexOrder

namespace GlobalTheory.Core.Ht2.AAUnitS

theorem aaUnit_bad_sharp : ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ B : Base D D.host.ccK dl, (ambOf s B χ cD).AAUnit (Sall sel mu u) := by
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ h B P hP
  have hcond := h.1.pr_cond
  obtain ⟨⟨-, -, -, hcc, -, -, -, -, -, hPr, -⟩, -, -, -, hmu, -⟩ := h
  subst hmu
  obtain ⟨l, hl, hlP, hd⟩ := GlobalTheory.ColNormsUnit.exists_prime hPr sel u P hP
  rw [hcond] at hd
  refine GlobalTheory.AAUnitAway.locP_AA D X s _ dl B χ cD P l hl ?_ ?_ hlP ?_
  · intro hs
    exact hd (((Nat.dvd_of_mem_primeFactors hs).mul_right _).mul_right _)
  · rintro rfl
    exact hd ((dvd_mul_left _ _).mul_right _)
  · rw [hcc, Ideal.absNorm_top]
    exact Nat.coprime_one_left _

end GlobalTheory.Core.Ht2.AAUnitS
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

theorem _root_.GlobalTheory.T.local_volume_agrees_row_subgroup_unitary : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → VolAgree (R := R) sel mu cst σ₀ P ι s W ν := by
  first | exact @GlobalTheory.VolBridge.vol_agree | exact GlobalTheory.VolBridge.vol_agree | (intros; apply GlobalTheory.VolBridge.vol_agree <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

theorem _root_.GlobalTheory.T.twistIndexData_representative_dependsOnDoubleCoset : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (m2 : ℕ) (G : ChGlob X R.m), (twIdx Ch sel mu cst m2).Ok Ch sel mu cst G m2 → IdxProd sel mu cst (twIdx Ch sel mu cst m2) := by
  first | exact @GlobalTheory.TwBridge.idxProd_twIdx | exact GlobalTheory.TwBridge.idxProd_twIdx | (intros; apply GlobalTheory.TwBridge.idxProd_twIdx <;> assumption)
end

section

noncomputable section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo

namespace GlobalTheory.CuspGeo.TraceUnitary

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

def trBil (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) : (Fin n → E) →ₗ[ℚ] (Fin n → E) →ₗ[ℚ] ℚ :=
  LinearMap.mk₂ ℚ (fun x y => Algebra.trace ℚ E (Formalism.UG.hform σ J x y))
    (fun x x' y => by
      rw [← map_add (f := _)]; congr 1
      simp [Formalism.UG.hform, add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      rw [← map_smul]; congr 1
      simp [Formalism.UG.hform, Finset.smul_sum, Rat.smul_def, mul_assoc])
    (fun x y y' => by
      rw [← map_add (f := _)]; congr 1
      simp [Formalism.UG.hform, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      rw [← map_smul]; congr 1
      simp only [Formalism.UG.hform, Finset.smul_sum, Rat.smul_def, Pi.smul_apply]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)

theorem trBil_apply (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    trBil σ J x y = Algebra.trace ℚ E (Formalism.UG.hform σ J x y) := rfl

omit [NumberField E] in
theorem hform_smul_right (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) (a : E) :
    Formalism.UG.hform σ J x (a • y) = a * Formalism.UG.hform σ J x y := by
  simp only [Formalism.UG.hform, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem span_eq_top {N : ℕ} (e : Fin N → Fin n → E)
    (h : ∀ u : Fin n → E, (∀ i, IsIntegral ℤ (u i)) → ∃ z : Fin N → ℤ, u = ∑ i, z i • e i) :
    Submodule.span ℚ (Set.range e) = ⊤ := by
  classical
  rw [eq_top_iff]
  intro u _
  obtain ⟨d, hd, hint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image u)
  obtain ⟨z, hz⟩ := h (d • u) (fun i => hint (u i) (Finset.mem_image_of_mem u (Finset.mem_univ i)))
  have h1 : (d : ℚ) • u ∈ Submodule.span ℚ (Set.range e) := by
    rw [Int.cast_smul_eq_zsmul, hz]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  exact (Submodule.smul_mem_iff _ hd').1 h1

theorem unitary_of_trace (σ : E →+* E) (J M : Matrix (Fin n) (Fin n) E) {N : ℕ} (e : Fin N → Fin n → E)
    (hs : Submodule.span ℚ (Set.range e) = ⊤)
    (h : ∀ i j, trBil σ J (M *ᵥ e i) (M *ᵥ e j) = trBil σ J (e i) (e j)) :
    Formalism.UG.cT σ M * J * M = J := by
  classical
  let f : (Fin n → E) →ₗ[ℚ] (Fin n → E) := (Matrix.mulVecLin M).restrictScalars ℚ
  have hB : (trBil σ J).compl₁₂ f f = trBil σ J := by
    refine LinearMap.ext_on_range hs fun i => LinearMap.ext_on_range hs fun j => ?_
    simpa [f] using h i j
  have hB' : ∀ x y, trBil σ J (M *ᵥ x) (M *ᵥ y) = trBil σ J x y := fun x y => by
    have := LinearMap.congr_fun₂ hB x y
    simpa [f] using this
  have hh : ∀ x y, Formalism.UG.hform σ J (M *ᵥ x) (M *ᵥ y) = Formalism.UG.hform σ J x y := fun x y => by
    by_contra hne
    have hD : Formalism.UG.hform σ J (M *ᵥ x) (M *ᵥ y) - Formalism.UG.hform σ J x y ≠ 0 := sub_ne_zero.2 hne
    have h1 := hB' x ((Formalism.UG.hform σ J (M *ᵥ x) (M *ᵥ y) - Formalism.UG.hform σ J x y)⁻¹ • y)
    rw [Matrix.mulVec_smul, trBil_apply, trBil_apply, hform_smul_right, hform_smul_right, ← sub_eq_zero,
      ← map_sub, ← mul_sub, inv_mul_cancel₀ hD, ← (algebraMap ℚ E).map_one, Algebra.trace_algebraMap] at h1
    have : Module.finrank ℚ E ≠ 0 := Module.finrank_pos.ne'
    simp [this] at h1
  ext i j
  have := hh (Pi.single i 1) (Pi.single j 1)
  simp only [Formalism.UG.hform, Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply] at this
  simp only [Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm, this]
  simp [apply_ite σ]

end GlobalTheory.CuspGeo.TraceUnitary

namespace GlobalTheory.CuspGeo

theorem unitary_of_trForm_zBasis (I : AutInst) {N : ℕ} (e : Fin N → Fin I.n → I.E)
    (M : Matrix (Fin I.n) (Fin I.n) I.E) (he : IsZBasis I e)
    (h : ∀ i j, trForm I (M *ᵥ e i) (M *ᵥ e j) = trForm I (e i) (e j)) :
    Formalism.UG.cT (starRingEnd I.E) M * I.J * M = I.J :=
  TraceUnitary.unitary_of_trace _ _ _ e (TraceUnitary.span_eq_top e fun u hu => (he.2 u).1 hu) h

end GlobalTheory.CuspGeo

end
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

theorem _root_.GlobalTheory.T.lastStep_testFunctions_agree_rationalPoints : ∀ (E K k : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (s κ : ℕ) (S : SymData k s κ), Comparison₂ P q ι σ₀ ψ₀ χ S → PhiTopAgree P q ι σ₀ ψ₀ χ S := by
  first | exact @GlobalTheory.SymBridge.phiTopAgree_of_tie | exact GlobalTheory.SymBridge.phiTopAgree_of_tie | (intros; apply GlobalTheory.SymBridge.phiTopAgree_of_tie <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

theorem _root_.GlobalTheory.T.psiDatum_agree_columnDatum_at_typePrime : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (S : SymData k s R.k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → AtType Ch sel mu cst σ₀ P ι S → PsiAgree Ch sel mu cst σ₀ P ι S := by
  first | exact @GlobalTheory.SymBridge.psiAgree_of_atType | exact GlobalTheory.SymBridge.psiAgree_of_atType | (intros; apply GlobalTheory.SymBridge.psiAgree_of_atType <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

theorem _root_.GlobalTheory.T.identityCoset_entry_proportional_columnDatum : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (S : SymData k s R.k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → AtType Ch sel mu cst σ₀ P ι S → EntryAgree Ch sel mu cst σ₀ P ι S ν := by
  first | exact @GlobalTheory.EntryBridge.entry_agree | exact GlobalTheory.EntryBridge.entry_agree | (intros; apply GlobalTheory.EntryBridge.entry_agree <;> assumption)
end
