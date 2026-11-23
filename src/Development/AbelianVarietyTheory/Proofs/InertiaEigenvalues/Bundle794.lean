module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle783
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle102
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle630
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle227
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle245
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle268
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle685
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle658
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle759
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle668
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle655
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle654
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle694
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle782
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle656
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTaylorShiftFrobeniusTwoVariableCompatible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle653
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle663
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicValNatFactorialBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle725
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrincipalCongruenceFixedVectorsLeSmoothVectors
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle066
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroSupercuspidalCuspidalModule
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Formalism.AlgebraicWeights.InertDatumExists
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle786
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.PhiFix

theorem frob_actB {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [NormedField K]
    [Algebra O K] [NormedAlgebra ℚ_[l] K] (T : LocLat (Gl l) ℚ_[l] K O) (g : Gl l) (x : TW (OB l O) T) :
    TWmap (frobOB l O) T (actB (sQ l) T g x) = actB (sQ l) T g (TWmap (frobOB l O) T x) := by
  have hB : ∀ r : OB l O, frobOB l O (galOB O (sQ l g) r) = galOB O (sQ l g) (frobOB l O r) := by
    intro r
    induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul o β =>
      simp only [frobOB, galOB, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      exact congrArg (fun y : Per.Bcris l => o ⊗ₜ[ℤ_[l]] y) ((GlobalTheory.MemLoc.ActLaws.act_laws l).2.2.2.2.1 _ β)
    | add r s hr hs => rw [map_add (galOB O (sQ l g)), map_add (frobOB l O), map_add (frobOB l O), map_add (galOB O (sQ l g)), hr, hs]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    simp only [actB, TWmap, TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply, hB]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem frob_fixed_coboundary : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, ∀ b, R.IsPotential y b → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → TWmap (frobOB l O) T (actB (sQ l) T g b - b) = actB (sQ l) T g b - b := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R y hyY b hb g hg
  obtain ⟨hy, m₀, σ, b₀, hm₀, -, hconn, hb₀, rfl⟩ := hb
  haveI : CompleteSpace K := GlobalTheory.T.completeSpace_of_finite_padicInt_unitBall l O K
  obtain ⟨d, hd⟩ := GlobalTheory.T.phi_sub_sub_mem_xi_of_monodromy_eq O K l e a ι η H D y hyY σ.1 hconn
  obtain ⟨-, hall⟩ := GlobalTheory.T.breuilKisin_bcris_comparison_frobenius_naturality l a e O K t ϖ ι D.toPhiMod T R.I
  obtain ⟨hφ, huniq, hfrobv, -, -⟩ := hall R.jB R.cmp
  have hσφ : D.phi σ.1 ∈ D.MMl := GlobalTheory.T.phi_mem_invertedLattice O K l e a ι η H D σ.1 σ.2
  have hyφ : D.phi y ∈ D.MMl := GlobalTheory.T.phi_mem_invertedPrime_lattice_of_mem_eisensteinInvariants O K l e a ι η H D y hyY

  have hv1 := IsCrisVal.sub t ϖ (hfrobv _ _ hb₀) hb₀
  have hv2 := GlobalTheory.T.tensorBcris_value_frobenius_of_inverse_eisenstein_twist l a e O K t ϖ ι η H D T R.jB y hyY hy hyφ
  have hw : phiW t ϖ D.toPhiMod (phiW t ϖ D.toPhiMod m₀) - phiW t ϖ D.toPhiMod m₀ =
      phiW t ϖ D.toPhiMod (toW t ϖ D.toPhiMod ⟨y, hy⟩) := by rw [← hm₀, map_sub]
  rw [hw] at hv1
  have hb0 := huniq _ _ _ hv1 hv2
  have hs := hφ σ ⟨D.phi σ.1, hσφ⟩ rfl
  have hmem : D.xi d ∈ D.MMl := by
    rw [← hd]; exact sub_mem (sub_mem hσφ σ.2) hyφ
  have hkey : TWmap (frobOB l O) T (R.jB (toBcris t ϖ D.toPhiMod σ) - b₀) -
      (R.jB (toBcris t ϖ D.toPhiMod σ) - b₀) = R.jB (toBcris t ϖ D.toPhiMod ⟨D.xi d, hmem⟩) := by
    have he : (⟨D.xi d, hmem⟩ : D.MMl) = ⟨D.phi σ.1, hσφ⟩ - σ - ⟨D.phi y, hyφ⟩ := Subtype.ext (by
      simp only [Submodule.coe_sub]; exact hd.symm)
    rw [he, map_sub, map_sub, map_sub, map_sub, map_sub, ← hs, ← hb0]
    abel
  have hfix := R.horiz g hg d hmem
  rw [← hkey, map_sub] at hfix
  rw [map_sub, frob_actB]
  exact sub_eq_sub_iff_sub_eq_sub.1 hfix

end GlobalTheory.BKGal.PhiFix
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CocycleKinf

variable {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e} {ι : Type} [Fintype ι]
  [DecidableEq ι] {G : Type} [Group G] [TopologicalSpace G] {T : LocLat G ℚ_[l] K O}

theorem inclL_smul (P : PhiMod O K l e a ι) (r : OA l O) (c : ι → OA l O) :
    inclL t ϖ P (r • c) = inclO l O r • inclL t ϖ P c := by
  rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
  congr 1
  ext1 i
  simp [map_mul]

theorem isCrisVal_add (P : PhiMod O K l e a ι) (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T)
    {w w' : ι → OW l O} {b b' : TW (OB l O) T} (h : IsCrisVal t ϖ P jB w b)
    (h' : IsCrisVal t ϖ P jB w' b') : IsCrisVal t ϖ P jB (w + w') (b + b') := by
  obtain ⟨m, c, hm, hw, hb⟩ := h
  obtain ⟨m', c', hm', hw', hb'⟩ := h'
  refine ⟨m * m', m' • c + m • c', ?_, ?_, ?_⟩
  · rw [map_mul]; exact hm.mul hm'
  · rw [map_add (f := _), inclL_smul, inclL_smul, ← hw, ← hw', smul_smul, smul_smul, smul_add, map_mul,
      mul_comm (inclO l O m) (inclO l O m')]
  · have e1 : (fun i => toB l O ((m' • c + m • c') i)) =
        toB l O m' • (fun i => toB l O (c i)) + toB l O m • (fun i => toB l O (c' i)) := by
      ext1 i
      simp [map_add (f := _), map_mul]
    rw [e1, map_add (f := _), map_smul, map_smul, ← hb, ← hb', map_mul, smul_add, smul_smul, smul_smul,
      mul_comm (toB l O m') (toB l O m)]

theorem cocycle_mem_lattice_of_mem_GKinf : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, ∀ b, R.IsPotential y b → ∀ g : Gl l, sQ l g ∈ ϖ.GKinf → ∃ x : ↥T.L.T, actB (sQ l) T g b - b = (1 : OB l O) ⊗ₜ[O] x := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R y hyY b hpot g hg
  obtain ⟨hy, m₀, σ, b₀, hm₀, hσ, -, hval, rfl⟩ := hpot
  obtain ⟨γ, hγ⟩ := GlobalTheory.T.exists_muSemidirectCyclic_cover_of_mem_GKinf_coeffs l a e O K t ϖ (sQ l g) hg

  have hσfix : actB (sQ l) T g (R.jB (toBcris t ϖ D.toPhiMod σ)) = R.jB (toBcris t ϖ D.toPhiMod σ) :=
    GlobalTheory.T.kisinInfGalois_acts_through_descentDatum l a e O K t ϖ ι D.toPhiMod T R.I R.jB D.desc R.cmp R.desc g γ hγ σ σ (hσ γ).symm

  have hyfix : R.I.act (sQ l g) g (toW t ϖ D.toPhiMod ⟨y, hy⟩) = toW t ϖ D.toPhiMod ⟨y, hy⟩ :=
    R.desc g γ hγ ⟨y, hy⟩ ⟨y, hy⟩ (((Descent.mem_invOf _).1 hyY).2 γ).symm

  set w := R.I.act (sQ l g) g m₀ - m₀ with hw
  have hφw : phiW t ϖ D.toPhiMod w = w := by
    have h1 : phiW t ϖ D.toPhiMod w - w =
        R.I.act (sQ l g) g (phiW t ϖ D.toPhiMod m₀ - m₀) - (phiW t ϖ D.toPhiMod m₀ - m₀) := by
      rw [hw, map_sub, map_sub, R.I.act_phiW]; abel
    rw [hm₀, hyfix, sub_self] at h1
    exact sub_eq_zero.1 h1
  obtain ⟨x, hx⟩ : w ∈ LinearMap.range R.I.ofT := by rw [R.I.range_ofT]; exact hφw
  obtain ⟨-, huniq, -, hofT, hgal⟩ :=
    (GlobalTheory.T.breuilKisin_bcris_comparison_frobenius_naturality l a e O K t ϖ ι D.toPhiMod T R.I).2 R.jB R.cmp
  have h2 : IsCrisVal t ϖ D.toPhiMod R.jB (R.I.act (sQ l g) g (phiW t ϖ D.toPhiMod m₀))
      (actB (sQ l) T g b₀) := hgal g (R.stable g) _ _ hval
  have h3 : R.I.act (sQ l g) g (phiW t ϖ D.toPhiMod m₀) = phiW t ϖ D.toPhiMod m₀ + R.I.ofT x := by
    rw [R.I.act_phiW, hx, ← hφw, hw, map_sub]; abel
  rw [h3] at h2
  have h4 := huniq _ _ _ h2 (GlobalTheory.CocycleKinf.isCrisVal_add D.toPhiMod R.jB hval (hofT x))
  refine ⟨-x, ?_⟩
  rw [map_sub, hσfix, h4, tmul_neg]
  abel

end GlobalTheory.CocycleKinf
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CrysStrat

theorem single_mem_M {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (σ : ZMod a) (j : ι) :
    (Pi.single σ (Pi.single j (1 : K⟦X⟧)) : Vec K a ι) ∈ P.M := by
  refine mem_tot.2 fun τ => mem_vecs.2 fun i => ?_
  by_cases h : τ = σ
  · subst h; rw [Pi.single_eq_same]
    by_cases h' : i = j
    · subst h'; rw [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne h']; exact zero_mem _
  · rw [Pi.single_eq_of_ne h]; exact zero_mem _

theorem mulVec_single_one' {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R) (j i : ι) :
    (M *ᵥ Pi.single j 1) i = M i j := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem exists_stratification : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∀ (sh : (↥LL.1)⟦X⟧ →+* (↥LL.1)⟦X⟧⟦X⟧) (φ₂ : (↥LL.1)⟦X⟧⟦X⟧ →+* (↥LL.1)⟦X⟧⟦X⟧), (∀ (f : (↥LL.1)⟦X⟧) (i : ℕ), (i.factorial : (↥LL.1)⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := ↥LL.1))^[i] f) → (∀ f : (↥LL.1)⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob (↥LL.1) l f)) → (∀ f : (↥LL.1)⟦X⟧, φ₂ (sh f) = sh (frob (↥LL.1) l f)) → ∃ ε : ZMod a → Matrix ι ι (↥LL.1)⟦X⟧⟦X⟧, (∀ τ, (ε τ).map PowerSeries.constantCoeff = 1) ∧ (∀ τ, ε τ * ((P.mx (τ - 1)).map (frob (↥LL.1) l)).map sh = ((P.mx (τ - 1)).map (frob (↥LL.1) l)).map PowerSeries.C * (ε (τ - 1)).map φ₂) ∧ ∀ (τ : ZMod a) (i j : ι) (k : ℕ), (k.factorial : (↥LL.1)⟦X⟧) * coeff k (ε τ i j) ∈ S (↥(OL LL)) (↥LL.1) e := by
  intro hBS l _ a e _ _ ϖ LL _ _ hl ι _ _ P T I hBK sh φ₂ hsh hφC hφsh
  obtain ⟨EE, c, hinj, hcM, hsurj, hsemi, hO, hfr⟩ := GlobalTheory.T.breuilKisinPrism_crystal_coordinates l a e _ _ (thetaW a LL) ϖ ι P _ _ hBS hBK
  obtain ⟨PP, S₀, p₀, p₁, δ, j, j₀, hI, hδ, hj₀, hjp, hjφ, hS, hS', -⟩ :=
    GlobalTheory.T.exists_crystalline_prisms l a e (↥(OL LL)) (↥LL.1) (thetaW a LL) ϖ hl sh φ₂ hsh hφC hφsh
  obtain ⟨lam₀, hl₀, hv₀⟩ := GlobalTheory.T.exists_crystal_coordinates_over_breuilKisin l a e _ _ (thetaW a LL) ϖ ι EE c hsemi PP p₀ j PowerSeries.C
    (fun τ w => (hjp τ w).1)
  obtain ⟨lam₁, hl₁, hv₁⟩ := GlobalTheory.T.exists_crystal_coordinates_over_breuilKisin l a e _ _ (thetaW a LL) ϖ ι EE c hsemi PP p₁ j sh
    (fun τ w => (hjp τ w).2)
  obtain ⟨ε, hε⟩ := GlobalTheory.T.crystalline_phi_module_map_exists l a e _ _ (thetaW a LL) ϖ ι P EE c hinj hcM hsurj hsemi hO sh hsh PP p₀ p₁ j hjp
    lam₀ lam₁ hl₀ hl₁ hv₀ hv₁
  have hsh0 : ∀ f, PowerSeries.constantCoeff (sh f) = f := fun f => by
    simpa using hsh f 0

  have hcol : ∀ (τ : ZMod a) (jj : ι), ∃ x, c x = Pi.single (τ - 1) (Pi.single jj 1) :=
    fun τ jj => hsurj _ (single_mem_M P _ jj)
  have hv1 : ∀ (τ : ZMod a) (jj : ι) (x : EE.M (ϖ.prism a)), c x = Pi.single (τ - 1) (Pi.single jj 1) →
      lam₁ (EE.tr p₁ x) τ = Pi.single jj 1 := fun τ jj x hx => funext fun i => by
    rw [hv₁, hx, Pi.single_eq_same]
    by_cases h : i = jj
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  have hv0 : ∀ (τ : ZMod a) (jj : ι) (x : EE.M (ϖ.prism a)), c x = Pi.single (τ - 1) (Pi.single jj 1) →
      ∀ i, lam₀ (EE.tr p₁ x) τ i = ε τ i jj := fun τ jj x hx i => by
    rw [hε, hv1 τ jj x hx, mulVec_single_one']
  have hlK : (l : ↥LL.1) ≠ 0 := by
    have h := (map_ne_zero (algebraMap ℚ_[l] ↥LL.1)).2
      (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero : (l : ℚ_[l]) ≠ 0)
    rwa [map_natCast] at h
  have hl0 : ((l : ℕ) : (↥LL.1)⟦X⟧⟦X⟧) ≠ 0 := fun h => hlK (by
    have := congrArg (fun f => PowerSeries.constantCoeff (PowerSeries.constantCoeff f)) h
    simpa using this)
  refine ⟨ε, fun τ => ?_, fun τ => ?_, fun τ i jj k => ?_⟩
  · refine Matrix.ext fun i jj => ?_
    obtain ⟨x, hx⟩ := hcol τ jj
    rw [Matrix.map_apply, ← hv0 τ jj x hx i,
      GlobalTheory.T.crystal_coordinates_constantCoeff_eq l a e _ _ (thetaW a LL) ϖ ι EE c hsemi sh hsh PP S₀ p₀ p₁ δ j j₀ hδ hj₀ hjp lam₀ lam₁ hl₀ hl₁ hv₀ hv₁,
      hv1 τ jj x hx, Matrix.one_apply, Pi.single_apply]
    split_ifs <;> simp
  · refine Matrix.ext fun i jj => ?_
    obtain ⟨x, hx⟩ := hcol (τ - 1) jj
    have hlI : ((l : ℕ) : PP.A) ∈ PP.I := by rw [hI]; exact Ideal.mem_span_singleton_self _
    obtain ⟨n, k, hn⟩ := exists_isFrac ((l : ℕ) : PP.A) (EE.Φ PP ⟨_, hlI⟩ (EE.tr p₁ x))
    have G₀ := GlobalTheory.T.crystal_frobenius_breuilKisin_coordinates l a e _ _ (thetaW a LL) ϖ ι P EE c hsemi hfr PP hlI p₀ j PowerSeries.C φ₂
      (fun τ w => (hjp τ w).1) hjφ hφC (PowerSeries.C_injective) lam₀ hl₀ hv₀ _ n k hn τ i
    have G₁ := GlobalTheory.T.crystal_frobenius_breuilKisin_coordinates l a e _ _ (thetaW a LL) ϖ ι P EE c hsemi hfr PP hlI p₁ j sh φ₂
      (fun τ w => (hjp τ w).2) hjφ hφsh (fun f g h => by rw [← hsh0 f, ← hsh0 g, h]) lam₁ hl₁ hv₁ _ n k hn
    have hy1 := hv1 (τ - 1) jj x hx
    have hy0 : ∀ m, lam₀ (EE.tr p₁ x) (τ - 1) m = ε (τ - 1) m jj := hv0 (τ - 1) jj x hx
    have hE := congrFun (hε n τ) i
    rw [G₀] at hE
    simp only [Matrix.mulVec, dotProduct, G₁, hy1, hy0] at hE
    have key : ((l : ℕ) : (↥LL.1)⟦X⟧⟦X⟧) ^ k *
        (((P.mx (τ - 1)).map (frob (↥LL.1) l)).map PowerSeries.C * (ε (τ - 1)).map φ₂) i jj =
        ((l : ℕ) : (↥LL.1)⟦X⟧⟦X⟧) ^ k * (ε τ * ((P.mx (τ - 1)).map (frob (↥LL.1) l)).map sh) i jj := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      have h1 : ∀ q, φ₂ ((Pi.single jj (1 : (↥LL.1)⟦X⟧⟦X⟧) : ι → (↥LL.1)⟦X⟧⟦X⟧) q) =
          (Pi.single jj 1 : ι → (↥LL.1)⟦X⟧⟦X⟧) q := fun q => by
        by_cases h : q = jj
        · subst h; simp
        · simp [Pi.single_eq_of_ne h]
      simp only [h1] at hE
      simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
        Finset.mem_univ, if_true] at hE
      simp only [Matrix.map_apply] at hE ⊢
      rw [hE, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    exact (mul_left_cancel₀ (pow_ne_zero k hl0) key).symm
  · obtain ⟨x, hx⟩ := hcol τ jj
    rw [← hv0 τ jj x hx i]
    exact GlobalTheory.T.factorial_mul_crystalCoord_coeff_mem l a e _ _ (thetaW a LL) ϖ ι P EE c hcM PP p₀ j hS' lam₀ hl₀ hv₀ _ τ i k

end GlobalTheory.CrysStrat
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CrysGal

open GlobalTheory.Prism

theorem span_range_tr {l : ℕ} {R : Type} [CommRing R] (E : FCrys l R) {P P' : Obj l R}
    (f : GlobalTheory.Prism.Hom P P') : Submodule.span P'.A (Set.range (E.tr f)) = ⊤ := by
  have hu := (E.tr_bc f (E.M P' ⧸ Submodule.span P'.A (Set.range (E.tr f))) 0).unique
    (y₁ := Submodule.mkQ _) (y₂ := 0)
    (fun x => by
      show Submodule.Quotient.mk _ = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact Submodule.subset_span ⟨x, rfl⟩)
    (fun x => rfl)
  rw [eq_top_iff]
  intro x _
  have := LinearMap.congr_fun hu x
  rwa [Submodule.mkQ_apply, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero] at this

theorem mem_span_tr {l : ℕ} {R : Type} [CommRing R] (E : FCrys l R) {P P' : Obj l R}
    (f : GlobalTheory.Prism.Hom P P') {O ι : Type} [Fintype ι] (oE : O → FHom E E) (b : ι → E.M P)
    (hgen : ∀ x : E.M P, ∃ (N : ℕ) (c : ι → Fin N → O) (s : ι → Fin N → P.A),
      x = ∑ j, ∑ q, s j q • (oE (c j q)).u P (b j)) (x : E.M P') :
    x ∈ Submodule.span P'.A (Set.range fun p : O × ι => (oE p.1).u P' (E.tr f (b p.2))) := by
  have hx : x ∈ Submodule.span P'.A (Set.range (E.tr f)) := (span_range_tr E f) ▸ Submodule.mem_top
  refine (Submodule.span_le.2 ?_) hx
  rintro _ ⟨z, rfl⟩
  obtain ⟨N, c, s, hz⟩ := hgen z

  rw [hz, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_

  rw [map_sum]
  refine Submodule.sum_mem _ fun q _ => ?_
  rw [map_smulₛₗ, ← (oE (c j q)).u_tr]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(c j q, j), rfl⟩)

theorem exists_rep {A M O ι : Type} [CommRing A] [AddCommGroup M] [Module A M] [Fintype ι] [DecidableEq ι]
    (v : O → ι → M) (x : ι → M) (hx : ∀ j, x j ∈ Submodule.span A (Set.range fun p : O × ι => v p.1 p.2)) :
    ∃ (Q : Type) (_ : Fintype Q) (c : ι → ι → Q → O) (y : ι → ι → Q → A),
      ∀ j, x j = ∑ i, ∑ q, y i j q • v (c i j q) i := by
  choose n w gg hgg using fun j => Submodule.mem_span_set'.1 (hx j)
  choose pc hpc using fun j k => (gg j k).2
  refine ⟨Σ j', Fin (n j'), inferInstance, fun i j q => (pc q.1 q.2).1,
    fun i j q => if q.1 = j then (if (pc q.1 q.2).2 = i then w q.1 q.2 else 0) else 0, fun j => ?_⟩
  rw [Finset.sum_comm]
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single j (fun j' _ hj' => by simp [hj']) (by simp)]
  rw [← hgg j]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [if_true, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ]
  rw [← hpc j k]

theorem conv_comb {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
    (g : ↥(GK (ϖ.field a))) {Q : Type} [Fintype Q] (c : Q → O) (z : Q → Per.Acris l)
    (F : Q → ℕ → (ZMod a → S O K e)) (G : ℕ → (ZMod a → S O K e)) (hG : ∀ k, G k = ∑ q, c q • F q k)
    (r : ℕ) (hconv : ∀ q, ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l O) ^ r ∣
      (1 : O) ⊗ₜ[ℤ_[l]] z q - ∑ k ∈ Finset.range n, ϖ.muDiv a O g k * ϖ.iC t K (F q k))
    (w : OCr l O) (hw : w = ∑ q, c q ⊗ₜ[ℤ_[l]] z q) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l O) ^ r ∣
      w - ∑ k ∈ Finset.range n, ϖ.muDiv a O g k * ϖ.iC t K (G k) := by
  subst hw
  choose n₀ hn₀ using hconv
  refine ⟨Finset.univ.sup n₀, fun n hn => ?_⟩

  simp_rw [hG, map_sum, map_smul, Finset.mul_sum, mul_smul_comm]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro q _
  rw [← Finset.smul_sum, show c q ⊗ₜ[ℤ_[l]] z q = c q • ((1 : O) ⊗ₜ[ℤ_[l]] z q) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], ← smul_sub, Algebra.smul_def]
  exact Dvd.dvd.mul_left (hn₀ q n (le_trans (Finset.le_sup (Finset.mem_univ q)) hn)) _

theorem comb_S {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    {a e : ℕ} {Q : Type} [Fintype Q] (c : Q → O) (w : ZMod a → Q → K⟦X⟧⟦X⟧)
    (G : ℕ → ZMod a → S O K e) (F : Q → ℕ → ZMod a → S O K e)
    (hG : ∀ k τ, (G k τ : K⟦X⟧) = (X : K⟦X⟧) ^ k * ((k.factorial : K⟦X⟧) * coeff k (∑ q, c q • w τ q)))
    (hF : ∀ q k τ, (F q k τ : K⟦X⟧) = (X : K⟦X⟧) ^ k * ((k.factorial : K⟦X⟧) * coeff k (w τ q))) :
    ∀ k, G k = ∑ q, c q • F q k := by
  intro k
  funext τ
  apply Subtype.ext

  rw [hG, Finset.sum_apply, AddSubmonoidClass.coe_finsetSum, map_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Pi.smul_apply, SetLike.val_smul, hF, PowerSeries.coeff_smul, mul_smul_comm, mul_smul_comm]



theorem galois_taylor_basis : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∀ (hS : ∀ (τ : ZMod a) (j : ι) (k : ℕ) (i : ι), (X : (↥LL.1)⟦X⟧) ^ k * (P.mxInv τ *ᵥ (P.nabla ^ k) (P.phi (bas j)) τ) i ∈ S (↥(OL LL)) (↥LL.1) e) (g : ↥(GK (ϖ.field a))), ∃ Γ, (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)).IsLMat (g : GQ l) g Γ ∧ ∀ (i j : ι) (r : ℕ), ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l ↥(OL LL)) ^ r ∣ toOCr l ↥(OL LL) (Γ i j) - ∑ k ∈ Finset.range n, ϖ.muDiv a ↥(OL LL) g k * ϖ.iC (thetaW a LL) ↥LL.1 (fun τ => ⟨_, hS τ j k i⟩) := by
  intro BS l _ a e _ _ ϖ LL _ _ hl2 ι _ _ P T I hBK hS g
  letI := zlLat (resF T (ϖ.field a))
  obtain ⟨E, jA, hR, hIm⟩ := hBK
  have hO : ∀ c : ↥(OL LL), ∃ u : FHom E E, ∀ x, jA (u.u (ainfObj (ϖ.field a)) x) =
      (OfCrystal.mulZ (resF T (ϖ.field a)) c).lTensor (WCb l) (jA x) := fun c => by
    obtain ⟨u, hu, -⟩ := (BS l (ϖ.field a) (ainfObj (ϖ.field a)) (ainfId (ϖ.field a)) hR.ainf).2 _ _ _ _ E E jA jA hR hR
      (OfCrystal.mulZ (resF T (ϖ.field a)) c) fun g x => (((resF T (ϖ.field a)).actT g).map_smul c x).symm
    exact ⟨u, hu⟩
  choose oE hoE using hO
  obtain ⟨b, hb, hgen⟩ := GlobalTheory.T.breuilKisinPrism_crystal_basis_and_span l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ι P (resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) E jA hR hIm oE hoE
  obtain ⟨sh, φ₂, hsh, hφC, hφsh⟩ := GlobalTheory.TaylorShift.shift_frob_exists l ↥LL.1
  obtain ⟨PP, S₀, p₀, p₁, δ, κ, κ₀, hPPI, hδ, hκ₀, hκp, hκφ, hSS, -, hev⟩ :=
    GlobalTheory.T.exists_crystalline_prisms l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ hl2 sh φ₂ hsh hφC hφsh
  obtain ⟨Q, _, c, y, hε⟩ := GlobalTheory.CrysGal.exists_rep (A := PP.A)
    (fun c i => (oE c).u PP (E.tr p₀ (b i))) (fun j => E.tr p₁ (b j))
    (fun j => GlobalTheory.CrysGal.mem_span_tr E p₀ oE b hgen _)
  have hF := GlobalTheory.T.crystal_changeOfBasis_frobenius_compat l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ι P (resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) E jA hR hIm oE hoE b hb sh φ₂ hsh hφC PP p₀ p₁ κ hPPI hκp hκφ Q c y hε
  have hD := GlobalTheory.T.prismCrystal_changeOfBasis_constantCoeff_eq_one l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ι P (resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) E jA hR hIm oE hoE b hb PP S₀ p₀ p₁ δ κ κ₀ hδ hκ₀ (fun τ x => (hκp τ x).1) Q c y hε
  have hK := GlobalTheory.T.frobeniusStratification_coeff_eq_connection_pow ↥(OL LL) ↥LL.1 l e a ι P sh φ₂ hsh hφC hφsh _ hD hF
  obtain ⟨Cr, eC, h, hCrI, heCφ, heCh⟩ := GlobalTheory.AcrisPrism.main l (ϖ.field a)
  have hev' := hev Cr eC h hCrI heCφ heCh g
  obtain ⟨ev, hevs⟩ := hev'
  have hG := GlobalTheory.T.galoisMatrix_eq_crystal_changeOfBasis_value l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ι P (resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) E jA hR hIm oE hoE b hb PP p₀ p₁ Q c y hε Cr eC h heCh g ev hevs.1 hevs.2.1
  obtain ⟨Γ, hΓ, hΓeq⟩ := hG
  have hconv := hevs.2.2
  refine ⟨Γ, hΓ, fun i j r => ?_⟩
  have hG := GlobalTheory.CrysGal.comb_S (e := e) (c i j) (fun τ q => κ τ (y i j q))
    (fun k τ => ⟨_, hS τ j k i⟩) (fun q k τ => ⟨_, hSS τ (y i j q) k⟩)
    (fun k τ => (congrArg ((X : (↥LL.1)⟦X⟧) ^ k * ·) (hK τ k i j)).symm) (fun q k τ => rfl)
  exact GlobalTheory.CrysGal.conv_comb (thetaW a LL) ϖ g (c i j) (fun q => eC (ev.f (y i j q)))
    (fun q k τ => ⟨_, hSS τ (y i j q) k⟩) (fun k τ => ⟨_, hS τ j k i⟩) hG r (fun q => hconv (y i j q) r)
    _ (hΓeq i j)

end GlobalTheory.CrysGal
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.JacMinCusp

open GlobalTheory.SmGL.CuspMax Matrix
open scoped TensorProduct

theorem blk_two_stdSum {a b n : ℕ} (h : a + b = n) (i : Fin n) :
    blk (two (stdSum h)) i = decide (a ≤ (i : ℕ)) := by
  obtain ⟨x, rfl⟩ := (stdSum h).surjective i
  rcases x with x | x
  · rw [← two_false, blk_apply]; simp [x.2]
  · rw [← two_true, blk_apply]; simp

theorem blk_two_stdSum_lt {a b n : ℕ} (h : a + b = n) (i j : Fin n) :
    blk (two (stdSum h)) i < blk (two (stdSum h)) j ↔ (i : ℕ) < a ∧ a ≤ (j : ℕ) := by
  rw [blk_two_stdSum, blk_two_stdSum]
  by_cases h1 : a ≤ (i : ℕ) <;> by_cases h2 : a ≤ (j : ℕ) <;> simp [h1, h2] <;> omega

theorem mem_unipRad_two_iff {R : Type} [CommRing R] {a b n : ℕ} (h : a + b = n) {g : GL (Fin n) R} :
    g ∈ unipRad R (two (stdSum h)) ↔ ∀ i j : Fin n, ¬ ((i : ℕ) < a ∧ a ≤ (j : ℕ)) →
      (g : Matrix (Fin n) (Fin n) R) i j = (1 : Matrix (Fin n) (Fin n) R) i j := by
  rw [mem_unipRad_iff_entries]
  simp only [blk_two_stdSum_lt]

end GlobalTheory.JacMinCusp
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.depthZeroSupercuspidal_cuspidalModule : ∀ (g : ℕ) [Fact g.Prime], TameGen.DepthZeroCuspidal g := by
  first | exact @GlobalTheory.DepthZeroCusp.depthZeroCuspidal | exact GlobalTheory.DepthZeroCusp.depthZeroCuspidal | (intros; apply GlobalTheory.DepthZeroCusp.depthZeroCuspidal <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.inert_frame_conj_extends_and_frame_map_surjective : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ), 0 < n → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (Dv : InertDatum L n v w) (b : GL (Fin n) (w.adicCompletion L)), b ∈ GlobalTheory.LFun.KGL w (n := n) → Formalism.UG.cT Dv.σw b.val * b.val = Formalism.UG.antiJ (w.adicCompletion L) n → ∀ p : locU n w →* Formalism.UG.GU Dv.σw n, (∀ x, (p x).val = b⁻¹ * cLoc w x.val * b) → (∀ x : L, Dv.σw (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) ∧ Function.Surjective p := by
  first | exact @GlobalTheory.InertFrameConj.conj_and_surjective | exact GlobalTheory.InertFrameConj.conj_and_surjective | (intros; apply GlobalTheory.InertFrameConj.conj_and_surjective <;> assumption)
end
