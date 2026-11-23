module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle007
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle002
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.H1cZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcCycKFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcGalCount
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcScalDim
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle010
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

local instance (priority := 2000) ratFieldIsTorsionFreeForSymplecticGSp4Bundle015 (Ω : Type) [Field Ω] [Algebra ℚ Ω] :
    Module.IsTorsionFree ℚ Ω := DivisionSemiring.to_moduleIsTorsionFree

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem nums_odd {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (hD : D.Good) {j : ℤ × ℤ} (hj : j ∈ oddRoots) :
    D.XVan (D.al ^ j.1 * D.Psi ^ j.2) ∧ (j.1 = 1 ∨ j.1 = -1) ∧
      ∃ a b, lamW a ≠ lamW b ∧ D.al ^ j.1 * D.Psi ^ j.2 * D.ps b = D.ps a := by
  have h1 := hD.xvan D.al (by simp)
  have h2 := hD.xvan D.be (by simp)
  have h3 := hD.xvan D.th (by simp)
  simp only [oddRoots, Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
  · have e : D.al ^ wAl.1 * D.Psi ^ wAl.2 = D.al := by simp [wAl]
    rw [e]
    exact ⟨h1.1, by decide, 2, 3, by decide, by simp [Raw.ps]⟩
  · have e : D.al ^ (-wAl).1 * D.Psi ^ (-wAl).2 = D.al⁻¹ := by simp [wAl]
    rw [e]
    exact ⟨h1.2, by decide, 3, 2, by decide, by simp [Raw.ps]⟩
  · have e : D.al ^ wBe.1 * D.Psi ^ wBe.2 = D.be := by simp [wBe, Raw.be, mul_comm]
    rw [e]
    exact ⟨h2.1, by decide, 1, 2, by decide, by simp [Raw.ps, Raw.be]⟩
  · have e : D.al ^ (-wBe).1 * D.Psi ^ (-wBe).2 = D.be⁻¹ := by simp [wBe, Raw.be, mul_comm]
    rw [e]
    exact ⟨h2.2, by decide, 2, 1, by decide, by simp [Raw.ps, Raw.be]⟩
  · have e : D.al ^ wTh.1 * D.Psi ^ wTh.2 = D.th := by simp [wTh, Raw.th]
    rw [e]
    exact ⟨h3.1, by decide, 0, 3, by decide, by simp [Raw.ps]⟩
  · have e : D.al ^ (-wTh).1 * D.Psi ^ (-wTh).2 = D.th⁻¹ := by simp [wTh, Raw.th, mul_comm]
    rw [e]
    exact ⟨h3.2, by decide, 3, 0, by decide, by simp [Raw.ps]⟩

private theorem nums_lc {Γ A : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group A] (ψ : Γ →* A)
    (h : IsOpen (ψ.ker : Set Γ)) : IsLocallyConstant ψ :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker ψ h

private theorem nums_gen (P : CohomologyHyp) {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    {SP : Set (HeightOneSpectrum (𝓞 ℚ))} {T Q : Finset ℕ} (v0 : T) {pl : ℕ → ValuationSubring Ω} {K : Subgroup (G ℚ Ω)}
    (hG : X.GalData l SP T Q pl K) (hK : IsOpen (K : Set (G ℚ Ω))) {k : Type} [Field k] [Finite k] [CharP k l] {M : Type}
    [AddCommGroup M] [Module k M] [Module.Finite k M] (ρ : Representation k (GS Ω SP) M) (γ : G ℚ Ω →* kˣ)
    (hγ : ∀ g m, ρ (toGS Ω SP g) m = (γ g : k) • m) (hKγ : K ≤ γ.ker) {σ : G ℚ Ω} (hσ : IsCC σ)
    (hd : Module.finrank k M = 0 ∨ ∃ g, γ g ≠ X.cycK Ω l k g) :
    Module.Finite k ((X.galFrame SP T Q v0 pl K).Ob ρ) ∧
      (γ σ = 1 → Module.finrank k ((X.galFrame SP T Q v0 pl K).Ob ρ) =
        Module.finrank k ((X.galFrame SP T Q v0 pl K).H1c ρ) + Module.finrank k M) ∧
      (Module.finrank k M = 0 ∨ γ σ ≠ 1 → Module.finrank k ((X.galFrame SP T Q v0 pl K).Ob ρ) =
        Module.finrank k ((X.galFrame SP T Q v0 pl K).H1c ρ)) := by
  have hlc : ∀ m, IsLocallyConstant fun g => ρ g m := fun m s =>
    (QuotientGroup.isQuotientMap_mk _).isOpen_preimage.1 (by
      have := ((nums_lc γ (Subgroup.isOpen_mono hKγ hK)).comp fun u => (u : k) • m) s
      simp only [Function.comp_def, ← hγ] at this
      exact this)
  obtain ⟨c1, -, c3⟩ := X.galCount ⟨P.loc.lf, P.loc.lt, P.loc.le, P.gf, P.ge, P.pt⟩ Ω l v0 hG k M
    ρ hlc (fun q _ g _ hg => LinearMap.ext fun m => by
      rw [hγ, show γ g = 1 from hKγ hg]; simp) σ hσ
  obtain ⟨s1, s2, s3⟩ := X.scalDim (ρ.comp (toGS Ω SP)) γ (X.cycK Ω l k) hγ
  rw [s3 hd, add_zero] at c3
  exact ⟨c1, fun e => c3.trans (congrArg _ (s1 σ e)), fun e => c3.trans (congrArg _ (s2 σ e))⟩

private theorem nums_zero {k Γ M : Type} [Field k] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module k M]
    [Module.Finite k M] (F : Frame Γ) (ρ : Representation k Γ M) (h : Module.finrank k M = 0) :
    Module.finrank k (F.H1c ρ) = 0 := by
  haveI : Subsingleton M := Module.finrank_zero_iff.1 h
  exact Module.finrank_zero_of_subsingleton

private theorem nums_all (P : CohomologyHyp) {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    {SP : Set (HeightOneSpectrum (𝓞 ℚ))} {T Q : Finset ℕ} (v0 : T) {pl : ℕ → ValuationSubring Ω} {K : Subgroup (G ℚ Ω)}
    (hG : X.GalData l SP T Q pl K) (hN : K.Normal) (hK : IsOpen (K : Set (G ℚ Ω))) {k : Type} [Field k] [Finite k]
    [CharP k l] {M : Type}
    [AddCommGroup M] [Module k M] [Module.Finite k M] (ρ : Representation k (GS Ω SP) M) (γ : G ℚ Ω →* kˣ)
    (hγ : ∀ g m, ρ (toGS Ω SP g) m = (γ g : k) • m) (hKγ : K ≤ γ.ker) {σ : G ℚ Ω} (hσ : IsCC σ)
    (k1 : X.cycK Ω l k σ = -1) (j : ℤ × ℤ) (hdim : Module.finrank k M = dimP j) (hcc : γ σ = (-1) ^ j.1)
    (sg : ℕ → G ℚ Ω) (hsg : ∀ v ∈ T, sg v ∈ Dec (F := ℚ) (pl v)) (e1 : X.cycK Ω l k (sg l) = 1)
    (hodd : j ∈ oddRoots → X.Van T pl K γ ∧ ∀ v ∈ T, γ (sg v) ≠ 1)
    (F : Frame (GS Ω SP)) (hF : F = X.galFrame SP T Q v0 pl K) :
    Module.Finite k (F.Ob ρ) ∧
    Module.finrank k (F.Ob ρ) = Module.finrank k (F.H1c ρ) + (if j = 0 then 2 else if j = wPs ∨ j = -wPs then 1 else 0) ∧
    (j ≠ 0 → j ≠ wPs → j ≠ -wPs → Module.finrank k (F.H1c ρ) = 0) := by
  subst hF
  have h2 : (-1 : kˣ) ≠ 1 := fun e => by
    have e' : ((2 : ℕ) : k) = 0 := by
      have := congrArg Units.val e
      simp only [Units.val_neg, Units.val_one] at this
      push_cast
      linear_combination -this
    exact hG.l_odd ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 ((CharP.cast_eq_zero_iff _ l 2).1 e'))
  have key := nums_gen P v0 hG hK ρ γ hγ hKγ hσ
  by_cases hj : j = 0 ∨ j = wPs ∨ j = -wPs
  · have e : γ σ = 1 := by
      rw [hcc]
      rcases hj with rfl | rfl | rfl <;> simp [wPs]
    obtain ⟨a1, a2, -⟩ := key (Or.inr ⟨σ, by rw [e, k1]; exact h2.symm⟩)
    refine ⟨a1, ?_, fun n1 n2 n3 => by tauto⟩
    rw [a2 e, hdim]
    congr 1
    rcases hj with rfl | rfl | rfl <;> decide
  rw [if_neg fun e => hj (Or.inl e), if_neg fun e => hj (Or.inr e), add_zero]
  by_cases ho : j ∈ oddRoots
  · obtain ⟨o1, hne⟩ := hodd ho
    have o2 : ∀ j ∈ oddRoots, j.1 = 1 ∨ j.1 = -1 := by decide
    have e : γ σ ≠ 1 := by
      rw [hcc]
      rcases o2 j ho with o | o <;> rw [o] <;> simpa using h2
    obtain ⟨a1, -, a2⟩ := key (Or.inr ⟨sg l, e1 ▸ hne l hG.l_mem⟩)
    refine ⟨a1, a2 (Or.inr e), fun _ _ _ => ?_⟩
    rw [X.h1cZero Ω l v0 hG hN _ _ ρ γ hγ hKγ (fun v hv => ⟨sg v, hsg v hv, hne v hv⟩) o1, finrank_bot]
  · have e : j ∉ wts := by
      simp only [wts, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [dimP, if_neg fun e => hj (Or.inl e), if_neg e] at hdim
    obtain ⟨a1, -, a2⟩ := key (Or.inl hdim)
    exact ⟨a1, a2 (Or.inl hdim), fun _ _ _ => nums_zero _ _ hdim⟩

theorem UpperTheory.V.GradeZeroInterpolatingElement.nums :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → CohomologyHyp → D.Nums := by
  intro Ω _ _ _ l hl c D hD P
  obtain ⟨-, f2, -, -, -, -, -, ⟨fc, -⟩, -, -, -, fo, -⟩ := facts D hD
  obtain ⟨hN, hI, hK⟩ := X.spKer D
  haveI : CharP (ResidueField c.O) l := (CharP.charP_iff_prime_eq_zero hl.out).2 (by
    obtain ⟨-, -, -, -, -, h0, -, hval, -⟩ := dvrFacts l c.O
    rw [hval, Ne, IsDiscreteValuationRing.addVal_eq_zero_iff] at h0
    rw [← map_natCast (residue c.O), residue_eq_zero_iff]
    exact h0)
  haveI : Finite (ResidueField c.O) := (abelian₂.dvr_finite l c.O).2.1
  have hTS : D.T ⊆ D.S := Finset.insert_subset hD.l_mem (by
    classical
    exact Finset.filter_subset _ _)
  have hU : ∀ p, (p ∈ D.T ∨ p ∈ D.S \ D.T) ↔ p ∈ D.S := fun p => by
    rw [← Finset.mem_union, Finset.union_sdiff_of_subset hTS]
  have hG : X.GalData l D.SP D.T (D.S \ D.T) D.pl D.rbar.ker :=
    ⟨hD.l_odd, fun p hp => hD.S_prime p ((hU p).1 hp), Finset.disjoint_sdiff, D.residueChar_mem_levelPrimes,
      fun v => exists_congr fun p => by rw [hU], fun p hp => hD.pl_over p (hD.S_prime p ((hU p).1 hp)),
      fun q _ hq => hI (hq.trans (Subgroup.relIndex_dvd_index_of_normal _ _))⟩
  obtain ⟨k1, k2⟩ := X.cycKFacts Ω l (ResidueField c.O)
  intro rb hrb h j
  let γ : G ℚ Ω →* (ResidueField c.O)ˣ := (Units.map (residue c.O).toMonoidHom).comp (D.al ^ j.1 * D.Psi ^ j.2)
  have hγ : ∀ g m, FormData.adRep h j (toGS Ω D.SP g) m = (γ g : ResidueField c.O) • m := X.spAct D rb hrb h j
  have hKγ : D.rbar.ker ≤ γ.ker := fun g hg => Units.ext (hK j g hg)
  have hdim := X.spDim c.O (ResidueField c.O) j
  have hcc : γ D.cc = (-1) ^ j.1 := by
    show Units.map (residue c.O).toMonoidHom (D.al D.cc ^ j.1 * D.Psi D.cc ^ j.2) = _
    rw [fc, hD.Psi_even, one_zpow, mul_one, map_zpow]
    congr 1
  have e1 : X.cycK Ω l (ResidueField c.O) (D.sg l) = 1 :=
    Units.ext ((k2 c (residue c.O) _).trans ((hD.om_bar _).symm.trans (f2 l D.residueChar_mem_levelPrimes).2.1))
  have hodd : j ∈ oddRoots → X.Van D.T D.pl D.rbar.ker γ ∧ ∀ v ∈ D.T, γ (D.sg v) ≠ 1 := fun ho => by
    obtain ⟨o1, -, a, b, hab, o3⟩ := nums_odd D hD ho
    refine ⟨fun z hz hc hu hT => o1 z hz hc (fun A hA g hg hk => hu A hA g hg hk) hT, fun v hv e => ?_⟩
    refine (f2 v hv).2.2 a b hab ?_
    have e' : Raw.bar (D.al ^ j.1 * D.Psi ^ j.2) (D.sg v) = 1 := congrArg Units.val e
    rw [← o3]
    show residue c.O (((D.al ^ j.1 * D.Psi ^ j.2) (D.sg v) : c.O) * (D.ps b (D.sg v) : c.O)) = _
    rw [map_mul]
    exact (congrArg (· * _) e').trans (one_mul _)
  have hF : D.frame = X.galFrame D.SP D.T (D.S \ D.T) ⟨l, D.residueChar_mem_levelPrimes⟩ D.pl D.rbar.ker := by
    unfold Raw.frame X.galFrame
    rfl
  exact nums_all P ⟨l, D.residueChar_mem_levelPrimes⟩ hG hN fo (FormData.adRep h j) γ hγ hKγ hD.isCC (k1 _ hD.isCC) j hdim hcc D.sg
    (fun v hv => (f2 v hv).1) e1 hodd D.frame hF
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem eii_step {R : Type} [CommRing R] (A : Submodule R (M4 R)) (hmul : ∀ x ∈ A, ∀ y ∈ A, x * y ∈ A)
    (y0 y1 y2 y3 : R) (hY : (!![y0, 0, y1, 0; 0, 0, 0, 0; y2, 0, y3, 0; 0, 0, 0, 0] : M4 R) ∈ A)
    (hu : IsUnit (y0 * y3 - y1 * y2)) : (!![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0] : M4 R) ∈ A := by
  have key : (y0 * y3 - y1 * y2) • (!![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0] : M4 R) =
      (y0 + y3) • (!![y0, 0, y1, 0; 0, 0, 0, 0; y2, 0, y3, 0; 0, 0, 0, 0] : M4 R) -
        (!![y0, 0, y1, 0; 0, 0, 0, 0; y2, 0, y3, 0; 0, 0, 0, 0] : M4 R) *
          (!![y0, 0, y1, 0; 0, 0, 0, 0; y2, 0, y3, 0; 0, 0, 0, 0] : M4 R) := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;> ring
  have hm : (y0 * y3 - y1 * y2) • (!![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0] : M4 R) ∈ A := by
    rw [key]
    exact A.sub_mem (A.smul_mem _ hY) (hmul _ hY _ hY)
  obtain ⟨u, hu⟩ := hu
  have hs := A.smul_mem (↑u⁻¹ : R) hm
  rwa [← hu, smul_smul, Units.inv_mul, one_smul] at hs

private theorem eii_alg {R : Type} [CommRing R] (A : Submodule R (M4 R)) (hmul : ∀ x ∈ A, ∀ y ∈ A, x * y ∈ A)
    (hone : (1 : M4 R) ∈ A) (hadj : ∀ x ∈ A, adj x ∈ A) (X : M4 R) (hX : X ∈ A) (hb : IsBlock X)
    (hu : IsUnit ((X 0 0 * X 0 0 + X 0 2 * X 2 0 - (X 1 1 + X 3 3) * X 0 0 + (X 1 1 * X 3 3 - X 1 3 * X 3 1)) *
      (X 2 0 * X 0 2 + X 2 2 * X 2 2 - (X 1 1 + X 3 3) * X 2 2 + (X 1 1 * X 3 3 - X 1 3 * X 3 1)) -
      (X 0 0 * X 0 2 + X 0 2 * X 2 2 - (X 1 1 + X 3 3) * X 0 2) * (X 2 0 * X 0 0 + X 2 2 * X 2 0 - (X 1 1 + X 3 3) * X 2 0)))
    (H : M4 R) (hH : H ∈ A) (h02 : H 0 2 = 0) (h20 : H 2 0 = 0) (hd : IsUnit (H 0 0 - H 2 2)) (i : Fin 4) :
    Matrix.single i i (1 : R) ∈ A := by
  have z : ∀ a b, lamW a ≠ lamW b → X a b = 0 := hb
  have x01 := z 0 1 (by simp [lamW])
  have x03 := z 0 3 (by simp [lamW])
  have x10 := z 1 0 (by simp [lamW])
  have x12 := z 1 2 (by simp [lamW])
  have x21 := z 2 1 (by simp [lamW])
  have x23 := z 2 3 (by simp [lamW])
  have x30 := z 3 0 (by simp [lamW])
  have x32 := z 3 2 (by simp [lamW])
  have hYA : X * X - (X 1 1 + X 3 3) • X + (X 1 1 * X 3 3 - X 1 3 * X 3 1) • (1 : M4 R) ∈ A :=
    A.add_mem (A.sub_mem (hmul X hX X hX) (A.smul_mem _ hX)) (A.smul_mem _ hone)
  have hE : (!![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0] : M4 R) ∈ A := by
    refine eii_step A hmul
      (X 0 0 * X 0 0 + X 0 2 * X 2 0 - (X 1 1 + X 3 3) * X 0 0 + (X 1 1 * X 3 3 - X 1 3 * X 3 1))
      (X 0 0 * X 0 2 + X 0 2 * X 2 2 - (X 1 1 + X 3 3) * X 0 2)
      (X 2 0 * X 0 0 + X 2 2 * X 2 0 - (X 1 1 + X 3 3) * X 2 0)
      (X 2 0 * X 0 2 + X 2 2 * X 2 2 - (X 1 1 + X 3 3) * X 2 2 + (X 1 1 * X 3 3 - X 1 3 * X 3 1)) ?_ hu
    convert hYA using 1
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, x01, x03, x10, x12, x21, x23, x30, x32] <;>
      ring
  have hZ : (H 0 0 - H 2 2) • Matrix.single 0 0 (1 : R) =
      (!![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0] : M4 R) * H *
          (!![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0] : M4 R) -
        H 2 2 • (!![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0] : M4 R) := by
    ext a b
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_four]
    fin_cases a <;> fin_cases b <;> simp [Matrix.single, h02, h20]
  have h0m : (H 0 0 - H 2 2) • Matrix.single 0 0 (1 : R) ∈ A := by
    rw [hZ]
    exact A.sub_mem (hmul _ (hmul _ hE _ hH) _ hE) (A.smul_mem _ hE)
  have e0 : Matrix.single 0 0 (1 : R) ∈ A := by
    obtain ⟨u, hu'⟩ := hd
    have hs := A.smul_mem (↑u⁻¹ : R) h0m
    rwa [← hu', smul_smul, Units.inv_mul, one_smul] at hs
  have e2 : Matrix.single 2 2 (1 : R) ∈ A := by
    have h : Matrix.single 2 2 (1 : R) =
        (!![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0] : M4 R) - Matrix.single 0 0 1 := by
      ext a b
      fin_cases a <;> fin_cases b <;> simp [Matrix.single]
    rw [h]
    exact A.sub_mem hE e0
  have hadjs : ∀ k : Fin 4, adj (Matrix.single k k (1 : R)) = Matrix.single k.rev k.rev 1 := by
    intro k
    ext a b
    fin_cases k <;> fin_cases a <;> fin_cases b <;> simp [adj_apply, Matrix.single, sgn, Fin.rev]
  fin_cases i
  · exact e0
  · have h := hadj _ e2
    rwa [hadjs] at h
  · exact e2
  · have h := hadj _ e0
    rwa [hadjs] at h

private theorem eii_span {R H : Type} [CommRing R] [Group H] (r : H →* M4 R) (ν : H → R) (hν : ∀ g, IsGSp (ν g) (r g)) :
    (∀ x ∈ Submodule.span R (Set.range r), ∀ y ∈ Submodule.span R (Set.range r), x * y ∈ Submodule.span R (Set.range r)) ∧
      ∀ x ∈ Submodule.span R (Set.range r), adj x ∈ Submodule.span R (Set.range r) := by
  have hadj : ∀ g, adj (r g) = ν g • r g⁻¹ := by
    intro g
    have hinv : r g * r g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have h0 : adj (r g) * r g * r g⁻¹ = ν g • 1 * r g⁻¹ := by rw [hν g]
    rw [mul_assoc, hinv, mul_one, smul_mul_assoc, one_mul] at h0
    exact h0
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · have h := Submodule.mul_mem_mul hx hy
    rw [Submodule.span_mul_span] at h
    refine Submodule.span_mono ?_ h
    rintro _ ⟨a, ⟨g, rfl⟩, b, ⟨k, rfl⟩, rfl⟩
    exact ⟨g * k, map_mul r g k⟩
  · let L : M4 R →ₗ[R] M4 R :=
      { toFun := adj
        map_add' := fun x y => by
          ext i j
          simp only [adj_apply, Matrix.add_apply, smul_add]
        map_smul' := fun c x => by
          ext i j
          simp only [adj_apply, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, zsmul_eq_mul]
          ring }
    have hle : Submodule.span R (Set.range r) ≤ (Submodule.span R (Set.range r)).comap L := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      show adj (r g) ∈ Submodule.span R (Set.range r)
      rw [hadj g]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g⁻¹, rfl⟩)
    exact hle hx

private theorem eii_unit {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] (x : R)
    (h : res O R x ≠ 0) : IsUnit x := by
  haveI : IsLocalRing R := IsCO.toIsLocalRing (O := O)
  by_contra hx
  exact h ((res_eq_zero_iff O R x).2 ((IsLocalRing.mem_maximalIdeal x).2 hx))

private theorem eii_abs {O R H : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] [Group H]
    (r : H →* M4 R) (ps : Fin 4 → H →* Oˣ) (ν : H → R) (hν : ∀ g, IsGSp (ν g) (r g))
    (hr : ∀ g i j, res O R (r g i j) = residue O (diagRep ps g i j)) (φ g : H) (hb : IsBlock (r φ))
    (hφ : ∀ i j, lamW i ≠ lamW j → residue O (ps i φ) ≠ residue O (ps j φ))
    (h0 : ps 0 g = ps 2 g * ps 1 g) (h1 : residue O (ps 1 g) ≠ 1) (h2 : residue O (ps 2 g) ≠ 1)
    (h02 : (r g + algebraMap O R (ps 0 g) • r g⁻¹) 0 2 = 0) (h20 : (r g + algebraMap O R (ps 0 g) • r g⁻¹) 2 0 = 0)
    (i : Fin 4) : Matrix.single i i (1 : R) ∈ Submodule.span R (Set.range r) := by
  obtain ⟨hmul, hadj⟩ := eii_span r ν hν
  have hone : (1 : M4 R) ∈ Submodule.span R (Set.range r) := Submodule.subset_span ⟨1, map_one r⟩
  have hdiag : ∀ k i, res O R (r k i i) = residue O (ps i k : O) := by
    intro k i
    rw [hr]
    simp [diagRep]
  have hoff : ∀ k i j, i ≠ j → res O R (r k i j) = 0 := by
    intro k i j h
    rw [hr]
    simp [diagRep, Matrix.diagonal_apply_ne _ h]
  have hHm : r g + algebraMap O R (ps 0 g) • r g⁻¹ ∈ Submodule.span R (Set.range r) :=
    Submodule.add_mem _ (Submodule.subset_span ⟨g, rfl⟩)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨g⁻¹, rfl⟩))
  refine eii_alg _ hmul hone hadj (r φ) (Submodule.subset_span ⟨φ, rfl⟩) hb ?_ _ hHm h02 h20 ?_ i
  · apply eii_unit (O := O)
    simp only [map_mul, map_add (f := _), map_sub, hdiag, hoff φ 0 2 (by decide), hoff φ 2 0 (by decide),
      hoff φ 1 3 (by decide), hoff φ 3 1 (by decide)]
    have n01 := sub_ne_zero.2 (hφ 0 1 (by simp [lamW]))
    have n03 := sub_ne_zero.2 (hφ 0 3 (by simp [lamW]))
    have n21 := sub_ne_zero.2 (hφ 2 1 (by simp [lamW]))
    have n23 := sub_ne_zero.2 (hφ 2 3 (by simp [lamW]))
    intro h
    apply mul_ne_zero (mul_ne_zero n01 n03) (mul_ne_zero n21 n23)
    linear_combination h
  · apply eii_unit (O := O)
    have hc : res O R (algebraMap O R (ps 0 g : O)) = residue O (ps 0 g : O) := by
      rw [AlgHom.commutes, IsLocalRing.ResidueField.algebraMap_eq]
    have hi : ∀ k, residue O (ps k g⁻¹ : O) * residue O (ps k g : O) = 1 := by
      intro k
      rw [← map_mul (residue O), ← Units.val_mul, ← map_mul (ps k), inv_mul_cancel, map_one,
        Units.val_one, map_one]
    have e0 : residue O (ps 0 g : O) = residue O (ps 2 g : O) * residue O (ps 1 g : O) := by
      rw [h0, Units.val_mul, map_mul]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_sub, map_add (f := _), map_mul, hc, hdiag]
    intro h
    have hp : (residue O (ps 1 g : O) - 1) * (residue O (ps 2 g : O) - 1) = 0 := by
      linear_combination h - e0 * (1 - residue O (ps 2 g⁻¹ : O)) - hi 0 + residue O (ps 1 g : O) * hi 2
    rcases mul_eq_zero.1 hp with h' | h'
    · exact h1 (sub_eq_zero.1 h')
    · exact h2 (sub_eq_zero.1 h')

theorem UpperTheory.V.GradeZeroInterpolatingElement.eii :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (ρ : Lift c.O D.rbar R), D.Mult ρ.hom → D.Nrm ρ.hom → ∀ i, Matrix.single i i (1 : R) ∈ Submodule.span R (Set.range ρ.hom) := by
  intro Ω _ _ _ l _ c D hG R _ _ _ ρ hM hN i
  obtain ⟨-, hT, -, -, -, -, -, -, -, hph, -⟩ := facts D hG
  have hrb : ∀ k j, D.rbar k j j = residue c.O (D.ps j k : c.O) := by
    intro k j
    simp [Raw.rbar, mapRep, Raw.r0, diagRep]
  refine eii_abs ρ.hom D.ps (fun g => algebraMap c.O R (D.th g : c.O)) hM ?_ D.ph D.g0 hN.1 ?_ ?_ ?_ ?_
    hN.2.1 hN.2.2 i
  · intro g a b
    rw [ρ.red]
    simp [Raw.rbar, mapRep, Raw.r0]
  · intro a b hab
    rw [← hrb, ← hrb, hph, hrb, hrb]
    exact (hT l (Finset.mem_insert_self _ _)).2.2 a b hab
  · rfl
  · exact hG.genElt_Psi
  · exact hG.genElt_alpha
end
