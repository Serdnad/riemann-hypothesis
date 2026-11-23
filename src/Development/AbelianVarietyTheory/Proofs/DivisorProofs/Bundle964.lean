module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle003
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle011
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqBasicOpen
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle050
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle934
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle010
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle637
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle754
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle821
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle791
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle935
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle936
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle930
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Formalism.SharpRestriction.GlobalSchurBounds.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLawPf
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

@[expose] public section

section

open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.minPadicValPowSubOneCoprime_eq_closedFormula : Formalism.PairingDivisionLocalBalance.MinVal → ∀ l n : ℕ, l.Prime → 2 ≤ n → Even n → mMin l n = Formalism.PairingDivisionLocalBalance.mE l n := by
  first | exact @GlobalTheory.MinValClosed.mMin_eq_mE | exact GlobalTheory.MinValClosed.mMin_eq_mE | (intros; apply GlobalTheory.MinValClosed.mMin_eq_mE <;> assumption)
end

section

open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.partialZetaDenomSumBound_of_local_bounds : ∀ {F : Type} [Field F] [NumberField F], Formalism.PairingDivisionLocalBalance.CESum → ∀ (k : ℕ) (z : ClassGroup (𝓞 F) → ℚ), 2 ≤ k → 16 ≤ finrank ℚ F * k →
    (∀ l : ℕ, l.Prime → cE z l ≤ finrank ℚ F * padicValNat l 2 + Formalism.PairingDivisionLocalBalance.mE l (finrank ℚ F * k)) → SumBound k z := by
  first | exact @GlobalTheory.Proof.partialZetaDenomSumBound_of_local_bounds.sumBound_of_local | exact GlobalTheory.Proof.partialZetaDenomSumBound_of_local_bounds.sumBound_of_local | (intros; apply GlobalTheory.Proof.partialZetaDenomSumBound_of_local_bounds.sumBound_of_local <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM Matrix

namespace GlobalTheory.FlatDegreeCompare

section Lie

variable {R K : Type} [CommRing R] [CommRing K]

def Indep {A : Over (Sp K)} [GrpObj A] {m : ℕ} (x : Fin m → (epsR K ⟶ A)) : Prop :=
  (∀ i, IsTangent (x i)) ∧ ∀ c c' w, IsLieComb c x w → IsLieComb c' x w → c = c'

theorem Indep.of_basis {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] {n : ℕ} {e : Fin n → (epsR K ⟶ A)}
    (he : IsLieBasis e) : Indep e :=
  ⟨he.1, fun c _ w h h' => (he.2 w ((LieComb.lieComb_algebra K A n e he.1).2.1 c w h)).unique h h'⟩

theorem Indep.of_eigBasis {O : Type} [CommRing O] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] {act : OAct O A}
    {χ : O →+* K} {m : ℕ} {x : Fin m → (epsR K ⟶ A)} (h : EigenvectorLieDegree.IsEigBasis act χ x) : Indep x := by
  refine ⟨fun i => (h.1 i).1, fun c c' w hc hc' => (h.2 w ?_).unique hc hc'⟩
  let y : Fin m → Serre.Lie act := fun i => Serre.Lie.mk act (x i) (h.1 i).1
  have hy : ∀ a i, a • y i = χ a • y i := fun a i => Serre.Lie.ext (Over.OverMorphism.ext ((h.1 i).2 a))
  obtain rfl := (Serre.Lie.isLieComb_iff c y w).1 hc
  refine ⟨Serre.Lie.isTangent _, fun a => ?_⟩
  have : a • ∑ i, c i • y i = χ a • ∑ i, c i • y i := by
    rw [Finset.smul_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_comm a, hy, smul_comm]
  exact congrArg (fun z : Serre.Lie act => z.hom.left) this

variable {f : R →+* K} {G : Over (Sp R)} [GrpObj G] {A : Over (Sp K)} [GrpObj A] {φ : A.left ⟶ G.left}

theorem exists_frame [IsLocalRing R] (hG : IsSemiAbelian G) (hφ : IsGrpPullback A G (spMap f) φ) {m : ℕ}
    {x : Fin m → (epsR K ⟶ A)} (hx : ∀ i, IsTangent (x i)) :
    ∃ (n : ℕ) (e : Fin n → (epsR R ⟶ G)) (e' : Fin n → (epsR K ⟶ A)) (P : Matrix (Fin m) (Fin n) K),
      IsLieBasis e ∧ IsLieBasis e' ∧ (∀ j, IsVecOver f φ (e j) (e' j)) ∧ ∀ i, IsLieComb (P i) e' (x i) := by
  have := hG.smooth
  obtain ⟨n, e, he⟩ := Chart.exists_isLieBasis G hG.smooth
  choose e' h _ using fun j => existsUnique_isVecOver hφ.1 (e j)
  have he' := Chart.isLieBasis_baseChange f hφ he h
  choose P hP _ using fun i => he'.2 _ (hx i)
  exact ⟨n, e, e', P, he, he', h, hP⟩

end Lie

section Local

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {k : Type} [Field k] [NumberField k]
  {t : SAB H (Sp k)} {m : ℕ} {x : Fin m → (epsR k ⟶ t.G)} {𝔭 : HeightOneSpectrum (𝓞 k)}

end Local

end GlobalTheory.FlatDegreeCompare
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.FlatSec
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.AmplePoint

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}

theorem exists_of_mem_map [Algebra R R'] {A A' : Type} [CommRing A] [CommRing A'] [Algebra R A] (p : A →+* A')
    (s' : R' →+* A') (e : R' ⊗[R] A ≃+ A') (he : ∀ c v, e (c ⊗ₜ v) = s' c * p v) (N : Ideal A) {y : A'}
    (hy : y ∈ N.map p) : ∃ x : R' ⊗[R] (N.restrictScalars R), e ((N.restrictScalars R).subtype.lTensor R' x) = y := by
  suffices h : ∀ r, ∃ x : R' ⊗[R] (N.restrictScalars R), e ((N.restrictScalars R).subtype.lTensor R' x) = r * y by
    simpa using h 1
  refine Submodule.span_induction (p := fun y _ => ∀ r, ∃ x : R' ⊗[R] (N.restrictScalars R),
    e ((N.restrictScalars R).subtype.lTensor R' x) = r * y) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨v, hv, rfl⟩ r
    obtain ⟨t, rfl⟩ := e.surjective r
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul c a => exact ⟨c ⊗ₜ ⟨a * v, N.mul_mem_left a hv⟩, by simp [he, mul_assoc]⟩
    | add a b ha hb =>
      obtain ⟨x, hx⟩ := ha
      obtain ⟨x', hx'⟩ := hb
      exact ⟨x + x', by rw [map_add (f := _), map_add (f := _), hx, hx', map_add (f := _), add_mul]⟩
  · exact fun r => ⟨0, by simp⟩
  · intro a b _ _ ha hb r
    obtain ⟨x, hx⟩ := ha r
    obtain ⟨x', hx'⟩ := hb r
    exact ⟨x + x', by rw [map_add (f := _), map_add (f := _), hx, hx', mul_add]⟩
  · intro a b _ hb r
    obtain ⟨x, hx⟩ := hb (r * a)
    exact ⟨x, by rw [hx, smul_eq_mul, mul_assoc]⟩

def vanIdeal (W U : X.Opens) : Ideal Γ(X, W) where
  carrier := {v | X.basicOpen v ≤ U}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => (X.basicOpen_add_le a b).trans (sup_le ha hb)
  smul_mem' := fun c a ha => by
    change X.basicOpen (c * a) ≤ U
    rw [Scheme.basicOpen_mul]
    exact inf_le_right.trans ha

theorem exists_pow_mem (π : X' ⟶ X) [IsAffineHom π] {W : X.Opens} (hW : IsAffineOpen W) (U : X.Opens)
    (t : Γ(X', π ⁻¹ᵁ W)) (ht : X'.basicOpen t ≤ π ⁻¹ᵁ U) : ∃ m, t ^ m ∈ (vanIdeal W U).map (π.app W).hom := by
  have hW' := hW.preimage π
  change t ∈ ((vanIdeal W U).map (π.app W).hom).radical
  rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
  rintro P ⟨hP, hp⟩
  by_contra h
  let z : Spec Γ(X', π ⁻¹ᵁ W) := ⟨P, hp⟩
  have key : ∀ s : Γ(X', π ⁻¹ᵁ W), hW'.fromSpec z ∈ X'.basicOpen s ↔ s ∉ P := fun s => by
    change z ∈ hW'.fromSpec ⁻¹ᵁ X'.basicOpen s ↔ _
    rw [hW'.fromSpec_preimage_basicOpen]
    rfl
  have hz := (key t).2 h
  obtain ⟨v, hv, hzv⟩ := hW.exists_basicOpen_le (V := U) ⟨π (hW'.fromSpec z), ht hz⟩ (X'.basicOpen_le t hz)
  refine (key ((π.app W).hom v)).1 ?_ (hP (Ideal.mem_map_of_mem _ hv))
  rw [← Scheme.preimage_basicOpen]
  exact hzv

theorem exists_sec_mem (g : R →+* R') (hg : g.Flat) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (CommRingCat.of R)) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of R'))
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom g))) (M : LB X) (hM : M.IsLB) {α : Type} [Fintype α]
    (W : α → X.Opens) (j : α → M.ι) (hA : ∀ a, IsAffineOpen (W a)) (hW : ∀ a, W a ≤ M.U (j a))
    (hc : ∀ y : X, ∃ a, y ∈ W a) (N : ∀ a, Ideal Γ(X, W a)) (σ : LB.Sec (M.pull π))
    (hσ : ∀ a, rs X' (le_pull M π (hW a)) (σ.f fun _ => j a) ∈ (N a).map (π.app (W a)).hom)
    (z : X') (hz : z ∈ nonzeroLocus σ) :
    ∃ u : M.Sec, π z ∈ nonzeroLocus u ∧ ∀ a, rs X (hW a) (u.f (j a)) ∈ N a := by
  let _ : Algebra R R' := g.toAlgebra
  have : Module.Flat R R' := hg
  let _ : ∀ U : X.Opens, Algebra R Γ(X, U) := fun U => (cst f U).toAlgebra
  choose e he using fun a => exists_equiv_of_isPushout (R := R) (π.app (W a)) (cst f' (π ⁻¹ᵁ W a))
    (isPushout_app hg H (hA a).isCompact (hA a).isQuasiSeparated)
  choose e' he' using fun p : α × α => exists_equiv_of_isPushout (R := R) (π.app (W p.1 ⊓ W p.2))
    (cst f' (π ⁻¹ᵁ (W p.1 ⊓ W p.2))) (isPushout_app hg H
      (QuasiSeparatedSpace.inter_isCompact _ _ (W p.1).isOpen (hA p.1).isCompact (W p.2).isOpen (hA p.2).isCompact)
      (IsQuasiSeparated.of_quasiSeparatedSpace _))
  let d : (∀ a, (N a).restrictScalars R) →ₗ[R] (∀ p : α × α, Γ(X, W p.1 ⊓ W p.2)) :=
    { toFun := fun v p => rs X inf_le_left (v p.1).1 -
        rs X (inf_le_inf (hW p.1) (hW p.2)) (M.g (j p.1) (j p.2)).val * rs X inf_le_right (v p.2).1
      map_add' := fun v w => funext fun p => by
        simp only [Pi.add_apply, Submodule.coe_add, map_add (f := _)]; ring
      map_smul' := fun r v => funext fun p => by
        simp only [Pi.smul_apply, Submodule.coe_smul, Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra, rs_cst,
          RingHom.id_apply]; ring }
  choose x hxe using fun a => exists_of_mem_map (π.app (W a)).hom (cst f' (π ⁻¹ᵁ W a)) (e a) (he a) (N a) (hσ a)
  have hx : ∀ {n : ℕ} {c : Fin n → R'} {v : Fin n → ∀ a, (N a).restrictScalars R},
      (∀ a, x a = ∑ i, AddEquiv.refl _ (c i ⊗ₜ v i a)) →
      ∀ a z, π z ∈ W a → gs (𝟙 X') z _ (σ.f fun _ => j a) =
        ∑ i, gs (𝟙 X') z ⊤ (cst f' ⊤ (c i)) * gs π z _ (v i a).1 := fun {n c v} h a z hz => by
    have h' := congrArg (gs (𝟙 X') z (π ⁻¹ᵁ W a)) (hxe a).symm

    simp only [h a, map_sum, AddEquiv.refl_apply, LinearMap.lTensor_tmul, Submodule.subtype_apply, he] at h'
    rw [gs_comb f' π _ z hz] at h'
    exact (gs_res (𝟙 X') z _ hz _).symm.trans h'
  obtain ⟨n, c, v, hv, hd⟩ := exists_comb_ker (fun a => AddEquiv.refl _) e' d x
    (fun n c v h p => fn_ext fun z hz => by
      simp only [he']
      rw [gs_comb f' π _ z hz, LBGerm.gs_zero (𝟙 X') z _ hz]
      have h₁ := gs_pull_trans σ z (hW _ hz.1) (hW _ hz.2)
      rw [hx h p.1 z hz.1, hx h p.2 z hz.2, Finset.mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib] at h₁
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h₁
      refine (congrArg _ (gs_diff (hW p.1) (hW p.2) (v i p.1).1 (v i p.2).1 π z hz)).trans ?_
      ring)
  choose u hu using fun i => exists_sec_of_refinement hM W j hW hc (fun a => (v i a).1) fun y a b ha hb => by
    have h := congrArg (gs (𝟙 X) y (W a ⊓ W b)) (congrFun (hd i) (a, b))
    exact sub_eq_zero.1 ((gs_diff (hW a) (hW b) (v i a).1 (v i b).1 (𝟙 X) y ⟨ha, hb⟩).symm.trans
      (h.trans (LBGerm.gs_zero (𝟙 X) y _ ⟨ha, hb⟩)))
  have hu' : ∀ i a, rs X (hW a) ((u i).f (j a)) = (v i a).1 := fun i a => fn_ext fun y hy => by
    rw [gs_res (𝟙 X) y _ hy, hu i y (j a) a (hW a hy) hy, gm_self hM (𝟙 X) y (hW a hy), Units.val_one,
      _root_.one_mul]
  obtain ⟨a, ha⟩ := hc (π z)
  have h₁ := (mem_nonzeroLocus_iff_isUnit σ (k := fun _ => j a) (mem_pull.2 (hW a ha))).1 hz
  replace h₁ := hx hv a z ha ▸ h₁
  obtain ⟨i, -, hi⟩ := IsLocalRing.exists_of_isUnit_sum h₁
  refine ⟨u i, (mem_nonzeroLocus_iff_pull (u i) π z (hW a ha)).2 ?_, fun b => hu' i b ▸ (v i b).2⟩
  rw [← gs_res π z (hW a) ha]
  exact (congrArg (fun w => IsUnit (gs π z _ w)) (hu' i a)).mpr (isUnit_of_mul_isUnit_right hi)

def chartPullPullPow (L : LB X) (f : X' ⟶ X) (n : ℕ) :
    ChartPull ((lbPow L n).pull f) (lbPow (L.pull f) n) (𝟙 X') where
  idx J := fun _ _ => J PUnit.unit PUnit.unit
  le _ _ hy := mem_powChart.2 (mem_pull.2 (mem_powChart.1 (mem_pull.1 hy)))
  g y J J' hJ hJ' := by
    have h₁ := mem_pull.1 hJ
    have h₂ := mem_pull.1 hJ'
    refine (gm_pull_g (lbPow L n) f (𝟙 X') y J J' hJ hJ').trans (Eq.symm ?_)
    refine ((chartPullPowPull L f n).g y _ _ (mem_powChart.2 (mem_pull.2 (mem_powChart.1 h₁)))
      (mem_powChart.2 (mem_pull.2 (mem_powChart.1 h₂)))).trans ?_
    rw [Category.id_comp]
    rfl

theorem exists_affine_locus : ∀ (R R' : Type) [CommRing R] [CommRing R'] (ρ : R →+* R'), ρ.Flat → ∀ (X : Scheme.{0}) (q : X ⟶ Sp R), QuasiCompact q → QuasiSeparated q → ∀ (L : LB X), L.IsLB → ∀ (x' : ↥(Limits.pullback q (spMap ρ))), (∃ n, 1 ≤ n ∧ ∃ s : (lbPow (L.pull (pullback.fst q (spMap ρ))) n).Sec, x' ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s)) → ∃ n, 1 ≤ n ∧ ∃ s : (lbPow L n).Sec, pullback.fst q (spMap ρ) x' ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s) := by
  rintro R R' _ _ ρ hρ X q _ _ L hL x' ⟨n, hn, s, hs, ha⟩
  have H := IsPullback.of_hasPullback q (spMap ρ)
  generalize pullback.snd q (spMap ρ) = q' at H
  have hπ : IsAffineHom (pullback.fst q (spMap ρ)) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback q (spMap ρ)).flip inferInstance
  generalize pullback.fst q (spMap ρ) = π at *
  generalize Limits.pullback q (spMap ρ) = X' at *
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated q
  have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace π
  have : QuasiSeparatedSpace X' := quasiSeparatedSpace_of_quasiSeparated π
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := π x') trivial
  obtain ⟨φ, hφ, hxφ⟩ := ha.exists_basicOpen_le (V := π ⁻¹ᵁ U) ⟨x', hx⟩ hs
  obtain ⟨k, hk, t, ht⟩ := exists_nonzeroLocus_eq_basicOpen (LB.isLB_pull hL π) s φ
  obtain ⟨α, _, W, J, hWa, hW, hc⟩ : ∃ (α : Type) (_ : Fintype α) (W : α → X.Opens) (J : α → PUnit → L.ι),
      (∀ a, IsAffineOpen (W a)) ∧ (∀ a, W a ≤ powChart L (J a)) ∧ ∀ y : X, ∃ a, y ∈ W a :=
    exists_finite_affine_refinement (isLB_lbPow hL 0)
  have le : ∀ a, π ⁻¹ᵁ W a ≤ powChart (L.pull π) (fun _ _ => J a PUnit.unit) := fun a y hy =>
    mem_powChart.2 (mem_pull.2 (mem_powChart.1 (hW a hy)))
  choose m hm using fun a => exists_pow_mem π (hWa a) U (resG X' (le a) (powFn t _)) fun y hy => by
    have hy₁ : y ∈ π ⁻¹ᵁ W a := X'.basicOpen_le _ hy
    have h := (LBGerm.isUnit_gs_iff (𝟙 X') y _ hy₁ _).2 hy
    exact hφ (ht.le ((mem_nonzeroLocus_iff_powFn t (le a hy₁)).2
      ((congrArg IsUnit (gs_res (𝟙 X') y (le a) hy₁ _)).mp h)))
  let K := Finset.univ.sup m + 1
  have hK : 1 ≤ K := Nat.le_add_left _ _
  obtain ⟨u, hxu, hu⟩ := exists_sec_mem ρ hρ q π q' H (lbPow L (n * k * K)) (isLB_lbPow hL _) W J hWa hW hc
    (fun a => vanIdeal (W a) U) (chartSec (chartPullPullPow L π _) (secPow t K)) (fun a => by
      have e : rs X' (le_pull (lbPow L (n * k * K)) π (hW a))
          ((chartSec (chartPullPullPow L π _) (secPow t K)).f fun _ => J a) = resG X' (le a) (powFn t _) ^ K :=
        fn_ext fun y hy => by
          refine (gs_res (𝟙 X') y _ hy _).trans ((gs_chartSec _ _ (𝟙 X') y _
            (le_pull (lbPow L (n * k * K)) π (hW a) hy)).trans ?_)
          rw [Category.comp_id, LBGerm.gs_pow (𝟙 X') y _ hy, gs_res (𝟙 X') y _ hy]
          exact LBGerm.gs_pow (𝟙 X') y _ (le a hy) _ _
      rw [e]
      exact Ideal.pow_mem_of_pow_mem _ (hm a) ((Finset.le_sup (f := m) (Finset.mem_univ a)).trans (Nat.le_succ _)))
    x' (by
      rw [nonzeroLocus_chartSec_id (chartPullPullPow L π _) _ fun y I hI => ⟨fun _ _ => I PUnit.unit PUnit.unit,
        mem_pull.2 (mem_powChart.2 (mem_pull.1 (mem_powChart.1 hI)))⟩, nonzeroLocus_secPow t hK, ht]
      exact hxφ)
  have hle : nonzeroLocus u ≤ U := fun y hy => by
    obtain ⟨a, hya⟩ := hc y
    refine (show X.basicOpen _ ≤ U from hu a) ((LBGerm.isUnit_gs_iff (𝟙 X) y _ hya _).1 ?_)
    exact (congrArg IsUnit (gs_res (𝟙 X) y (hW a) hya _)).mpr ((mem_nonzeroLocus_iff_isUnit u (hW a hya)).1 hy)
  have h := isAffineOpen_nonzeroLocus_inf (isLB_lbPow hL _) u hU
  rw [inf_eq_left.2 hle] at h
  exact ⟨_, Nat.mul_pos (Nat.mul_pos hn hk) hK, u, hxu, h⟩

end GlobalTheory.AmplePoint
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.relAmple_pos_pow_affine_base : ∀ (R : Type) [CommRing R] (B : Over (Spec (CommRingCat.of R))) (L : LB B.left), L.IsLB → RelAmple B L → ∀ a : ℕ, 1 ≤ a → RelAmple B (GlobalTheory.AbLaw.pw L (a : ℤ)) := by
  first | exact @GlobalTheory.PowAmple.relAmple_pw | exact GlobalTheory.PowAmple.relAmple_pw | (intros; apply GlobalTheory.PowAmple.relAmple_pw <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
open GlobalTheory.LB (toMod)

theorem _root_.GlobalTheory.T.cechComplexLineBundle_term_torsionFree_charZero : ∀ {X : Scheme.{0}} [AlgebraicGeometry.IsIntegral X], CharZero Γ(X, ⊤) → ∀ (f : X ⟶ Sp ℤ) (M : LB X) {κ : Type} [LinearOrder κ] (D : κ → X.Opens) (n : ℕ) (m : ℤ), m ≠ 0 → ∀ x : (GlobalTheory.AbLaw.cechLB f M D).X n, m • x = 0 → x = 0 := by
  first | exact @GlobalTheory.CechPic.cechLB_X_noZSMulDivisors | exact GlobalTheory.CechPic.cechLB_X_noZSMulDivisors | (intros; apply GlobalTheory.CechPic.cechLB_X_noZSMulDivisors <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_translationClosed_charts_subordinate_to_cover : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (u : Unif F s σ), X.IsSeparated → ∀ {N : Type} (𝒰 : N → X.Opens), ⨆ i, 𝒰 i = ⊤ → ∃ (K : Charts F) (r : Real K s σ) (j : K.K → N), K.Rich ∧ (∀ l k', ∃ k, K.le l k' k ∧ K.le (-l) k k') ∧ r.IsFor u ∧ ∀ k, ⊤ ≤ r.x k ⁻¹ᵁ 𝒰 (j k) := by
  first | exact @GlobalTheory.AnPer.exists_charts_subordinate | exact GlobalTheory.AnPer.exists_charts_subordinate | (intros; apply GlobalTheory.AnPer.exists_charts_subordinate <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.holomorphicPeriods_natural_along_covered_morphism : ∀ {I₁ : Type} [Fintype I₁] {g₁ : ℕ} {Λ₁ : Type} [AddCommGroup Λ₁] {F₁ : Fam I₁ g₁ Λ₁} {B₁ : Type} [CommRing B₁] {X₁ : Scheme.{0}} {s₁ : X₁ ⟶ Sp B₁} {σ₁ : B₁ →+* Hol F₁.V} {I₂ : Type} [Fintype I₂] {g₂ : ℕ} {Λ₂ : Type} [AddCommGroup Λ₂] {F₂ : Fam I₂ g₂ Λ₂} {B₂ : Type} [CommRing B₂] {X₂ : Scheme.{0}} {s₂ : X₂ ⟶ Sp B₂} {σ₂ : B₂ →+* Hol F₂.V} (u₁ : Unif F₁ s₁ σ₁) (u₂ : Unif F₂ s₂ σ₂), X₁.IsSeparated → X₂.IsSeparated → ∀ (b : (I₁ → ℂ) → I₂ → ℂ) (hb : AnalyticOnNhd ℂ b F₁.V) (hbV : ∀ z ∈ F₁.V, b z ∈ F₂.V) (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) (A : Λ₁ →+ Λ₂), (∀ l, ∀ z ∈ F₁.V, F₂.τ (A l) (b z) = M (F₁.τ l z)) → ∀ (β : B₂ →+* B₁) (φ : X₁ ⟶ X₂) (m : IsMor (dp0 B₂) s₂ (dp0 B₁) s₁ β φ), (∀ x, σ₁ (β x) = Hol.comap b hb hbV (σ₂ x)) → (∀ p : Tot I₁ g₁, p.1 ∈ F₁.V → u₁.E p ≫ φ = u₂.E (b p.1, M p.2)) → ∀ (c : FirstDeRham s₂) (per₂ : Λ₂ →+ Hol F₂.V) (per₁ : Λ₁ →+ Hol F₁.V), IsPeriod u₂ c per₂ → IsPeriod u₁ (m.pull1 c) per₁ → ∀ l, per₁ l = Hol.comap b hb hbV (per₂ (A l)) := by
  first | exact @GlobalTheory.AnPer.isPeriod_pull1_eq_comap | exact GlobalTheory.AnPer.isPeriod_pull1_eq_comap | (intros; apply GlobalTheory.AnPer.isPeriod_pull1_eq_comap <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem isChar_cusp_and_norm_of_reg (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (m k : ℕ) (hm : 0 < m)
    (hk : Reg (Nat.card F) m k) :
    IsChar ℂ ℂ (cusp θ m k) ∧
      ∑ᶠ x, cusp θ m k x * star (cusp θ m k x) = (Nat.card (GL (Fin m) F) : ℂ) := by
  obtain ⟨h1, h2⟩ := isChar_psi_rootSum_of_regular F θ hθ m k hm hk
  refine ⟨h1, ?_⟩
  have hip := ipGL_eq_finsum_GL (F := F) (d := m) (psi (rootSum θ k) (Fin m → F))
    (psi (rootSum θ k) (Fin m → F))
  rw [h2] at hip
  have hsq : ((-1 : ℂ) ^ (m - 1)) * star ((-1 : ℂ) ^ (m - 1)) = 1 := by
    rw [star_pow, star_neg, star_one, ← mul_pow]
    norm_num
  have hterm : ∀ x : GL (Fin m) F, cusp θ m k x * star (cusp θ m k x) =
      psi (rootSum θ k) (Fin m → F) (Matrix.toLin' (x : Matrix (Fin m) (Fin m) F)) *
        star (psi (rootSum θ k) (Fin m → F) (Matrix.toLin' (x : Matrix (Fin m) (Fin m) F))) := by
    intro x
    simp only [cusp, psiG, star_mul']
    linear_combination (psi (rootSum θ k) (Fin m → F) (Matrix.toLin' (x : Matrix (Fin m) (Fin m) F)) *
        star (psi (rootSum θ k) (Fin m → F) (Matrix.toLin' (x : Matrix (Fin m) (Fin m) F)))) * hsq
  rw [finsum_congr hterm, ← hip]
  rfl

end GlobalTheory.Shin
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem kills_const_mul {G : Type} [Group G] [Finite G] (c : ℂ) (f Y : G → ℂ) (h : Kills f Y) :
    Kills (fun g => c * f g) Y := by
  intro V _ _ _ ρ hY
  have hk := h V ρ hY
  have : Fintype G := Fintype.ofFinite G
  rw [finsum_eq_sum_of_fintype] at hk ⊢
  have e : (fun g => star (c * f g) • ρ g) = fun g => star c • (star (f g) • ρ g) := by
    funext g; rw [star_mul', mul_smul]
  simp only []
  rw [e, ← Finset.smul_sum, hk, smul_zero]

theorem kills_of_norm_one_of_pairing_prime :
    ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime →
      s ≠ 1 → ∀ X ∈ Virt ℂ ℂ (G ⋊[φ] Γ), ∑ᶠ g, X (inl g * inr s) * star (X (inl g * inr s)) = (Nat.card G : ℂ) →
      ∀ Y : G → ℂ, IsChar ℂ ℂ Y → (∀ g, Y (φ s g) = Y g) → ∀ z : ℤ,
      ∑ᶠ g, X (inl g) * star (Y g) = z * (Nat.card G : ℂ) → ¬ ((Nat.card Γ : ℤ) ∣ z) →
      Kills (fun δ => X (inl δ * inr s)) Y := by
  intro G Γ _ _ _ _ φ s hp hs X hX hn Y hY hYs z hz hl
  obtain ⟨χ, e, hχ, hχG, hXe⟩ := GlobalTheory.T.virtualCharacter_coset_normOne_single G Γ φ s hp hs X hX hn
  have hgen : ∀ t : Γ, t ∈ Subgroup.zpowers s := by
    haveI : Fact (Nat.card Γ).Prime := ⟨hp⟩
    intro t
    rw [zpowers_eq_top_of_prime_card rfl hs]
    exact Subgroup.mem_top t
  obtain ⟨Z, hZ, hZY⟩ := GlobalTheory.T.exists_semidirect_character_ext_of_stable G Γ φ s hgen Y hY hYs
  have hZv : Z ∈ Virt ℂ ℂ (G ⋊[φ] Γ) := AddSubgroup.subset_closure hZ
  have hXZ : ∑ᶠ g, X (inl g) * star (Z (inl g)) = z * (Nat.card G : ℂ) := by
    simp only [hZY]; exact hz
  have hc := GlobalTheory.T.finsum_semidirect_coset_pairing_ne_zero G Γ φ s hp hs X hX Z hZv z hXZ hl
  have hχc : ∑ᶠ g, χ (inl g * inr s) * star (Z (inl g * inr s)) ≠ 0 := by
    intro h0
    apply hc
    have : (fun g => X (inl g * inr s) * star (Z (inl g * inr s)))
        = fun g => e * (χ (inl g * inr s) * star (Z (inl g * inr s))) := by
      funext g; rw [hXe, mul_assoc]
    rw [this, ← mul_finsum, h0, mul_zero]
  have hχchar : IsChar ℂ ℂ χ := by
    obtain ⟨n, ρ, -, h⟩ := hχ; exact ⟨n, ρ, h⟩
  have hχY : ∑ᶠ g, χ (inl g) * star (Y g) ≠ 0 := by
    intro h0
    apply hχc
    apply GlobalTheory.T.finsum_semidirect_coset_character_orth_zero G Γ φ s hp hs χ Z hχchar hZ
    simp only [hZY]; exact h0
  have hK := GlobalTheory.T.twisted_restricted_character_in_isotypic_part G Γ φ s χ Y hχchar hχG hY hχY
  have := kills_const_mul e _ Y hK
  simpa only [hXe] using this

end GlobalTheory.Shin
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.twistedHarishChandra_isotypic_part : ∀ (F : Type) [Field F] [Finite F], ∀ (t : F →+* F) (a b n : ℕ), n = a + b → ∀ (α A : GL (Fin a) F → ℂ) (β B : GL (Fin b) F → ℂ), IsChar ℂ ℂ A → IsChar ℂ ℂ B → Kills α A → Kills β B → Kills (hcTw t a b α β n) (hc a b A B n) := by
  first | (exact @GlobalTheory.Shin.HcIso.kills_hcTw) | (exact GlobalTheory.Shin.HcIso.kills_hcTw) | (intros; apply GlobalTheory.Shin.HcIso.kills_hcTw <;> assumption)
end
