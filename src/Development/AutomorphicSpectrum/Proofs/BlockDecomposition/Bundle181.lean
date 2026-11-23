module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle173
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DFormMem
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormAlternating
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle145
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.SchCut
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle166
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableCartan
public import GroundTheory.AutomorphicForms.GKModules.Casimir
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle171
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Fin.Tuple.Sort
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.FewEq

open GlobalTheory.SmallExtLift

theorem exists_local_of_gen {R : Type} [CommRing R] {X Y : Scheme.{0}} (s : X ⟶ Sp R) (J : Ideal R)
    {π : Y ⟶ X} {f' : Y ⟶ Sp (R ⧸ J)}
    (H : IsPullback π f' s (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    (M : LB X) (A : Type) (V : A → X.Opens) (j : A → M.ι) (hj : ∀ a, V a ≤ M.U (j a))
    (hV : ∀ a, IsAffineOpen (V a)) (hVV : ∀ a b, IsAffineOpen (V a ⊓ V b))
    (t : LB.Gen (M.pull π)) (ht : t.IsGen) :
    ∃ y z : ∀ a, Γ(X, V a), (∀ a, y a * z a - 1 ∈ ext s J (V a)) ∧
      ∀ a b, rs X inf_le_left (y a) - tr M V j hj a b * rs X inf_le_right (y b) ∈
        ext s J (V a ⊓ V b) := by
  choose y hy using fun a => app_surj Ideal.Quotient.mk_surjective H (hV a)
    (rs Y (pull_le M π (j a) (hj a)) (t.s fun _ => j a).val)
  choose z hz using fun a => app_surj Ideal.Quotient.mk_surjective H (hV a)
    (rs Y (pull_le M π (j a) (hj a)) (t.s fun _ => j a)⁻¹.val)
  refine ⟨y, z, fun a => ?_, fun a b => ?_⟩
  · have h := mem_of_app_eq_zero Ideal.Quotient.mk_surjective H (hV a) (y a * z a - 1) (by
      rw [map_sub, map_mul, map_one, hy, hz, ← map_mul, Units.mul_inv, map_one, sub_self])
    rwa [Ideal.mk_ker] at h
  · have h := mem_of_app_eq_zero Ideal.Quotient.mk_surjective H (hVV a b)
      (rs X inf_le_left (y a) - tr M V j hj a b * rs X inf_le_right (y b)) (gr_ext fun w hw => by
        have e : ∀ c (h : (𝟙 Y ≫ π) w ∈ V c), gr (𝟙 Y ≫ π) w (V c) h (y c) =
            gr (𝟙 Y) w _ (pull_le M π (j c) le_rfl (hj c h)) (t.s fun _ => j c).val := fun c h =>
          (gr_app (𝟙 Y) π w (V c) h (y c)).symm.trans
            ((congrArg _ (hy c)).trans (gr_res (𝟙 Y) w _ h _))
        refine (gr_app _ _ _ _ _ _).trans ?_
        simp only [tr]
        rw [map_zero, map_sub, map_mul, gr_res, gr_res, gr_res, e, e, sub_eq_zero]
        exact gr_gen ht (𝟙 Y) w (hj a hw.1) (hj b hw.2))
    rwa [Ideal.mk_ker] at h

theorem exists_local_of_triv : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Ideal R) (M : LB X), M.IsLB →
    ∀ (A : Type) (V : A → X.Opens) (j : A → M.ι) (hj : ∀ a, V a ≤ M.U (j a)),
      (∀ a, IsAffineOpen (V a)) → (∀ a b, IsAffineOpen (V a ⊓ V b)) →
      GlobalTheory.AbLaw.Triv (M.pull (pullback.fst s (spMap (Ideal.Quotient.mk J)))) →
      ∃ y z : ∀ a, Γ(X, V a), (∀ a, y a * z a - 1 ∈ ext s J (V a)) ∧
        ∀ a b, rs X inf_le_left (y a) - tr M V j hj a b * rs X inf_le_right (y b) ∈ ext s J (V a ⊓ V b) := by
  intro R _ X s J M _ A V j hj hV hVV ⟨t, ht⟩
  exact exists_local_of_gen s J (IsPullback.of_hasPullback s (spMap (Ideal.Quotient.mk J))) M A V j
    hj hV hVV t ht

end GlobalTheory.CompanionTheory.FewEq
end
end

section

set_option maxSynthPendingDepth 1

open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.CompanionTheory.HCRep

open AutomorphicForm GlobalTheory.CompanionTheory.ArchSmooth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def smL (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) :
    Sm E a →ₗ[ℂ] AutomorphicForm.archSmooth E a where
  toFun φ := ⟨φ.1, sm_mem_archSmooth E a φ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem smL_injective : Function.Injective (smL E a) := fun _ _ h =>
  Subtype.ext (congrArg (fun ψ : AutomorphicForm.archSmooth E a => ψ.1) h)

def liB (X : (isExpLieAlgebra E a).lieSubalgebra) : Module.End ℂ (Sm E a) :=
  lie E a (mMap E a (X : ArchMatrix E a))

def lapOp {d : ℕ} (b : Fin d → (isExpLieAlgebra E a).lieSubalgebra) : Module.End ℂ (Sm E a) :=
  ∑ i, liB (b i) * liB (b i)

def omegaOp {d : ℕ} (b : Fin d → (isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ) :
    Module.End ℂ (Sm E a) :=
  ∑ i, (ε i : ℂ) • (liB (b i) * liB (b i))

theorem smL_liB (X : (isExpLieAlgebra E a).lieSubalgebra) (ψ : Sm E a) :
    smL E a (liB X ψ) = uAction (UniversalEnvelopingAlgebra.ι ℝ X) (smL E a ψ) := by
  apply Subtype.ext
  funext g
  rw [uAction_ι_apply]
  change lieD (mMap E a (X : ArchMatrix E a)) ψ.1 g = _
  have h1 := (isExpLieAlgebra E a).hasDerivAt_rightDeriv (sm_mem_archSmooth E a ψ g)
    ((isExpLieAlgebra E a).ofLie X) 1
  let L : ArchMatrix E a →L[ℝ] Lie E a := LinearMap.toContinuousLinearMap (mMap E a)
  have hc : HasDerivAt (fun t : ℝ => toL (toGL E a ((isExpLieAlgebra E a).expG
      (t • (isExpLieAlgebra E a).ofLie X))).val) (mMap E a (X : ArchMatrix E a)) 0 := by
    have h3 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • (X : ArchMatrix E a)))
        (NormedSpace.exp ((0 : ℝ) • (X : ArchMatrix E a)) * (X : ArchMatrix E a)) 0 :=
      hasDerivAt_exp_smul_const (X : ArchMatrix E a) (0 : ℝ)
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at h3
    have h4 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h3
    refine h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    exact toL_toGL E a _
  have h0 : toGL E a ((isExpLieAlgebra E a).expG ((0 : ℝ) • (isExpLieAlgebra E a).ofLie X)) = 1 := by
    simp [toGL]
  have h2 := hasDerivAt_curve ψ g (fun t => toGL E a ((isExpLieAlgebra E a).expG
      (t • (isExpLieAlgebra E a).ofLie X))) (mMap E a (X : ArchMatrix E a)) h0 hc
  refine h2.unique (h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_))
  simp only [archSlice_apply, one_mul, infEmb_eq]

theorem smL_lapOp {d : ℕ} (b : Fin d → (isExpLieAlgebra E a).lieSubalgebra) (ψ : Sm E a) :
    smL E a (lapOp b ψ) = ∑ i, uAction (UniversalEnvelopingAlgebra.ι ℝ (b i))
      (uAction (UniversalEnvelopingAlgebra.ι ℝ (b i)) (smL E a ψ)) := by

  simp only [lapOp, LinearMap.sum_apply, map_sum, Module.End.mul_apply, smL_liB]

theorem smL_omegaOp {d : ℕ} (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ)
    (ψ : Sm E a) : smL E a (omegaOp b ε ψ) = uAction (casimir b ε) (smL E a ψ) := by

  simp only [omegaOp, casimir, LinearMap.sum_apply, map_sum, LinearMap.smul_apply, map_smul,
  Module.End.mul_apply, smL_liB, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ext g
  simp [Complex.real_smul]

theorem omegaOp_comm_liB {d : ℕ} (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (horth : ∀ i j, archTraceForm E a (b i) (b j) = if i = j then ε i else 0)
    (X : (isExpLieAlgebra E a).lieSubalgebra) :
    omegaOp b ε * liB X = liB X * omegaOp b ε := by
  have hε2 : ∀ i, ε i * ε i = 1 := fun i => by rcases hε i with e | e <;> rw [e] <;> norm_num
  have hz : casimir b ε ∈ (isExpLieAlgebra E a).centerU :=
    casimir_mem_center hε2 horth archTraceForm_symm archTraceForm_lie
  have hc := Subalgebra.mem_center_iff.1 hz (UniversalEnvelopingAlgebra.ι ℝ X)
  refine LinearMap.ext fun ψ => smL_injective ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, smL_omegaOp, smL_liB, smL_liB, smL_omegaOp,
    ← Module.End.mul_apply, ← map_mul, ← hc, map_mul, Module.End.mul_apply]

end GlobalTheory.CompanionTheory.HCRep

end
end

section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal

section Collapse
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {d : ℕ}

theorem form_sum_zsmul (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) {m : ℕ} (I : Fin m → Fin d)
    {ι : Type} [Fintype ι] (a : ι → ℤ) (w : ι → Φ.A.obj E.D) (u : ComposableArrows C m) :
    E.form σ I (∑ i, a i • w i) u = ∑ i, a i • E.form σ I (w i) u := by
  unfold Frame.form

  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, mul_smul_comm]

theorem form_zsmul (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) {m : ℕ} (I : Fin m → Fin d)
    (a : ℤ) (w : Φ.A.obj E.D) (u : ComposableArrows C m) :
    E.form σ I (a • w) u = a • E.form σ I w u := by
  unfold Frame.form
  rw [map_zsmul, mul_smul_comm]

theorem sgn_eq_zero_of_not_injective {m : ℕ} (I : Idx m d) {J : Fin m → Fin d} (h : ¬ Function.Injective J) :
    sgn I J = 0 := by
  refine Finset.sum_eq_zero fun π _ => if_neg ?_
  intro e
  exact h (e ▸ I.2.injective.comp π.injective)

theorem exists_increasing {m : ℕ} {J : Fin m → Fin d} (h : Function.Injective J) :
    ∃ (I : Idx m d) (π : Equiv.Perm (Fin m)), J = I.1 ∘ π := by
  refine ⟨⟨J ∘ Tuple.sort J, (Tuple.monotone_sort J).strictMono_of_injective
    (h.comp (Tuple.sort J).injective)⟩, (Tuple.sort J)⁻¹, ?_⟩
  funext k
  simp

theorem sgn_comp_self {m : ℕ} (I : Idx m d) (π : Equiv.Perm (Fin m)) :
    sgn I (I.1 ∘ π) = (Equiv.Perm.sign π : ℤ) := by
  unfold sgn
  rw [Finset.sum_eq_single π]
  · simp
  · intro b _ hb
    refine if_neg fun e => hb ?_
    exact (Equiv.ext fun k => I.2.injective (congrFun e k)).symm
  · simp

theorem sgn_comp_of_ne {m : ℕ} {I I' : Idx m d} (π : Equiv.Perm (Fin m)) (h : I' ≠ I) :
    sgn I' (I.1 ∘ π) = 0 := by
  refine Finset.sum_eq_zero fun π' _ => if_neg fun e => h (Subtype.ext ?_)
  refine (StrictMono.range_inj I'.2 I.2).1 ?_
  have e' := congrArg Set.range e
  rw [π.surjective.range_comp, π'.surjective.range_comp] at e'
  exact e'.symm

theorem rep_finset_sum {A : C ⥤ CommAlgCat.{0} R} {a b : IdF A} {j : ℕ} {ι : Type} (t : Finset ι)
    {z : ι → ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))} {c : ι → CH.H (sq a b) j}
    (h : ∀ i, CrystallineSemistableComparison.Pb.Rep a b (z i) (c i)) :
    CrystallineSemistableComparison.Pb.Rep a b (fun s => ∑ i ∈ t, z i s) (∑ i ∈ t, c i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact rep_zero fun s => Ideal.zero_mem _
  | insert i t hi ih =>
    simp only [Finset.sum_insert hi]
    exact rep_add (h i) ih

theorem rep_collapse_one {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T)
    (hc : E.GrConst Fil) (m : ℕ) (r : ℤ) (hr : r = m) (J : Fin m → Fin d) (w : Φ.A.obj E.D)
    (c : CH.H (gr Fil r) m) (h : CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) (E.form σ J w) c) :
    CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) (fun u => ∑ I : Idx m d, E.form σ I.1 (sgn I J • w) u) c := by
  have hw : w ∈ (Fil ((0 : ℕ) : ℤ)).S E.D := by
    rw [hF.top _ (by simp)]
    trivial
  have hr0 : r = (m : ℤ) + ((0 : ℕ) : ℤ) := by simpa using hr
  by_cases hJ : Function.Injective J
  · obtain ⟨I, π, rfl⟩ := exists_increasing hJ
    obtain ⟨c₀, h₀⟩ := GlobalTheory.CompanionTheory.CocProd.rep_form hF E σ hc m 0 r hr0 I.1 w hw
    have h₁ := (GlobalTheory.CompanionTheory.AltForm.form_alternating hF E σ hc m 0 r hr0 I.1 w hw c₀ h₀).2.1 π
    obtain rfl := rep_unique h h₁
    have h₂ := GlobalTheory.CompanionTheory.AltForm.Rep.zsmul (Equiv.Perm.sign π : ℤ) h₀
    refine rep_congr h₂ fun u => ?_
    rw [Finset.sum_eq_single I, sgn_comp_self, form_zsmul, Pi.smul_apply, sub_self]
    · exact Ideal.zero_mem _
    · intro I' _ hI'
      rw [sgn_comp_of_ne π hI', zero_smul]
      unfold Frame.form
      simp
    · simp
  · obtain rfl := (GlobalTheory.CompanionTheory.AltForm.form_alternating hF E σ hc m 0 r hr0 J w hw c h).1 hJ
    refine rep_zero fun u => ?_
    rw [Finset.sum_eq_zero]
    · exact Ideal.zero_mem _
    · intro I _
      rw [sgn_eq_zero_of_not_injective I hJ, zero_smul]
      unfold Frame.form
      simp

theorem rep_collapse : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} {d : ℕ} (hF : IsFil Φ Fil) (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil)
    (m : ℕ) (r : ℤ), r = m → ∀ {ι : Type} [Fintype ι] (J : ι → Fin m → Fin d) (w : ι → Φ.A.obj E.D) (x : CH.H (gr Fil r) m),
      CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) (fun u => ∑ i, E.form σ (J i) (w i) u) x →
      CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) (fun u => ∑ I : Idx m d, E.form σ I.1 (∑ i, sgn I (J i) • w i) u) x := by
  intro R _ C _ Φ Fil d hF E σ hc m r hr ι _ J w x h
  have hw : ∀ i, w i ∈ (Fil ((0 : ℕ) : ℤ)).S E.D := fun i => by
    rw [hF.top _ (by simp)]
    trivial
  have hr0 : r = (m : ℤ) + ((0 : ℕ) : ℤ) := by simpa using hr
  choose c hcl using fun i => GlobalTheory.CompanionTheory.CocProd.rep_form hF E σ hc m 0 r hr0 (J i) (w i) (hw i)
  obtain rfl := rep_unique h (rep_finset_sum Finset.univ hcl)
  have h₂ := rep_finset_sum Finset.univ fun i => rep_collapse_one hF E σ hc m r hr (J i) (w i) (c i) (hcl i)
  refine rep_congr h₂ fun u => ?_
  rw [Finset.sum_comm]
  have e : ∀ I : Idx m d, E.form σ I.1 (∑ i, sgn I (J i) • w i) u = ∑ i, E.form σ I.1 (sgn I (J i) • w i) u := by
    intro I
    rw [form_sum_zsmul]
    exact Finset.sum_congr rfl fun i _ => (form_zsmul E σ I.1 _ _ u).symm
  simp only [e, sub_self]
  exact Ideal.zero_mem _

end Collapse

end GlobalTheory.CompanionTheory.ConeLocal
end
end

section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal

theorem taylor_alg {K A B : Type} [CommRing K] [CommRing A] [Algebra K A] [CommRing B] [Algebra K B] {d : ℕ}
    (t : Fin d → A)
    (hf : (MvPolynomial.eval₂Hom (algebraMap K A) t : MvPolynomial (Fin d) K →+* A).FormallyUnramified)
    (D : Fin d → Derivation K A A) (hD : ∀ k j, D k (t j) = if k = j then 1 else 0)
    (N P : Ideal B) (hNP : N * N ≤ P) (a b : A →ₐ[K] B) (hab : ∀ x, a x - b x ∈ N) (x : A) :
    a x - b x - ∑ k, (a (t k) - b (t k)) * b (D k x) ∈ P := by
  classical
  let f : MvPolynomial (Fin d) K →+* A := MvPolynomial.eval₂Hom (algebraMap K A) t
  let π : B →+* B ⧸ P := Ideal.Quotient.mk P
  let e : Fin d → B := fun k => a (t k) - b (t k)
  have he : ∀ k, e k ∈ N := fun k => hab _
  let S : A → B := fun x => ∑ k, e k * b (D k x)
  have hS : ∀ x, S x ∈ N := fun x => Ideal.sum_mem _ fun k _ => N.mul_mem_right _ (he k)
  have hSadd : ∀ x y, S (x + y) = S x + S y := fun x y => by
    simp only [S, map_add (f := _), mul_add, Finset.sum_add_distrib]
  have hSmul : ∀ x y, S (x * y) = b x * S y + b y * S x := fun x y => by
    simp only [S, Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul, mul_add, Finset.sum_add_distrib,
      Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun k _ => by ring
  have hSone : S 1 = 0 := by simp [S]
  have hSzero : S 0 = 0 := by simp [S]
  let c : A →+* B ⧸ P :=
    { toFun := fun x => π (b x + S x)
      map_one' := by simp [hSone]
      map_zero' := by simp [hSzero]
      map_add' := fun x y => by
        rw [hSadd, map_add b, ← map_add π]
        congr 1
        ring
      map_mul' := fun x y => by
        rw [← map_mul π]
        refine Ideal.Quotient.eq.2 ?_
        have h := hNP (Ideal.mul_mem_mul (hS x) (hS y))
        have e2 : b (x * y) + S (x * y) - (b x + S x) * (b y + S y) = -(S x * S y) := by
          rw [hSmul, map_mul]
          ring
        rw [e2]
        exact P.neg_mem h }
  have hc : ∀ x, c x = π (b x + S x) := fun _ => rfl
  have hcf : c.comp f = π.comp ((a : A →+* B).comp f) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) fun i => ?_
    · simp only [RingHom.comp_apply, f, MvPolynomial.eval₂Hom_C, hc]
      have : S (algebraMap K A r) = 0 := by simp [S]
      simp [this]
    · simp only [RingHom.comp_apply, f, MvPolynomial.eval₂Hom_X', hc]
      have : S (t i) = e i := by simp [S, hD, e]
      rw [this]
      simp [e]
  letI algA : Algebra (MvPolynomial (Fin d) K) A := f.toAlgebra
  letI algC : Algebra (MvPolynomial (Fin d) K) (B ⧸ P) := (π.comp ((a : A →+* B).comp f)).toAlgebra
  haveI : Algebra.FormallyUnramified (MvPolynomial (Fin d) K) A := hf
  let g₁ : A →ₐ[MvPolynomial (Fin d) K] B ⧸ P :=
    { toRingHom := π.comp (a : A →+* B), commutes' := fun _ => rfl }
  let g₂ : A →ₐ[MvPolynomial (Fin d) K] B ⧸ P :=
    { toRingHom := c, commutes' := fun p => RingHom.congr_fun hcf p }
  have hnil : IsNilpotent (N.map π) := by
    refine ⟨2, ?_⟩
    rw [pow_two, ← Ideal.map_mul, Ideal.zero_eq_bot]
    refine le_bot_iff.1 ((Ideal.map_mono hNP).trans ?_)
    rw [Ideal.map_quotient_self]
  have hg : g₁ = g₂ := by
    refine Algebra.FormallyUnramified.ext (N.map π) hnil fun y => ?_
    refine Ideal.Quotient.eq.2 ?_
    have : g₁ y - g₂ y = π (a y - (b y + S y)) := by
      rw [map_sub]
      rfl
    rw [this]
    refine Ideal.mem_map_of_mem π ?_
    have e3 : a y - (b y + S y) = (a y - b y) - S y := by ring
    rw [e3]
    exact N.sub_mem (hab y) (hS y)
  have h1 : π (a x) = π (b x + S x) := DFunLike.congr_fun hg x
  have h2 := Ideal.Quotient.eq.1 h1
  have e4 : a x - (b x + S x) = a x - b x - ∑ k, (a (t k) - b (t k)) * b (D k x) := by
    simp only [S, e]
    ring
  rwa [e4] at h2

theorem taylor_loc : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {W : X.Opens} {d : ℕ} (c : Coord q W d) (s : ℕ) (E : Frame (sP (KS q s {W})) d)
    (ε : Γ(X, W) ≃+* (sP (KS q s {W})).A.obj E.D), IsLoc q s c.t E ε →
    letI := (strV q W).toAlgebra
    ∀ (D : Fin d → Derivation K Γ(X, W) Γ(X, W)), (∀ k j, D k (c.t j) = if k = j then 1 else 0) →
    Taylor (sFil (KS q s {W})) E (fun k x => ε (D k (ε.symm x))) := by
  intro K _ _ X q W d c s E ε h
  letI := (strV q W).toAlgebra
  intro D hD
  obtain ⟨-, -, h3, h4, h5⟩ := h
  intro T u v x
  obtain ⟨y, rfl⟩ := ε.surjective x
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {W})
  have hcomm : ∀ (w : E.D ⟶ T) (r : K), ((sP (KS q s {W})).A.map w).hom (ε (algebraMap K Γ(X, W) r)) =
      algebraMap K ((sP (KS q s {W})).A.obj T) r := fun w r => by
    have e : ε (algebraMap K Γ(X, W) r) = algebraMap K _ r := h3 r
    rw [e]
    exact AlgHom.commutes _ r
  let ev' : (E.D ⟶ T) → (Γ(X, W) →ₐ[K] (sP (KS q s {W})).A.obj T) := fun w =>
    { toRingHom := RingHom.comp (AlgHom.toRingHom ((sP (KS q s {W})).A.map w).hom) ε.toRingHom
      commutes' := hcomm w }
  have hNP : (sFil (KS q s {W}) 1).S T * (sFil (KS q s {W}) 1).S T ≤ (sFil (KS q s {W}) 2).S T :=
    Ideal.mul_le.2 fun a ha b hb => hF.mul 1 1 T ha hb
  have hab : ∀ g, ev' u g - ev' v g ∈ (sFil (KS q s {W}) 1).S T := fun g => by
    rw [hF.one T]
    have e := (h4 T u g).symm.trans (h4 T v g)
    exact Ideal.Quotient.eq.1 e
  have hf : (MvPolynomial.eval₂Hom (algebraMap K Γ(X, W)) c.t : MvPolynomial (Fin d) K →+* Γ(X, W)).FormallyUnramified :=
    by
      have he := c.etale
      letI := (MvPolynomial.eval₂Hom (strV q W) c.t : MvPolynomial (Fin d) K →+* Γ(X, W)).toAlgebra
      haveI : Algebra.Etale (MvPolynomial (Fin d) K) Γ(X, W) := he
      exact (inferInstance : Algebra.FormallyUnramified (MvPolynomial (Fin d) K) Γ(X, W))
  have key := taylor_alg c.t hf D hD _ _ hNP (ev' u) (ev' v) hab y
  have e : ∀ k, E.τ k v u = ev' u (c.t k) - ev' v (c.t k) := fun k => h5 k v u
  simp only [ε.symm_apply_apply, e]
  exact key

end GlobalTheory.CompanionTheory.ConeLocal
end
end

section

noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.density_integral : PositivityTheory.PfSWUS.SchInf.DensInt := by
  first | exact @GlobalTheory.CompanionTheory.SW.DensInt.density_identity_inf | exact GlobalTheory.CompanionTheory.SW.DensInt.density_identity_inf | (intros; apply GlobalTheory.CompanionTheory.SW.DensInt.density_identity_inf <;> assumption)
end
end

section

noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.archimedean_scaling : PositivityTheory.PfSWUS.SchInf.ScaleInf := by
  first | exact @GlobalTheory.CompanionTheory.SW.HaarScale.scaleInf | exact GlobalTheory.CompanionTheory.SW.HaarScale.scaleInf | (intros; apply GlobalTheory.CompanionTheory.SW.HaarScale.scaleInf <;> assumption)
end
end
