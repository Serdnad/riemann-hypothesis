module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle628
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle735
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle630
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle403
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle082
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle143
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle146
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle655
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle733
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle631

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix GlobalTheory.BKGal.XiFil
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.XiPole

section Rings

variable {l : ℕ} [Fact l.Prime]

theorem ι_aB (C : GlobalTheory.MemLoc.Core l) (w : Per.Ainf l) :
    C.ι (Per.aB l w) = algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l w) :=
  GlobalTheory.MemLoc.ULaws.iota_aB C w

private theorem aB_alg (C : GlobalTheory.MemLoc.Core l) (w : Per.Ainf l) :
    algebraMap (Per.Acris l) (Per.Bcris l) (algebraMap (Per.Ainf l) (Per.Acris l) w) = Per.aB l w :=
  GlobalTheory.MemLoc.ULaws.iota_injective C (by rw [C.ι_j, GlobalTheory.MemLoc.TFil.j_alg C.j_cris, ι_aB])

private theorem toB_tmul (C : GlobalTheory.MemLoc.Core l) {O : Type} [CommRing O] [Algebra ℤ_[l] O] (o : O)
    (w : Per.Ainf l) : toB l O (o ⊗ₜ[ℤ_[l]] w) = o ⊗ₜ[ℤ_[l]] Per.aB l w :=
  congrArg (fun y : Per.Bcris l => (o ⊗ₜ[ℤ_[l]] y : OB l O)) (aB_alg C w)

end Rings

section Tensor

variable {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K]
  {G : Type} [Group G] [TopologicalSpace G]

theorem smul_TWincl_mem_filT (C : GlobalTheory.MemLoc.Core l) (T : LocLat G ℚ_[l] K O) {n : ℤ} {d : Per.Bcris l}
    (hd : C.ι d ∈ Per.FilD l n) (z : TW (OA l O) T) :
    ((1 : O) ⊗ₜ[ℤ_[l]] d : OB l O) • TWincl (toB l O) T z ∈ filT C T n := by
  unfold filT
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, smul_zero]; exact zero_mem _
  | tmul c x =>
    change ((1 : O) ⊗ₜ[ℤ_[l]] d : OB l O) • (toB l O c ⊗ₜ[O] x) ∈ _
    rw [smul_tmul', smul_eq_mul]
    induction c using TensorProduct.induction_on with
    | zero => rw [map_zero, mul_zero, zero_tmul]; exact zero_mem _
    | tmul o w =>
      have e : ((1 : O) ⊗ₜ[ℤ_[l]] d : OB l O) * toB l O (o ⊗ₜ w) =
          o • ((1 : O) ⊗ₜ[ℤ_[l]] (d * Per.aB l w) : OB l O) := by
        rw [toB_tmul C o w, Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [e, ← smul_tmul']
      refine Submodule.smul_mem _ o (Submodule.subset_span ⟨d * Per.aB l w, x, ?_, rfl⟩)
      rw [map_mul, ι_aB, mul_comm, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ hd
    | add c c' hc hc' => rw [map_add (f := _), mul_add, add_tmul]; exact add_mem hc hc'
  | add z z' hz hz' => rw [map_add (f := _), smul_add]; exact add_mem hz hz'

end Tensor

end GlobalTheory.BKGal.XiPole


open GlobalTheory.BKGal.XiPole in
theorem GlobalTheory.BKGal.XiPole.jB_single_mem_filT : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T) (C : GlobalTheory.MemLoc.Core l) (i : ι), R.jB (Pi.single i 1) ∈ filT C T (-(η : ℤ)) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R C i

  obtain ⟨ζ, ε, h0, -, hz1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : ε.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps ε := ⟨he, fun hh => hz1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  have hδl : ((frobeniusEquiv (Per.Fl l) l).symm ε) ^ l = ε := by
    rw [← frobenius_def, ← frobeniusEquiv_apply, RingEquiv.apply_symm_apply]
  have hEps : IsEps ε := ⟨he, _, hδl, hE.2⟩

  obtain ⟨-, -, -, hK4⟩ := GlobalTheory.T.breuilKisin_lattice_exponents_ainf_comparison l a e O K t ϖ ι D.toPhiMod T R.I η H D.upper D.lower ε _ hEps hδl
  obtain ⟨z, hz⟩ := hK4 (inclL t ϖ D.toPhiMod (Pi.single i 1)) ⟨Pi.single i 1, rfl⟩
  rw [← inclL_smul_coord] at hz
  have hB := R.cmp _ z hz
  set m : OA l O := (1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ η) with hm
  have e1 : (fun j => toB l O (m * (Pi.single i (1 : OA l O) : ι → OA l O) j)) = toB l O m • (Pi.single i (1 : OB l O)) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_apply, hj]
  rw [e1, map_smul] at hB
  have htm : toB l O m = (1 : O) ⊗ₜ[ℤ_[l]] Per.aB l (muOf ε ^ η) := toB_tmul C _ _

  have hμu : IsUnit (Per.aB l (muOf ε)) := by
    rw [← aB_alg C]
    exact GlobalTheory.MemLoc.TFil.isUnit_mu hE
  set d : Per.Bcris l := ((hμu.unit⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) ^ η with hd
  have hdm : d * Per.aB l (muOf ε ^ η) = 1 := by
    rw [hd, map_pow, ← mul_pow, IsUnit.val_inv_mul, one_pow]
  clear_value d
  have hjB : R.jB (Pi.single i 1) = ((1 : O) ⊗ₜ[ℤ_[l]] d : OB l O) • TWincl (toB l O) T z := by
    rw [← hB, smul_smul, htm, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hdm,
      ← Algebra.TensorProduct.one_def, one_smul]

  have hν : IsUnit (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.TiedUnif.piOne ε)) :=
    (GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ (GlobalTheory.MemLoc.TiedUnif.theta_piOne hE)
  obtain ⟨v', hv'⟩ := hν.exists_right_inv
  set U := (GlobalTheory.MemLoc.TiedUnif.isUnit_xi hE).unit with hUdef
  have hUval : (U : Per.BdR l) = algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi ε)) :=
    IsUnit.unit_spec _
  have hιμ : C.ι (Per.aB l (muOf ε)) = (U : Per.BdR l) *
      algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.TiedUnif.piOne ε)) := by
    rw [ι_aB, hUval, ← map_mul, ← map_mul]
    exact congrArg _ (congrArg _ (GlobalTheory.MemLoc.TiedUnif.mu_eq ε))
  have h1 : C.ι d * (C.ι (Per.aB l (muOf ε))) ^ η = 1 := by
    rw [← map_pow, ← map_mul, ← map_pow, hdm, map_one]
  rw [hιμ] at h1
  have hpq : ((U : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.TiedUnif.piOne ε)) *
      (((U⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) v')) ^ η = 1 := by
    rw [show ((U : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.TiedUnif.piOne ε)) *
      (((U⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) v')) =
      ((U : Per.BdR l) * ((U⁻¹ : (Per.BdR l)ˣ) : Per.BdR l)) *
        algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.TiedUnif.piOne ε) * v') by
      rw [map_mul]; ring, Units.mul_inv, hv', map_one, one_mul, one_pow]
  have hU : ((U ^ (-(η : ℤ)) : (Per.BdR l)ˣ) : Per.BdR l) = ((U⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) ^ η := by
    rw [_root_.zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
  have hdF : C.ι d ∈ Per.FilD l (-(η : ℤ)) := by
    refine (GlobalTheory.MemLoc.TiedUnif.mem_FilD_iff hE _ _).2 ⟨v' ^ η, ?_⟩
    rw [← hUdef, hU, map_pow]
    calc C.ι d = C.ι d * ((U : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l)
            (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.TiedUnif.piOne ε)) *
          (((U⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) v')) ^ η := by
          rw [hpq, mul_one]
      _ = (C.ι d * ((U : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l)
            (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.TiedUnif.piOne ε))) ^ η) *
          (((U⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) v') ^ η := by
          rw [mul_pow _ _ η, mul_assoc]
      _ = _ := by rw [h1, one_mul, mul_pow]
  rw [hjB]
  exact smul_TWincl_mem_filT C T hdF z
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKExact

theorem det_mul_eq_sum_fun' {R : Type*} [CommRing R] {ι m : Type*} [Fintype ι] [DecidableEq ι] [Fintype m]
    [DecidableEq m] (A : Matrix ι m R) (B : Matrix m ι R) :
    (A * B).det = ∑ f : ι → m, (∏ β, B (f β) β) * (A.submatrix id f).det := by
  simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum, Finset.mul_sum, Fintype.piFinset_univ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun σ _ => ?_
  simp only [Finset.prod_mul_distrib, Matrix.submatrix_apply, id]
  ring

def selCols {R : Type*} [CommRing R] {m n : Type*} [DecidableEq n] (s : m → n) : Matrix n m R :=
  fun k i => if s i = k then (1 : R) else 0

theorem mul_selCols {R : Type*} [CommRing R] {m n : Type*} [Fintype n] [DecidableEq n] (N : Matrix m n R)
    (s : m → n) : N * (selCols (R := R) s) = N.submatrix id s := by
  ext i j
  rw [Matrix.mul_apply]
  simp [selCols]

theorem exists_right_of_minor {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (N : Matrix m n (A O K)) (s : m → n) :
    ∃ Y : Matrix n m K⟦X⟧, (∀ i j, Y i j ∈ A O K) ∧
      N.map (A O K).val * Y = ((N.submatrix id s).det : K⟦X⟧) • (1 : Matrix m m K⟦X⟧) := by
  refine ⟨(selCols (R := A O K) s * (N.submatrix id s).adjugate).map (A O K).val, fun i j => (_ : A O K).2, ?_⟩
  have h1 : N.map (A O K).val * (selCols (R := A O K) s * (N.submatrix id s).adjugate).map (A O K).val =
      (N * (selCols (R := A O K) s * (N.submatrix id s).adjugate)).map (A O K).val := by
    simp only [Matrix.map_mul]
  rw [h1, ← Matrix.mul_assoc, mul_selCols, Matrix.mul_adjugate]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem exists_right {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} {O K : Type} [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
    {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (M : Matrix m n (ZMod a → A O K))
    (Z : Matrix n m (OW l O)) (hZ : M.map (fun x => inclO l O (ϖ.iTot t K x)) * Z = 1) (τ : ZMod a) :
    ∃ (Y : Matrix n m K⟦X⟧) (g : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧ g ∈ A O K ∧ (∃ k, ‖coeff k g‖ = 1) ∧
      (Matrix.of fun i j => (M i j τ : K⟦X⟧)) * Y = g • (1 : Matrix m m K⟦X⟧) := by
  let φ : (ZMod a → A O K) →+* OW l O := (inclO l O).toRingHom.comp (ϖ.iTot t K).toRingHom
  have h1 := congrArg Matrix.det hZ
  rw [Matrix.det_one, det_mul_eq_sum_fun'] at h1
  have h2 : ∀ f : m → n, ((M.map fun x => inclO l O (ϖ.iTot t K x)).submatrix id f).det =
      inclO l O (ϖ.iTot t K (M.submatrix id f).det) := fun f => by
    exact (RingHom.map_det φ (M.submatrix id f)).symm
  simp only [h2] at h1
  obtain ⟨f, k, hk⟩ := GlobalTheory.T.exists_unit_coeff_wittTilt_relation t ϖ (fun f => (M.submatrix id f).det) _ h1 τ
  let N : Matrix m n (A O K) := fun i j => M i j τ
  have h3 : (M.submatrix id f).det τ = (N.submatrix id f).det :=
    RingHom.map_det (Pi.evalRingHom (fun _ : ZMod a => A O K) τ) (M.submatrix id f)
  obtain ⟨Y, hY, hNY⟩ := exists_right_of_minor N f
  refine ⟨Y, _, hY, (N.submatrix id f).det.2, ⟨k, ?_⟩, hNY⟩
  rw [← h3]
  exact hk

theorem isExactTriple_of_isSESLat_gen {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e] {O K : Type} [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a]
    (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {G : Type} [Group G] [TopologicalSpace G]
    {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ]
    {P₀ : PhiMod O K l e a ι} {P₁ : PhiMod O K l e a κ} {P₂ : PhiMod O K l e a μ}
    {T₀ T₁ T₂ : LocLat G ℚ_[l] K O} {I₀ : Ident t ϖ P₀ T₀} {I₁ : Ident t ϖ P₁ T₁} {I₂ : Ident t ϖ P₂ T₂}
    {f : LatHom T₀.L T₁.L} {g : LatHom T₁.L T₂.L} {F : BK.Hom P₀ P₁} {H : BK.Hom P₁ P₂}
    (hS : IsSESLat (Qp := ℚ_[l]) f g) (hF : IsMapOf I₀ I₁ f F) (hH : IsMapOf I₁ I₂ g H) : IsExactTriple F H := by
  obtain ⟨⟨Z, hZ⟩, ⟨Yw, hYw⟩⟩ := GlobalTheory.T.phiModuleHom_shortExact_split_wittTilt_alt t ϖ hS hF hH
  have hex := GlobalTheory.T.tame_setting_group_action_compat t ϖ hS hF hH
  let φ : (ZMod a → A O K) →+* OW l O := (inclO l O).toRingHom.comp (ϖ.iTot t K).toRingHom
  have hφ : Function.Injective φ := inclO_injective.comp (ϖ.iTot_injective t K)
  let ψ : ZMod a → (ZMod a → A O K) →+* K⟦X⟧ := fun τ =>
    (A O K).val.toRingHom.comp (Pi.evalRingHom (fun _ : ZMod a => A O K) τ)
  have extPi : ∀ {m n : Type} (M N : Matrix m n (ZMod a → A O K)),
      (∀ τ, M.map (ψ τ) = N.map (ψ τ)) → M = N := fun M N h => by
    funext i j τ
    exact Subtype.ext (congrFun₂ (h τ) i j)
  let Ht : Matrix μ κ (ZMod a → A O K) := fun i j τ => ⟨H.mat τ i j, H.mem τ i j⟩
  let Ft : Matrix κ ι (ZMod a → A O K) := fun i j τ => ⟨F.mat τ i j, F.mem τ i j⟩
  have hHr : ∀ τ, ∃ (Y : Matrix κ μ K⟦X⟧) (c : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧
      c ∈ A O K ∧ (∃ k, ‖coeff k c‖ = 1) ∧ H.mat τ * Y = c • (1 : Matrix μ μ K⟦X⟧) :=
    fun τ => exists_right t ϖ Ht Z hZ τ
  have hFl : ∀ τ, ∃ (Y : Matrix ι κ K⟦X⟧) (c : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧
      c ∈ A O K ∧ (∃ k, ‖coeff k c‖ = 1) ∧ Y * F.mat τ = c • (1 : Matrix ι ι K⟦X⟧) := by
    intro τ
    have hT : Ftᵀ.map (fun x => inclO l O (ϖ.iTot t K x)) * Ywᵀ = 1 := by
      rw [Matrix.transpose_map, ← Matrix.transpose_mul]
      exact (congrArg Matrix.transpose hYw).trans Matrix.transpose_one
    obtain ⟨Y, c, hY, hc, hk, h⟩ := exists_right t ϖ Ftᵀ Ywᵀ hT τ
    refine ⟨Yᵀ, c, fun i j => hY j i, hc, hk, ?_⟩
    have h1 := congrArg Matrix.transpose h
    rw [Matrix.transpose_mul, Matrix.transpose_smul, Matrix.transpose_one] at h1
    exact h1
  choose YH cH hYH hcH hkH hHY using hHr
  choose YF cF hYF hcF hkF hFY using hFl
  have hne : ∀ {c : K⟦X⟧}, (∃ k, ‖coeff k c‖ = 1) → c ≠ 0 := by
    rintro c ⟨k, hk⟩ rfl
    simp at hk
  refine ⟨?_, ?_, ?_⟩
  · intro v hv hFv
    funext τ
    have h1 : cF τ • v τ = 0 := by
      have h2 := congrArg (fun x => YF τ *ᵥ x τ) hFv
      simp only [Hom.app_apply, Matrix.mulVec_mulVec, hFY, Matrix.smul_mulVec, Matrix.one_mulVec,
        Pi.zero_apply, Matrix.mulVec_zero] at h2
      exact h2
    exact (smul_eq_zero.1 h1).resolve_left (hne (hkF τ))
  · intro v hv
    constructor
    · intro hHv
      refine (GlobalTheory.T.finiteLength_coker_of_surjective_mod_uniformizer O K l e a ι κ P₀ P₁ F).2 (fun τ => ⟨YF τ, cF τ, hYF τ, hkF τ, hFY τ⟩) v hv
        (∏ τ, cF τ) (prod_mem fun τ _ => hcF τ) (Finset.prod_ne_zero_iff.2 fun τ _ => hne (hkF τ)) ?_
      let Yt : Matrix ι κ (ZMod a → A O K) := fun i j τ => ⟨YF τ i j, hYF τ i j⟩
      let gt : ZMod a → A O K := fun τ => ⟨cF τ, hcF τ⟩
      let vt : κ → ZMod a → A O K := fun i τ => ⟨v τ i, mem_tot.1 hv τ i⟩
      have hYFt : Yt * Ft = Matrix.diagonal fun _ => gt := by
        refine extPi _ _ fun τ => ?_
        rw [Matrix.map_mul, Matrix.diagonal_map (map_zero _)]
        exact (hFY τ).trans (Matrix.smul_one_eq_diagonal _)
      have hv' : toW t ϖ P₁ ⟨v, mem_ME_of_mem_M hv⟩ = fun i => φ (vt i) :=
        funext fun i => ϖ.iW_of_mem t K (vt i)
      have h0 : homW t ϖ H (toW t ϖ P₁ ⟨v, mem_ME_of_mem_M hv⟩) = 0 := by
        rw [homW_toW]
        have : (⟨H.app v, H.app_mem_Mext (le_away _ _) (mem_ME_of_mem_M hv)⟩ : ME P₂) = 0 :=
          Subtype.ext hHv
        rw [this, map_zero]
      obtain ⟨w, hw⟩ := hex _ h0
      rw [homW_apply, hv'] at hw
      change Ft.map φ *ᵥ w = fun i => φ (vt i) at hw
      have h1 : (Ft * Yt).map φ *ᵥ (fun i => φ (vt i)) = φ gt • (fun i => φ (vt i)) := by
        rw [← hw, Matrix.map_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc,
          show Yt.map φ * Ft.map φ = (Yt * Ft).map φ from (Matrix.map_mul).symm, hYFt,
          Matrix.diagonal_map (map_zero _), ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one,
          Matrix.smul_mulVec]
      have h2 : (Ft * Yt) *ᵥ vt = gt • vt := by
        funext i
        apply hφ
        rw [RingHom.map_mulVec]
        refine (congrFun h1 i).trans ?_
        show φ gt * φ (vt i) = φ (gt * vt i)
        rw [map_mul]
      have hkey : ∀ τ, F.mat τ *ᵥ (YF τ *ᵥ v τ) = cF τ • v τ := fun τ => by
        funext i
        have := congrArg (ψ τ) (congrFun h2 i)
        rw [RingHom.map_mulVec, Matrix.map_mul] at this
        rw [Matrix.mulVec_mulVec]
        exact this.trans (map_mul (ψ τ) gt (vt i))
      refine ⟨fun τ => (∏ σ ∈ Finset.univ.erase τ, cF σ) • (YF τ *ᵥ v τ), mem_tot.2 fun τ i => ?_, ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
        exact mul_mem (prod_mem fun σ _ => hcF σ)
          (sum_mem fun j _ => mul_mem (hYF τ i j) (mem_tot.1 hv τ j))
      · change F.app _ = _
        funext τ
        rw [Hom.app_apply, Matrix.mulVec_smul, hkey, smul_smul,
          Finset.prod_erase_mul _ _ (Finset.mem_univ τ)]
        rfl
    · rintro ⟨w, hw, rfl⟩
      have hlat : ∀ z, latW g (latW f z) = 0 := by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => simp only [map_zero]
        | tmul w x =>
          have h0 : ((g.f.restrictScalars O).restrict g.T_le) (((f.f.restrictScalars O).restrict f.T_le) x) = 0 :=
            Subtype.ext ((hS.2.2.2.1 (f.f x)).2 ⟨x, rfl⟩)
          simp only [latW, TensorProduct.map_tmul, LinearMap.id_apply, h0, TensorProduct.tmul_zero]
        | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]
      have hW : ∀ x, homW t ϖ H (homW t ϖ F x) = 0 := fun x =>
        I₂.j.injective (by rw [hH, hF, hlat, map_zero])
      have hM : (Ht * Ft).map φ = 0 := by
        ext i j
        have := congrFun (hW (Pi.single j 1)) i
        rw [homW_apply, homW_apply, Matrix.mulVec_mulVec] at this
        simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.zero_apply] at this
        rw [Matrix.map_mul]
        exact this
      have hz : Ht * Ft = 0 := Matrix.map_injective hφ (hM.trans (Matrix.map_zero _ (map_zero φ)).symm)
      have hHF : ∀ τ, H.mat τ * F.mat τ = 0 := fun τ => by
        have := congrArg (fun M => M.map (ψ τ)) hz
        simp only [Matrix.map_mul, Matrix.map_zero _ (map_zero (ψ τ))] at this
        exact this
      change H.app (F.app w) = 0
      funext τ
      rw [Hom.app_apply, Hom.app_apply, Matrix.mulVec_mulVec, hHF τ, Matrix.zero_mulVec]
      rfl
  · exact (GlobalTheory.T.finiteLength_coker_of_surjective_mod_uniformizer O K l e a κ μ P₁ P₂ H).1 fun τ => ⟨YH τ, cH τ, hYH τ, hkH τ, hHY τ⟩

theorem isExactTriple_of_isSESLat : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (κ : Type) [Fintype κ] [DecidableEq κ] (μ : Type) [Fintype μ] [DecidableEq μ] (P₀ : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (P₁ : PhiMod ↥(OL LL) ↥LL.1 l e a κ) (P₂ : PhiMod ↥(OL LL) ↥LL.1 l e a μ) (T₀ T₁ T₂ : QLat LL) (I₀ : Ident (thetaW a LL) ϖ P₀ T₀) (I₁ : Ident (thetaW a LL) ϖ P₁ T₁) (I₂ : Ident (thetaW a LL) ϖ P₂ T₂) (f : LatHom T₀.L T₁.L) (g : LatHom T₁.L T₂.L) (F : GlobalTheory.BK.Hom P₀ P₁) (G : GlobalTheory.BK.Hom P₁ P₂), IsSESLat (Qp := ℚ_[l]) f g → IsMapOf I₀ I₁ f F → IsMapOf I₁ I₂ g G → IsExactTriple F G := by
  intro l _ a e _ _ ϖ LL _ _ ι _ _ κ _ _ μ _ _ P₀ P₁ P₂ T₀ T₁ T₂ I₀ I₁ I₂ f g F G hS hF hG
  exact isExactTriple_of_isSESLat_gen (thetaW a LL) ϖ hS hF hG

end GlobalTheory.BKExact
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal

noncomputable section

namespace GlobalTheory.BKGal.HatVal.BasisCoord

variable {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K]
  {G : Type} [Group G] [TopologicalSpace G]

theorem tWincl_smul' {R R' : Type} [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R'] (f : R →ₐ[O] R')
    (T : LocLat G ℚ_[l] K O) (r : R) (z : TW R T) : TWincl f T (r • z) = f r • TWincl f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul s x =>
    simp only [TWincl, smul_tmul', TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply,
      smul_eq_mul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

end GlobalTheory.BKGal.HatVal.BasisCoord


open GlobalTheory.BKGal.HatVal.BasisCoord in
theorem GlobalTheory.BKGal.HatVal.coord_E_pow_basis : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T) (ε δ : OCb l), IsEps ε → δ ^ l = ε → ∀ j : ι, ∃ c : ι → OA l O, inclL t ϖ D.toPhiMod c = inclO l O (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H) • (Pi.single j 1 : ι → OW l O) ∧ ∃ z : TW (OA l O) T, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf δ ^ η)) • R.jB (fun i => toB l O (c i)) = TWincl (toB l O) T (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H • z) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R ε δ hε hδ j

  let ej : Vec K a ι := fun _ => Pi.single j 1
  have hej : ej ∈ D.toPhiMod.M := mem_tot.2 fun τ i => by
    by_cases h : i = j
    · subst h; simp only [ej, Pi.single_eq_same]; exact one_mem _
    · simp only [ej, Pi.single_eq_of_ne h]; exact zero_mem _
  have hL : E K l e ^ H • ej ∈ D.toPhiMod.L := D.lower _ hej
  obtain ⟨c, hc⟩ := toW_mem_LA t ϖ D.toPhiMod hL

  have hw : toW t ϖ D.toPhiMod ⟨ej, mem_ME_of_mem_M hej⟩ = (Pi.single j 1 : ι → OW l O) := by
    ext1 i
    rw [toW_apply]
    by_cases h : i = j
    · subst h
      rw [Pi.single_eq_same]
      convert map_one (ϖ.iW t K) using 1
      exact congrArg _ (funext fun τ => Subtype.ext (by simp [ej]))
    · rw [Pi.single_eq_of_ne h]
      convert map_zero (ϖ.iW t K) using 1
      exact congrArg _ (funext fun τ => Subtype.ext (by simp [ej, Pi.single_eq_of_ne h]))

  have hE : ϖ.iW t K (fun _ => ⟨E K l e ^ H, le_away _ _ (pow_mem (E_mem l e _) H)⟩) =
      inclO l O (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H) := by
    have h1 := ϖ.iW_of_mem t K (fun _ => EIn l e (A O K) ^ H)
    have h2 : ϖ.iTot t K (fun _ => EIn l e (A O K) ^ H) = ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H := by
      rw [show (fun _ : ZMod a => EIn l e (A O K) ^ H) = (fun _ => EIn l e (A O K)) ^ H from rfl, map_pow,
        PiSys.iTot_E t K ϖ]
    rw [h2] at h1
    rw [← h1]
    exact congrArg _ (funext fun τ => Subtype.ext (by simp [EIn]))
  have hwE : toW t ϖ D.toPhiMod ⟨E K l e ^ H • ej, mem_ME_of_mem_L hL⟩ =
      inclO l O (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H) • (Pi.single j 1 : ι → OW l O) := by
    rw [toW_smul t ϖ D.toPhiMod (fun _ => ⟨E K l e ^ H, le_away _ _ (pow_mem (E_mem l e _) H)⟩)
      ⟨ej, mem_ME_of_mem_M hej⟩ _ (fun τ => rfl), hE, hw]
  have h1 : inclL t ϖ D.toPhiMod c =
      inclO l O (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H) • (Pi.single j 1 : ι → OW l O) :=
    hc.trans hwE
  refine ⟨c, h1, ?_⟩

  obtain ⟨-, hK2, -, -⟩ := GlobalTheory.T.breuilKisin_lattice_exponents_ainf_comparison l a e O K t ϖ ι D.toPhiMod T R.I η H D.upper D.lower ε δ hε hδ
  have hv : (Pi.single j 1 : ι → OW l O) ∈ MA D.toPhiMod :=
    ⟨Pi.single j 1, funext fun i => by
      by_cases h : i = j
      · subst h; simp [inclV]
      · simp [inclV, Pi.single_eq_of_ne h]⟩
  obtain ⟨z, hz⟩ := hK2 _ hv
  refine ⟨z, ?_⟩
  set m : OA l O := (1 : O) ⊗ₜ[ℤ_[l]] (muOf δ ^ η) with hm
  set Eh : OA l O := ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H with hEh
  have hB := R.cmp (fun i => m * c i) (Eh • z) (by
    rw [inclL_smul_coord, h1, smul_comm, map_smul, hz, tWincl_smul'])
  have e1 : (fun i => toB l O (m * c i)) = toB l O m • fun i => toB l O (c i) :=
    funext fun i => by simp only [map_mul, Pi.smul_apply, smul_eq_mul]
  rw [e1, map_smul] at hB
  exact hB
end
end
