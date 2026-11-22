import Development.AbelianVarietyTheory.Definitions.Degenerations.LabKerUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecEqOfSecConst
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ZH
open ReciprocityTheory.ChartRestriction.G.Out Classical
namespace DimZero
open Inh

alias res_one := RealModel.res_one
alias pullU_one := RealModel.pullU_one
alias res_res := RealModel.res_res

def oneG {X Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
    LB.Gen (LB.LinComb (trivLB X) φ ε) := ⟨fun _ => 1⟩

theorem oneG_gen {X Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
    (oneG φ ε).IsGen := by
  intro i j; rw [linComb_triv_g, _root_.one_mul]; exact (res_one _).trans (res_one _).symm

def oneS {X Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
    LB.Sec (LB.LinComb (trivLB X) φ ε) := ⟨fun _ => 1, by
  intro i j; rw [linComb_triv_g, Units.val_one, _root_.one_mul]; exact (map_one _).trans (map_one _).symm⟩

alias wchart_triv := RealModel.wchart_triv
alias corr_of_one := RealModel.corr_of_one
alias isoOne := RealModel.isoOne

variable (B : Scheme.{0})

alias hypS_zero := RealModel.hypS_zero
alias liftFun_bij := RealModel.liftFun_bij
alias translT_id := RealModel.translT_id
alias corr_comm := RealModel.corr_comm
alias weil_zero := RealModel.weil_zero

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

def sys0 (ζ : o) (hζ : IsPrimitiveRoot ζ ((3 * 81) ^ 2)) (hu : IsUnit ((3 * 81 : ℕ) : o)) (R : Subalgebra o Ω)
    (fg : R.FG) (frac : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) : ThetaSys o Ω :=
  RealModel.sys0 ζ hζ hu R fg frac

alias fn_one := RealModel.fn_one
alias liftFun_one := RealModel.liftFun_one

theorem basis_zero (T : Over B) (k : ℤ) (J : Type) [Fintype J] [Unique J] (σ : LB.Sec (LPow (zeroPolAV B).A (zeroPolAV B).L k T)) :
    ∃! c : J → Γ(T.left, ⊤), ∀ j, σ.f j = ∑ i, liftFun (zeroPolAV B).A _ (c i) *
      (oneS _ _ : LB.Sec (LPow (zeroPolAV B).A (zeroPolAV B).L k T)).f j := by
  let d : (LPow (zeroPolAV B).A (zeroPolAV B).L k T).ι := fun _ => PUnit.unit
  have hb := liftFun_bij B T ((LPow (zeroPolAV B).A (zeroPolAV B).L k T).U d) (wchart_triv _ _)
  obtain ⟨c, hc⟩ := hb.2 (σ.f d)
  refine ⟨fun _ => c, fun j => ?_, fun c' h' => ?_⟩
  · rw [Fintype.sum_unique]; exact hc.symm.trans (_root_.mul_one _).symm
  · funext i
    have := h' d
    rw [Fintype.sum_unique] at this
    rw [Subsingleton.elim i default]
    exact hb.1 (((_root_.mul_one _).symm.trans this.symm).trans hc.symm)

theorem value_one (k : ℤ) {T : Over B} (z : T ⟶ (zeroPolAV B).A)
    (τ : LB.Gen (LB.LinComb (zeroPolAV B).L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => k))) (hτ : ∀ j, τ.s j = 1) :
    IsValueAt (zeroPolAV B).A (zeroPolAV B).L k (oneS _ _) z τ 1 := by
  intro j
  refine ((congrArg _ (map_one _)).trans (map_one _)).trans ?_
  rw [map_one, _root_.one_mul]
  exact (congrArg Units.val (hτ j)).symm

alias mul_s_one := RealModel.mul_s_one
alias pull_s_one := RealModel.pull_s_one
alias inv_s_one := RealModel.inv_s_one

theorem rigT_one (T : Over B) (k : ℤ) (j) : (rigT (zeroPolAV B).A (zeroPolAV B).L (oneG _ _) T k).s j = 1 :=
  (congrArg (· ^ k) ((congrArg _ (pullU_one _ _)).trans (res_one _))).trans (one_zpow _)

theorem tors_zero (n : ℕ) {T : Over B} (x : T ⟶ (zeroPolAV B).A) :
    IsTorsFrame (zeroPolAV B) (oneG _ _) n x (oneG _ _) := by
  refine ⟨toUnit_unique _ _, oneG_gen _ _, oneG _ _, oneG_gen _ _, ?_, ?_⟩
  · exact corr_of_one _ _ _ _ _ _ _ (pull_s_one _ _ _ _ _ fun _ => rfl)
      (mul_s_one _ _ _ _ _ _ _ (fun _ => one_zpow _) (inv_s_one _ _ _ _ fun _ => rfl))
  · exact corr_of_one _ _ _ _ _ _ _ (fun _ => one_zpow _)
      (mul_s_one _ _ _ _ _ _ _ (pull_s_one _ _ _ _ _ fun _ => rfl) (rigT_one B _ _))

theorem symLift_zero (k : ℤ) (n : ℕ) {T : Over B} (x : T ⟶ (zeroPolAV B).A) :
    SymLift (zeroPolAV B).A (zeroPolAV B).L k n x ⟨x, oneG _ _, oneG_gen _ _⟩ := by
  refine ⟨rfl, corr_of_one _ _ _ _ _ _ _ (fun j => ?_) (fun _ => rfl), oneG _ _, oneG_gen _ _,
    corr_of_one _ _ _ _ _ _ _ ?_ (fun _ => rfl)⟩
  · show (∏ j₀ : Fin n, (_ : Γ((T ⊗ (zeroPolAV B).A).left, LB.wchart (zeroPolAV B).L (powφ (zeroPolAV B).A x n) j)ˣ)) = 1
    refine Finset.prod_eq_one fun j₀ _ => ?_
    exact (congrArg _ ((congrArg _ (pullU_one _ _)).trans (res_one _))).trans (res_one _)
  · exact mul_s_one _ _ _ _ _ _ _ (mul_s_one _ _ _ _ _ _ _ (pull_s_one _ _ _ _ _ fun _ => rfl) fun _ => rfl)
      (mul_s_one _ _ _ _ _ _ _ (pull_s_one _ _ _ _ _ fun _ => rfl)
        (inv_s_one _ _ _ _ (pull_s_one _ _ _ _ _ fun _ => rfl)))

theorem twist_one {T : Over B} (ψ : T ⊗ (zeroPolAV B).A ⟶ T ⊗ (zeroPolAV B).A) (m) (hm : ψ ≫ snd T _ = m) (a b : ℤ) :
    IsTwistPull (zeroPolAV B).A (zeroPolAV B).L ψ m hm a b (oneG _ _) (oneS _ _) (oneS _ _) := by
  intro j
  refine (map_one _).trans ?_
  exact ((congrArg₂ (· * ·) rfl ((congrArg _ (map_one _)).trans (map_one _))).trans (_root_.one_mul _)).symm

theorem act_one {T : Over B} (x : T ⟶ (zeroPolAV B).A) (k : ℤ) (σ : LB.Sec (LPow (zeroPolAV B).A (zeroPolAV B).L k T))
    (h : IsActOf (zeroPolAV B).A (zeroPolAV B).L k ⟨x, oneG _ _, oneG_gen _ _⟩ (oneS _ _) σ) (j) : σ.f j = 1 := by
  have h1 := (h (fun _ => PUnit.unit)).trans
    ((congrArg₂ (· * ·) rfl ((congrArg _ (map_one _)).trans (map_one _))).trans (_root_.one_mul _))
  have key : ∀ (Y : Scheme.{0}) (U V : Y.Opens) (hle : V ≤ U) (_ : U = ⊤) (_ : V = ⊤) (f : Γ(Y, U)),
      (Y.presheaf.map (homOfLE hle).op).hom f = 1 → f = 1 := by
    intro Y U V hle hU hV f hf
    subst hU hV
    have : (homOfLE hle).op = 𝟙 _ := rfl
    rw [this, CategoryTheory.Functor.map_id] at hf
    exact hf
  exact key _ _ _ _ (wchart_triv _ _) (wchart_triv _ _) _ h1

def real0 (ζ : o) (hζ : IsPrimitiveRoot ζ ((3 * 81) ^ 2)) (hu : IsUnit ((3 * 81 : ℕ) : o)) (R : Subalgebra o Ω)
    (fg : R.FG) (frac : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) : (sys0 ζ hζ hu R fg frac).Real :=
  RealModel.real0 ζ hζ hu R fg frac

section Padic
variable (p : ℕ) [Fact p.Prime]

def fracToCl : FractionRing ℤ_[p] →+* PadicAlgCl p :=
  (algebraMap ℚ_[p] (PadicAlgCl p)).comp (FractionRing.algEquiv ℤ_[p] ℚ_[p]).toRingEquiv.toRingHom

theorem norm_fracToCl_le (x : FractionRing ℤ_[p]) :
    ‖fracToCl p x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap ℤ_[p] (FractionRing ℤ_[p])) := by
  have h : ‖fracToCl p x‖ = ‖FractionRing.algEquiv ℤ_[p] ℚ_[p] x‖ := PadicAlgCl.norm_extends _ _
  rw [h]
  constructor
  · intro hx
    refine ⟨⟨_, hx⟩, (FractionRing.algEquiv ℤ_[p] ℚ_[p]).injective ?_⟩
    exact AlgEquiv.commutes _ _
  · rintro ⟨a, rfl⟩
    rw [AlgEquiv.commutes]; exact a.2

end Padic

section Tests
variable (ζ : o) (hζ : IsPrimitiveRoot ζ ((3 * 81) ^ 2)) (hu : IsUnit ((3 * 81 : ℕ) : o)) (R : Subalgebra o Ω)
  (fg : R.FG) (frac : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) (p : ℕ) [Fact p.Prime]
  (yK : R →+* FractionRing ℤ_[p])

def utest0 : (real0 ζ hζ hu R fg frac).UTest p ((fracToCl p).comp yK) where
  V := ℤ_[p]
  complete := inferInstance
  alg := (fracToCl p).toAlgebra
  norm_le := norm_fracToCl_le p
  yK := yK
  fac := rfl
  A := zeroPolAV _
  φ := spMap yK
  cart := ⟨@IsPullback.of_vert_isIso _ _ _ _ _ _ _ _ _ _ (inferInstanceAs (IsIso (𝟙 _))) (inferInstanceAs (IsIso (𝟙 _)))
      ⟨(Category.comp_id _).trans (Category.id_comp _).symm⟩, fun T x y x₀ y₀ _ _ => by
    have h1 := Over.w (x₀ * y₀)
    have h2 := Over.w (x * y)
    exact ((Category.comp_id _).symm.trans h1).trans
      (congrArg (· ≫ spMap yK) (h2.symm.trans (Category.comp_id _)))⟩
  lb := isoOne _ _ (fun _ _ => rfl) (fun _ _ => linComb_triv_g _ _ _ _)
  G := 𝟙_ _
  comm := (zeroPolAV _).isAb.comm
  semi := GlobalTheory.isSemiAbelian_of_isAbelianScheme _ (zeroPolAV _).isAb
  D := UnifZero.zeroData _ _
  U := ⟨UnifZero.zeroPre _ _, fun k _ => UnifZero.expBij k⟩

def labOfZero {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p}
    (u : ρ.UTest p y₀) (hg : IsEmpty (Fin S.g)) (hX : Subsingleton u.D.toPre.X) (hψ : ∀ χ, u.PsiNorm χ 1)
    (hI : ∀ a, u.Integral a) : u.Lab where
  q := 0
  pos := by
    rw [Filter.cofinite_eq_bot]; exact Filter.tendsto_bot
  q_eq := fun χ => by simpa using hψ χ
  yy := 0
  yy_onto := fun x => ⟨0, by
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [Subsingleton.elim y 0]; rfl⟩
  yy_eq := fun _ pk _ _ _ => by rw [Subsingleton.elim pk.y 0]; rfl
  ker_iff := fun a => ⟨fun _ => hI a, fun _ => rfl⟩
  isoFree := by
    refine ⟨fun a _ h _ => Finset.sum_eq_zero fun i _ => hg.elim i, 0, ?_⟩
    have key : ∀ T : AddSubgroup S.Gam, Nonempty (T ≃+ (Fin 0 → ZMod (S.r * S.N))) := fun T => by
      haveI : Unique T := uniqueOfSubsingleton 0
      exact ⟨AddEquiv.ofUnique⟩
    exact key _
  wt := 0
  wt_eq := fun x α _ t => by
    have h0 : eStd S.g _ t.1 x = 0 := Finset.sum_eq_zero fun i _ => hg.elim i
    rw [h0, map_zero]; rfl

theorem valF_one {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (hU : U = ⊤) (f : Γ(X, U))
    (hf : f = 1) : valF x U f = 1 := by
  subst hU hf
  rw [valF, dif_pos (by simp), map_one, map_one]

theorem psiNorm_utest0 (χ) : (utest0 ζ hζ hu R fg frac p yK).PsiNorm χ 1 := by
  intro j _
  refine (congrArg (fun z => ‖fracToCl p z‖) (valF_one _ _ (wchart_triv _ _) _ ?_)).trans (by simp)
  exact congrArg Units.val
    (((ToricData.psi_isConst (K := ℤ_[p]) (X := PUnit) (fun _ => 1) χ).of_eq ToricData.unitOn_one j).trans
      (UnifZero.gv_one _))

theorem integral_utest0 (a) : (utest0 ζ hζ hu R fg frac p yK).Integral a := by
  refine ⟨𝟙 _, pullback.lift (jK ℤ_[p]) (𝟙 _) ((Category.comp_id _).trans (Category.id_comp _).symm),
    Category.comp_id _, (pullback.lift_fst _ _ _).trans (Category.comp_id _).symm, pullback.lift_snd _ _ _, ?_⟩
  have h1 : (utest0 ζ hζ hu R fg frac p yK).U.gen.hom.left = pullback.snd (𝟙 (Sp ℤ_[p])) (jK ℤ_[p]) :=
    (Category.comp_id _).symm.trans (Over.w (utest0 ζ hζ hu R fg frac p yK).U.gen.hom)
  have h2 : ((real0 ζ hζ hu R fg frac).pt a).left = 𝟙 _ :=
    (Category.comp_id _).symm.trans (Over.w ((real0 ζ hζ hu R fg frac).pt a))
  rw [h1, h2]
  exact ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ spMap yK) (pullback.lift_snd _ _ _)).trans
    (Category.id_comp _))).trans (Category.comp_id _).symm

def lab0 : (utest0 ζ hζ hu R fg frac p yK).Lab :=
  labOfZero _ (inferInstanceAs (IsEmpty (Fin 0))) (inferInstanceAs (Subsingleton PUnit))
    (psiNorm_utest0 ζ hζ hu R fg frac p yK) (integral_utest0 ζ hζ hu R fg frac p yK)
end Tests

section Arith
open NumberField

abbrev intAway (K : Type) [Field K] [NumberField K] : Subalgebra (𝓞 K) K :=
  Localization.subalgebra.ofField K (Submonoid.powers (3 : 𝓞 K))
    (powers_le_nonZeroDivisors_of_noZeroDivisors (by norm_num))

theorem arithBase_intAway (K : Type) [Field K] [NumberField K] : ArithBase (intAway K) K where
  ded := IsLocalization.isDedekindDomain (𝓞 K) (M := Submonoid.powers (3 : 𝓞 K))
    (powers_le_nonZeroDivisors_of_noZeroDivisors (by norm_num)) _
  ft := by
    haveI : Algebra.FinitePresentation (𝓞 K) (intAway K) := IsLocalization.Away.finitePresentation (3 : 𝓞 K)
    exact Algebra.FiniteType.trans (S := 𝓞 K) inferInstance inferInstance
  char := inferInstance
  inj := Subtype.val_injective

theorem isUnit_three_intAway (K : Type) [Field K] [NumberField K] : IsUnit (3 : intAway K) := by
  have := IsLocalization.Away.algebraMap_isUnit (S := intAway K) (3 : 𝓞 K)
  rwa [map_ofNat] at this

end Arith

example {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (ζ : o) (hζ) (hu) (R : Subalgebra o Ω) (fg) (frac)
    (p : ℕ) [Fact p.Prime] (y₀ : R →+* PadicAlgCl p) : (sys0 ζ hζ hu R fg frac).delta y₀ = 1 := by
  have : ∀ x, ‖y₀ ⟨(sys0 ζ hζ hu R fg frac).th x, (sys0 ζ hζ hu R fg frac).th_mem x⟩‖ = 1 := fun x =>
    (congrArg _ (map_one y₀)).trans norm_one
  exact (iSup_congr this).trans ciSup_const

example {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (hg : S.g = 1) (hN : S.N = 81)
    (hr : S.r = 243) : S.Big := by
  have h1 : (2 : ℝ) ^ ((1 : ℝ) / 2) ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have h2 : (2 : ℝ) ^ ((1 : ℝ) / 2 - 1) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  rw [Real.rpow_one] at h1
  simp only [ThetaSys.Big, hg, hN, hr]
  push_cast
  refine ⟨by linarith, by simp only [Nat.factorial_one, Nat.cast_one]; linarith, by norm_num⟩

example {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (hg : S.g = 1) (hN : S.N = 81)
    (hr : S.r = 81) : ¬ S.Big := by
  have h2 : (2 : ℝ) ^ (-1 : ℝ) ≤ (2 : ℝ) ^ ((1 : ℝ) / 2 - 1) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  rw [Real.rpow_neg_one] at h2
  simp only [ThetaSys.Big, hg, hN, hr]
  push_cast
  rintro ⟨-, h, -⟩
  simp only [Nat.factorial_one, Nat.cast_one] at h
  linarith

end DimZero
end GlobalTheory.ZH
end
