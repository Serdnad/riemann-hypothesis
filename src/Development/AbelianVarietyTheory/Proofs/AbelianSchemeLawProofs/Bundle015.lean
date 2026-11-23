module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal

@[expose] public section

section

noncomputable section

namespace GlobalTheory.AbLaw.Cube

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem corr_of_val_section {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {Y : Over S}
    (hY : Function.Surjective Y.hom.appTop.hom) (e : 𝟙_ (Over S) ⟶ Y) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y.left ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y.left ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ' ε' φ ε)
    {u : LB.Gen (LB.LinComb L φ ε)} {u' : LB.Gen (LB.LinComb L φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen)
    (h : ∀ y J, Good L y J → val u e.left y J = val u' e.left y J) : LB.Gen.Corr L φ ε φ' ε' u u' :=
  corr_of_val hL fun y J hJ => gen_unique' hL hF Y.hom e.left (Over.w e) hY hu hu' h _ _ y J hJ

theorem surj_tensor (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {T : Over S}
    (hT : Function.Surjective T.hom.appTop.hom) : Function.Surjective (A ⊗ T).hom.appTop.hom := by
  rw [← Over.w (snd A T)]
  exact surj_comp (surj_snd hG hA T) hT

variable [IsCommMonObj A] {L : LB A.left}

omit [IsCommMonObj A] in
theorem prod_theta {U : Type} [CommGroup U] (h : ((G3 A).left ⟶ A.left) → U) :
    ∏ I : thK.{0}, h (thφ A (x3 A) I) ^ thε I =
      ∏ I : thK.{0}, h ((lift (x3 A 0) (lift (x3 A 1) (x3 A 2))).left ≫ thφ A (x3 A) I) ^ thε I := by
  have e : lift (x3 A 0) (lift (x3 A 1) (x3 A 2)) = 𝟙 (G3 A) := by ext <;> simp [x3]
  rw [e]
  exact Finset.prod_congr rfl fun I _ => congrArg (fun q => h q ^ thε I) (Category.id_comp _).symm

omit [GrpObj A] [IsCommMonObj A] in
theorem oneGen_isGen {Y : Scheme.{0}} : (LB.oneGen L (Y := Y)).IsGen :=
  fun _ _ => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm

def IsNormalised (t : LB.Gen (Theta A L)) : Prop :=
  ∀ (y : (𝟙_ (Over S)).left) J, Good L y J →
    val (L := L) (φ := thφ A (x3 A)) (ε := thε) t (lift (1 : 𝟙_ (Over S) ⟶ A) (lift 1 1)).left y J = 1

theorem exists_normalised (hL : L.IsLB) (t : LB.Gen (Theta A L)) (ht : t.IsGen) :
    ∃ t' : LB.Gen (Theta A L), t'.IsGen ∧ IsNormalised t' := by
  obtain ⟨t', ht', hv⟩ := exists_gen hL (φ' := thφ A (x3 A)) (ε' := thε) (fun V _ k => by
      refine Eq.trans (DVR.prod_sum₂ (K := thK) (K' := thK) (U := V) _
          (c := ∏ i, k (thφ A (x3 A) i) ^ thε i) rfl
          (DVR.prod_neg _ _ (prod_cub (1 : G3 A ⟶ A) 1 1 k))) ?_
      simp)
    (LB.mulGen L (thφ A (x3 A)) thε _ _ t (LB.invGen L _ _
      (LB.pullGen L (thφ A (x3 A)) thε t (lift (1 : G3 A ⟶ A) (lift 1 1)).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
  refine ⟨t', ht', fun y J hJ => ?_⟩
  refine (hv _ _ y J hJ).trans ((val_mul hJ _ _ _).trans ((congrArg _ (val_inv _ _)).trans
    (mul_inv_eq_one.2 (Eq.symm ((val_pull hJ _ _ _).trans ?_)))))
  rw [← Over.comp_left, comp_lift, comp_lift, MonObj.comp_one]
  rfl

theorem IsNormalised.pull {t : LB.Gen (Theta A L)} (ht : IsNormalised t) {T : Over S} (e : 𝟙_ (Over S) ⟶ T)
    {a b c : T ⟶ A} (ha : e ≫ a = 1) (hb : e ≫ b = 1) (hc : e ≫ c = 1) {y J} (hJ : Good L y J) :
    val (LB.pullGen L (thφ A (x3 A)) thε t (lift a (lift b c)).left) e.left y J = 1 := by
  refine (val_pull hJ _ _ _).trans ?_
  rw [← Over.comp_left, comp_lift, comp_lift, ha, hb, hc]
  exact ht y J hJ

def cubicalOfNormalised (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (M : RigLB A) (t : LB.Gen (Theta A M.L))
    (ht : t.IsGen) (hn : IsNormalised t) : CubicalStr A M :=
  have s₁ := (hG _ _ hA).2
  have s₂ := surj_tensor hG hA s₁
  have s₃ := surj_tensor hG hA s₂
  have s₄ := surj_tensor hG hA s₃
  { t := t
    isGen := ht
    face := fun i => by
      have key : ∀ a b c : G2 A ⟶ A, lift 1 1 ≫ a = (1 : 𝟙_ (Over S) ⟶ A) → lift 1 1 ≫ b = (1 : 𝟙_ (Over S) ⟶ A) →
          lift 1 1 ≫ c = (1 : 𝟙_ (Over S) ⟶ A) → a = 1 ∨ b = 1 ∨ c = 1 →
          LB.Gen.Corr M.L _ _ (Y := (G2 A).left) _ _
            (LB.pullGen M.L (thφ A (x3 A)) thε t (lift a (lift b c)).left) (LB.oneGen M.L) := by
        intro a b c ha hb hc h
        refine corr_of_val_section M.isLB s₂ (lift 1 1) (fun V _ k => ?_) (DVR.pullGen_isGen _ _ _ _ ht _) oneGen_isGen
          (fun y J hJ => (hn.pull _ ha hb hc hJ).trans (val_one _).symm)
        refine (Fintype.prod_empty _).trans (Eq.trans ?_ (prod_cub a b c k).symm)
        apply Additive.ofMul.injective
        rcases h with rfl | rfl | rfl <;> simp only [_root_.mul_one, _root_.one_mul, ofMul_mul, ofMul_inv, ofMul_one] <;> abel
      fin_cases i
      · exact key 1 (x2 A 0) (x2 A 1) (MonObj.comp_one _) (by simp [x2]) (by simp [x2]) (.inl rfl)
      · exact key (x2 A 0) 1 (x2 A 1) (by simp [x2]) (MonObj.comp_one _) (by simp [x2]) (.inr (.inl rfl))
      · exact key (x2 A 0) (x2 A 1) 1 (by simp [x2]) (by simp [x2]) (MonObj.comp_one _) (.inr (.inr rfl))
    cubeSymmetric_swap_first := by
      refine corr_of_val_section M.isLB s₃ (lift 1 (lift 1 1)) (φ := thφ A (x3 A)) (ε := thε) (fun V _ k => ?_) ht
        (DVR.pullGen_isGen _ _ _ _ ht _) (fun y J hJ => (hn y J hJ).trans
          (hn.pull _ (by simp [x3]) (by simp [x3]) (by simp [x3]) hJ).symm)
      refine (prod_cub _ _ _ k).trans (Eq.trans ?_ ((prod_theta k).trans (prod_cub _ _ _ k)).symm)
      rw [_root_.mul_comm (x3 A 1) (x3 A 0)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    cubeSymmetric_swap_last := by
      refine corr_of_val_section M.isLB s₃ (lift 1 (lift 1 1)) (φ := thφ A (x3 A)) (ε := thε) (fun V _ k => ?_) ht
        (DVR.pullGen_isGen _ _ _ _ ht _) (fun y J hJ => (hn y J hJ).trans
          (hn.pull _ (by simp [x3]) (by simp [x3]) (by simp [x3]) hJ).symm)
      refine (prod_cub _ _ _ k).trans (Eq.trans ?_ ((prod_theta k).trans (prod_cub _ _ _ k)).symm)
      rw [_root_.mul_comm (x3 A 2) (x3 A 1), mul_right_comm (x3 A 0) (x3 A 2)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    cocycle := by
      let e : 𝟙_ (Over S) ⟶ G4 A := lift 1 (lift 1 (lift 1 1))
      have e₀ : e ≫ x4 A 0 = 1 := by simp [e, x4]
      have e₁ : e ≫ x4 A 1 = 1 := by simp [e, x4]
      have e₂ : e ≫ x4 A 2 = 1 := by simp [e, x4]
      have e₃ : e ≫ x4 A 3 = 1 := by simp [e, x4]
      have f₀ : e ≫ padd A (x4 A 0) (x4 A 1) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [e₀, e₁, _root_.mul_one])
      have f₁ : e ≫ padd A (x4 A 1) (x4 A 2) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [e₁, e₂, _root_.mul_one])
      refine corr_of_val_section M.isLB s₄ e (fun V _ k => ?_)
        (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _) (DVR.pullGen_isGen _ _ _ _ ht _))
        (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _) (DVR.pullGen_isGen _ _ _ _ ht _))
        (fun y J hJ => ((val_mul hJ _ _ _).trans
          (congrArg₂ (· * ·) (hn.pull e f₀ e₂ e₃ hJ) (hn.pull e e₀ e₁ e₃ hJ))).trans ((val_mul hJ _ _ _).trans
          (congrArg₂ (· * ·) (hn.pull e e₀ f₁ e₃ hJ) (hn.pull e e₁ e₂ e₃ hJ))).symm)
      refine (DVR.prod_sum₂ (K := thK) (K' := thK) (U := V) _ (prod_cub (x4 A 0) (x4 A 1 * x4 A 2) (x4 A 3) k)
        (prod_cub (x4 A 1) (x4 A 2) (x4 A 3) k)).trans (Eq.trans ?_
        (DVR.prod_sum₂ (K := thK) (K' := thK) (U := V) _ (prod_cub (x4 A 0 * x4 A 1) (x4 A 2) (x4 A 3) k)
        (prod_cub (x4 A 0) (x4 A 1) (x4 A 3) k)).symm)
      apply Additive.ofMul.injective
      simp only [_root_.mul_assoc (x4 A 0), ofMul_mul, ofMul_inv]
      abel }

theorem cubical_unique (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {M : RigLB A} (c c' : CubicalStr A M) :
    LB.Gen.Corr M.L _ _ _ _ c.t c'.t :=
  corr_of_val_section M.isLB (surj_tensor hG hA (surj_tensor hG hA (hG _ _ hA).2)) (lift 1 (lift 1 1))
    (φ := thφ A (x3 A)) (ε := thε) (φ' := thφ A (x3 A)) (ε' := thε) (fun _ _ _ => rfl) c.isGen c'.isGen
    fun _ _ hJ => ((isCub_cubV c hJ).face 1 1).trans ((isCub_cubV c' hJ).face 1 1).symm

theorem cube_of_gen : GlobalFnsSt → (∀ (S : Scheme.{0}) (P : PolAV S) (M : LB P.A.left), M.IsLB →
    ∃ t : LB.Gen (Theta P.A M), t.IsGen) → CubeSt := by
  intro hG hT S _ P M _
  have := P.isAb.comm
  obtain ⟨t, ht⟩ := hT S P M.L M.isLB
  obtain ⟨t', ht', hn⟩ := exists_normalised M.isLB t ht
  exact ⟨⟨cubicalOfNormalised hG P.isAb M t' ht' hn⟩, cubical_unique hG P.isAb⟩

end GlobalTheory.AbLaw.Cube
end
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_gen_of_local_on_base {X Y S : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (p : Y ⟶ S) (e : S ⟶ Y) (he : e ≫ p = 𝟙 S)
    (hp : ∀ V : S.Opens, Function.Surjective (pullback.snd p V.ι).appTop.hom)
    (h0 : ∀ (U : Type) [CommGroup U] (h : (S ⟶ X) → U), ∏ k, h (e ≫ φ k) ^ ε k = 1)
    (h : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
      ∃ t : LB.Gen (LB.LinComb L (fun k => (p ⁻¹ᵁ U).ι ≫ φ k) ε), t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L φ ε), u.IsGen := by
  have loc : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ ∃ t : LB.Gen (LB.LinComb L (fun i => (p ⁻¹ᵁ U).ι ≫ φ i) ε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (p ⁻¹ᵁ U).toScheme) (b : Z ⟶ S) (z : Z) (J), Good L z J →
        r ≫ (p ⁻¹ᵁ U).ι = b ≫ e → val t r z J = 1 := by
    intro s
    obtain ⟨U, hs, t, ht⟩ := h s
    obtain ⟨n, n₁⟩ : ∃ n : (p ⁻¹ᵁ U).toScheme ⟶ (p ⁻¹ᵁ U).toScheme,
        n ≫ (p ⁻¹ᵁ U).ι = (p ⁻¹ᵁ U).ι ≫ p ≫ e :=
      ⟨IsOpenImmersion.lift (p ⁻¹ᵁ U).ι ((p ⁻¹ᵁ U).ι ≫ p ≫ e) (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        have e' := congrArg (fun q => q (p y.1)) he
        exact (congrArg (· ∈ U) e').mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩
    obtain ⟨t', ht', hv⟩ := exists_gen hL (φ' := fun i => (p ⁻¹ᵁ U).ι ≫ φ i) (ε' := ε)
      (fun V _ k => by
        have q := h0 V (fun χ => k ((p ⁻¹ᵁ U).ι ≫ p ≫ χ))
        refine Eq.trans (DVR.prod_sum₂ (K := K) (K' := K) (U := V) _
          (c := ∏ i, k ((p ⁻¹ᵁ U).ι ≫ φ i) ^ ε i) rfl
          (DVR.prod_neg _ _ ((Finset.prod_congr rfl fun i _ => by
            show k (n ≫ _ ≫ _) ^ _ = _
            rw [← Category.assoc n, n₁]; simp only [Category.assoc]).trans q))) ?_
        simp)
      (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ (LB.pullGen L _ _ t n)))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht n)))
    refine ⟨U, hs, t', ht', fun Z r b z J hJ hr => ?_⟩
    have : r ≫ n = r := by
      rw [← cancel_mono (p ⁻¹ᵁ U).ι, Category.assoc, n₁, ← Category.assoc, hr, Category.assoc,
        ← Category.assoc e, he, Category.id_comp]
    rw [hv Z r z J hJ, val_mul hJ, val_inv, val_pull hJ, this, mul_inv_cancel]
  choose U hU t ht hn using loc
  have agree : ∀ (s s' : S) (Z : Scheme.{0}) (r : Z ⟶ (p ⁻¹ᵁ U s).toScheme)
      (r' : Z ⟶ (p ⁻¹ᵁ U s').toScheme) (z : Z) (J), Good L z J →
      r ≫ (p ⁻¹ᵁ U s).ι = r' ≫ (p ⁻¹ᵁ U s').ι → val (t s) r z J = val (t s') r' z J := by
    intro s s' Z r r' z J hJ hr
    let V : S.Opens := U s ⊓ U s'
    have mk : ∀ W : S.Opens, V ≤ W → ∃ m : pullback p V.ι ⟶ (p ⁻¹ᵁ W).toScheme,
        m ≫ (p ⁻¹ᵁ W).ι = pullback.fst p V.ι := fun W hW =>
      ⟨IsOpenImmersion.lift (p ⁻¹ᵁ W).ι (pullback.fst p V.ι) (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        have e' := congrArg (fun q => q y) (pullback.condition (f := p) (g := V.ι))
        exact (congrArg (· ∈ W) e').mpr (hW (pullback.snd p V.ι y).2)), IsOpenImmersion.lift_fac _ _ _⟩
    obtain ⟨m, hm⟩ := mk (U s) inf_le_left
    obtain ⟨m', hm'⟩ := mk (U s') inf_le_right
    let e' : V.toScheme ⟶ pullback p V.ι := pullback.lift (V.ι ≫ e) (𝟙 _) (by simp [he])
    have he' : e' ≫ pullback.fst p V.ι = V.ι ≫ e := pullback.lift_fst _ _ _
    obtain ⟨v, hv⟩ : ∃ v : Z ⟶ V.toScheme, v ≫ V.ι = (r ≫ (p ⁻¹ᵁ U s).ι) ≫ p :=
      ⟨IsOpenImmersion.lift V.ι ((r ≫ (p ⁻¹ᵁ U s).ι) ≫ p) (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact ⟨(r y).2, (congrArg (fun q => p (q y) ∈ U s') hr).mpr (r' y).2⟩), IsOpenImmersion.lift_fac _ _ _⟩
    let ρ : Z ⟶ pullback p V.ι := pullback.lift (r ≫ (p ⁻¹ᵁ U s).ι) v hv.symm
    have hρ : ρ ≫ pullback.fst p V.ι = r ≫ (p ⁻¹ᵁ U s).ι := pullback.lift_fst _ _ _
    have r₁ : ρ ≫ m = r := by rw [← cancel_mono (p ⁻¹ᵁ U s).ι, Category.assoc, hm, hρ]
    have r₂ : ρ ≫ m' = r' := by rw [← cancel_mono (p ⁻¹ᵁ U s').ι, Category.assoc, hm', hρ, hr]
    have key := gen_unique' hL (φ := fun i => m ≫ (p ⁻¹ᵁ U s).ι ≫ φ i) (ε := ε)
      (φ' := fun i => m' ≫ (p ⁻¹ᵁ U s').ι ≫ φ i) (ε' := ε)
      (fun W _ k => Finset.prod_congr rfl fun i _ => by
        show k (m' ≫ _ ≫ _) ^ _ = k (m ≫ _ ≫ _) ^ _
        rw [← Category.assoc, ← Category.assoc m, hm, hm'])
      (pullback.snd p V.ι) e' (pullback.lift_snd _ _ _) (hp V) (DVR.pullGen_isGen _ _ _ _ (ht s) m)
      (DVR.pullGen_isGen _ _ _ _ (ht s') m') (fun y I hI => by
        rw [val_pull hI, val_pull hI, hn s _ _ V.ι y I hI (by rw [Category.assoc, hm, he']),
          hn s' _ _ V.ι y I hI (by rw [Category.assoc, hm', he'])]) Z ρ z J hJ
    rwa [val_pull hJ, val_pull hJ, r₁, r₂] at key
  obtain ⟨u, hu, -⟩ := glue_gen hL φ ε (fun s => p ⁻¹ᵁ U s) (fun y => ⟨p y, hU _⟩) t ht agree
  exact ⟨u, hu⟩

theorem exists_gen_zsmul {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (k : ℤ) :
    ∃ u : LB.Gen (LB.LinComb L φ (fun i => k * ε i)), u.IsGen := by
  refine ⟨⟨fun j => t.s j ^ k⟩, fun i j => ?_⟩
  have h := congrArg (· ^ k) (ht i j)
  simp only [mul_zpow, ← map_zpow] at h
  refine h.trans (congrArg₂ (· * ·) ?_ rfl)
  refine (Finset.prod_zpow _ _ _).symm.trans (Finset.prod_congr rfl fun a _ => ?_)
  exact (zpow_mul _ _ _).symm.trans (congrArg _ (mul_comm _ _))

theorem exists_gen_neg_of_sym (hG : GlobalFnsSt) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {L : LB A.left} (hL : L.IsLB) (hs : Out.Sym A L) :
    ∃ u : LB.Gen (LB.LinComb L (K := Fin 2) ![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] ![1, -1]), u.IsGen := by
  refine exists_gen_of_local_on_base hL _ _ A.hom η[A].left (Over.w η[A]) (fun V => surj_snd hG hA (Over.mk V.ι))
    (fun U _ h => ?_) (fun s => ?_)
  · have e : η[A].left ≫ (GrpObj.inv : A ⟶ A).left = η[A].left :=
      congrArg (fun q => q.left) (show η[A] ≫ (GrpObj.inv : A ⟶ A) = η[A] from GrpObj.one_inv)
    rw [Fin.prod_univ_two]
    show h (η[A].left ≫ (GrpObj.inv : A ⟶ A).left) ^ (1 : ℤ) * h (η[A].left ≫ 𝟙 _) ^ (-1 : ℤ) = 1
    rw [e, Category.comp_id]; simp
  · obtain ⟨U, hU, t, ht⟩ := hs s
    obtain ⟨t', ht', -⟩ := exists_gen hL
      (φ' := fun k => (A.hom ⁻¹ᵁ U).ι ≫ (![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] : Fin 2 → _) k) (ε' := ![1, -1])
      (fun V _ h => by simp [Fin.prod_univ_two]) t ht
    exact ⟨U, hU, t', ht'⟩

theorem exists_gen_negLB : GlobalFnsSt → ∀ (S : Scheme.{0}) (P : PolAV S) (k : ℤ) (T : Over S),
    ∃ nu : LB.Gen (negLB P.A P.L k T), nu.IsGen := by
  intro hG S P k T
  obtain ⟨u, hu⟩ := exists_gen_neg_of_sym hG P.isAb P.isLB P.sym
  obtain ⟨w, hw⟩ := exists_gen_zsmul _ (DVR.pullGen_isGen _ _ _ _ hu (snd T P.A).left) (-k)
  obtain ⟨t, ht, -⟩ := exists_gen P.isLB (K' := Fin 2)
    (φ' := ![(snd T P.A).left, (snd T P.A ≫ (GrpObj.inv : P.A ⟶ P.A)).left]) (ε' := ![k, -k])
    (fun V _ h => by simp [Fin.prod_univ_two, mul_comm]) w hw
  exact ⟨t, ht⟩

end GlobalTheory
end
end
