module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PreimageEqTopOfSurjective
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.ContrMor

variable {R : Type} [CommRing R] {A B : Over (Sp R)} [GrpObj A] [GrpObj B]
  {D : Type} [CommRing D] [Algebra R D] {D' : Type} [CommRing D'] [Algebra R D']

omit [GrpObj A] in
theorem specOverOfAlgHom_pointWithZeroSecondCoord (φ : D →ₐ[R] D') (x : Pt A D) :
    spOver φ ≫ pt0 B x = pt0 B (spOver φ ≫ x : Pt A D') := by
  simp [pt0, comp_lift, MonObj.comp_one]

omit [GrpObj A] in
theorem spOver_fst_ptV (v : epsR R ⟶ B) (hv : IsTangent v) (x : Pt A D) :
    spOver (TrivSqZeroExt.fstHom R D D) ≫ ptV v x = pt0 B x := by
  have k : spOver (TrivSqZeroExt.fstHom R D D) ≫ spOver (EpsWeil.epsMap R D) =
      toUnit _ ≫ GrpTangent.epsZero R := by
    refine Over.OverMorphism.ext ?_
    rw [spOver_comp, PDiv.spOver_left, Over.comp_left, Over.toUnit_left]
    refine Eq.trans (congrArg spMap (RingHom.ext fun a ↦ ?_)) (Cris.spMap_comp
      (TrivSqZeroExt.fstHom R R R).toRingHom (algebraMap R D))
    simp [EpsWeil.epsMap, DualNumber.lift_apply_apply, TrivSqZeroExt.algebraMap_eq_inl']
  ext1
  · simp only [ptV, pt0, comp_lift, lift_fst, ← Category.assoc, spOver_comp]
    rw [show (TrivSqZeroExt.fstHom R D D).comp (TrivSqZeroExt.inlAlgHom R D D) = AlgHom.id R D from
      AlgHom.ext fun _ ↦ rfl, PDiv.spOver_id, Category.id_comp]
  · simp only [ptV, pt0, comp_lift, lift_snd]
    rw [← Category.assoc, k, Category.assoc, (GrpTangent.isTangent_iff v).1 hv, MonObj.comp_one]

omit [GrpObj A] [GrpObj B] in
theorem spOver_epsHom_ptV (v : epsR R ⟶ B) (φ : D →ₐ[R] D') (x : Pt A D) :
    spOver (epsHom φ) ≫ ptV v x = ptV v (spOver φ ≫ x : Pt A D') := by
  ext1
  · simp only [ptV, comp_lift, lift_fst, ← Category.assoc, spOver_comp]
    congr 2
    ext c <;> simp [epsHom]
  · simp only [ptV, comp_lift, lift_snd, ← Category.assoc, spOver_comp]
    congr 2
    ext <;> simp only [AlgHom.comp_apply, EpsWeil.epsMap, epsHom, DualNumber.lift_apply_eps]

def sHom (x : Pt A D) : trivAt (pt0 B x) ⟶ thickAt B x :=
  (epsExt R D).secHom (Pt.w (pt0 B x)) (epsExt R D).i (epsExt R D).π_i

def iHom (v : epsR R ⟶ B) (hv : IsTangent v) (x : Pt A D) : trivAt (ptV v x) ⟶ thickAt B x :=
  Thick.trivHom (T := thickAt B x) (AlgHom.id R (DualNumber D)) (by
    have := congrArg Over.Hom.left (spOver_fst_ptV v hv x)
    rw [Over.comp_left, PDiv.spOver_left] at this
    exact this)

def aHom (φ : D →ₐ[R] D') (x : Pt A D) :
    trivAt (pt0 B x) ⟶ trivAt (pt0 B (spOver φ ≫ x : Pt A D')) :=
  Thick.trivHom φ (by
    have := congrArg Over.Hom.left (specOverOfAlgHom_pointWithZeroSecondCoord (B := B) φ x)
    rw [Over.comp_left, PDiv.spOver_left] at this
    exact this)

def bHom (v : epsR R ⟶ B) (φ : D →ₐ[R] D') (x : Pt A D) :
    trivAt (ptV v x) ⟶ trivAt (ptV v (spOver φ ≫ x : Pt A D')) :=
  Thick.trivHom (epsHom φ) (by
    have := congrArg Over.Hom.left (spOver_epsHom_ptV v φ x)
    rw [Over.comp_left, PDiv.spOver_left] at this
    exact this)

def τHom (φ : D →ₐ[R] D') (x : Pt A D) :
    thickAt B x ⟶ thickAt B (spOver φ ≫ x : Pt A D') :=
  (epsExt R D).thickHom (epsExt R D') (epsHom φ) φ
    (fun c ↦ by simp [epsHom, DualNumber.lift_apply_apply]) _ _ (by
    have := congrArg Over.Hom.left (specOverOfAlgHom_pointWithZeroSecondCoord (B := B) φ x)
    rw [Over.comp_left, PDiv.spOver_left] at this
    exact this)

end GlobalTheory.PtExt.ContrMor

namespace GlobalTheory.PtExt.ContrMor

theorem exists_contr : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B]
    (v : epsR R ⟶ B), IsTangent v →
    (∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
      (φ : D →ₐ[R] D') (x : Pt A D),
      let y : Pt A D' := spOver φ ≫ x
      ∃ (s : trivAt (pt0 B x) ⟶ thickAt B x) (i : trivAt (ptV v x) ⟶ thickAt B x)
        (s' : trivAt (pt0 B y) ⟶ thickAt B y) (i' : trivAt (ptV v y) ⟶ thickAt B y)
        (a : trivAt (pt0 B x) ⟶ trivAt (pt0 B y)) (b : trivAt (ptV v x) ⟶ trivAt (ptV v y))
        (τ : thickAt B x ⟶ thickAt B y),
        (∀ r, s.φ r = TrivSqZeroExt.inl r) ∧ (∀ r, i.φ r = r) ∧
        (∀ r, s'.φ r = TrivSqZeroExt.inl r) ∧ (∀ r, i'.φ r = r) ∧
        (∀ r, a.φ r = φ r) ∧ (∀ r, b.φ r = epsHom φ r) ∧ (∀ r, τ.φ r = epsHom φ r)) ∧
    ∀ z : C2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)), ∃ κ : Fn1 A, IsContr z v κ := by
  intro R _ A B _ _ v hv
  refine ⟨fun D _ _ D' _ _ φ x ↦ ⟨sHom x, iHom v hv x, sHom _, iHom v hv _, aHom φ x, bHom v φ x, τHom φ x,
    fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩, fun z ↦ ?_⟩
  refine ⟨fun D _ _ D' _ _ φ x ↦ TrivSqZeroExt.snd (R := D')
    (z _ _ _ (sHom x) (τHom φ x) - z _ _ _ (aHom φ x) (sHom _) - z _ _ _ (iHom v hv x) (τHom φ x) +
      z _ _ _ (bHom v φ x) (iHom v hv _)), ?_⟩
  intro D _ _ D' _ _ φ x s i s' i' a b τ hs hi hs' hi' ha hb hτ
  obtain rfl : s = sHom x := Thick.hom_ext fun r ↦ (hs r).trans rfl
  obtain rfl : i = iHom v hv x := Thick.hom_ext fun r ↦ (hi r).trans rfl
  obtain rfl : s' = sHom _ := Thick.hom_ext fun r ↦ (hs' r).trans rfl
  obtain rfl : i' = iHom v hv _ := Thick.hom_ext fun r ↦ (hi' r).trans rfl
  obtain rfl : a = aHom φ x := Thick.hom_ext fun r ↦ (ha r).trans rfl
  obtain rfl : b = bHom v φ x := Thick.hom_ext fun r ↦ (hb r).trans rfl
  obtain rfl : τ = τHom φ x := Thick.hom_ext fun r ↦ (hτ r).trans rfl
  rfl

end GlobalTheory.PtExt.ContrMor
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R] {X : Over (Sp R)} {K : Type}

abbrev SmallCat (W : K → X.left.Opens) : Type 1 := (IsSmall (dp0 R) (X.hom ≫ 𝟙 _) W).FullSubcategory

abbrev smallAt (W : K → X.left.Opens) {D : Type} [CommRing D] [Algebra R D] (x : Pt X D) (h : Sm W x) :
    SmallCat W := ⟨trivAt x, h⟩

theorem Sm.map {W : K → X.left.Opens} {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') {x : Pt X D} (h : Sm W x) : Sm W (D := D') (spOver φ ≫ x) := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, (trivMap φ x).le_preimage hi⟩


open Classical in
def cocOf (W : K → X.left.Opens) (n : C1 ((IsSmall (dp0 R) (X.hom ≫ 𝟙 _) W).ι ⋙ O (dp0 R) (X.hom ≫ 𝟙 _))) :
    Fn1 X := fun _ _ _ _ _ _ φ x ↦
  if h : Sm W x then n (smallAt W x h) (smallAt W _ (h.map φ)) (ObjectProperty.homMk (trivMap φ x)) else 0

end GlobalTheory.PtExt

namespace GlobalTheory.PtExt
variable {R : Type} [CommRing R] {X : Over (Sp R)} {K : Type}

private theorem thickHom_ext {T T' : Thick (dp0 R) (X.hom ≫ 𝟙 _)}
    {f g : Thick.Hom T T'} (h : ∀ b, f.φ b = g.φ b) : f = g := by
  rcases f with ⟨φ, φ₀, comm, dp, pt⟩
  rcases g with ⟨ψ, ψ₀, comm', dp', pt'⟩
  obtain rfl : φ = ψ := AlgHom.ext h
  obtain rfl : φ₀ = ψ₀ := RingHom.ext fun c ↦ by
    obtain ⟨b, rfl⟩ := T.surj c
    rw [comm, comm']
  rfl

theorem isCoc_cocOf (W : K → X.left.Opens)
    (n : C1 ((IsSmall (dp0 R) (X.hom ≫ 𝟙 _) W).ι ⋙ O (dp0 R) (X.hom ≫ 𝟙 _)))
    (hn : ∀ (T T' T'' : SmallCat W) (a : T ⟶ T') (b : T' ⟶ T''), T.obj.J = ⊥ → T'.obj.J = ⊥ →
      T''.obj.J = ⊥ → d1 _ n T T' T'' a b = 0) : IsCoc W (cocOf W n) := by
  intro D _ _ D' _ _ D'' _ _ φ ψ x hx
  have tr : ∀ (y y' : Pt X D'') (e : y = y') (h : Sm W y) (h' : Sm W y')
      (f : smallAt W x hx ⟶ smallAt W y h) (f' : smallAt W x hx ⟶ smallAt W y' h'),
      (∀ r, f.hom.φ r = f'.hom.φ r) → n _ _ f = n _ _ f' := by
    rintro y _ rfl h h' f f' hf
    have : f = f' := ObjectProperty.hom_ext _ (thickHom_ext hf)
    subst this; rfl
  have key := hn (smallAt W x hx) (smallAt W _ (hx.map φ)) (smallAt W _ ((hx.map φ).map ψ))
    (ObjectProperty.homMk (trivMap φ x)) (ObjectProperty.homMk (trivMap ψ _)) rfl rfl rfl
  rw [d1_apply] at key
  simp only [cocOf, dite_eq_left hx, dite_eq_left (hx.map φ)]
  have e := tr (spOver (ψ.comp φ) ≫ x) (spOver ψ ≫ spOver φ ≫ x)
    (by rw [← spOver_comp, Category.assoc]) (hx.map (ψ.comp φ)) ((hx.map φ).map ψ)
    (ObjectProperty.homMk (trivMap (ψ.comp φ) x))
    ((ObjectProperty.homMk (trivMap φ x) : smallAt W x hx ⟶ smallAt W _ (hx.map φ)) ≫
      (ObjectProperty.homMk (trivMap ψ (spOver φ ≫ x)) : smallAt W _ (hx.map φ) ⟶ smallAt W _ ((hx.map φ).map ψ)))
    (fun _ ↦ rfl)
  rw [e]
  change ψ _ - _ + _ = 0 at key
  linear_combination -key
end GlobalTheory.PtExt
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

def sqToEps {M S : Type} [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
    [CommRing S] [Algebra R S] (k : M →ₗ[R] S) : TrivSqZeroExt R M →ₐ[R] DualNumber S where
  toFun z := (algebraMap R S z.fst, k z.snd)
  map_one' := TrivSqZeroExt.ext (map_one (algebraMap R S)) (map_zero k)
  map_mul' a b := TrivSqZeroExt.ext (map_mul (algebraMap R S) _ _) (by
    change k (a.fst • b.snd + MulOpposite.op b.fst • a.snd) =
      algebraMap R S a.fst * k b.snd + k a.snd * algebraMap R S b.fst
    rw [op_smul_eq_smul, map_add (f := _), map_smul, map_smul, Algebra.smul_def, Algebra.smul_def,
      mul_comm (k a.snd)])
  map_zero' := TrivSqZeroExt.ext (map_zero (algebraMap R S)) (map_zero k)
  map_add' a b := TrivSqZeroExt.ext (map_add (algebraMap R S) _ _) (map_add k _ _)
  commutes' _ := TrivSqZeroExt.ext rfl (map_zero k)

attribute [local instance] cotOp cotCentral cotTower

theorem tanDer_cotVal {A : Over (Sp R)} [GrpObj A] {p : ℕ} {G : PDivGroup p R} (t : G.TorsionTower A)
    (β : Form (A.hom ≫ 𝟙 _)) {v : epsR R ⟶ A} (hv : IsTangent v) (n : ℕ) :
    t.tanDer hv n (cotVal β.1 (t.y n)) = algebraMap R (PDiv.ModPow p R n) (tanVal v β) := by
  let S := PDiv.ModPow p R n
  let E : SqExt R := SqExt.ofModule R S S
  let ρ : (cotExt R (G.A n)).C →ₐ[R] DualNumber S := sqToEps (t.tanDer hv n)
  let y' : Pt A (cotExt R (G.A n)).C := spOver (cotPt R (G.A n)) ≫ t.y n
  have hρ : ρ.comp (cotPt R (G.A n)) = t.tanPt hv n := AlgHom.ext fun a ↦ by
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [t.fst_tanPt]
      exact congrArg (algebraMap R S) (add_zero _)
    · rw [← t.tanDer_d]
      exact congrArg (t.tanDer hv n) (zero_add _)
  have e : spOver ρ ≫ y' = epsRedPow p n v := by
    rw [← Category.assoc, spOver_comp, hρ, t.tanPt_y]
  have k1 := (cotExt R (G.A n)).val_map E ρ (Algebra.ofId R S) (fun _ ↦ rfl)
    (fun _ ↦ TrivSqZeroExt.ext rfl (map_zero (t.tanDer hv n))) y'.left y'.w _
    (Pt.w (epsRedPow p n v)) (congrArg Over.Hom.left e) β
  have k2 := (SqExt.dual R).val_map E (epsTo R S) (Algebra.ofId R S) (fun c ↦ (fst_epsTo S c).symm)
    (fun c ↦ TrivSqZeroExt.ext (fst_epsTo S _) ((snd_epsTo S _).trans (map_zero _))) v.left (pt_w v) _
    (Pt.w (epsRedPow p n v)) rfl β
  have h0 : fv β.1 (G.A n) (cotExt R (G.A n)).C (cotPt R (G.A n)) (t.y n) = 0 := β.2 _ rfl rfl
  have k3 := congrArg TrivSqZeroExt.snd (k1.symm.trans k2)
  rw [snd_epsTo] at k3
  refine Eq.trans ?_ k3
  change t.tanDer hv n (cotSnd R _ (_ - fv β.1 (G.A n) (cotExt R (G.A n)).C (cotPt R (G.A n)) (t.y n))) = _
  rw [h0, sub_zero]
  rfl

theorem lie_cotVal_eq_tanVal : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R) (t : G.TorsionTower A), IsNilpotent (p : R) → ∀ (β : Form (A.hom ≫ 𝟙 _)) (w : G.omega), (∀ n, w.1 n = cotVal β.1 (t.y n)) → ∀ (x : G.Lie) (v : epsR R ⟶ A), t.LieCorr x v → x w = tanVal v β := by
  intro R _ A _ p G t ⟨n, hn⟩ β w hw x v h
  have h1 := (t.lieCorr_iff h.1 x).1 h n w
  rw [hw, tanDer_cotVal] at h1
  have h2 := Ideal.Quotient.eq.1 h1
  rw [hn, Ideal.mem_span_singleton, zero_dvd_iff] at h2
  exact sub_eq_zero.1 h2

end GlobalTheory.PtExt
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PtExt

abbrev locAlg (R : Type) [CommRing R] {D : Type} [CommRing D] [Algebra R D] (s : D) :
    D →ₐ[R] Localization.Away s :=
  IsScalarTower.toAlgHom R D (Localization.Away s)

theorem sm_loc_of_mem {R : Type} [CommRing R] {X : Over (Sp R)} {K : Type} (W : K → X.left.Opens)
    (hW : ⨆ i, W i = ⊤) {D : Type} [CommRing D] [Algebra R D] (x : Pt X D) (P : PrimeSpectrum D) :
    ∃ s : D, s ∉ P.asIdeal ∧ Sm W (D := Localization.Away s) (spOver (locAlg R s) ≫ x) := by
  have h1 : x.left.base P ∈ (⨆ i, W i) := by rw [hW]; trivial
  obtain ⟨i, hi⟩ := (TopologicalSpace.Opens.mem_iSup).mp h1
  obtain ⟨V, ⟨s, rfl⟩, hPV, hVU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (a := P)
      (u := (x.left ⁻¹ᵁ W i).1) hi (x.left ⁻¹ᵁ W i).isOpen
  refine ⟨s, hPV, i, fun q _ ↦ ?_⟩
  have hq : (spMap (algebraMap D (Localization.Away s))).base q ∈ PrimeSpectrum.basicOpen s := by
    change s ∉ (PrimeSpectrum.comap (algebraMap D (Localization.Away s)) q).asIdeal
    intro h
    exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit s))
  exact hVU hq

end GlobalTheory.PtExt

namespace GlobalTheory.PtExt

def awR (R : Type) [CommRing R] {D : Type} [CommRing D] [Algebra R D] (a b : D) :
    Localization.Away a →ₐ[R] Localization.Away (a * b) where
  toRingHom := IsLocalization.Away.awayToAwayRight (P := Localization.Away (a * b)) a b
  commutes' r := by
    change IsLocalization.Away.awayToAwayRight (P := Localization.Away (a * b)) a b (algebraMap R _ r) = _
    rw [IsScalarTower.algebraMap_apply R D (Localization.Away a),
      IsLocalization.Away.awayToAwayRight_eq, ← IsScalarTower.algebraMap_apply]

def awL (R : Type) [CommRing R] {D : Type} [CommRing D] [Algebra R D] (a b : D) :
    Localization.Away b →ₐ[R] Localization.Away (a * b) where
  toRingHom := IsLocalization.Away.awayToAwayLeft (P := Localization.Away (a * b)) b a
  commutes' r := by
    change IsLocalization.Away.awayToAwayLeft (P := Localization.Away (a * b)) b a (algebraMap R _ r) = _
    rw [IsScalarTower.algebraMap_apply R D (Localization.Away b),
      IsLocalization.Away.awayToAwayLeft_eq, ← IsScalarTower.algebraMap_apply]

theorem awR_comp (R : Type) [CommRing R] {D : Type} [CommRing D] [Algebra R D] (a b : D) :
    (awR R a b).comp (locAlg R a) = locAlg R (a * b) := by
  ext z
  rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', IsScalarTower.coe_toAlgHom']
  exact IsLocalization.Away.awayToAwayRight_eq (P := Localization.Away (a * b)) a b z

theorem awL_comp (R : Type) [CommRing R] {D : Type} [CommRing D] [Algebra R D] (a b : D) :
    (awL R a b).comp (locAlg R b) = locAlg R (a * b) := by
  ext z
  rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', IsScalarTower.coe_toAlgHom']
  exact IsLocalization.Away.awayToAwayLeft_eq (P := Localization.Away (a * b)) b a z

end GlobalTheory.PtExt

namespace GlobalTheory.PtExt

theorem natFamily_existsUnique :
    ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens),
    ⨆ i, W i = ⊤ → ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D)
      (τ : ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E),
    (∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E']
      (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'),
      Sm W (D := E) (spOver ψ ≫ x) → τ E' (θ.comp ψ) = θ (τ E ψ)) →
    ∃! d : D, ∀ (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E),
      Sm W (D := E) (spOver ψ ≫ x) → τ E ψ = ψ d := by
  intro R _ X K W hW D _ _ x τ hτ
  let S : Set D := {s | Sm W (D := Localization.Away s) (spOver (locAlg R s) ≫ x)}
  have key : ∀ (s : D), s ∈ S → ∀ (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E)
      (θ : Localization.Away s →ₐ[R] E), θ.comp (locAlg R s) = ψ → θ (τ _ (locAlg R s)) = τ E ψ := by
    intro s hs E _ _ ψ θ h
    rw [← hτ _ _ _ θ hs, h]
  have span : Ideal.span S = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hSM⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨s, hsM, hs⟩ := sm_loc_of_mem W hW x ⟨M, hM.isPrime⟩
    exact hsM (hSM (Ideal.subset_span hs))
  let v : ∀ a : S, Localization.Away a.1 := fun a ↦ τ _ (locAlg R a.1)
  obtain ⟨d, hd, hu⟩ := Localization.existsUnique_algebraMap_eq_of_span_eq_top S span v (fun a b ↦ by
    have e1 := key a a.2 _ _ (awR R (a : D) b) (awR_comp R _ _)
    have e2 := key b b.2 _ _ (awL R (a : D) b) (awL_comp R _ _)
    exact e1.trans e2.symm)
  refine ⟨d, fun E _ _ ψ hψ ↦ ?_, fun d' hd' ↦ hu d' fun a ↦ (hd' _ (locAlg R a.1) a.2).symm⟩
  have spanE : Ideal.span ((ψ : D →+* E) '' S) = ⊤ := by
    rw [← Ideal.map_span, span, Ideal.map_top]
  apply Localization.algebraMap_injective_of_span_eq_top _ spanE
  funext ⟨t, s, hs, ht⟩
  subst ht
  let θ : E →ₐ[R] Localization.Away (ψ s) := locAlg R (ψ s)
  let θ' : Localization.Away s →ₐ[R] Localization.Away (ψ s) := Localization.awayMapₐ ψ s
  have hc : θ'.comp (locAlg R s) = θ.comp ψ := AlgHom.ext fun z ↦ by
    simp [θ', θ, IsLocalization.Away.mapₐ, IsLocalization.Away.map, IsLocalization.map_eq]
  change θ (τ E ψ) = θ (ψ d)
  have e : τ _ (locAlg R s) = algebraMap D _ d := (hd ⟨s, hs⟩).symm
  rw [← hτ E _ ψ θ hψ, ← hc, ← key s hs _ _ θ' rfl, e]
  exact DFunLike.congr_fun hc d

end GlobalTheory.PtExt
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

theorem spOver_epsHom_ptV {A B : Over (Sp R)} [GrpObj A] [GrpObj B] (v : epsR R ⟶ B)
    {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt A D) :
    (spOver (epsHom φ) ≫ ptV v x : Pt (A ⊗ B) (DualNumber D')) =
      ptV v (spOver φ ≫ x : Pt A D') := by
  have h1 : (epsHom φ).comp (TrivSqZeroExt.inlAlgHom R D D) = (TrivSqZeroExt.inlAlgHom R D' D').comp φ :=
    AlgHom.ext fun a ↦ by simp [epsHom]
  have h2 : (epsHom φ).comp (EpsWeil.epsMap R D) = EpsWeil.epsMap R D' :=
    DualNumber.algHom_ext (by simp [epsHom, EpsWeil.epsMap, DualNumber.lift_apply_apply])
  simp only [ptV, comp_lift, ← Category.assoc, spOver_comp, h1, h2]

theorem fst_ptV {A B : Over (Sp R)} [GrpObj A] [GrpObj B] {v : epsR R ⟶ B} (hv : IsTangent v)
    {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) :
    (spOver (TrivSqZeroExt.fstHom R D D) ≫ ptV v x : Pt (A ⊗ B) D) = pt0 B x := by
  have h1 : (TrivSqZeroExt.fstHom R D D).comp (TrivSqZeroExt.inlAlgHom R D D) = AlgHom.id R D :=
    AlgHom.ext fun _ ↦ rfl
  have h2 : (TrivSqZeroExt.fstHom R D D).comp (EpsWeil.epsMap R D) =
      (Algebra.ofId R D).comp (TrivSqZeroExt.fstHom R R R) :=
    DualNumber.algHom_ext (by simp [EpsWeil.epsMap, DualNumber.lift_apply_apply])
  rw [ptV, pt0, comp_lift, ← Category.assoc, spOver_comp, h1, spOver_id, Category.id_comp,
    ← Category.assoc, spOver_comp, h2, ← spOver_comp, Category.assoc]
  congr 1
  ext1
  rw [Over.comp_left, Over.comp_left, spOver_left, spOver_left, Hom.one_def, Over.comp_left, Over.toUnit_left]
  have := hv
  unfold IsTangent at this
  erw [this]
  rfl

theorem sm_ptV {A B : Over (Sp R)} [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left) {v : epsR R ⟶ B}
    (hv : IsTangent v) {D : Type} [CommRing D] [Algebra R D] {x : Pt A D}
    (hx : Sm (chartsA (A := A) (B := B) P) x) : Sm (X := A ⊗ B) P.U (ptV v x) := by
  obtain ⟨i, hi⟩ := hx
  refine ⟨i, ?_⟩
  have hsurj : Surjective (spOver (TrivSqZeroExt.fstHom R D D)).left := by
    rw [spOver_left]
    refine GlobalTheory.TorusLift.surjective_specMap _ (fun a ↦ ⟨TrivSqZeroExt.inl a, rfl⟩) ⟨2, ?_⟩
    rw [sq, Ideal.zero_eq_bot, eq_bot_iff]
    refine Ideal.mul_le.2 fun a ha b hb ↦ ?_
    have ha' : a.fst = 0 := ha
    have hb' : b.fst = 0 := hb
    rw [Ideal.mem_bot]
    ext <;> simp [ha', hb']
  have e : (spOver (TrivSqZeroExt.fstHom R D D) ≫ ptV v x : Pt (A ⊗ B) D).left =
      x.left ≫ (AbDual.inl A B).left := by
    rw [fst_ptV hv, ← Over.comp_left, pt0, AbDual.inl, comp_lift, Category.comp_id, MonObj.comp_one]
  have := GlobalTheory.TorusLift.preimage_eq_top_of_surjective (spOver (TrivSqZeroExt.fstHom R D D)).left
    (ptV v x).left (U := P.U i) (by
      rw [← Over.comp_left, e, Scheme.Hom.comp_preimage]
      exact top_unique hi)
  exact this.ge

end GlobalTheory.PtExt
end
end
