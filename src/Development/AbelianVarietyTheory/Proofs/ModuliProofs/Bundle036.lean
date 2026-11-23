module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.LocDerExt

theorem der_unique {A B C : Type} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] (f : A)
    [IsLocalization.Away f B] (φ : B →+* C) (δ₁ δ₂ : B → C)
    (h₁ : ∀ a b, δ₁ (a * b) = φ a * δ₁ b + φ b * δ₁ a)
    (h₂ : ∀ a b, δ₂ (a * b) = φ a * δ₂ b + φ b * δ₂ a)
    (h : ∀ a, δ₁ (algebraMap A B a) = δ₂ (algebraMap A B a)) (s : B) : δ₁ s = δ₂ s := by
  obtain ⟨⟨a, t⟩, e⟩ := IsLocalization.surj (Submonoid.powers f) s
  have hu : IsUnit (φ (algebraMap A B t)) := (IsLocalization.map_units B t).map φ
  have e₁ := h₁ s (algebraMap A B t)
  have e₂ := h₂ s (algebraMap A B t)
  dsimp only at e
  rw [e] at e₁ e₂
  rw [h, e₂, h] at e₁
  exact (hu.mul_left_cancel (add_left_cancel e₁)).symm

theorem der_exists {A B C : Type} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] (f : A)
    [IsLocalization.Away f B] (φ : B →+* C) (d : A → C)
    (hadd : ∀ a b, d (a + b) = d a + d b)
    (hmul : ∀ a b, d (a * b) = φ (algebraMap A B a) * d b + φ (algebraMap A B b) * d a) :
    ∃ δ : B → C, (∀ a b, δ (a + b) = δ a + δ b) ∧ (∀ a b, δ (a * b) = φ a * δ b + φ b * δ a) ∧
      ∀ a, δ (algebraMap A B a) = d a := by
  have h0 : d 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  have h1 : d 1 = 0 := by
    have := hmul 1 1
    simp only [_root_.mul_one, map_one, _root_.one_mul] at this
    exact left_eq_add.mp this
  obtain ⟨ψ, hψ1, hψ2⟩ : ∃ ψ : A →+* DualNumber C, (∀ a, (ψ a).fst = φ (algebraMap A B a)) ∧
      ∀ a, (ψ a).snd = d a :=
    ⟨{ toFun := fun a => TrivSqZeroExt.inl (φ (algebraMap A B a)) + TrivSqZeroExt.inr (d a)
       map_one' := by ext <;> simp [h1]
       map_zero' := by ext <;> simp [h0]
       map_add' := fun a b => by ext <;> simp [hadd]
       map_mul' := fun a b => by ext <;> simp [hmul, mul_comm] }, fun a => by simp, fun a => by simp⟩
  have hu : IsUnit (ψ f) := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, hψ1]
    exact (IsLocalization.Away.algebraMap_isUnit f).map φ
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : B →+* DualNumber C, ∀ a, Ψ (algebraMap A B a) = ψ a :=
    ⟨IsLocalization.Away.lift f hu, fun a => IsLocalization.Away.lift_eq f hu a⟩
  obtain ⟨π, hπ⟩ : ∃ π : DualNumber C →+* C, ∀ x, π x = x.fst :=
    ⟨(TrivSqZeroExt.fstHom C C C).toRingHom, fun _ => rfl⟩
  have hf : π.comp Ψ = φ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext a
    simp only [RingHom.comp_apply, hΨ, hπ, hψ1]
  have hf' : ∀ b, (Ψ b).fst = φ b := fun b => by rw [← hf, RingHom.comp_apply, hπ]
  refine ⟨fun b => (Ψ b).snd, fun a b => by simp only [map_add (f := _), TrivSqZeroExt.snd_add],
    fun a b => ?_, fun a => by simp only [hΨ, hψ2]⟩
  simp only [map_mul, DualNumber.snd_mul, hf']
  ring

theorem res_res (X : Scheme.{0}) {U V W : X.Opens} (h : V ≤ U) (k : W ≤ V) (s : Γ(X, U)) :
    resG X k (resG X h s) = resG X (k.trans h) s := by
  change (X.presheaf.map _ ≫ X.presheaf.map _).hom s = _
  rw [← Functor.map_comp]
  rfl

theorem res_const {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens}
    (h : V ≤ U) (a : R) : resG X h (constFn p U a) = constFn p V a :=
  congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map p (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)

theorem pre_le {Y X : Scheme.{0}} (m : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) : m ⁻¹ᵁ V ≤ m ⁻¹ᵁ U :=
  fun _ hy => h hy

theorem app_res {Y X : Scheme.{0}} (m : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (s : Γ(X, U)) :
    (m.app V).hom (resG X h s) = resG Y (pre_le m h) ((m.app U).hom s) :=
  congrArg (fun φ => φ.hom s) (Scheme.Hom.naturality m (homOfLE h).op)

theorem cover {Y X : Scheme.{0}} (m : Y ⟶ X) {W₀ : X.Opens} (hW : IsAffineOpen W₀) {W : X.Opens}
    (h : W ≤ W₀) :
    m ⁻¹ᵁ W ≤ ⨆ i : {f : Γ(X, W₀) // X.basicOpen f ≤ W}, m ⁻¹ᵁ X.basicOpen i.1 := by
  intro y hy
  obtain ⟨f, hf, hx⟩ := hW.exists_basicOpen_le (V := W) ⟨m y, hy⟩ (h hy)
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, hf⟩, hx⟩

theorem sep {Y X : Scheme.{0}} (m : Y ⟶ X) {W₀ : X.Opens} (hW : IsAffineOpen W₀) {W : X.Opens}
    (h : W ≤ W₀) (s t : Γ(Y, m ⁻¹ᵁ W))
    (e : ∀ (f : Γ(X, W₀)) (k : X.basicOpen f ≤ W), resG Y (pre_le m k) s = resG Y (pre_le m k) t) :
    s = t :=
  Y.sheaf.eq_of_locally_eq' (fun i : {f : Γ(X, W₀) // X.basicOpen f ≤ W} => m ⁻¹ᵁ X.basicOpen i.1)
    (m ⁻¹ᵁ W) (fun i => homOfLE (pre_le m i.2)) (cover m hW h) s t (fun i => e i.1 i.2)

theorem exists_locDer : ∀ (R : Type) [CommRing R] (Y X : Scheme.{0}) (q : Y ⟶ Sp ℂ) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → ℂ) (W₀ : X.Opens), IsAffineOpen W₀ → ∀ d₀ : Γ(X, W₀) → Γ(Y, m ⁻¹ᵁ W₀), (∀ a b, d₀ (a + b) = d₀ a + d₀ b) → (∀ a b, d₀ (a * b) = (m.app W₀).hom a * d₀ b + (m.app W₀).hom b * d₀ a) → (∀ r, d₀ (constFn p W₀ r) = constFn q (m ⁻¹ᵁ W₀) (D r)) → ∃ d, LocDer q p m D W₀ d ∧ d W₀ = d₀ := by
  intro R _ Y X q p m D W₀ hW d₀ hadd hmul hbase
  have H : ∀ f : Γ(X, W₀), ∃ δ : Γ(X, X.basicOpen f) → Γ(Y, m ⁻¹ᵁ X.basicOpen f),
      (∀ a b, δ (a + b) = δ a + δ b) ∧
      (∀ a b, δ (a * b) = (m.app _).hom a * δ b + (m.app _).hom b * δ a) ∧
      ∀ a, δ (resG X (X.basicOpen_le f) a) = resG Y (pre_le m (X.basicOpen_le f)) (d₀ a) := by
    intro f
    haveI := hW.isLocalization_basicOpen f
    refine der_exists f (m.app (X.basicOpen f)).hom
      (fun a => resG Y (pre_le m (X.basicOpen_le f)) (d₀ a)) (fun a b => by simp only [hadd, map_add (f := _)])
      (fun a b => ?_)
    have e : ∀ a, (m.app (X.basicOpen f)).hom (algebraMap Γ(X, W₀) Γ(X, X.basicOpen f) a) =
        resG Y (pre_le m (X.basicOpen_le f)) ((m.app W₀).hom a) :=
      fun a => app_res m (X.basicOpen_le f) a
    rw [e, e]
    simp only [hmul, map_add (f := _), map_mul]
  choose δ δadd δmul δres using H
  have compat : ∀ (f g : Γ(X, W₀)) (k : X.basicOpen g ≤ X.basicOpen f) (s : Γ(X, X.basicOpen f)),
      resG Y (pre_le m k) (δ f s) = δ g (resG X k s) := by
    intro f g k s
    haveI := hW.isLocalization_basicOpen f
    refine der_unique f ((m.app (X.basicOpen g)).hom.comp (resG X k))
      (fun s => resG Y (pre_le m k) (δ f s)) (fun s => δ g (resG X k s)) (fun a b => ?_)
      (fun a b => ?_) (fun a => ?_) s
    · simp only [δmul, map_add (f := _), map_mul, RingHom.comp_apply, app_res m k]
    · simp only [δmul, map_mul, RingHom.comp_apply]
    · change resG Y (pre_le m k) (δ f (resG X (X.basicOpen_le f) a)) =
        δ g (resG X k (resG X (X.basicOpen_le f) a))
      rw [res_res X, δres, δres, res_res Y]
  have G : ∀ (W : X.Opens), W ≤ W₀ → ∀ s : Γ(X, W), ∃ t : Γ(Y, m ⁻¹ᵁ W),
      ∀ (f : Γ(X, W₀)) (k : X.basicOpen f ≤ W), resG Y (pre_le m k) t = δ f (resG X k s) := by
    intro W h s
    obtain ⟨t, ht, -⟩ := Y.sheaf.existsUnique_gluing'
      (fun i : {f : Γ(X, W₀) // X.basicOpen f ≤ W} => m ⁻¹ᵁ X.basicOpen i.1)
      (m ⁻¹ᵁ W) (fun i => homOfLE (pre_le m i.2)) (cover m hW h)
      (fun i => δ i.1 (resG X i.2 s)) (fun i j => by
        have e : X.basicOpen (i.1 * j.1) = X.basicOpen i.1 ⊓ X.basicOpen j.1 := X.basicOpen_mul _ _
        have ki : X.basicOpen (i.1 * j.1) ≤ X.basicOpen i.1 := e.le.trans inf_le_left
        have kj : X.basicOpen (i.1 * j.1) ≤ X.basicOpen j.1 := e.le.trans inf_le_right
        have k : m ⁻¹ᵁ X.basicOpen i.1 ⊓ m ⁻¹ᵁ X.basicOpen j.1 ≤ m ⁻¹ᵁ X.basicOpen (i.1 * j.1) :=
          fun y hy => e.ge hy
        have e' : resG Y (pre_le m ki) (δ i.1 (resG X i.2 s)) =
            resG Y (pre_le m kj) (δ j.1 (resG X j.2 s)) := by
          rw [compat _ _ ki, compat _ _ kj, res_res X, res_res X]
        have e'' := congrArg (resG Y k) e'
        rw [res_res Y, res_res Y] at e''
        exact e'')
    exact ⟨t, fun f k => ht ⟨f, k⟩⟩
  choose t ht using G
  classical
  refine ⟨fun W s => if h : W ≤ W₀ then t W h s else 0, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro W h a b
    simp only [dif_pos h]
    refine sep m hW h _ _ (fun f k => ?_)
    rw [map_add (f := _), ht W h _ f k, ht W h _ f k, ht W h _ f k, map_add (f := _), δadd]
  · intro W h a b
    simp only [dif_pos h]
    refine sep m hW h _ _ (fun f k => ?_)
    rw [map_add (f := _), map_mul, map_mul, ht W h _ f k, ht W h _ f k, ht W h _ f k, map_mul, δmul, app_res m k, app_res m k]
  · intro W W' h' h a
    simp only [dif_pos h, dif_pos (h'.trans h)]
    refine sep m hW (h'.trans h) _ _ (fun f k => ?_)
    refine Eq.trans ?_ (res_res Y (pre_le m h') (pre_le m k) _).symm
    rw [ht W' _ _ f k, ht W h a f (k.trans h'), res_res X]
  · intro W h r
    simp only [dif_pos h]
    refine sep m hW h _ _ (fun f k => ?_)
    rw [ht W h _ f k, res_const, res_const, ← res_const p (X.basicOpen_le f), δres, hbase, res_const]
  · funext a
    simp only [dif_pos (le_refl W₀)]
    refine sep m hW le_rfl _ _ (fun f k => ?_)
    rw [ht W₀ _ _ f k, δres]

end GlobalTheory.LocDerExt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam.ListedSubgroup

variable {S : Scheme.{0}}

theorem eq_comp_section {X : Scheme.{0}} (f : X ⟶ S) [IsSeparated f] (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)
    {k : Type} [Field k] (z : Sp k ⟶ X) (q : Sp k) (hz : z q ∈ Set.range s) : z = (z ≫ f) ≫ s := by
  have := isClosedImmersion_of_section_of_isSeparated f s hs
  have hsurj : Surjective (pullback.fst z s) := by
    refine ⟨fun y => ?_⟩
    obtain rfl : y = q := Subsingleton.elim _ _
    have h : y ∈ Set.range (pullback.fst z s) := by
      rw [Scheme.Pullback.range_fst]
      exact hz
    exact h
  have : IsIso (pullback.fst z s) := isIso_of_isClosedImmersion_of_surjective _
  rw [← cancel_epi (pullback.fst z s)]
  simp only [pullback.condition_assoc, pullback.condition, Category.assoc, reassoc_of% hs]

theorem section_eq [ConnectedSpace S] (G : Over S) [GrpObj G] [IsAbelianScheme G] {N : ℕ}
    (hN : IsUnit (N : Γ(S, ⊤))) {a b : 𝟙_ (Over S) ⟶ G} (ha : a ^ N = 1) (hb : b ^ N = 1)
    {k : Type} [Field k] (x : Sp k ⟶ S) (h : x ≫ a.left = x ≫ b.left) : a = b := by
  obtain ⟨-, hfin, het⟩ := GrpTangent.finiteEtale_mulN_torsion G hN
  obtain ⟨a', rfl, -⟩ := LatticeTorsion.existsUnique_torsion G N a ha
  obtain ⟨b', rfl, -⟩ := LatticeTorsion.existsUnique_torsion G N b hb
  have hx : ((toUnit (Over.mk x) ≫ a') ≫ torsion.ι G N) = (toUnit (Over.mk x) ≫ b') ≫ torsion.ι G N := by
    rw [Category.assoc, Category.assoc]
    exact Over.OverMorphism.ext h
  have hpow : ((toUnit (Over.mk x) ≫ a') ≫ torsion.ι G N) ^ N = 1 := by
    rw [Category.assoc, ← MonObj.comp_pow, ha, MonObj.comp_one]
  have hab : toUnit (Over.mk x) ≫ a' = toUnit (Over.mk x) ≫ b' :=
    (LatticeTorsion.existsUnique_torsion G N _ hpow).unique rfl hx.symm
  have : a' = b' := Over.OverMorphism.ext
    (eq_of_preconnected_of_unramified (T := S) (torsion G N).hom ((Over.w a').trans (Over.w b').symm) x
      (congrArg CommaMorphism.left hab))
  rw [this]

end GlobalTheory.HkFam.ListedSubgroup

namespace GlobalTheory.HkFam


open ListedSubgroup in
theorem exists_subgroup_eq_range_of_lists :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ) (S : Scheme.{0}) [ConnectedSpace S] (t : SAB H S) (σ : Fin n → (𝟙_ (Over S) ⟶ t.G)) (K : Set t.G.left), IsProper t.G.hom → IsUnit (p : Γ(S, ⊤)) → Lists (p ^ 2) σ K → HeckeSet D t 𝔓 p i K → ∃ C : Subgroup (𝟙_ (Over S) ⟶ t.G), (C : Set _) = Set.range σ := by
  intro E _ _ _ H D 𝔓 p i n S _ t σ K hpr hp ⟨hσ, hK, _⟩ hH
  have hab : IsAbelianScheme t.G := ⟨t.comm, t.semi.smooth, hpr, t.semi.geomConnected⟩
  have hN : IsUnit ((p ^ 2 : ℕ) : Γ(S, ⊤)) := by
    rw [Nat.cast_pow]
    exact hp.pow 2
  obtain ⟨s₀⟩ : Nonempty S := inferInstance
  let k : Type := AlgebraicClosure (S.residueField s₀)
  let x : Sp k ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s₀) k)) ≫ S.fromSpecResidueField s₀
  obtain ⟨C, hC, -⟩ := hH k x
  obtain ⟨q⟩ : Nonempty (Sp k) := inferInstance
  have hmem : ∀ j, toUnit (Over.mk x) ≫ σ j ∈ C := fun j => by
    rw [hC, hK]
    rintro _ ⟨y, rfl⟩
    exact Set.mem_iUnion.2 ⟨j, x y, (Scheme.Hom.comp_apply x (σ j).left y).symm⟩
  have key : ∀ a : 𝟙_ (Over S) ⟶ t.G, a ^ (p ^ 2) = 1 → toUnit (Over.mk x) ≫ a ∈ C → a ∈ Set.range σ := by
    intro a ha h
    rw [hC, hK] at h
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (h ⟨q, rfl⟩)
    have h1 := eq_comp_section t.G.hom (σ j).left (Over.w (σ j)) _ q hj
    rw [Over.w (toUnit (Over.mk x) ≫ a)] at h1
    exact ⟨j, (section_eq t.G hN ha (hσ j) x h1).symm⟩
  refine ⟨{ carrier := Set.range σ, mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, rfl⟩
  · rintro _ _ ⟨j, rfl⟩ ⟨j', rfl⟩
    refine key _ (by rw [mul_pow, hσ, hσ, _root_.one_mul]) ?_
    rw [MonObj.comp_mul]
    exact C.mul_mem (hmem j) (hmem j')
  · refine key _ (one_pow _) ?_
    rw [MonObj.comp_one]
    exact C.one_mem
  · rintro _ ⟨j, rfl⟩
    refine key _ (by rw [inv_pow, hσ, inv_one]) ?_
    rw [GrpObj.comp_inv]
    exact C.inv_mem (hmem j)

end GlobalTheory.HkFam
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

theorem etSet_of_lists : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (φ : G'.left ⟶ G.left) (N n : ℕ) (σ : Fin n → (𝟙_ (Over S') ⟶ G')) (K : Set G.left), IsAbelianScheme G → IsGrpPullback G' G f φ → IsUnit (N : Γ(S, ⊤)) → IsFinite f → Etale f → Surjective f → Lists N σ (φ ⁻¹' K) → EtSet G K := by
  intro S S' f G G' _ _ φ N n σ K hG h hN hfin het hsurj hL
  obtain ⟨hpow, hK, -⟩ := hL
  obtain ⟨-, hWf, hWe⟩ := GrpTangent.finiteEtale_mulN_torsion G hN
  have := hG.proper
  let T : Over S := Over.mk ((𝟙_ (Over S')).hom ≫ f)
  have hTf : IsFinite T.hom := by
    change IsFinite (𝟙 S' ≫ f); infer_instance
  have hTe : Etale T.hom := by
    change Etale (𝟙 S' ≫ f); infer_instance
  let ρ : (𝟙_ (Over S') ⟶ G') →* (T ⟶ G) :=
    MonoidHom.mk' (fun x => Over.homMk (x.left ≫ φ) (by
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w x]; rfl))
      fun x y => Over.OverMorphism.ext (h.2 _ x y _ _ rfl rfl).symm
  have hρ : ∀ j, ρ (σ j) ^ N = 1 := fun j => by rw [← map_pow, hpow, map_one]
  choose τ hτ using fun j => (LatticeTorsion.existsUnique_torsion G N (ρ (σ j)) (hρ j)).exists
  have hτl : ∀ j, (τ j).left ≫ (torsion.ι G N).left = (σ j).left ≫ φ := fun j =>
    congrArg (fun z => z.left) (hτ j)
  have hτf : ∀ j, IsFinite (τ j).left := fun j => by
    have : IsFinite ((τ j).left ≫ (torsion G N).hom) := by rw [Over.w]; exact hTf
    exact IsFinite.of_comp _ (torsion G N).hom
  have hτe : ∀ j, Etale (τ j).left := fun j => by
    have : Etale ((τ j).left ≫ (torsion G N).hom) := by rw [Over.w]; exact hTe
    exact Etale.of_comp _ (torsion G N).hom
  have hop : IsOpen (⋃ j, Set.range (τ j).left) :=
    isOpen_iUnion fun j => (τ j).left.isOpenMap.isOpen_range
  have hcl : IsClosed (⋃ j, Set.range (τ j).left) :=
    isClosed_iUnion_of_finite fun j => (τ j).left.isClosedMap.isClosed_range
  let U : (torsion G N).left.Opens := ⟨_, hop⟩
  have hU : IsClosedImmersion U.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hcl)
  have hη : IsClosedImmersion η[G].left := by
    have : IsClosedImmersion (η[G].left ≫ G.hom) := by
      rw [Over.w]; exact inferInstanceAs (IsClosedImmersion (𝟙 S))
    exact IsClosedImmersion.of_comp _ G.hom
  have hι : IsClosedImmersion (torsion.ι G N).left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (GrpTangent.isPullback_torsion G N).flip hη
  have hφ : Surjective φ := MorphismProperty.of_isPullback (P := @Surjective) h.1.flip hsurj
  refine ⟨Over.mk (U.ι ≫ (torsion G N).hom), Over.homMk (U.ι ≫ (torsion.ι G N).left) (by simp), ?_, ?_, ?_, ?_⟩
  · change IsFinite (U.ι ≫ _); infer_instance
  · change Etale (U.ι ≫ _); infer_instance
  · change IsClosedImmersion (U.ι ≫ _); infer_instance
  · change Set.range (U.ι ≫ (torsion.ι G N).left) = K
    rw [← Set.image_preimage_eq K φ.surjective, hK, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι]
    change _ '' (⋃ j, Set.range (τ j).left) = _
    rw [Set.image_iUnion, Set.image_iUnion]
    refine Set.iUnion_congr fun j => ?_
    rw [← Set.range_comp, ← Set.range_comp, ← TopCat.coe_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
      ← Scheme.Hom.comp_base, hτl]

end GlobalTheory.HkFam
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section
namespace GlobalTheory.KSInh

variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g)

theorem dom_id (W : A₀.left.Opens) : dom u (𝟙 _) W = {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ W} := by
  ext z
  unfold dom
  simp only [Category.comp_id]

theorem fn_id (W : A₀.left.Opens) (f : Γ(A₀.left, W)) :
    fn u (𝟙 _) W f = fun z => valAt' (u.ex z).left W f := by
  funext z
  unfold fn
  rw [Category.comp_id]

theorem isOpen_dom (W : A₀.left.Opens) : IsOpen (dom u (𝟙 _) W) := by
  rw [dom_id]
  exact (u.hol W 0).1

theorem differentiableOn_fn (W : A₀.left.Opens) (f : Γ(A₀.left, W)) :
    DifferentiableOn ℂ (fn u (𝟙 _) W f) (dom u (𝟙 _) W) := by
  rw [dom_id, fn_id]
  exact (u.hol W f).2

theorem differentiableAt_fn (W : A₀.left.Opens) (f : Γ(A₀.left, W)) {z : Fin g → ℂ} (hz : z ∈ dom u (𝟙 _) W) :
    DifferentiableAt ℂ (fn u (𝟙 _) W f) z :=
  (differentiableOn_fn u W f).differentiableAt ((isOpen_dom u W).mem_nhds hz)

theorem ex_add_period (l : u.Λ) (z : Fin g → ℂ) : u.ex (z + l) = u.ex z := by
  rw [u.ex_add, (u.ker _).2 l.2, _root_.mul_one]

theorem ksRel_const (w : Fin g → ℂ) :
    KSRel u A₀.hom (𝟙 _) (fun _ => 0) 0 (fun z W f => fderiv ℂ (fn u (𝟙 _) W f) z w) := by
  refine { der := ?der, base := ?base, hol := ?hol, per := ?per }
  case der =>
    intro z
    have hd : ∀ (W : A₀.left.Opens) (k : Γ(A₀.left, W)), ⊤ ≤ ((u.ex z).left ≫ 𝟙 _) ⁻¹ᵁ W →
        DifferentiableAt ℂ (fn u (𝟙 _) W k) z :=
      fun W k hW => differentiableAt_fn u W k hW
    refine ⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' h hW' f => ?_⟩
    · have e : fn u (𝟙 _) W (f + f') = fn u (𝟙 _) W f + fn u (𝟙 _) W f' := by
        funext y
        simp only [fn, valAt', Pi.add_apply]
        split_ifs with hy
        · simp only [valAt, map_add (f := _)]
        · exact (add_zero 0).symm
      show fderiv ℂ (fn u (𝟙 _) W (f + f')) z w =
        fderiv ℂ (fn u (𝟙 _) W f) z w + fderiv ℂ (fn u (𝟙 _) W f') z w
      rw [e, fderiv_add (hd W f hW) (hd W f' hW)]
      rfl
    · have e : fn u (𝟙 _) W (f * f') = fn u (𝟙 _) W f * fn u (𝟙 _) W f' := by
        funext y
        simp only [fn, valAt', Pi.mul_apply]
        split_ifs with hy
        · simp only [valAt, map_mul]
        · exact (mul_zero 0).symm
      show fderiv ℂ (fn u (𝟙 _) W (f * f')) z w =
        fn u (𝟙 _) W f z * fderiv ℂ (fn u (𝟙 _) W f') z w + fn u (𝟙 _) W f' z * fderiv ℂ (fn u (𝟙 _) W f) z w
      rw [e, fderiv_mul (hd W f hW) (hd W f' hW)]
      rfl
    · show fderiv ℂ (fn u (𝟙 _) W' (resG A₀.left h f)) z w = fderiv ℂ (fn u (𝟙 _) W f) z w
      have hev : fn u (𝟙 _) W' (resG A₀.left h f) =ᶠ[nhds z] fn u (𝟙 _) W f := by
        filter_upwards [(isOpen_dom u W').mem_nhds hW'] with y hy
        have hyW' : ⊤ ≤ ((u.ex y).left ≫ 𝟙 _) ⁻¹ᵁ W' := hy
        have hy' : ⊤ ≤ ((u.ex y).left ≫ 𝟙 _) ⁻¹ᵁ W := hyW'.trans (Scheme.Hom.preimage_mono _ h)
        simp only [fn, valAt', dite_eq_left hyW', dite_eq_left hy']
        unfold valAt resG
        have key : A₀.left.presheaf.map (homOfLE h).op ≫ Scheme.Hom.appLE ((u.ex y).left ≫ 𝟙 _) W' ⊤ hyW' =
            Scheme.Hom.appLE ((u.ex y).left ≫ 𝟙 _) W ⊤ hy' :=
          Scheme.Hom.map_appLE _ _ _
        rw [← key]
        rfl
      rw [hev.fderiv_eq]
  case base =>
    intro z r
    show fderiv ℂ (fn u (𝟙 _) ⊤ (constFn A₀.hom ⊤ r)) z w = 0
    obtain ⟨K, hK⟩ : ∃ K : ℂ, ∀ y, fn u (𝟙 _) ⊤ (constFn A₀.hom ⊤ r) y = K := by
      refine ⟨(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom
        ((Scheme.Hom.appLE (𝟙_ (Over (Sp ℂ))).hom ⊤ ⊤ (Scheme.Hom.preimage_top _).ge).hom
          ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r)), fun y => ?_⟩
      have ht : ⊤ ≤ ((u.ex y).left ≫ 𝟙 _) ⁻¹ᵁ (⊤ : A₀.left.Opens) := (Scheme.Hom.preimage_top _).ge
      have key : Scheme.Hom.appLE A₀.hom ⊤ ⊤ (Scheme.Hom.preimage_top _).ge ≫ Scheme.Hom.appLE ((u.ex y).left ≫ 𝟙 _) ⊤ ⊤ ht =
          Scheme.Hom.appLE (𝟙_ (Over (Sp ℂ))).hom ⊤ ⊤ (Scheme.Hom.preimage_top _).ge := by
        rw [Scheme.Hom.appLE_comp_appLE]
        congr 1
        simp
      simp only [fn, valAt', dite_eq_left ht]
      unfold valAt constFn
      rw [← key]
      rfl
    have e : fn u (𝟙 _) ⊤ (constFn A₀.hom ⊤ r) = fun _ => K := funext hK
    rw [e]
    simp
  case hol =>
    intro W f
    exact ((cauchyRiemann_iff_differentiableOn_complex g _ _ (isOpen_dom u W)).2 (differentiableOn_fn u W f)).2 w
  case per =>
    intro l W f z _
    show fderiv ℂ (fn u (𝟙 _) W f) (z + l) w =
      fderiv ℂ (fn u (𝟙 _) W f) z w + fderiv ℂ (fn u (𝟙 _) W f) z ((0 : Matrix (Fin g) (Fin g) ℂ).mulVec (star (l : Fin g → ℂ)))
    have hp : (fun y => fn u (𝟙 _) W f (y + l)) = fn u (𝟙 _) W f := by
      funext y
      unfold fn
      rw [ex_add_period]
    rw [Matrix.zero_mulVec, map_zero, add_zero, ← fderiv_comp_add_right, hp]

theorem exists_goodU_ksRel : ThetaUnifAV → ∀ P₀ : Out.PolAV (Sp ℂ), ∃ (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ ∧ ∀ w : Fin P₀.g → ℂ, KSRel u P₀.A.hom (𝟙 _) (fun _ => 0) 0 (fun z W f => fderiv ℂ (fn u (𝟙 _) W f) z w) := by
  intro hT P₀
  obtain ⟨rig, hrig⟩ : ∃ rig : LB.Gen (P₀.L.pull (eSec P₀.A)), rig.IsGen := P₀.rigid
  obtain ⟨u, Hm, χ, _, hAH, -, ht₁, ht₂, hend, hth, -⟩ := hT P₀ rig hrig
  exact ⟨u, Hm, χ, ⟨hAH, ht₁, ht₂, hend, fun n θ hθ => ((hth n).2 θ hθ).exists⟩, fun w => ksRel_const u w⟩

end GlobalTheory.KSInh
end
end
