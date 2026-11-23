module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle854
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle862
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle480
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle950
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle916
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle925
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle951
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle952
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle932
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle953
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle014
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle003
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open IsLocalRing
universe u

theorem _root_.GlobalTheory.T.exists_sigmaStable_summand_from_lifted_eigenCoords : ∀ {C : Type} [CommRing C] (I : Ideal C), I ^ 2 = ⊥ →
  ∀ {A : Type} [CommRing A] {H : Type u} [AddCommGroup H] [Module C H]
  (σ : A →+* Module.End C H), (letI := GlobalTheory.HTSummand.tensorModOf σ; Module.Projective (C ⊗[ℤ] A) H) →
  ∀ (a : ℕ) (χ : Fin a → A →+* C) (π : Module.End C H), π * π = π → (∀ c, σ c * π = π * σ c) →
  ∀ (F : Submodule C H), I • ⊤ ≤ F →
  ∀ (n : ℕ) (κ : Fin n → Fin a) (ℓ : Fin n → H →ₗ[C] C ⧸ I) (y : Fin n → H),
    (∀ k c x, ℓ k (σ c x) = Ideal.Quotient.mk I (χ (κ k) c) * ℓ k x) →
    (∀ x ∈ LinearMap.range π, x ∈ F ↔ ∀ k, ℓ k x = 0) →
    (∀ k, y k ∈ LinearMap.range π) → (∀ j k, ℓ j (y k) = if j = k then 1 else 0) →
  ∃ G₀ M₀ : Submodule C H, G₀ ⊓ M₀ = ⊥ ∧ G₀ ⊔ M₀ = LinearMap.range π ∧ (∀ c, ∀ x ∈ G₀, σ c x ∈ G₀) ∧
    G₀ ⊔ I • LinearMap.range π = F ⊓ LinearMap.range π ∧
    ∀ d ∈ LinearMap.range π, ∃ w : Fin a → H, (∀ i c, σ c (w i) - χ i c • w i ∈ G₀) ∧ d - ∑ i, w i ∈ G₀ := by
  first | exact @GlobalTheory.HTSummand.summand_of_liftedCoords | exact GlobalTheory.HTSummand.summand_of_liftedCoords | (intros; apply GlobalTheory.HTSummand.summand_of_liftedCoords <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj

namespace GlobalTheory.PureTower

open ReciprocityTheory.ChartRestriction.G.Out (thick thickTrans thickObj thickMap thickTrans_comp)

theorem exists_end {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (W : G ⟶ G) [IsMonHom W] :
    ∃ U : G' ⟶ G', IsMonHom U ∧ U.left ≫ φ = φ ≫ W.left := by
  let U : G' ⟶ G' := Over.homMk (h.1.lift (φ ≫ W.left) G'.hom (by rw [Category.assoc, Over.w, h.1.w]))
    (h.1.lift_snd _ _ _)
  have e : U.left ≫ φ = φ ≫ W.left := h.1.lift_fst _ _ _
  exact ⟨U, Out.PullGtPf.isMonHom_of_grpPullback h h W U e, e⟩

variable {T : Type} [CommRing T] (I : Ideal T)

theorem thickMap_fst (e : ℕ) (A : Over (Sp T)) :
    thickMap T I e A ≫ pullback.fst A.hom (thick T I (e + 1)) = pullback.fst A.hom (thick T I e) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem thickMap_hom (e : ℕ) (A : Over (Sp T)) :
    thickMap T I e A ≫ (thickObj T I (e + 1) A).hom = (thickObj T I e A).hom ≫ thickTrans T I e :=
  pullback.lift_snd _ _ _

theorem isGrpPullback_thickMap (e : ℕ) (A : Over (Sp T)) [GrpObj A] :
    IsGrpPullback (thickObj T I e A) (thickObj T I (e + 1) A) (thickTrans T I e) (thickMap T I e A) :=
  (isGrpPullback_pullback A _).cancel
    ((isGrpPullback_pullback A _).congr (thickTrans_comp T I e).symm (thickMap_fst I e A).symm) (thickMap_hom I e A)

theorem ker_factor_sq (e : ℕ) :
    RingHom.ker (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) : I ^ (e + 1 + 1) ≤ I ^ (e + 1))) ^ 2
      = ⊥ := by
  rw [pow_two, eq_bot_iff, Ideal.mul_le]
  intro x hx y hy
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hx hy
  rw [Ideal.mem_bot, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, pow_succ]
  exact Ideal.mul_mem_mul hx (Ideal.pow_le_self (Nat.succ_ne_zero e) hy)

variable {S : Type} [CommRing S] {G : Over (Sp S)} [GrpObj G]

theorem isGrpPullback_red {a : S →+* T} {A : Over (Sp T)} [GrpObj A] {φ : A.left ⟶ G.left}
    (h : IsGrpPullback A G (spMap a) φ) (e : ℕ) :
    IsGrpPullback (thickObj T I e A) G (spMap ((Ideal.Quotient.mk (I ^ (e + 1))).comp a))
      (pullback.fst A.hom (thick T I e) ≫ φ) :=
  ((isGrpPullback_pullback A _).comp h).congr (by rw [← Spec.map_comp]; rfl) rfl

theorem exists_end_red {a : S →+* T} {A : Over (Sp T)} [GrpObj A] {φ : A.left ⟶ G.left}
    (h : IsGrpPullback A G (spMap a) φ) (W : G ⟶ G) [IsMonHom W] :
    ∃ U : ∀ e, thickObj T I e A ⟶ thickObj T I e A, (∀ e, IsMonHom (U e)) ∧
      (∀ e, (U e).left ≫ pullback.fst A.hom (thick T I e) ≫ φ = (pullback.fst A.hom (thick T I e) ≫ φ) ≫ W.left) ∧
      ∀ e, thickMap T I e A ≫ (U (e + 1)).left = (U e).left ≫ thickMap T I e A := by
  choose U hU eU using fun e => exists_end (isGrpPullback_red I h e) W
  refine ⟨U, hU, eU, fun e => (isGrpPullback_red I h (e + 1)).1.hom_ext ?_ ?_⟩
  · rw [Category.assoc, eU, Category.assoc (U e).left, ← Category.assoc (thickMap T I e A),
      ← Category.assoc (thickMap T I e A), thickMap_fst, eU]
  · rw [Category.assoc, Over.w, Category.assoc, thickMap_hom, ← Category.assoc, Over.w]

theorem existsUnique_hom (hF : GlobalTheory.Published.FormalAlgebraisation) (hM : GlobalTheory.Published.GrothendieckMessing) {g : ℕ}
    (hG : IsAbelianScheme G) (hg : SmoothOfRelativeDimension g G.hom) (W : G ⟶ G) [IsMonHom W] {r s : S}
    (hW : IsPureBC G W r s) [IsNoetherianRing T] (hI : IsAdicComplete I T) {p : ℕ} (hp : p.Prime) (hpI : (p : T) ∈ I)
    {a b : S →+* T} (hab : ∀ x, a x - b x ∈ I) (hu : IsUnit (a r - b s)) {A B : Over (Sp T)} [GrpObj A] [GrpObj B]
    {φ : A.left ⟶ G.left} {ψ : B.left ⟶ G.left} (hA : IsGrpPullback A G (spMap a) φ)
    (hB : IsGrpPullback B G (spMap b) ψ) :
    ∃! F : A ⟶ B, IsMonHom F ∧ ∀ (X : Scheme.{0}) (x : X ⟶ A.left) (t : X ⟶ Sp (T ⧸ I ^ (0 + 1))),
      x ≫ A.hom = t ≫ thick T I 0 → x ≫ F.left ≫ ψ = x ≫ φ := by
  obtain ⟨U, hU, eU, cU⟩ := exists_end_red I hA W
  obtain ⟨V, hV, eV, cV⟩ := exists_end_red I hB W
  have rA := isGrpPullback_red I hA
  have rB := isGrpPullback_red I hB
  have e0 : (Ideal.Quotient.mk (I ^ (0 + 1))).comp a = (Ideal.Quotient.mk (I ^ (0 + 1))).comp b :=
    RingHom.ext fun x => Ideal.Quotient.eq.2 (by simpa using hab x)
  obtain ⟨f₀, hf₀, ef₀⟩ := grpPullback_iso (rA 0) ((rB 0).congr (by rw [e0]) rfl)
  let P : ℕ → Type := fun e => {f : thickObj T I e A ⟶ thickObj T I e B // IsMonHom f ∧ U e ≫ f = f ≫ V e}
  have step : ∀ (e : ℕ) (f : P e), ∃ f' : P (e + 1), thickMap T I e A ≫ f'.1.left = f.1.left ≫ thickMap T I e B ∧
      ∀ k : thickObj T I (e + 1) A ⟶ thickObj T I (e + 1) B, IsMonHom k →
        thickMap T I e A ≫ k.left = f.1.left ≫ thickMap T I e B → k = f'.1 := by
    intro e f
    have := f.2.1
    obtain ⟨k, h₁, h₂, h₃, h₄⟩ := GlobalTheory.T.pure_endomorphism_hom_lift_square_zero hM p hp _ _
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) : I ^ (e + 1 + 1) ≤ I ^ (e + 1)))
      ⟨e + 1 + 1, by
        rw [← map_natCast (Ideal.Quotient.mk (I ^ (e + 1 + 1))), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.pow_mem_pow hpI _⟩
      (Ideal.Quotient.factor_surjective _) (ker_factor_sq I e) g g _ _ _ _ _ _
      (PolPull.isAbelianScheme_of_isGrpPullback hG (rA (e + 1)))
      ((smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (rA (e + 1)).1 hg)
      (PolPull.isAbelianScheme_of_isGrpPullback hG (rB (e + 1)))
      ((smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (rB (e + 1)).1 hg)
      (isGrpPullback_thickMap I e A) (isGrpPullback_thickMap I e B) (U (e + 1)) (V (e + 1)) (U e) (V e) (cU e) (cV e)
      _ _ _ _ (hW _ _ _ _ (rA (e + 1)) _ (eU _)) (hW _ _ _ _ (rB (e + 1)) _ (eV _))
      (by simpa using hu.map (Ideal.Quotient.mk (I ^ (e + 1 + 1)))) f.1 f.2.2
    exact ⟨⟨k, h₁, h₃⟩, h₂, h₄⟩
  choose nx h₁ h₂ using step
  have c₀ : U 0 ≫ f₀.hom = f₀.hom ≫ V 0 := Over.OverMorphism.ext ((rB 0).1.hom_ext
    (by rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, ef₀, eU, eV, ← Category.assoc f₀.hom.left,
      ef₀]) (by rw [Over.w, Over.w]))
  let f : ∀ e, P e := fun e => Nat.rec ⟨f₀.hom, hf₀, c₀⟩ nx e
  obtain ⟨F, hF₁, hF₂, hF₃⟩ := GlobalTheory.grpHom_algebraise hF.1 T I hI A B
    (PolPull.isAbelianScheme_of_isGrpPullback hG hA).proper (PolPull.isAbelianScheme_of_isGrpPullback hG hB).proper
    (fun e => thickObj T I e A) (fun e => thickObj T I e B) (fun e => thickMap T I e A) (fun e => thickMap T I e B)
    _ _ (fun e => isGrpPullback_pullback A _) (fun e => thickMap_fst I e A) (fun e => isGrpPullback_pullback B _)
    (fun e => thickMap_fst I e B) (fun e => (f e).1) (fun e => (f e).2.1) (fun e => h₁ e (f e))
  refine ⟨F, ⟨hF₁, fun X x t ht => ?_⟩, fun K ⟨hK, eK⟩ => hF₃ K fun e => ?_⟩
  · have h0 : pullback.fst A.hom (thick T I 0) ≫ F.left = f₀.hom.left ≫ pullback.fst B.hom (thick T I 0) := hF₂ 0
    rw [← pullback.lift_fst x t ht, Category.assoc, Category.assoc, ← Category.assoc _ F.left, h0, Category.assoc, ef₀]
  · have n : ∀ e, ((Over.pullback (thick T I e)).map K).left ≫ pullback.fst B.hom (thick T I e) =
        pullback.fst A.hom (thick T I e) ≫ K.left := fun e => pullback.lift_fst _ _ _
    have key : ∀ e, (Over.pullback (thick T I e)).map K = (f e).1 := by
      intro e
      induction e with
      | zero =>
        refine Over.OverMorphism.ext ((rB 0).1.hom_ext ?_ (by rw [Over.w, Over.w]))
        rw [← Category.assoc, n, Category.assoc, eK _ _ _ pullback.condition]
        exact ef₀.symm
      | succ e ih =>
        refine h₂ e (f e) _ inferInstance ?_
        rw [← ih]
        refine (isGrpPullback_pullback B (thick T I (e + 1))).1.hom_ext ?_ ?_
        · rw [Category.assoc, n, ← Category.assoc, thickMap_fst, Category.assoc, thickMap_fst, n]
        · rw [Category.assoc, Over.w, Category.assoc, thickMap_hom, thickMap_hom, ← Category.assoc, Over.w]
    rw [← key, n]

theorem exists_isGrpPullback_of_congr : GlobalTheory.Published.FormalAlgebraisation → GlobalTheory.Published.GrothendieckMessing → ∀ (S : Type) [CommRing S] (G : Over (Sp S)) [GrpObj G] (g : ℕ), IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → ∀ (W : G ⟶ G) [IsMonHom W] (r s : S), IsPureBC G W r s → ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T], IsAdicComplete (IsLocalRing.maximalIdeal T) T → ∀ p : ℕ, p.Prime → (p : T) ∈ IsLocalRing.maximalIdeal T → ∀ a b : S →+* T, (∀ x, a x - b x ∈ IsLocalRing.maximalIdeal T) → IsUnit (a (r - s)) → ∀ (A : Over (Sp T)) [GrpObj A] (φ : A.left ⟶ G.left), IsGrpPullback A G (spMap a) φ → ∃ φ' : A.left ⟶ G.left, IsGrpPullback A G (spMap b) φ' ∧ ∀ x : Sp (IsLocalRing.ResidueField T) ⟶ A.left, x ≫ A.hom = spMap (IsLocalRing.residue T) → x ≫ φ = x ≫ φ' := by
  intro hF hM S _ G _ g hG hg W _ r s hW T _ _ _ hI p hp hpI a b hab hu A _ φ hA
  have hB := isGrpPullback_pullback G (spMap b)
  have hba : ∀ x, b x - a x ∈ IsLocalRing.maximalIdeal T := fun x => by
    simpa using neg_mem (hab x)
  have un : ∀ y z : T, IsUnit y → z ∈ IsLocalRing.maximalIdeal T → IsUnit (y + z) := fun y z hy hz => by
    by_contra h
    exact (IsLocalRing.mem_maximalIdeal y).1
      (by simpa using sub_mem ((IsLocalRing.mem_maximalIdeal _).2 h) hz) hy
  rw [map_sub] at hu
  have u₁ : IsUnit (a r - b s) := by simpa using un _ _ hu (hab s)
  have u₂ : IsUnit (b r - a s) := by
    have := un _ _ hu (hba r)
    rwa [add_comm, sub_add_sub_cancel] at this
  have u₃ : IsUnit (b r - b s) := by simpa using un _ _ u₂ (hab s)
  obtain ⟨F, ⟨hF₁, hF₂⟩, -⟩ := existsUnique_hom _ hF hM hG hg W hW hI hp hpI hab u₁ hA hB
  obtain ⟨K, ⟨hK₁, hK₂⟩, -⟩ := existsUnique_hom _ hF hM hG hg W hW hI hp hpI hba u₂ hB hA
  have FK : F ≫ K = 𝟙 A := (existsUnique_hom _ hF hM hG hg W hW hI hp hpI (fun x => by simp) hu hA hA).unique
    ⟨inferInstance, fun X x t ht => by
      rw [Over.comp_left, Category.assoc, ← Category.assoc x, hK₂ _ _ t (by rw [Category.assoc, Over.w, ht]),
        Category.assoc, hF₂ _ _ t ht]⟩ ⟨inferInstance, fun X x t ht => by simp⟩
  have KF : K ≫ F = 𝟙 _ := (existsUnique_hom _ hF hM hG hg W hW hI hp hpI (fun x => by simp) u₃ hB hB).unique
    ⟨inferInstance, fun X x t ht => by
      rw [Over.comp_left, Category.assoc, ← Category.assoc x, hF₂ _ _ t (by rw [Category.assoc, Over.w, ht]),
        Category.assoc, hK₂ _ _ t ht]⟩ ⟨inferInstance, fun X x t ht => by simp⟩
  refine ⟨F.left ≫ _, ((isGrpPullback_of_iso ⟨F, K, FK, KF⟩).comp hB).congr (Category.id_comp _) rfl,
    fun x hx => (hF₂ _ x (spMap (Ideal.Quotient.lift _ (IsLocalRing.residue T) fun y hy =>
      (IsLocalRing.residue_eq_zero_iff y).2 (by simpa using hy))) ?_).symm⟩
  rw [hx, ← Spec.map_comp]
  rfl

end GlobalTheory.PureTower
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.Dieu.EtFromConn

theorem _root_.GlobalTheory.T.etaleDieudonneTranspose_eq_rigidifiedExtensionPullback : ∀ (p : ℕ) [Fact p.Prime] (B : Base p (fun _ _ G => G.IsConn)) (k k' : Type) [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p] [PerfectRing k' p] (σ : k →+* k') (G' : PDivGroup p k') (G : PDivGroup p k) (h' : G'.IsEt) (h : G.IsEt) (s : SemiHom σ G' G) (l : Mod B G h) (l' : Mod B G' h'), IsTr B σ h' h s l l' → red B G' h' l' = s.rig (red B G h l) := by
  first | exact @GlobalTheory.Dieu.EtFromConn.red_of_isTr | exact GlobalTheory.Dieu.EtFromConn.red_of_isTr | (intros; apply GlobalTheory.Dieu.EtFromConn.red_of_isTr <;> assumption)
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.Dieu.EtFromConn

theorem _root_.GlobalTheory.T.etaleDieudonneTranspose_ofHom_eq_comp_dualHom : ∀ (p : ℕ) [Fact p.Prime] (B : Base p (fun _ _ G => G.IsConn)) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (hG : G.IsEt) (hH : H.IsEt) (f : G ⟶ H) (l : Mod B H hH), IsTr B (RingHom.id k) hG hH (SemiHom.ofHom f) l (l ∘ₗ B.map (dual_conn hH) (dual_conn hG) (dualHom G H f)) := by
  first | exact @GlobalTheory.Dieu.EtFromConn.isTr_ofHom | exact GlobalTheory.Dieu.EtFromConn.isTr_ofHom | (intros; apply GlobalTheory.Dieu.EtFromConn.isTr_ofHom <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.oLinearLevel_pullback_universal_factorisation : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (N : ℕ) (H : Scheme.{0}) (AH : Over H) [GrpObj AH] (actH : OActN D.O AH) (Y : Over H) (u : D.La → (Y ⟶ AH)) (AE : Over Y.left) [GrpObj AE] (φE : AE.left ⟶ AH.left) (ηE : D.La → (𝟙_ (Over Y.left) ⟶ AE)), IsGrpPullback AE AH Y.hom φE → (∀ y, (ηE y).left ≫ φE = (u y).left) → (∀ (T : Over H) (u' : D.La → (T ⟶ AH)), (∀ x y, u' (x + y) = u' x * u' y) → (∀ (c : D.O) x, u' (c • x) = u' x ≫ actH.act c) → (∀ x, u' (N • x) = 1) → ∃! h : T ⟶ Y, ∀ x, h ≫ u x = u' x) → ∀ (T : Scheme.{0}) (g : T ⟶ H) (AT : Over T) [GrpObj AT] (φ : AT.left ⟶ AH.left) (act : OActN D.O AT) (eta : D.La → (𝟙_ (Over T) ⟶ AT)), IsGrpPullback AT AH g φ → (∀ a : D.O, (act.act a).left ≫ φ = φ ≫ (actH.act a).left) → EtaOK D N act eta → ∃! z : T ⟶ Y.left, z ≫ Y.hom = g ∧ ∃ ψ : AT.left ⟶ AE.left, IsGrpPullback AT AE z ψ ∧ ψ ≫ φE = φ ∧ ∀ y, (eta y).left ≫ ψ = z ≫ (ηE y).left := by
  first | (exact @GlobalTheory.UPel.HT.pullUnivP) | (exact GlobalTheory.UPel.HT.pullUnivP) | (intros; apply GlobalTheory.UPel.HT.pullUnivP  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.exists_pullback_group_oLinear_torsion_level : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (N : ℕ) (H : Scheme.{0}) (AH : Over H) [GrpObj AH] [IsCommMonObj AH] (actH : OActN D.O AH) (Y : Over H) (u : D.La → (Y ⟶ AH)), (∀ x y, u (x + y) = u x * u y) → (∀ (c : D.O) x, u (c • x) = u x ≫ actH.act c) → (∀ x, u (N • x) = 1) → ∃ (AE : Over Y.left) (_ : GrpObj AE) (_ : IsCommMonObj AE) (φE : AE.left ⟶ AH.left) (actE : OActN D.O AE) (ηE : D.La → (𝟙_ (Over Y.left) ⟶ AE)), IsGrpPullback AE AH Y.hom φE ∧ (∀ a : D.O, (actE.act a).left ≫ φE = φE ≫ (actH.act a).left) ∧ EtaOK D N actE ηE ∧ ∀ y, (ηE y).left ≫ φE = (u y).left := by
  first | (exact @GlobalTheory.UPel.HT.LevPull.exists_pull_level) | (exact GlobalTheory.UPel.HT.LevPull.exists_pull_level) | (intros; apply GlobalTheory.UPel.HT.LevPull.exists_pull_level  <;> assumption)
end

section

open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.isNarrowRayClassLFunction_mul_prime_wideIndicator : ∀ {F : Type} [Field F] [NumberField F] (𝔪 𝔭 : Ideal (𝓞 F)), 𝔭.IsMaximal → 𝔭 ≠ ⊥ → 𝔭 ⊔ 𝔪 = ⊤ →
    ∀ (C : ClassGroup (𝓞 F)) (Z Z' : ℂ → ℂ), IsRayL 𝔪 (wideInd C) Z → IsRayL 𝔪 (wideInd (C * (cls 𝔭)⁻¹)) Z' →
    IsRayL (𝔪 * 𝔭) (wideInd C) (fun s => Z s - ((Ideal.absNorm 𝔭 : ℕ) : ℂ) ^ (-s) * Z' s) := by
  first | exact @GlobalTheory.isRayL_mul_prime_wideInd | exact GlobalTheory.isRayL_mul_prime_wideInd | (intros; apply GlobalTheory.isRayL_mul_prime_wideInd <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_homFixRep_iso_of_universal : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (hL : L.IsLB) (hM : M.IsLB) (X : Scheme.{0}) (u : HomGlue.Pt A B L M X), (∀ (Z : Scheme.{0}) (x : HomGlue.Pt A B L M Z), ∃! c : Z ⟶ X, u.map hL hM c = x) → ∃ (R : HomFixRep A B L M) (e : R.H ≅ X), e.hom ≫ u.t = R.π := by
  first | exact @GlobalTheory.EndLoc.HomGlue.homFixRep_of_universal | exact GlobalTheory.EndLoc.HomGlue.homFixRep_of_universal | (intros; apply GlobalTheory.EndLoc.HomGlue.homFixRep_of_universal; all_goals assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_universal_pt_of_isGrpPullback : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (hL : L.IsLB) (hM : M.IsLB) (V : Scheme.{0}) (j : V ⟶ S) [IsOpenImmersion j] (A' B' : Over V) [GrpObj A'] [GrpObj B'] (φA : A'.left ⟶ A.left) (φB : B'.left ⟶ B.left) (R : HomFixRep A' B' (L.pull φA) (M.pull φB)), IsGrpPullback A' A j φA → IsGrpPullback B' B j φB → ∃ y : HomGlue.Pt A B L M R.H, y.t = R.π ≫ j ∧ ∀ (Z : Scheme.{0}) (x : HomGlue.Pt A B L M Z) (b : Z ⟶ V), x.t = b ≫ j → ∃! c : Z ⟶ R.H, y.map hL hM c = x := by
  first | exact @GlobalTheory.EndLoc.HomGlue.localRep_universal | exact GlobalTheory.EndLoc.HomGlue.localRep_universal | (intros; apply GlobalTheory.EndLoc.HomGlue.localRep_universal; all_goals assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

noncomputable section

namespace GlobalTheory.EffBound

open GlobalTheory.CechPic TopologicalSpace

theorem res_res_apply {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(X, U)) :
    (X.presheaf.map (homOfLE h₂).op).hom ((X.presheaf.map (homOfLE h₁).op).hom x) =
      (X.presheaf.map (homOfLE (h₂.trans h₁)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem mul_compat {X : Scheme.{0}} {A₁ A₂ B₁ B₂ : X.Opens} (s₁ : Γ(X, A₁)) (s₂ : Γ(X, A₂))
    (t₁ : Γ(X, B₁)) (t₂ : Γ(X, B₂)) (gA : Γ(X, A₁ ⊓ A₂)ˣ) (gB : Γ(X, B₁ ⊓ B₂)ˣ)
    (hs : (X.presheaf.map (homOfLE (inf_le_left : A₁ ⊓ A₂ ≤ A₁)).op).hom s₁ =
      (gA : Γ(X, A₁ ⊓ A₂)) * (X.presheaf.map (homOfLE (inf_le_right : A₁ ⊓ A₂ ≤ A₂)).op).hom s₂)
    (ht : (X.presheaf.map (homOfLE (inf_le_left : B₁ ⊓ B₂ ≤ B₁)).op).hom t₁ =
      (gB : Γ(X, B₁ ⊓ B₂)) * (X.presheaf.map (homOfLE (inf_le_right : B₁ ⊓ B₂ ≤ B₂)).op).hom t₂) :
    (X.presheaf.map (homOfLE (inf_le_left : A₁ ⊓ B₁ ⊓ (A₂ ⊓ B₂) ≤ A₁ ⊓ B₁)).op).hom
        ((X.presheaf.map (homOfLE (inf_le_left : A₁ ⊓ B₁ ≤ A₁)).op).hom s₁ *
          (X.presheaf.map (homOfLE (inf_le_right : A₁ ⊓ B₁ ≤ B₁)).op).hom t₁) =
      ((res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
          A₁ ⊓ B₁ ⊓ (A₂ ⊓ B₂) ≤ A₁ ⊓ A₂) gA *
        res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          A₁ ⊓ B₁ ⊓ (A₂ ⊓ B₂) ≤ B₁ ⊓ B₂) gB : Γ(X, A₁ ⊓ B₁ ⊓ (A₂ ⊓ B₂))ˣ) : Γ(X, A₁ ⊓ B₁ ⊓ (A₂ ⊓ B₂))) *
      (X.presheaf.map (homOfLE (inf_le_right : A₁ ⊓ B₁ ⊓ (A₂ ⊓ B₂) ≤ A₂ ⊓ B₂)).op).hom
        ((X.presheaf.map (homOfLE (inf_le_left : A₂ ⊓ B₂ ≤ A₂)).op).hom s₂ *
          (X.presheaf.map (homOfLE (inf_le_right : A₂ ⊓ B₂ ≤ B₂)).op).hom t₂) := by
  have hσ := congrArg (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left)
    (inf_le_right.trans inf_le_left) : A₁ ⊓ B₁ ⊓ (A₂ ⊓ B₂) ≤ A₁ ⊓ A₂)).op).hom hs
  have hτ := congrArg (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right)
    (inf_le_right.trans inf_le_right) : A₁ ⊓ B₁ ⊓ (A₂ ⊓ B₂) ≤ B₁ ⊓ B₂)).op).hom ht
  rw [res_res_apply, map_mul, res_res_apply] at hσ hτ
  simp only [res, Units.val_mul, Units.coe_map, MonoidHom.coe_coe, map_mul, res_res_apply]
  rw [hσ, hτ]
  ring

def tensSec {X : Scheme.{0}} {A B : LB X} (σ : LB.Sec A) (τ : LB.Sec B) : LB.Sec (tens A B) where
  f p := (X.presheaf.map (homOfLE (inf_le_left : A.U p.1 ⊓ B.U p.2 ≤ A.U p.1)).op).hom (σ.f p.1) *
    (X.presheaf.map (homOfLE (inf_le_right : A.U p.1 ⊓ B.U p.2 ≤ B.U p.2)).op).hom (τ.f p.2)
  compat p q := mul_compat _ _ _ _ _ _ (σ.compat p.1 q.1) (τ.compat p.2 q.2)

theorem germ_sec_ne_zero {X : Scheme.{0}} [IsIntegral X] {N : LB X} (σ : LB.Sec N) {j : N.ι}
    (hj : σ.f j ≠ 0) (i : N.ι) (y : X) (hy : y ∈ N.U i) : X.presheaf.germ (N.U i) y hy (σ.f i) ≠ 0 := by
  intro h0
  have hi0 : σ.f i = 0 := germ_injective_of_isIntegral X y hy (by rw [h0, map_zero])
  apply hj
  by_cases hne : (N.U j : Set X).Nonempty
  · obtain ⟨z, hz⟩ := hne
    obtain ⟨w, hwi, hwj⟩ :=
      nonempty_preirreducible_inter (N.U i).isOpen (N.U j).isOpen ⟨y, hy⟩ ⟨z, hz⟩
    apply germ_injective_of_isIntegral X w hwj
    rw [map_zero]
    have hw : w ∈ N.U i ⊓ N.U j := ⟨hwi, hwj⟩
    have e := congrArg (X.presheaf.germ (N.U i ⊓ N.U j) w hw) (σ.compat i j)
    rw [X.presheaf.germ_res_apply, hi0, map_zero, map_mul, X.presheaf.germ_res_apply] at e
    rcases mul_eq_zero.mp e.symm with h | h
    · exact absurd h (((N.g i j).isUnit.map (X.presheaf.germ (N.U i ⊓ N.U j) w hw).hom).ne_zero)
    · exact h
  · have hT : N.U j = ⊥ := by
      ext x
      simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hne ⟨x, hx⟩
    haveI : Subsingleton Γ(X, N.U j) := CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hT)
    exact Subsingleton.elim _ _

theorem eff_add {X : Scheme.{0}} [IsIntegral X] (a b : Pic X) (ha : Eff a) (hb : Eff b) : Eff (a + b) := by
  obtain ⟨A, hA, rfl, σ, j, hσ⟩ := ha
  obtain ⟨B, hB, rfl, τ, k, hτ⟩ := hb
  obtain ⟨y⟩ := (inferInstance : Nonempty X)
  have hyA : y ∈ ⨆ i, A.U i := hA.cover ▸ trivial
  have hyB : y ∈ ⨆ i, B.U i := hB.cover ▸ trivial
  obtain ⟨p, hp⟩ := Opens.mem_iSup.1 hyA
  obtain ⟨q, hq⟩ := Opens.mem_iSup.1 hyB
  refine ⟨tens A B, isLB_tens hA hB, cls_tens hA hB _, tensSec σ τ, (p, q), ?_⟩
  have hy : y ∈ A.U p ⊓ B.U q := ⟨hp, hq⟩
  intro h0
  have h0' : (X.presheaf.map (homOfLE (inf_le_left : A.U p ⊓ B.U q ≤ A.U p)).op).hom (σ.f p) *
      (X.presheaf.map (homOfLE (inf_le_right : A.U p ⊓ B.U q ≤ B.U q)).op).hom (τ.f q) = 0 := h0
  have e' := congrArg (X.presheaf.germ (A.U p ⊓ B.U q) y hy) h0'
  rw [map_mul, X.presheaf.germ_res_apply, X.presheaf.germ_res_apply, map_zero] at e'
  rcases mul_eq_zero.mp e' with h | h
  · exact germ_sec_ne_zero σ hσ p y hp h
  · exact germ_sec_ne_zero τ hτ q y hq h

end GlobalTheory.EffBound
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.EffBound

open GlobalTheory.CechPic

theorem eff_pull_of_veryAmpleBy : ∀ (R : Type) [CommRing R] {X Y : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (hH : H.IsLB), GlobalTheory.AbLaw.VeryAmpleBy f H s → ∀ (φ : Y ⟶ X), Nonempty Y → GlobalTheory.EffBound.Eff (GlobalTheory.CechPic.pull φ (GlobalTheory.CechPic.cls H hH)) := by
  intro R _ X Y f H m s hH hva φ hY
  obtain ⟨y⟩ := hY
  have hy : φ y ∈ ⨆ i, nonzeroLocus (s i) := by rw [hva.1]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  have hy' : y ∈ nonzeroLocus (GlobalTheory.secPull (s i) φ) := by
    rw [GlobalTheory.nonzeroLocus_secPull]; exact hi
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hy'
  have hne : (GlobalTheory.secPull (s i) φ).f k ≠ 0 := by
    intro h0
    rw [h0, Scheme.basicOpen_zero] at hk
    exact hk
  rw [← cls_pull hH φ (pull_isLB hH φ)]
  exact eff_of_sec _ _ _ k hne

end GlobalTheory.EffBound
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleRigid

open GlobalTheory.CechPic

def ConstSt : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A →
    ∀ (L : LB A.left) (hL : L.IsLB), Out.RelAmple A L → ∀ m : Pic A.left, ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
      ∀ ψ : A ⟶ A, IsMonHom ψ → GlobalTheory.EffBound.Eff (m - t • pull ψ.left (cls L hL)) → ψ = 1

def CubeSt : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L → ∀ (c : Pic A.left) (x y z : A ⟶ A),
      pull (x * y * z).left c + pull x.left c + pull y.left c + pull z.left c =
        pull (x * y).left c + pull (x * z).left c + pull (y * z).left c + pull (1 : A ⟶ A).left c

def FiniteOrderSt : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (L : LB A.left) (hL : L.IsLB), Out.RelAmple A L → ∀ σ : A ≅ A, IsMonHom σ.hom →
      pull σ.hom.left (cls L hL) = cls L hL → ∃ m : ℕ, m ≠ 0 ∧ (GlobalTheory.SerreField.iter σ m).hom = 𝟙 A

def SeparatedSt : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L → ∀ q : ℕ, 2 ≤ q → ∀ u : A ⟶ A,
      (∀ k : ℕ, ∃ ψ : A ⟶ A, IsMonHom ψ ∧ u = ψ ^ (q ^ k)) → u = 1

def SerreAmpleSt : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (L : LB A.left) (hL : L.IsLB), Out.RelAmple A L → ∀ N : ℕ, 3 ≤ N → (N : K) ≠ 0 →
      ∀ σ : A ≅ A, IsMonHom σ.hom → pull σ.hom.left (cls L hL) = cls L hL →
      (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Sp K) (x : Over.mk t ⟶ A), x ^ N = 1 → x ≫ σ.hom = x) →
      σ.hom = 𝟙 A


end GlobalTheory.AmpleRigid
end
end
