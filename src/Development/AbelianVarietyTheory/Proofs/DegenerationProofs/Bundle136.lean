module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle118
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle128
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenOfFrames
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMatrixBasisAllPlacesTorsionDet
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TraitSectionBasisDescendsFiniteDvrExtension
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle121
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSecOfCompatible
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle122
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsIntegralOfIsAbelianSchemeField
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle122
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

theorem _root_.GlobalTheory.T.sectionPower_calculus_geometric_fibre : ∀ (Z : Scheme.{0}) (G₀ : Over Z) [GrpObj G₀] (L₀ : LB G₀.left), L₀.IsLB → ∀ (R : Type) [CommRing R] [IsDomain R] (x : Sp (FractionRing R) ⟶ Z) (A : PolAV (Sp (FractionRing R))) (φ : A.A.left ⟶ G₀.left) (w : LB.Iso A.L (L₀.pull φ)), IsGrpPullback A.A G₀ x φ → w.IsGen → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), (∀ (T : Over Z) (p : Sp F ⟶ T.left), p ≫ T.hom = jFK (R := R) F ≫ x → ∀ s : LB.Sec (LPow G₀ L₀ (k : ℤ) T), ∃! t : SecA A F k, Thru w k (T' := TFK (R := R) F) p s t) ∧ (∀ (R' : Type) [CommRing R'] (y : Sp R' ⟶ Z) (T : Over Z) (h : Over.mk y ⟶ T) (ga : R' →+* F), spMap ga ≫ y = jFK (R := R) F ≫ x → ∀ (n : ℕ) (b : Fin n → LB.Sec (LPow G₀ L₀ (k : ℤ) T)) (c : Fin n → R') (s : LB.Sec (LPow G₀ L₀ (k : ℤ) (Over.mk y))) (bF : Fin n → SecA A F k) (t : SecA A F k), Lin G₀ L₀ k h b (fun i => fnR (c i)) s → (∀ i, Thru w k (T' := TFK (R := R) F) (spMap ga ≫ h.left) (b i) (bF i)) → Thru w k (T' := TFK (R := R) F) (T := Over.mk y) (spMap ga) s t → Cmb bF (fun i => ga (c i)) t) ∧ ∀ (K : Type) [Field K] (y : Sp K ⟶ Z) (ga : K →+* F), spMap ga ≫ y = jFK (R := R) F ≫ x → ∀ (n : ℕ) (τ : Fin n → LB.Sec (LPow G₀ L₀ (k : ℤ) (Over.mk y))) (τF : Fin n → SecA A F k), AllBasis G₀ L₀ k y τ → (∀ i, Thru w k (T' := TFK (R := R) F) (T := Over.mk y) (spMap ga) (τ i) (τF i)) → ∀ t : SecA A F k, ∃! a : Fin n → F, Cmb τF a t := by
  first | exact @GlobalTheory.OneBasis.Calc.main | exact GlobalTheory.OneBasis.Calc.main | (intros; apply GlobalTheory.OneBasis.Calc.main <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

theorem _root_.GlobalTheory.T.shortestRepresentatives_form_sum_depends_on_lattice : ∀ (X₀ : Type) [AddCommGroup X₀] [Module.Free ℤ X₀] [Module.Finite ℤ X₀] (q₀ : X₀ → ℤ) (k r : ℕ), 1 ≤ k → (∀ y, 0 ≤ q₀ y) → ∃ d C : ℕ, 1 ≤ d ∧ ∀ (X : Type) [AddCommGroup X] (Q : X → ℤ) (e : X₀ ≃+ X) (w : ℕ), 0 < w → (∀ y, Q (e y) = w * q₀ y) → ∀ (cls : Fin r → X) (mu : ℕ), Adapted k Q cls mu → (d : ℤ) * ∑ i, Q (cls i) = C * w * k := by
  first | exact @GlobalTheory.OneBasis.sum_adapted_eq | exact GlobalTheory.OneBasis.sum_adapted_eq | (intros; apply GlobalTheory.OneBasis.sum_adapted_eq <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

theorem _root_.GlobalTheory.T.exists_thetaBasis_after_every_field_extension : Laws → Laws2 → ∀ (Z : Scheme.{0}) (G₀ : Over Z) [GrpObj G₀] (L₀ : LB G₀.left), L₀.IsLB → ∀ (K : Type) [Field K] (x : Sp K ⟶ Z) (A : PolAV (Sp K)) (φ : A.A.left ⟶ G₀.left) (w : LB.Iso A.L (L₀.pull φ)), IsGrpPullback A.A G₀ x φ → w.IsGen → ∀ k : ℕ, 1 ≤ k → ∃ (r : ℕ) (τ : Fin r → LB.Sec (LPow G₀ L₀ (k : ℤ) (Over.mk x))), AllBasis G₀ L₀ k x τ := by
  first | exact @GlobalTheory.OneBasis.AllExt.exists_allBasis | exact GlobalTheory.OneBasis.AllExt.exists_allBasis | (intros; apply GlobalTheory.OneBasis.AllExt.exists_allBasis <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.Recombine
open GlobalTheory.FrameGen

variable {Z : Scheme.{0}} {G : Over Z} {L : LB G.left} {N : ℕ}

theorem exists_lin (hL : L.IsLB) {T T' : Over Z} (h : T' ⟶ T) {n : ℕ} (b : Fin n → LB.Sec (LPow G L (N : ℤ) T))
    (c : Fin n → Γ(T'.left, ⊤)) : ∃ s, Lin G L N h b c s := by
  choose b' hb' using fun i => exists_pull hL h (b i)
  refine ⟨SectionLimit.linSec (fun i => (fst T' G).left.appTop.hom (c i)) b', fun z J hJ => ?_⟩
  refine (SectionScalarValuation.sval_lin (s := SectionLimit.linSec (fun i => (fst T' G).left.appTop.hom (c i)) b')
    (fun i => (fst T' G).left.appTop.hom (c i)) b' (fun _ => rfl) (𝟙 _) z hJ).trans
    (Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) ?_ ?_)
  · exact (gs_pull (𝟙 _) (fst T' G).left z ⊤ trivial (c i)).trans (by rw [Category.id_comp])
  · exact (hb' i _ (𝟙 _) z J hJ).trans (by rw [Category.id_comp]; rfl)

section
variable {T T₁ T₂ T₃ : Over Z} {m n l : ℕ} {h₁ : T ⟶ T₁} {a : Fin m → LB.Sec (LPow G L (N : ℤ) T₁)} {h₂ : T ⟶ T₂}
  {b : Fin n → LB.Sec (LPow G L (N : ℤ) T₂)} {h₃ : T ⟶ T₃} {c : Fin l → LB.Sec (LPow G L (N : ℤ) T₃)}

theorem rel_id_iff (hL : L.IsLB) {a : Fin m → LB.Sec (LPow G L (N : ℤ) T)} {M : Matrix (Fin m) (Fin n) Γ(T.left, ⊤)} :
    Rel G L N (𝟙 _) a h₂ b M ↔ ∀ k, Lin G L N h₂ b (M k) (a k) := by
  constructor
  · intro H k z J hJ
    have := H k _ (𝟙 _) z J hJ
    simp only [Category.id_comp, ← gs_top, id_whiskerRight, Over.id_left] at this
    exact this
  · intro H k Y r z J hJ
    rw [id_whiskerRight, Over.id_left, Category.comp_id]
    exact lin_all hL (H k) r z hJ

theorem rel_inv {M : Matrix (Fin m) (Fin n) Γ(T.left, ⊤)} {V : Matrix (Fin n) (Fin m) Γ(T.left, ⊤)}
    (H : Rel G L N h₁ a h₂ b M) (e : V * M = (1 : Matrix (Fin n) (Fin n) Γ(T.left, ⊤))) : Rel G L N h₂ b h₁ a V := by
  intro k Y r z J hJ
  rw [Rel.refl (h₁ := h₂) (a := b) k Y r z J hJ, ← e]

  simp only [H _ Y r z J hJ, Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul, _root_.mul_assoc]
  exact Finset.sum_comm

theorem basisAlong_of_rel (hL : L.IsLB) {a : Fin n → LB.Sec (LPow G L (N : ℤ) T₁)} {M V : Matrix (Fin n) (Fin n) Γ(T.left, ⊤)}
    (hb : BasisAlong G L N h₂ b)
    (H : Rel G L N h₁ a h₂ b M) (e : V * M = 1) (e' : M * V = 1) : BasisAlong G L N h₁ a := by
  intro s
  obtain ⟨P, hP⟩ := exists_rel hL hb (𝟙 _) (fun _ : Fin 1 => s)
  have key : ∀ c, Lin G L N h₁ a c s → Matrix.of (fun _ : Fin 1 => c) = P * V := fun c hc => by
    have r : Rel G L N (𝟙 _) (fun _ : Fin 1 => s) h₁ a (Matrix.of fun _ : Fin 1 => c) := (rel_id_iff hL).2 fun _ => hc
    rw [hP.unique hL hb (r.trans H), Matrix.mul_assoc, e', Matrix.mul_one]
  exact ⟨(P * V) 0, (rel_id_iff hL).1 (hP.trans (rel_inv H e)) 0, fun c hc => congrFun (key c hc) 0⟩

theorem exists_common (hL : L.IsLB) {b : Fin m → LB.Sec (LPow G L (N : ℤ) T₂)} {M} (H : Rel G L N h₁ a h₃ c M)
    (H' : Rel G L N h₂ b h₃ c M) (k : Fin m) :
    ∃ s, Lin G L N h₁ (fun _ : Fin 1 => a k) (fun _ => 1) s ∧ Lin G L N h₂ (fun _ : Fin 1 => b k) (fun _ => 1) s := by
  obtain ⟨s, hs⟩ := exists_lin hL h₁ (fun _ : Fin 1 => a k) (fun _ => 1)
  refine ⟨s, hs, fun z J hJ => (hs z J hJ).trans ?_⟩
  rw [Fin.sum_univ_one, Fin.sum_univ_one]
  have := (H k _ (𝟙 _) z J hJ).trans (H' k _ (𝟙 _) z J hJ).symm
  rw [Category.id_comp, Category.id_comp] at this
  exact congrArg _ this

theorem exists_common_pull (hL : L.IsLB) {b : Fin n → LB.Sec (LPow G L (N : ℤ) T₂)} {b' : Fin m → LB.Sec (LPow G L (N : ℤ) T₂)}
    {p : T₁ ⟶ T₃} {P : Matrix (Fin m) (Fin l) Γ(T₁.left, ⊤)} {U : Matrix (Fin m) (Fin n) Γ(T₂.left, ⊤)}
    {B : Matrix (Fin n) (Fin l) Γ(T.left, ⊤)} (r₁ : Rel G L N (𝟙 _) a p c P) (r₂ : Rel G L N (𝟙 _) b' (𝟙 _) b U)
    (r₃ : Rel G L N h₂ b h₃ c B) (e₁ : h₁ ≫ p = h₃) (e₂ : P.map h₁.left.appTop.hom = U.map h₂.left.appTop.hom * B)
    (k : Fin m) :
    ∃ s, Lin G L N h₁ (fun _ : Fin 1 => a k) (fun _ => 1) s ∧ Lin G L N h₂ (fun _ : Fin 1 => b' k) (fun _ => 1) s := by
  have r₄ := r₁.pull h₁
  have r₅ := r₂.pull h₂
  rw [Category.comp_id] at r₄ r₅
  rw [e₁, e₂] at r₄
  exact exists_common hL r₄ (r₅.trans r₃) k

end

abbrev fnHom (R : Type) [CommRing R] : R →+* Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem map_fnHom {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {m n : ℕ} (M : Matrix (Fin m) (Fin n) R) :
    (M.map (fnHom R)).map (spMap f).appTop.hom = (M.map f).map (fnHom R') := by
  ext1 i j
  exact (congrArg (fun q => q.hom (M i j)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm

theorem exists_rel_id (hL : L.IsLB) {T T' : Over Z} (h : T' ⟶ T) {m n : ℕ} (b : Fin n → LB.Sec (LPow G L (N : ℤ) T))
    (M : Matrix (Fin m) (Fin n) Γ(T'.left, ⊤)) : ∃ a, Rel G L N (𝟙 _) a h b M := by
  choose a ha using fun i => exists_lin hL h b (M i)
  exact ⟨a, (rel_id_iff hL).2 ha⟩

theorem map_inv_mul {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {n : ℕ} {U : Matrix (Fin n) (Fin n) R}
    (hU : IsUnit U.det) : U⁻¹.map f * U.map f = 1 ∧ U.map f * U⁻¹.map f = 1 :=
  ⟨Matrix.map_mul.symm.trans (by rw [Matrix.nonsing_inv_mul _ hU, Matrix.map_one _ (map_zero _) (map_one _)]),
    Matrix.map_mul.symm.trans (by rw [Matrix.mul_nonsing_inv _ hU, Matrix.map_one _ (map_zero _) (map_one _)])⟩

theorem map_fnHom_mul {R W F : Type} [CommRing R] [CommRing W] [CommRing F] (f : R →+* F) (g : W →+* F) {n : ℕ}
    {P : Matrix (Fin n) (Fin n) R} {U : Matrix (Fin n) (Fin n) W} {B : Matrix (Fin n) (Fin n) F}
    (e : P.map f = U.map g * B) : (P.map (fnHom R)).map (spMap f).appTop.hom =
      (U.map (fnHom W)).map (spMap g).appTop.hom * B.map (fnHom F) := by
  rw [map_fnHom, map_fnHom, e, Matrix.map_mul]

theorem exists_recombination : ∀ (Z : Scheme.{0}) (G : Over Z) (L : LB G.left), L.IsLB → ∀ (N : ℕ) (K K₂ : Type) [Field K] [Field K₂] (x : Sp K ⟶ Z) (ie : K →+* K₂) (x₂ : Sp K₂ ⟶ Z), spMap ie ≫ x = x₂ → ∀ (n : ℕ) (τ : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk x))) (Φ : Matrix (Fin n) (Fin n) K₂), ∃ f : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk x₂)), ∀ (W : Type) [CommRing W] [IsDomain W] (gam : K₂ →+* FractionRing W) (χ : Sp W ⟶ Z) (h : spMap (gam.comp ie) ≫ x = jK W ≫ χ) (h₂ : spMap gam ≫ x₂ = jK W ≫ χ) (B : Matrix (Fin n) (Fin n) (FractionRing W)) (U : Matrix (Fin n) (Fin n) W), BasisBy G L N x (gam.comp ie) χ h τ B → IsUnit U.det → Φ.map gam = U.map (algebraMap W (FractionRing W)) * B → FrameAt G L N x₂ gam χ h₂ f := by
  intro Z G L hL N K K₂ _ _ x ie x₂ hx n τ Φ
  obtain ⟨f, r₁⟩ := exists_rel_id hL (Over.homMk (spMap ie) hx : Over.mk x₂ ⟶ Over.mk x) τ (Φ.map (fnHom K₂))
  refine ⟨f, fun W _ _ gam χ h h₂ B U H hU e => ?_⟩
  obtain ⟨b, hb, hB⟩ := H
  obtain ⟨b', r₂⟩ := exists_rel_id hL (𝟙 (Over.mk χ)) b (U.map (fnHom W))
  have r₃ : Rel G L N (Over.homMk (jK W) rfl : Over.mk (jK W ≫ χ) ⟶ Over.mk χ) b
      (Over.homMk (spMap (gam.comp ie)) h : Over.mk (jK W ≫ χ) ⟶ Over.mk x) τ (B.map (fnHom (FractionRing W))) :=
    rel_of_lin hL fun k => (hB k).imp fun _ H => H.symm
  exact ⟨b', basisAlong_of_rel hL hb r₂ (map_inv_mul (fnHom W) hU).1 (map_inv_mul (fnHom W) hU).2,
    exists_common_pull hL r₁ r₂ r₃ (Over.OverMorphism.ext (spMap_comp' ie gam).symm) (map_fnHom_mul gam _ e)⟩

end GlobalTheory.Recombine
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

theorem _root_.GlobalTheory.T.exists_global_matrix_eq_unit_det_mul_local : ∀ (K : Type) [Field K] (r : ℕ) (T : Tab K r) (N n d : ℕ) (κ : K) (P : Set (ValuationSubring K)) (S₀ : ValuationSubring K), 1 ≤ N → 1 ≤ n → 1 ≤ d → S₀ ∈ P → T.Full N n → (∀ S ∈ P, ∃ (K' : Type) (_ : Field K') (σ : K →+* K') (O : ValuationSubring K') (T' : Tab K' r) (B : Matrix (Fin r) (Fin r) K'), O.comap σ = S ∧ T.Near N n d κ σ O T' B) → (∀ x : K, (∀ S ∈ P, x ∈ S) → S₀.valuation x = 1 → ∀ S ∈ P, S.valuation x = 1) → ∃ Φ : Matrix (Fin r) (Fin r) K, ∀ (K' : Type) [Field K'] (σ : K →+* K') (O : ValuationSubring K') (T' : Tab K' r) (B : Matrix (Fin r) (Fin r) K'), O.comap σ ∈ P → T.Near N n d κ σ O T' B → ∃ U : Matrix (Fin r) (Fin r) O, IsUnit U.det ∧ Φ.map σ = U.map O.subtype * B := by
  first | exact @GlobalTheory.OneBasis.Places.exists_basis_all_places | exact GlobalTheory.OneBasis.Places.exists_basis_all_places | (intros; apply GlobalTheory.OneBasis.Places.exists_basis_all_places <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

theorem _root_.GlobalTheory.T.trait_sectionBasis_descends_finite_dvr_extension : ∀ (Z : Scheme.{0}) (G : Over Z) (L : LB G.left), Flat G.hom → L.IsLB → ∀ (N : ℕ) (K : Type) [Field K] (x : Sp K ⟶ Z) (W W' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CommRing W'] [IsDomain W'] [IsDiscreteValuationRing W'] (io : W →+* W') (io' : FractionRing W →+* FractionRing W'), io.Finite → (∀ y, io' (algebraMap W _ y) = algebraMap W' _ (io y)) → ∀ (gam : K →+* FractionRing W) (χ : Sp W ⟶ Z) (h : spMap gam ≫ x = jK W ≫ χ) (h' : spMap (io'.comp gam) ≫ x = jK W' ≫ spMap io ≫ χ) (n : ℕ) (f : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk x))), FrameAt G L N x (io'.comp gam) (spMap io ≫ χ) h' f → FrameAt G L N x gam χ h f := by
  first | exact @GlobalTheory.OneBasis.TraitDescent.frameAt_of_finite | exact GlobalTheory.OneBasis.TraitDescent.frameAt_of_finite | (intros; apply GlobalTheory.OneBasis.TraitDescent.frameAt_of_finite <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

namespace GlobalTheory.Relabel

theorem fibre_ext_of_torsion (hL : Laws) {S : Scheme.{0}} (P : PolAV S) {F : Type} [Field F] [IsAlgClosed F]
    (t : Sp F ⟶ S) {n : ℕ} (hn : 2 ≤ n) (hF : (n : F) ≠ 0) {Y : Over S} [IsSeparated Y.hom]
    (f g : Over.mk t ⊗ P.A ⟶ Y)
    (h : ∀ (j : ℕ) (b : Over.mk t ⟶ P.A), b ^ n ^ j = 1 → lift (𝟙 _) b ≫ f = lift (𝟙 _) b ≫ g)
    (b : Over.mk t ⟶ P.A) : lift (𝟙 _) b ≫ f = lift (𝟙 _) b ≫ g := by
  obtain ⟨P', β, hβ, -, hm, -⟩ := hL.polBaseChange S _ t P
  have hD := PrimePowerTorsion.dense_torsion hL.ample hL.kerPow hL.irred F P' n hn hF
  have := polAV_isIntegral_of_isAlgClosed F P'
  let X : Over S := Over.mk (P'.A.hom ≫ t)
  have : AlgebraicGeometry.IsReduced X.left := inferInstanceAs (AlgebraicGeometry.IsReduced P'.A.left)
  let s : X ⟶ Over.mk t := Over.homMk P'.A.hom rfl
  let c : X ⟶ P.A := Over.homMk β hβ.w
  let m : X ⟶ Over.mk t ⊗ P.A := lift s c
  have hpt : ∀ (y : Sp F ⟶ P'.A.left) (b : Over.mk t ⟶ P.A), y ≫ P'.A.hom = 𝟙 _ → b.left = y ≫ β →
      (lift (𝟙 _) b).left = y ≫ m.left := fun y b hy hb => by
    let y' : Over.mk t ⟶ X := Over.homMk y (by
      change y ≫ P'.A.hom ≫ t = t
      rw [← Category.assoc, hy, Category.id_comp])
    have e : lift (𝟙 _) b = y' ≫ m := by
      rw [comp_lift]
      congr 1
      · exact Over.OverMorphism.ext hy.symm
      · exact Over.OverMorphism.ext hb
    rw [e]; rfl
  have key : m.left ≫ f.left = m.left ≫ g.left := by
    suffices IsDominant (equalizer.ι (m.left ≫ f.left) (m.left ≫ g.left)) from
      ext_of_isDominant_of_isSeparated Y.hom ((Over.w (m ≫ f)).trans (Over.w (m ≫ g)).symm)
        (equalizer.ι (m.left ≫ f.left) (m.left ≫ g.left)) (equalizer.condition _ _)
    refine ⟨Dense.mono (fun y hy => ?_) hD⟩
    obtain ⟨x, ⟨j, hx⟩, q, rfl⟩ := Set.mem_iUnion₂.1 hy
    let ρ : Over.mk t ⟶ Over.mk ((𝟙_ (Over (Sp F))).hom ≫ t) :=
      Over.homMk (𝟙 _) ((Category.id_comp _).trans (Category.id_comp _))
    let Φ : (𝟙_ (Over (Sp F)) ⟶ P'.A) →* (Over.mk t ⟶ P.A) :=
      MonoidHom.mk' (fun y => ρ ≫ toBase hβ.w y) (fun a b => by rw [hm, MonObj.comp_mul])
    have hΦ : (Φ x).left = x.left ≫ β := Category.id_comp _
    have e := hpt x.left (Φ x) (Over.w x) hΦ
    have h₁ := congrArg Over.Hom.left (h j (Φ x) (by rw [← map_pow, hx, map_one]))
    rw [Over.comp_left, Over.comp_left, e, Category.assoc, Category.assoc] at h₁
    exact ⟨equalizer.lift (f := m.left ≫ f.left) (g := m.left ≫ g.left) x.left h₁ q, by
      rw [← Scheme.Hom.comp_apply, equalizer.lift_ι]⟩
  have hb : b.left ≫ P.A.hom = 𝟙 _ ≫ t := (Over.w b).trans (Category.id_comp _).symm
  have e := hpt (hβ.lift b.left (𝟙 _) hb) b (hβ.lift_snd _ _ _) (hβ.lift_fst _ _ _).symm
  refine Over.OverMorphism.ext ?_
  rw [Over.comp_left, Over.comp_left, e, Category.assoc, Category.assoc, key]

theorem actV_compat_of_torsion : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N') (I : NumB.Iso N.toNumB N'.toNumB), GeoIso ν ν' I → ∀ (O : Type) [CommRing O] [StarRing O] (oa : D.P.OAct O) (oa' : D'.P.OAct O) (n : ℕ), n.Prime → (n : F) ≠ 0 → ∀ x : O, (∀ (j : ℕ) (b : N.A), b ^ n ^ j = 1 → I.φ (actV ν oa x b) = actV ν' oa' x (I.φ b)) → ∀ b, I.φ (actV ν oa x b) = actV ν' oa' x (I.φ b) := by
  intro hL R _ _ D D' F _ _ _ N N' ν ν' I ⟨φ, _, _, _, _, hφ, _⟩ O _ _ oa oa' n hn hF x h b
  have := D'.P.isAb.proper
  have e₁ : ∀ b, lift (𝟙 _) (ν.eA b) ≫ (_ ◁ oa.act x) ≫ φ.hom ≫ snd _ _ = ν'.eA (I.φ (actV ν oa x b)) := fun b => by
    rw [lift_whiskerLeft_assoc, ← ν.eA.apply_symm_apply (ν.eA b ≫ oa.act x), reassoc_of% hφ, lift_snd]
    rfl
  have e₂ : ∀ b, lift (𝟙 _) (ν.eA b) ≫ φ.hom ≫ snd _ _ ≫ oa'.act x = ν'.eA (actV ν' oa' x (I.φ b)) := fun b => by
    rw [reassoc_of% hφ, lift_snd_assoc, actV, MulEquiv.apply_symm_apply]
  refine ν'.eA.injective ?_
  rw [← e₁, ← e₂]
  refine fibre_ext_of_torsion hL D.P _ hn.two_le hF _ _ (fun j c hc => ?_) _
  obtain ⟨c, rfl⟩ := ν.eA.surjective c
  exact (e₁ c).trans ((congrArg ν'.eA (h j c (ν.eA.injective (by rw [map_pow, hc, map_one])))).trans (e₂ c).symm)

end GlobalTheory.Relabel
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.AbPartIso

noncomputable section
namespace GlobalTheory.Ex.AbPartCube

theorem exists_move {X₁ X₂ B Y : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : B ⟶ X₁} {f₂ : B ⟶ X₂}
    (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (hw : w.IsGen) (h₁ : L₁.IsLB) (h₂ : L₂.IsLB) {K : Type} [Fintype K]
    (φ' : K → (Y ⟶ B)) {φ₁ : K → (Y ⟶ X₁)} (e : ∀ k, φ' k ≫ f₁ = φ₁ k) {ε : K → ℤ}
    (t₁ : LB.Gen (LB.LinComb L₁ φ₁ ε)) (ht : t₁.IsGen) :
    ∃ t₂ : LB.Gen (LB.LinComb L₂ (fun k => φ' k ≫ f₂) ε), t₂.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J₁ J₂, Good L₁ z J₁ → Good L₂ z J₂ → val t₂ r z J₂ =
        (∏ k, gw w (r ≫ φ' k) z (J₂ ((r ≫ φ' k) ≫ f₂)) (fun _ => J₁ ((r ≫ φ' k) ≫ f₁)) ^ ε k) * val t₁ r z J₁ := by
  obtain rfl : (fun k => φ' k ≫ f₁) = φ₁ := funext e
  have le : ∀ j : K → PUnit → L₁.ι, LB.wchart (L₁.pull f₁) φ' j ≤
      LB.wchart L₁ (fun k => φ' k ≫ f₁) (fun k => j k PUnit.unit) :=
    fun j y hy => Set.mem_iInter.2 fun k => mem_pull (x := φ' k y).1 (Set.mem_iInter.1 hy k)
  let a : LB.Gen (LB.LinComb (L₁.pull f₁) φ' ε) := ⟨fun j => res (le j) (t₁.s fun k => j k PUnit.unit)⟩
  have ha : a.IsGen := isGen_of_gm a fun y j j' hj hj' => by
    refine (gm_res (𝟙 Y) y (le j) hj _).trans ((gen_trans ht (𝟙 Y) y (le j hj) (le j' hj')).trans
      (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_) (gm_res (𝟙 Y) y (le j') hj' _).symm))
    refine Eq.trans ?_ (gm_pull_g L₁ f₁ (𝟙 Y ≫ φ' k) y (j k) (j' k) (Set.mem_iInter.1 hj k)
      (Set.mem_iInter.1 hj' k)).symm
    rw [Category.assoc]
  obtain ⟨t, ht', hv⟩ := exists_up ((isGen_iff w).1 hw) h₂ (pull_isLB h₁ f₁) a ha
  refine ⟨t, ht', fun Z r z J₁ J₂ hJ₁ hJ₂ => ?_⟩
  have m : r z ∈ LB.wchart (L₁.pull f₁) φ' (fun k _ => J₁ (r ≫ φ' k ≫ f₁)) :=
    Set.mem_iInter.2 fun k => mem_pull.2 (hJ₁ (r ≫ φ' k ≫ f₁))
  refine (hv Z r z _ _ (hJ₂.mem _ r) m).trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_)
    (gm_res r z (le _) m _))
  rw [Category.assoc, Category.assoc]

variable {S : Scheme.{0}} {A A' T : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']

theorem prod_cub_pt {Z : Over S} (x x' y : Z ⟶ A) {U : Type} [CommGroup U] (h : (Z ⟶ A) → U) :
    ∏ I : thK, h (lift x (lift x' y) ≫ psum A (x3 A) I.down) ^ thε I =
      h (x * x' * y) * (h (x * x'))⁻¹ * (h (x * y))⁻¹ * (h (x' * y))⁻¹ * h x * h x' * h y * (h 1)⁻¹ := by
  classical
  let h' : (Z.left ⟶ A.left) → U := fun q => if hq : q ≫ A.hom = Z.hom then h (Over.homMk q hq) else 1
  have e : ∀ q : Z ⟶ A, h' q.left = h q := fun q => dif_pos (Over.w q)
  have p := prod_cub x x' y h'
  simp only [e] at p
  exact (Finset.prod_congr rfl fun I _ => congrArg (· ^ thε I) (e _).symm).trans p

theorem cubV_move (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {L : RigLB A} {L' : RigLB A'} (c : CubicalStr A L)
    (c' : CubicalStr A' L') (g : T ⊗ A ⟶ A')
    (hg : ∀ (Z : Over S) (t : Z ⟶ T) (x y : Z ⟶ A), lift t (x * y) ≫ g = (lift t x ≫ g) * (lift t y ≫ g))
    (w : LB.Iso (L.L.pull (snd T A).left) (L'.L.pull g.left)) (hw : w.IsGen) {Z : Over S} (σ : Z ⟶ T) (z : Z.left)
    {J J'} (hJ : Good L.L z J) (hJ' : Good L'.L z J') (Ω : (Z ⟶ A) → (Z.left.presheaf.stalk z)ˣ)
    (hΩ : ∀ q, Ω q = gw w (lift σ q).left z (J' (lift σ q ≫ g).left) (fun _ => J q.left)) (x y u : Z ⟶ A) :
    cubV c' z J' (lift σ x ≫ g) (lift σ y ≫ g) (lift σ u ≫ g) =
      Ω (x * y * u) * (Ω (x * y))⁻¹ * (Ω (x * u))⁻¹ * (Ω (y * u))⁻¹ * Ω x * Ω y * Ω u * (Ω 1)⁻¹ * cubV c z J x y u := by
  have g1 : ∀ (Z : Over S) (t : Z ⟶ T), lift t (1 : Z ⟶ A) ≫ g = 1 := fun Z t =>
    mul_eq_left.1 ((hg Z t 1 1).symm.trans (by rw [_root_.mul_one]))
  let Y : Over S := A ⊗ A ⊗ A ⊗ T
  let t : Y ⟶ T := snd _ _ ≫ snd _ _ ≫ snd _ _
  let x₁ : Y ⟶ A := fst _ _
  let x₂ : Y ⟶ A := snd _ _ ≫ fst _ _
  let x₃ : Y ⟶ A := snd _ _ ≫ snd _ _ ≫ fst _ _
  obtain ⟨t₂, ht₂, hv⟩ := exists_move w hw L.isLB L'.isLB
    (fun I : thK => (lift t (lift x₁ (lift x₂ x₃) ≫ psum A (x3 A) I.down)).left)
    (φ₁ := fun I => (lift x₁ (lift x₂ x₃)).left ≫ thφ A (x3 A) I)
    (fun I => by rw [← Over.comp_left, lift_snd]; rfl)
    (LB.pullGen L.L (thφ A (x3 A)) thε c.t (lift x₁ (lift x₂ x₃)).left) (DVR.pullGen_isGen _ _ _ _ c.isGen _)
  have ev : ∀ {Z : Over S} (σ : Z ⟶ T) (z : Z.left) {J J'}, Good L.L z J → Good L'.L z J' →
      ∀ (Ω : (Z ⟶ A) → (Z.left.presheaf.stalk z)ˣ),
      (∀ q, Ω q = gw w (lift σ q).left z (J' (lift σ q ≫ g).left) (fun _ => J q.left)) → ∀ x y u : Z ⟶ A,
      val t₂ (lift x (lift y (lift u σ)) : Z ⟶ Y).left z J' =
        Ω (x * y * u) * (Ω (x * y))⁻¹ * (Ω (x * u))⁻¹ * (Ω (y * u))⁻¹ * Ω x * Ω y * Ω u * (Ω 1)⁻¹ * cubV c z J x y u ∧
      val (LB.pullGen L'.L (thφ A' (x3 A')) thε c'.t (lift (lift t x₁ ≫ g) (lift (lift t x₂ ≫ g) (lift t x₃ ≫ g))).left)
        (lift x (lift y (lift u σ)) : Z ⟶ Y).left z J' =
        cubV c' z J' (lift σ x ≫ g) (lift σ y ≫ g) (lift σ u ≫ g) := by
    intro Z σ z J J' hJ hJ' Ω hΩ x y u
    have r₀ : (lift x (lift y (lift u σ)) : Z ⟶ Y) ≫ t = σ := by simp [t, Y]
    have r₁ : (lift x (lift y (lift u σ)) : Z ⟶ Y) ≫ x₁ = x := by simp [x₁, Y]
    have r₂ : (lift x (lift y (lift u σ)) : Z ⟶ Y) ≫ x₂ = y := by simp [x₂, Y]
    have r₃ : (lift x (lift y (lift u σ)) : Z ⟶ Y) ≫ x₃ = u := by simp [x₃, Y]
    refine ⟨(hv _ _ z J J' hJ hJ').trans (congrArg₂ (· * ·) (Eq.trans (Finset.prod_congr rfl fun I _ => ?_)
      (prod_cub_pt x y u Ω)) ((val_cub c _ hJ _ _ _).trans (by rw [r₁, r₂, r₃]))), (val_cub c' _ hJ' _ _ _).trans ?_⟩
    · rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, comp_lift, r₀, ← Category.assoc, comp_lift, comp_lift,
        r₁, r₂, r₃, lift_snd, hΩ]
    · rw [comp_lift_assoc, comp_lift_assoc, comp_lift_assoc, r₀, r₁, r₂, r₃]
  have sj : Function.Surjective
      ((snd A (A ⊗ A ⊗ T)).left ≫ (snd A (A ⊗ T)).left ≫ (snd A T).left).appTop.hom :=
    surj_comp (surj_snd hG hA _) (surj_comp (surj_snd hG hA _) (surj_snd hG hA _))
  have key := gen_unique' L'.isLB (fun V _ k => ?_) _ (lift 1 (lift 1 (lift 1 (𝟙 T))) : T ⟶ Y).left ?_ sj
    (DVR.pullGen_isGen L'.L (thφ A' (x3 A')) thε c'.t c'.isGen
      (lift (lift t x₁ ≫ g) (lift (lift t x₂ ≫ g) (lift t x₃ ≫ g))).left) ht₂ (fun y I' hI' => ?_) _
    (lift x (lift y (lift u σ)) : Z ⟶ Y).left z J' hJ'
  · exact (ev σ z hJ hJ' Ω hΩ x y u).2.symm.trans (key.trans (ev σ z hJ hJ' Ω hΩ x y u).1)
  · refine (prod_cub_pt x₁ x₂ x₃ (fun q => k (lift t q ≫ g).left)).trans (Eq.trans ?_ (prod_cub _ _ _ k).symm)
    simp only [hg, g1]
  · rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, lift_snd_assoc, lift_snd_assoc, lift_snd]; rfl
  · choose I hI using fun χ : T.left ⟶ A.left => exists_chart L.isLB (χ y)
    have E := ev (𝟙 T) y hI hI' _ (fun _ => rfl) 1 1 1
    have E₂ := E.2
    rw [g1, (isCub_cubV c' hI').face] at E₂
    refine E₂.trans (Eq.trans ?_ E.1.symm)
    rw [(isCub_cubV c hI).face]
    have fin : ∀ {G U : Type} [Group G] [CommGroup U] (h : G → U), 1 = h (1 * 1 * 1) * (h (1 * 1))⁻¹ * (h (1 * 1))⁻¹ *
        (h (1 * 1))⁻¹ * h 1 * h 1 * h 1 * (h 1)⁻¹ * 1 := fun h => by simp
    exact fin fun q : T ⟶ A => gw w (lift (𝟙 T) q).left y (I' (lift (𝟙 T) q ≫ g).left) (fun _ => I q.left)

theorem theta_move : GlobalFnsSt → AllIso fun {_} _ _ {_} {_} {F} _ _ {N} {N'} ν ν' {_} w f => ∀ x y u, (N'.θ (f x) (f y) (f u) : F) * wVal ν ν' w f (x * y) * wVal ν ν' w f (x * u) * wVal ν ν' w f (y * u) * wVal ν ν' w f 1 = (N.θ x y u : F) * wVal ν ν' w f (x * y * u) * wVal ν ν' w f x * wVal ν ν' w f y * wVal ν ν' w f u := by
  intro hG R _ _ D D' F _ _ N N' ν ν' φ w f hφ hw hf x y u
  obtain ⟨z⟩ : Nonempty (Sp F) := inferInstanceAs (Nonempty (PrimeSpectrum F))
  have hJ : Good D.P.L z ν.J := fun ψ => ν.good ψ trivial
  have hJ' : Good D'.P.L z ν'.J := fun ψ => ν'.good ψ trivial
  have im : ∀ a, lift (𝟙 _) (ν.eA a) ≫ φ.hom ≫ snd _ _ = ν'.eA (f a) := fun a => by
    rw [← Category.assoc, hf a, lift_snd]
  let Ω : (TF (R := R) F ⟶ D.P.A) → ((Sp F).presheaf.stalk z)ˣ := fun q =>
    gw w (lift (𝟙 _) q).left z (ν'.J (lift (𝟙 _) q ≫ φ.hom ≫ snd _ _).left) (fun _ => ν.J q.left)
  have vw : ∀ a, toStk z (wVal ν ν' w f a) = (Ω (ν.eA a)).val := fun a => by
    have m₁ : (snd (TF (R := R) F) D.P.A).left ((lift (𝟙 _) (ν.eA a)).left z) ∈ D.P.L.U (ν.J (ν.eA a).left) := by
      exact (congrArg (fun q : TF (R := R) F ⟶ D.P.A => q.left z ∈ D.P.L.U (ν.J (ν.eA a).left))
        (lift_snd (𝟙 _) (ν.eA a))).mpr (hJ _)
    have m₂ : (φ.hom ≫ snd (TF (R := R) F) D'.P.A).left ((lift (𝟙 _) (ν.eA a)).left z) ∈
        D'.P.L.U (ν'.J (ν'.eA (f a)).left) := by
      exact (congrArg (fun q : TF (R := R) F ⟶ D'.P.A => q.left z ∈ D'.P.L.U (ν'.J (ν'.eA (f a)).left))
        (im a)).mpr (hJ' _)
    refine (toStk_valF (lift (𝟙 (TF (R := R) F)) (ν.eA a)).left _ z (by exact ⟨mem_pull.2 m₂, mem_pull.2 m₁⟩) _).trans ?_
    simp only [Ω, im]
    rfl
  have v : toStk z (N.θ x y u : F) = (cubV D.cub (T := TF (R := R) F) z ν.J (ν.eA x) (ν.eA y) (ν.eA u)).val :=
    (congrArg (toStk z) (ν.θ_eq x y u)).trans (toStk_valF _ _ z (hJ.mem _ _) _)
  have v' : toStk z (N'.θ (f x) (f y) (f u) : F) =
      (cubV D'.cub (T := TF (R := R) F) z ν'.J (ν'.eA (f x)) (ν'.eA (f y)) (ν'.eA (f u))).val :=
    (congrArg (toStk z) (ν'.θ_eq _ _ _)).trans (toStk_valF _ _ z (hJ'.mem _ _) _)
  have key := cubV_move hG D.P.isAb D.cub D'.cub (φ.hom ≫ snd _ _) hφ.2 w hw (𝟙 (TF (R := R) F)) z hJ hJ' Ω
    (fun _ => rfl) (ν.eA x) (ν.eA y) (ν.eA u)
  rw [im, im, im] at key
  have alg : ∀ {U : Type} [CommRing U] {a b p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ : Uˣ},
      a = p₁ * p₂⁻¹ * p₃⁻¹ * p₄⁻¹ * p₅ * p₆ * p₇ * p₈⁻¹ * b →
      a.val * p₂.val * p₃.val * p₄.val * p₈.val = b.val * p₁.val * p₅.val * p₆.val * p₇.val := by
    rintro U _ a b p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ rfl
    simp only [← Units.val_mul]
    refine congrArg Units.val (Additive.ofMul.injective ?_)
    simp only [ofMul_mul, ofMul_inv]
    abel
  apply (toStk z).injective
  simp only [map_mul, vw, v, v', map_one]
  exact alg key

end GlobalTheory.Ex.AbPartCube
end
end
