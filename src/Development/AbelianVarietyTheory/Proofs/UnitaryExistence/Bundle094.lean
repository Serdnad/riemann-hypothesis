module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle086
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle075
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle091
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle019
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle088
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle090
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle082
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle025
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle070
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle074
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle072
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle035
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle076
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle083
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

private theorem fib_gram_eq {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (x : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ G x = xᵀ * (G.map τ * x.map (starRingEnd ℂ)) := by
  ext a b
  simp [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.mul_apply, Finset.mul_sum, mul_assoc]

private theorem fib_cancel {R G : Type} [CommRing R] [Group G] {n : ℕ} (f : G →* GL (Fin n) R) (g g' : G) (N : ℕ)
    (p v w w' y : Fin n → R) (e : p - (f g).1 *ᵥ v = N • w) (e' : p - (f g').1 *ᵥ v = N • w')
    (ey : (f g).1 *ᵥ y = w - w') : (f (g⁻¹ * g')).1 *ᵥ v - v = N • y := by
  have e2 : (f g').1 *ᵥ v - (f g).1 *ᵥ v = N • ((f g).1 *ᵥ y) := by
    rw [ey, smul_sub, ← e, ← e']; abel
  have hi : ∀ z, (f g⁻¹).1 *ᵥ ((f g).1 *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
      Matrix.one_mulVec]
  have e3 := congrArg (fun z => (f g⁻¹).1 *ᵥ z) e2
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, hi] at e3
  rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
  exact e3

theorem mem_level_of_mark_of_frame_eq : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ (Kf : Subgroup (GA D V)), IsLevelK V l.M Kf → ∀ h h' k γ γ', C.Mark h k γ → C.Mark h' k γ' → C.fr (γ * h) k = C.fr (γ' * h') k → (γ * h)⁻¹ * (γ' * h') ∈ Kf := by
  intro D H Dw l Xo c σ V r C hC Kf hK h h' k γ γ' hm hm' hfr
  obtain rfl : V.rank = r := C.hr
  obtain ⟨-, hL, hM⟩ := hm
  obtain ⟨-, hL', hM'⟩ := hm'
  generalize γ * h = g at *
  generalize γ' * h' = g' at *
  obtain ⟨hA, hG, -⟩ := GlobalTheory.T.archimedeanMatrix_unitary_continuous_multiplicative D V C.θ hC.inf
  rw [hK]
  refine ⟨hG _ fun τ hτ => ?_, ?_⟩
  · have hΨ : τ ∈ (C.M.X k).Ψ := by
      rw [(hC.base.type k).2, hC.iota.rt, hC.iota.rt0]; exact hτ
    have hx : (C.x₀ τ).det ≠ 0 := by
      intro h0
      have h1 := congrArg Matrix.det (hC.orth k τ hΨ)
      simp only [fib_gram_eq, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul,
        Matrix.det_diagonal] at h1
      refine Finset.prod_ne_zero_iff.2 (fun a _ => ?_) h1.symm
      unfold sgn
      split_ifs <;> simp
    have h1 : archM V (C.θ τ) g * C.x₀ τ = archM V (C.θ τ) g' * C.x₀ τ := congrFun hfr ⟨τ, hΨ⟩
    have hu : IsUnit (C.x₀ τ) := (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit hx)
    have h2 := hu.mul_right_cancel h1
    rw [(hA τ).2.1, ← h2, ← (hA τ).2.1, inv_mul_cancel, (hA τ).1]
  · have hlat : (latG V g : Set (Fin V.rank → D.host.E)) = latG V g' := by
      have e := hL.symm.trans hL'
      have e1 : (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast C.hr.symm) = id := rfl
      rwa [e1, Set.image_id, Set.image_id] at e
    have hhat : latGHat V g' = latGHat V g := by
      rw [(GlobalTheory.T.adelicElementLattice_full_and_completion D V g).2.2.2.2.1, (GlobalTheory.T.adelicElementLattice_full_and_completion D V g').2.2.2.2.1, hlat]
    have himg := (GlobalTheory.T.adelicElementLattice_full_and_completion D V g).2.2.2.1
    rw [← (GlobalTheory.T.adelicElementLattice_full_and_completion D V 1).2.2.2.2.1] at himg
    refine ((GlobalTheory.T.principalLevel_eq_halfMarking_stabilizer D H l V).1 _).2 ((((GlobalTheory.T.congruence_lattice_fractionalMultiple_agree D V) _).2 _ _).2 ?_)
    intro a ha
    rw [← hC.iota.emb.2, LinearMap.range_eq_map, ← Submodule.map_smul''] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    obtain ⟨w, hw, e⟩ := hM b hb
    obtain ⟨w', hw', e'⟩ := hM' b hb
    rw [hhat] at hw'
    have hd : w - w' ∈ (latGHat V g : Set _) := sub_mem hw hw'
    rw [himg] at hd
    obtain ⟨y, hy, ey⟩ := hd
    exact ⟨y, hy, fib_cancel (finHom V) g g' l.M _ _ w w' y e e' ey⟩

end GlobalTheory.Member
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.ConjPermutesAnyLevel

open GlobalTheory.ConjPermutes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

theorem exists_map (F : FamilyUnif Xo σ ty) (hD : 1 ≤ D.p + D.q) (hσ : σ (baseKA l).ρ = H.rt0)
    (hty : IsTypeFn H D.p D.q ty) (hA : ∀ x : KA l, σ x = (x : ℂ)) (τ : ℂ ≃+* ℂ)
    (hτ : ∀ x : KA l, τ (x : ℂ) = x) :
    ∃ π : Fin F.n → Fin F.n, ConjugationPermutesPeriods F τ π := by
  have hτσ : (τ : ℂ →+* ℂ).comp σ = σ := RingHom.ext fun x => by
    show τ (σ x) = σ x
    rw [hA, hτ]
  have hon : ∀ i P, IsPeriod (F.Di i) ty P → ∃ i' P', IsPeriod (F.Di i') ty P' ∧
      F.u i' P' = spMap (τ : ℂ →+* ℂ) ≫ F.u i P := fun i P hP =>
    F.onto _ (by rw [Category.assoc, F.over_σ i P hP, ConjPermutes.spMap_comp, hτσ])
  choose P₀ hP₀ using exists_period F hty
  choose π P₁ hP₁ hu₁ using fun i => hon i (P₀ i) (hP₀ i)
  refine ⟨π, fun i P hP => ?_⟩
  obtain ⟨i', P', hP', hu'⟩ := hon i P hP
  obtain ⟨c₀⟩ : Nonempty (Coeff l) := inferInstance
  obtain ⟨c, -, hc⟩ := GlobalTheory.T.exists_coeffField_idempotents_periodSpaces_anyLevel E H D l Xo σ g ty F hD hσ hty hA c₀
  obtain ⟨e, he, hv⟩ := hc (π i)
  let j : c.F →+* ℂ := (τ.symm : ℂ →+* ℂ).comp c.F.val.toRingHom
  have hj : (τ : ℂ →+* ℂ).comp j = c.F.val.toRingHom := RingHom.ext fun a => τ.apply_symm_apply _
  have hjσ : σ = j.comp (IntermediateField.inclusion c.le).toRingHom := RingHom.ext fun x => by
    rw [hA]
    exact (τ.symm_apply_eq.2 (hτ x).symm).symm
  have w : ∀ Q, IsPeriod (F.Di i) ty Q →
      F.u i Q ≫ Xo.s = spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom := fun Q hQ => by
    rw [F.over_σ i Q hQ, ConjPermutes.spMap_comp, ← hjσ]
  have key : ∀ Q (hQ : IsPeriod (F.Di i) ty Q) k Q', IsPeriod (F.Di k) ty Q' →
      F.u k Q' = spMap (τ : ℂ →+* ℂ) ≫ F.u i Q →
      τ (valAt' (X := Xo.XF c) (pullback.lift _ _ (w Q hQ)) ⊤ e) = if k = π i then 1 else 0 := by
    intro Q hQ k Q' hQ' h
    rw [← hv k Q' hQ' (spMap (τ : ℂ →+* ℂ) ≫ pullback.lift _ _ (w Q hQ))
      (by rw [Category.assoc, pullback.lift_fst, h]) (by rw [Category.assoc, pullback.lift_snd, ConjPermutes.spMap_comp, hj]),
      valAt'_spMap_comp]
    rfl
  have hconst := GlobalTheory.T.regularFunction_const_of_finite_values_any_level E H D l Xo σ g ty F hD hσ hty c j e {0, 1} (Set.toFinite _)
    (fun x _ => valAt'_idem x he) i P (P₀ i) hP (hP₀ i) (pullback.lift _ _ (w P hP))
    (pullback.lift _ _ (w _ (hP₀ i))) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  have h₁ := key P hP i' P' hP' hu'
  rw [hconst, key _ (hP₀ i) (π i) (P₁ i) (hP₁ i) (hu₁ i), if_pos rfl] at h₁
  obtain rfl : i' = π i := by
    by_contra hne
    rw [if_neg hne] at h₁
    exact one_ne_zero h₁
  exact ⟨P', hP', hu'.symm⟩

theorem exists_perm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → (∀ x : KA l, σ x = (x : ℂ)) → ∀ τ : ℂ ≃+* ℂ, (∀ x : KA l, τ (x : ℂ) = x) → ∃ π : Equiv.Perm (Fin F.n), ConjugationPermutesPeriods F τ π := by
  intro E _ _ _ H D l Xo σ g ty F hD hσ hty hA τ hτ
  obtain ⟨π, hπ⟩ := exists_map F hD hσ hty hA τ hτ
  obtain ⟨π', hπ'⟩ := exists_map F hD hσ hty hA τ.symm (fun x => τ.symm_apply_eq.2 (hτ x).symm)
  have hinv : Function.LeftInverse π' π := fun i => by
    obtain ⟨P, hP⟩ := exists_period F hty i
    obtain ⟨P', hP', h'⟩ := hπ i P hP
    obtain ⟨P'', hP'', h''⟩ := hπ' (π i) P' hP'
    have e : (τ.symm : ℂ →+* ℂ).comp (τ : ℂ →+* ℂ) = RingHom.id ℂ := RingHom.ext fun a => τ.symm_apply_apply a
    have e' : spMap (RingHom.id ℂ) = 𝟙 _ := Spec.map_id (CommRingCat.of ℂ)
    rw [← h', ← Category.assoc, ConjPermutes.spMap_comp, e, e', Category.id_comp] at h''
    exact (F.disj _ _ _ _ hP hP'' h'').symm
  exact ⟨Equiv.ofBijective π (Finite.injective_iff_bijective.1 hinv.injective), hπ⟩

end GlobalTheory.ConjPermutesAnyLevel
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem ChartCover.exists_lift {S : Type} [CommRing S] [Algebra c.F S] (w : FrPt Xo c S) :
    ∃ xF : Sp S ⟶ Xo.XF c, xF ≫ pullback.fst _ _ = w.x ∧ xF ≫ pullback.snd _ _ = spMap (algebraMap c.F S) := by
  refine ⟨pullback.lift w.x (spMap (algebraMap c.F S)) ?_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  rw [w.x_over, spMap_comp_ring]
  rfl

theorem ChartCover.near (hS : Out.SecBaseChangeSt) {R A : Type} [CommRing R] [Algebra c.F R] [CommRing A]
    [Algebra c.F A] {j : Sp R ⟶ Xo.XF c} {y₀ : FrPt Xo c R} {π : R →ₐ[c.F] A}
    {X : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A} {s : Aˣ} {u : FrPt Xo c A}
    (hj : OpenChart j y₀) (hu : UnivFrame y₀ π X s u) {S : Type} [CommRing S] [Algebra c.F S] (w : FrPt Xo c S)
    (xF : Sp S ⟶ Xo.XF c) (h1 : xF ≫ pullback.fst _ _ = w.x)
    (h2 : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F S)) (p : Sp S) (hp : xF p ∈ Set.range j) :
    ∃ g : S, g ∉ p.asIdeal ∧ ∀ (T : Type) [CommRing T] [Algebra c.F T] (lam : S →ₐ[c.F] T), IsUnit (lam g) →
      ∃ (z : FrPt Xo c T) (a : A →ₐ[c.F] T), FrMap lam w z ∧ FrMap a u z := by
  obtain ⟨g, hg, hT⟩ := openChart_factor_near_prime E H Dw l Xo c R j y₀ hj S xF h2 p hp
  refine ⟨g, hg, fun T _ _ lam hl => ?_⟩
  obtain ⟨ψ, hψ⟩ := hT T lam hl
  obtain ⟨z, hz⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algebraMap hS E H Dw l Xo c S T lam w
  have hx : z.x = spMap ψ.toRingHom ≫ y₀.x := by
    rw [hz.1, ← h1, ← hj.2.1, ← Category.assoc, hψ, Category.assoc]
  obtain ⟨a, ⟨_, ha⟩, _⟩ := GlobalTheory.T.universalFrame_classifies_framedPoints hS E H Dw l Xo c R A y₀ π X s u hu T z ψ hx
  exact ⟨z, a, hz, ha⟩

theorem ChartCover.cls_loc (hS : Out.SecBaseChangeSt) {R : Type} [CommRing R] [Algebra c.F R] {A : TRing c.F}
    {j : Sp R ⟶ Xo.XF c} {y₀ : FrPt Xo c R} {π : R →ₐ[c.F] A.R}
    {X : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A.R} {s : (A.R)ˣ} {u : FrPt Xo c A.R}
    (hj : OpenChart j y₀) (hu : UnivFrame y₀ π X s u) {S : Type} [CommRing S] [Algebra c.F S] (w : FrPt Xo c S)
    (xF : Sp S ⟶ Xo.XF c) (h1 : xF ≫ pullback.fst _ _ = w.x)
    (h2 : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F S)) (m : Ideal S) [hm : m.IsPrime]
    (hp : xF (⟨m, hm⟩ : PrimeSpectrum S) ∈ Set.range j) :
    ∃ cw : A.R →ₐ[c.F] Localization.AtPrime m,
      ChartCls (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w m u cw ∧
      ChartLoc (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w m A u := by
  obtain ⟨g, hg, hT⟩ := ChartCover.near hS hj hu w xF h1 h2 (⟨m, hm⟩ : PrimeSpectrum S) hp
  obtain ⟨z, a, hz, ha⟩ := hT (Localization.AtPrime m) (locM c.F m)
    (IsLocalization.map_units (Localization.AtPrime m) (⟨g, hg⟩ : m.primeCompl))
  refine ⟨a, ⟨z, hz, ha⟩, ?_⟩
  intro p φ y hy
  obtain ⟨yF, k1, k2⟩ := ChartCover.exists_lift y
  have e : spMap φ.toRingHom ≫ yF = xF := by
    apply pullback.hom_ext
    · rw [Category.assoc, k1, h1, hy.1]
    · rw [Category.assoc, k2, h2, spMap_comp_ring]
      congr 1
      exact φ.comp_algebraMap
  have hq : yF (spMap φ.toRingHom (⟨m, hm⟩ : PrimeSpectrum S)) ∈ Set.range j := by
    rw [← e] at hp
    exact hp
  obtain ⟨g', hg', hT'⟩ := ChartCover.near hS hj hu y yF k1 k2 _ hq
  obtain ⟨p', lam, hl, hlam⟩ := GlobalTheory.testRing_localizationAway c.F p g'
  obtain ⟨z', a', hz', ha'⟩ := hT' p'.R lam hl
  exact ⟨g', hg', p', lam, z', a', hlam, hz', ha'⟩

end

theorem chartCoverF_of_secBaseChange : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ChartCoverF Xo c := by
  intro hS E _ _ _ H Dw l Xo c S _ _ w w' hw m hm
  obtain ⟨xF, h1, h2⟩ := ChartCover.exists_lift w
  obtain ⟨p, j, y₀, hj, hp⟩ := GlobalTheory.T.exists_openChart_framedPoint_testRing hS E H Dw l Xo c (xF (⟨m, hm.isPrime⟩ : PrimeSpectrum S))
  obtain ⟨A, π, X, s, u, hu⟩ := GlobalTheory.T.exists_universalFrame_testRing hS E H Dw l Xo c p y₀
  obtain ⟨cw, hc, hl⟩ := ChartCover.cls_loc hS hj hu w xF h1 h2 m hp
  obtain ⟨cw', hc', hl'⟩ := ChartCover.cls_loc hS hj hu w' xF (h1.trans hw.symm) h2 m hp
  exact ⟨A, u, cw, cw', GlobalTheory.T.universalFrame_classifies_unique_openChart hS E H Dw l Xo c p.R A.R j y₀ π X s u hj hu,
    GlobalTheory.T.exists_borelPairs_universalFrame_openChart hS E H Dw l Xo c p A j y₀ π X s u hj hu, hc, hl, hc', hl'⟩

end GlobalTheory.Frames
end
