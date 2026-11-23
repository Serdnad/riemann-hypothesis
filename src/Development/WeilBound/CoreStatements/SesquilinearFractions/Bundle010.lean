module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle014
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle186
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle170
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle093
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle064
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle120
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle021
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle034
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle004
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle005
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle009
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalRootReZeroImSq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.Xgf.TransportLieModel

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R] {x : Sp R ⟶ S}

def transport {E E' : Type} [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R E'] (M : LieModel G x E)
    (e : E ≃ₗ[R] E') : LieModel G x E' where
  pt v := M.pt (e.symm v)
  tan v := M.tan _
  inj a b h := e.symm.injective (M.inj h)
  onto v hv := by
    obtain ⟨w, hw⟩ := M.onto v hv
    exact ⟨e w, by simpa using hw⟩
  add a b := by rw [map_add (f := _), M.add]
  smul c a := by rw [map_smul]; exact M.smul c _

theorem isTanAt_comp {v : epsAt x ⟶ G} (hv : IsTanAt G x v) (f : G ⟶ G) [IsMonHom f] : IsTanAt G x (v ≫ f) := by
  unfold IsTanAt at hv ⊢
  rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, MonObj.one_comp]

theorem mul_comp' {T : Over S} (u v : T ⟶ G) (f : G ⟶ G) [IsMonHom f] : (u * v) ≫ f = (u ≫ f) * (v ≫ f) := by
  simp [Hom.mul_def]

variable {E : Type} [AddCommGroup E] [Module R E]

def endo (M : LieModel G x E) (f : G ⟶ G) [IsMonHom f] (e : E) : E :=
  Classical.choose (M.onto (M.pt e ≫ f) (isTanAt_comp (M.tan e) f))

theorem endo_spec (M : LieModel G x E) (f : G ⟶ G) [IsMonHom f] (e : E) : M.pt (endo M f e) = M.pt e ≫ f :=
  Classical.choose_spec (M.onto (M.pt e ≫ f) (isTanAt_comp (M.tan e) f))

def diff (M : LieModel G x E) (f : G ⟶ G) [IsMonHom f] : E →ₗ[R] E where
  toFun := endo M f
  map_add' a b := M.inj (by rw [endo_spec, M.add, M.add, endo_spec, endo_spec, mul_comp'])
  map_smul' c a := M.inj (by
    rw [endo_spec, RingHom.id_apply, LieModel.pt_smul, LieModel.pt_smul, endo_spec, Category.assoc])

theorem diff_spec (M : LieModel G x E) (f : G ⟶ G) [IsMonHom f] (e : E) : M.pt (diff M f e) = M.pt e ≫ f :=
  endo_spec M f e

def rho {O : Type} [CommRing O] (act : OAct O G) (M : LieModel G x E) : O →+* Module.End R E where
  toFun a := letI := act.hom a; diff M (act.act a)
  map_one' := by
    ext e
    apply M.inj
    letI := act.hom 1
    show M.pt (diff M (act.act 1) e) = M.pt e
    rw [diff_spec, act.one, Category.comp_id]
  map_mul' a b := by
    ext e
    apply M.inj
    letI := act.hom a; letI := act.hom b; letI := act.hom (a * b)
    show M.pt (diff M (act.act (a * b)) e) = M.pt (diff M (act.act a) (diff M (act.act b) e))
    rw [diff_spec, diff_spec, diff_spec, mul_comm, act.mul, Category.assoc]
  map_zero' := by
    ext e
    apply M.inj
    letI := act.hom 0
    show M.pt (diff M (act.act 0) e) = M.pt 0
    have h0 : act.act 0 = 1 := by
      have := act.add 0 0
      rw [add_zero] at this
      exact mul_eq_left.1 this.symm
    rw [diff_spec, LieModel.pt_zero, h0, Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (M.pt e ≫ toUnit G)]
  map_add' a b := by
    ext e
    apply M.inj
    letI := act.hom a; letI := act.hom b; letI := act.hom (a + b)
    show M.pt (diff M (act.act (a + b)) e) = M.pt (diff M (act.act a) e + diff M (act.act b) e)
    rw [diff_spec, M.add, diff_spec, diff_spec, act.add, comp_mul]

theorem rho_isActOf {O : Type} [CommRing O] (act : OAct O G) (M : LieModel G x E) : M.IsActOf act.act (rho act M) :=
  fun a e => by letI := act.hom a; exact diff_spec M (act.act a) e

end PositivityTheory.Xgf.TransportLieModel

namespace PositivityTheory.Xgf

open TransportLieModel in
theorem lie_model_action_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (R : Type) [CommRing R] [IsLocalRing R] (x : Sp R ⟶ S), ∃ (n : ℕ) (M : LieModel t.G x (Fin n → R)) (ρ : 𝓞 E →+* Module.End R (Fin n → R)), M.IsActOf t.act.act ρ ∧ ∀ (R' : Type) [CommRing R'] (f : R →+* R') (x' : Sp R' ⟶ S), x' = spMap f ≫ x → ∃ (M' : LieModel t.G x' (Fin n → R')) (ρ' : 𝓞 E →+* Module.End R' (Fin n → R')), M'.IsActOf t.act.act ρ' ∧ (∀ u, (M'.pt (f ∘ u)).left = spMap (dualMap f) ≫ (M.pt u).left) ∧ ∀ a u, ρ' a (f ∘ u) = f ∘ ρ a u := by
  intro E _ _ _ H S t R _ _ x
  letI := t.grp
  haveI := t.comm
  haveI : Smooth t.G.hom := t.semi.smooth
  obtain ⟨L, _, _, ⟨M0⟩⟩ := lieModel_exists S t.G R x
  obtain ⟨hfin, hproj⟩ := T.lie_model_finite_projective S t.G R x L M0
  haveI := hfin
  haveI := hproj
  haveI : Module.Free R L := Module.free_of_flat_of_isLocalRing
  let b := Module.finBasis R L
  let M := transport M0 b.equivFun
  refine ⟨Module.finrank R L, M, rho t.act M, rho_isActOf t.act M, ?_⟩
  intro R' _ f x' hx'
  subst hx'
  letI : Algebra R R' := f.toAlgebra
  obtain ⟨T', _, _, _, _, M1, j, hj, hbc⟩ := FlagFib.lieModel_liftBaseChange S t.G R R' x L M0
  let b' := hbc.basis b
  let M' : LieModel t.G (spMap f ≫ x) (Fin (Module.finrank R L) → R') := transport M1 b'.equivFun
  have key : ∀ u : Fin (Module.finrank R L) → R, b'.equivFun.symm (f ∘ u) = j (b.equivFun.symm u) := by
    intro u
    apply b'.equivFun.injective
    rw [LinearEquiv.apply_symm_apply]
    funext i
    rw [Module.Basis.equivFun_apply, IsBaseChange.basis_repr_comp_apply, ← Module.Basis.equivFun_apply,
      LinearEquiv.apply_symm_apply]
    rfl
  have hpt : ∀ u, M'.pt (f ∘ u) = M1.pt (j (b.equivFun.symm u)) := by
    intro u
    show M1.pt (b'.equivFun.symm (f ∘ u)) = _
    rw [key]
  refine ⟨M', rho t.act M', rho_isActOf t.act M', ?_, ?_⟩
  · intro u
    rw [hpt]
    have h3 := hj (b.equivFun.symm u)
    simp only [LieModel.Lifts, Category.comp_id] at h3
    exact h3
  · intro a u
    apply M'.inj
    have h1 := rho_isActOf t.act M' a (f ∘ u)
    have h2 : M0.pt (b.equivFun.symm (rho t.act M a u)) = M0.pt (b.equivFun.symm u) ≫ t.act.act a :=
      rho_isActOf t.act M a u
    rw [h1, hpt, hpt]
    have h3 := hj (b.equivFun.symm u)
    have h4 := hj (b.equivFun.symm (rho t.act M a u))
    simp only [LieModel.Lifts, Category.comp_id] at h3 h4
    ext1
    rw [Over.comp_left, h3, h4, h2, Over.comp_left, Category.assoc]

end PositivityTheory.Xgf
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.Xgf.isogeny_decomposition_product

theorem tan_comp {S : Scheme.{0}} {R : Type} [CommRing R] {A B : Over S} [GrpObj A] [GrpObj B] {x : Sp R ⟶ S}
    (t : epsAt x ⟶ A) (ht : IsTanAt A x t) (g : A ⟶ B) [IsMonHom g] : IsTanAt B x (t ≫ g) := by
  unfold IsTanAt at ht ⊢
  rw [Over.comp_left, ← Category.assoc, ht, ← Over.comp_left, MonObj.one_comp]

theorem one_left {S : Scheme.{0}} {X A : Over S} [GrpObj A] : (1 : X ⟶ A).left = X.hom ≫ η[A].left := by
  rw [Hom.one_def]; simp

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    spMap b ≫ spMap a = spMap (b.comp a) := by
  simp [spMap, ← Spec.map_comp]

theorem bc_one {R V : Type} [CommRing R] [CommRing V] (f : R →+* V) {A : Over (Sp R)} [GrpObj A] :
    spMap (dualMap f) ≫ (1 : epsR R ⟶ A).left = (1 : epsAt (spMap f ≫ 𝟙 (Sp R)) ⟶ A).left := by
  rw [one_left, one_left, ← Category.assoc]
  congr 1
  simp only [Over.mk_hom, Category.comp_id]
  rw [spMap_comp, spMap_comp]
  congr 1
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem bc_eps {R V : Type} [CommRing R] [CommRing V] (f : R →+* V) (N : ℕ) :
    spMap (dualMap f) ≫ spMap (GlobalTheory.CompanionTheory.Ar.epsMul (N : R)) = spMap (GlobalTheory.CompanionTheory.Ar.epsMul (N : V)) ≫ spMap (dualMap f) := by
  rw [spMap_comp, spMap_comp]
  congr 1
  ext a <;> simp [dualMap, GlobalTheory.CompanionTheory.Ar.epsMul, TrivSqZeroExt.algebraMap_eq_inl, mul_comm]

theorem pow_left {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] [IsCommMonObj A] (v : epsR R ⟶ A)
    (hv : IsLieBasis ![v]) (N : ℕ) :
    v.left ≫ (𝟙 A ^ N).left = spMap (GlobalTheory.CompanionTheory.Ar.epsMul (N : R)) ≫ v.left := by
  obtain ⟨E, _, _, ⟨M⟩⟩ := lieModel_exists (Sp R) A R (𝟙 (Sp R))
  obtain ⟨b, hb⟩ := basis_of_lieBasis v hv M
  have e1 : toAt v = M.pt (b 0) := Over.OverMorphism.ext (by rw [toAt_left, hb])
  have h := congrArg Over.Hom.left (comp_pow' (toAt v) (𝟙 A) N)
  rw [Category.comp_id, e1, ← pt_nsmul, Over.comp_left, ← e1, toAt_left, ← Nat.cast_smul_eq_nsmul R,
    M.smul, ← e1, toAt_left] at h
  exact h

end PositivityTheory.Xgf.isogeny_decomposition_product

namespace PositivityTheory.Xgf

open PositivityTheory.Xgf.isogeny_decomposition_product in
theorem isogeny_decomposition_product : ∀ (R V : Type) [CommRing R] [CommRing V] [IsLocalRing V] (f : R →+* V) (n N : ℕ) (C : Fin n → Out.PolAV (Sp R)) (v : ∀ k, epsR R ⟶ (C k).A) (B : Out.PolAV (Sp R)) (ψ : ∀ k, (C k).A ⟶ B.A) (χ : ∀ k, B.A ⟶ (C k).A) (G : Over (Sp V)) [GrpObj G] (π : G.left ⟶ B.A.left), B.g = n → (∀ k, IsLieBasis ![v k]) → (∀ k, IsMonHom (ψ k)) → (∀ k, IsMonHom (χ k)) → (∀ k, ψ k ≫ χ k = 𝟙 (C k).A ^ N) → (∀ k k', k ≠ k' → ψ k ≫ χ k' = 1) → IsUnit (N : V) → IsGrpPullback G B.A (spMap f) π → ∃ u : Fin n → (epsAt (𝟙 (Sp V)) ⟶ G), (∀ k, (u k).left ≫ π = spMap (dualMap f) ≫ (v k).left ≫ (ψ k).left) ∧ (∀ k, IsTanAt G _ (u k)) ∧ ∀ w, IsTanAt G _ w → ∃! cc : Fin n → V, IsComb cc u w := by
  intro R V _ _ _ f n N C v B ψ χ G _ π hg hv hψ hχ hpc hpo hN hpb
  obtain ⟨EBR, _, _, ⟨MBR⟩⟩ := lieModel_exists (Sp R) B.A R (𝟙 (Sp R))
  obtain ⟨EBV, _, _, ⟨MBV⟩⟩ := lieModel_exists (Sp R) B.A V (spMap f ≫ 𝟙 (Sp R))
  obtain ⟨j, hj, -⟩ := GlobalTheory.T.lie_model_existsUnique_semilinear (Sp R) B.A R V f (𝟙 _) EBR EBV MBR MBV
  have hx : spMap f ≫ 𝟙 (Sp R) = 𝟙 (Sp V) ≫ spMap f := by simp
  obtain ⟨MG, hMG⟩ := (GlobalTheory.T.lie_model_pullback_equivalence (Sp R) (Sp V) B.A G (spMap f) π hpb V (𝟙 (Sp V)) EBV).1 (castM hx MBV)
  have hMG' : ∀ e, (MG.pt e).left ≫ π = (MBV.pt e).left := fun e => (hMG e).trans (castM_left hx MBV e)

  have hvt : ∀ k, IsTanAt B.A (𝟙 (Sp R)) (toAt (v k) ≫ ψ k) := fun k => by
    haveI := hψ k; exact tan_comp _ (toAt_tan (v k) ((hv k).1 0)) (ψ k)
  choose eR heR using fun k => MBR.onto _ (hvt k)
  let EV : Fin n → EBV := fun k => j (eR k)
  have hlift : ∀ e, (MBV.pt (j e)).left = spMap (dualMap f) ≫ (MBR.pt e).left := fun e =>
    (Category.comp_id (MBV.pt (j e)).left).symm.trans (hj e)
  have hEV : ∀ k, (MBV.pt (EV k)).left = spMap (dualMap f) ≫ (v k).left ≫ (ψ k).left := fun k => by
    show (MBV.pt (j (eR k))).left = _
    rw [hlift, heR, Over.comp_left, toAt_left]

  choose EC iC mC MC bC hbC using fun k => lc (C k) (v k) (hv k) V f
  have hd : ∀ k, ∃ A : EBV →ₗ[V] EC k, ∀ e, (MC k).pt (A e) = MBV.pt e ≫ χ k := fun k => by
    haveI := hχ k
    exact (GlobalTheory.T.lie_model_functorial_map (Sp R) B.A (C k).A V (spMap f ≫ 𝟙 (Sp R)) EBV (EC k) MBV (MC k) (χ k)).exists
  choose dχ hdχ using hd
  let fV : Fin n → (EBV →ₗ[V] V) := fun k => ((bC k).coord 0).comp (dχ k)
  have hval : ∀ i k, fV k (EV i) = if i = k then (N : V) else 0 := by
    intro i k
    have hleft : ((MC k).pt (dχ k (EV i))).left = spMap (dualMap f) ≫ (v i).left ≫ (ψ i ≫ χ k).left := by
      rw [hdχ, Over.comp_left, hEV, Over.comp_left]; simp only [Category.assoc]
    split_ifs with hik
    · subst hik
      have e2 : dχ i (EV i) = (N : V) • bC i 0 := by
        apply (MC i).inj
        apply Over.OverMorphism.ext
        rw [hleft, hpc, (MC i).smul, hbC, pow_left (v i) (hv i) N, ← Category.assoc, bc_eps, Category.assoc]
      simp [fV, e2]
    · have e2 : dχ k (EV i) = 0 := by
        apply (MC k).inj
        apply Over.OverMorphism.ext
        rw [hleft, hpo i k hik, pt_zero, ← bc_one f]
        congr 1
        rw [← Over.comp_left, MonObj.comp_one]
      simp [fV, e2]
  obtain ⟨bB⟩ := GlobalTheory.T.lie_model_free_of_smooth (Sp R) B.A n (hg ▸ B.smoothDim) V (spMap f ≫ 𝟙 (Sp R)) EBV MBV
  obtain ⟨hli, hsp⟩ := GlobalTheory.T.dual_family_is_basis V EBV n bB EV fV (N : V) hN hval
  have bridge := (GlobalTheory.T.lie_model_eigenvectors_action (Sp V) V G (𝟙 (Sp V)) EBV MG).1 n
  refine ⟨fun k => MG.pt (EV k), fun k => hMG' (EV k) ▸ hEV k, fun k => MG.tan _, fun w hw => ?_⟩
  obtain ⟨e, rfl⟩ := MG.onto w hw
  have hmem : e ∈ Submodule.span V (Set.range EV) := hsp ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun V).1 hmem
  refine ⟨c, (bridge c EV _).2 (by rw [hc]), fun c' hc' => ?_⟩
  have h1 := MG.inj ((bridge c' EV _).1 hc')
  rw [← hc] at h1
  have h2 := Fintype.linearIndependent_iff.1 hli (c' - c) (by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h1, sub_self])
  funext i
  have := h2 i
  rw [Pi.sub_apply, sub_eq_zero] at this
  exact this

end PositivityTheory.Xgf

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem symplectic_form_skew (D : Datum H) (x y : D.La) : D.EF x y = -D.EF y x := by
  have h := D.alt (x + y)
  simp only [map_add (f := _), LinearMap.add_apply, D.alt x, D.alt y, zero_add, add_zero] at h
  linarith

theorem Host_rt0_ne_neg : H.rt0 ≠ -H.rt0 := by
  intro h
  have h0 : H.rt0 = 0 := by linear_combination h / 2
  have hs := H.sqrt_neg_disc_sq
  rw [h0] at hs
  have hd : (H.d : ℂ) ≠ 0 := by exact_mod_cast H.d_prime.ne_zero
  apply hd
  linear_combination hs

theorem pure_type_lattices_orthogonal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) (a b : D.La), a ∈ PureType.lat hP (sgnRt H true) → b ∈ PureType.lat hP (sgnRt H false) → sesq D a b = 0 ∧ sesq D b a = 0 := by
  intro E _ _ _ H D g ty P hP a b ha hb
  simp only [sgnRt, if_true, Bool.false_eq_true, if_false] at ha hb
  constructor
  · unfold sesq
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [GlobalTheory.CM.FamCompare.orth_of_pure hP ((PureType.lat hP H.rt0).smul_mem _ ha) hb]
    simp
  · unfold sesq
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [symplectic_form_skew D, GlobalTheory.CM.FamCompare.orth_of_pure hP ha ((PureType.lat hP (-H.rt0)).smul_mem _ hb)]
    simp

theorem pure_family_decomposition : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) (p q : ℕ) (x : Fin p ⊕ Fin q → D.La) (n : ℕ), IsPure hP x → (∀ y : D.La, n • y ∈ Submodule.span (𝓞 E) (Set.range x)) → (∀ y : D.La, ∃ a ∈ PureType.lat hP (sgnRt H true), ∃ b ∈ PureType.lat hP (sgnRt H false), n • y = a + b) ∧ (∀ y ∈ PureType.lat hP (sgnRt H true), n • y ∈ Submodule.span (𝓞 E) (Set.range (x ∘ Sum.inl))) ∧ ∀ y ∈ PureType.lat hP (sgnRt H false), n • y ∈ Submodule.span (𝓞 E) (Set.range (x ∘ Sum.inr)) := by
  intro E _ _ _ H D g ty P hP p q x n hx hn

  have hsplit : ∀ y : D.La, ∃ a ∈ Submodule.span (𝓞 E) (Set.range (x ∘ Sum.inl)),
      ∃ b ∈ Submodule.span (𝓞 E) (Set.range (x ∘ Sum.inr)), n • y = a + b := by
    intro y
    have h := hn y
    have e : Set.range x = Set.range (x ∘ Sum.inl) ∪ Set.range (x ∘ Sum.inr) := by
      ext z; constructor
      · rintro ⟨(i | j), rfl⟩
        · exact Or.inl ⟨i, rfl⟩
        · exact Or.inr ⟨j, rfl⟩
      · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
        · exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
    rw [e, Submodule.span_union, Submodule.mem_sup] at h
    obtain ⟨a, ha, b, hb, hab⟩ := h
    exact ⟨a, ha, b, hb, hab.symm⟩
  have hlatL : Submodule.span (𝓞 E) (Set.range (x ∘ Sum.inl)) ≤ PureType.lat hP (sgnRt H true) :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hx.1 i)
  have hlatR : Submodule.span (𝓞 E) (Set.range (x ∘ Sum.inr)) ≤ PureType.lat hP (sgnRt H false) :=
    Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hx.2 j)
  have hboth : ∀ z, z ∈ PureType.lat hP (sgnRt H true) → z ∈ PureType.lat hP (sgnRt H false) → z = 0 := by
    intro z h1 h2
    apply hP.2.1
    rw [map_zero]
    funext j
    by_cases hj : ty j (H.rt : E) = H.rt0
    · have : ty j (H.rt : E) ≠ -H.rt0 := by rw [hj]; exact Host_rt0_ne_neg
      exact h2 j (by simpa [sgnRt] using this)
    · exact h1 j (by simpa [sgnRt] using hj)
  refine ⟨fun y => ?_, fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨a, ha, b, hb, e⟩ := hsplit y
    exact ⟨a, hlatL ha, b, hlatR hb, e⟩
  · obtain ⟨a, ha, b, hb, e⟩ := hsplit y
    have hb0 : b = 0 := hboth b (by
      have : b = n • y - a := by rw [e]; abel
      rw [this]
      exact Submodule.sub_mem _ (Submodule.smul_of_tower_mem _ _ hy) (hlatL ha)) (hlatR hb)
    rw [e, hb0, add_zero]; exact ha
  · obtain ⟨a, ha, b, hb, e⟩ := hsplit y
    have ha0 : a = 0 := hboth a (hlatL ha) (by
      have : a = n • y - b := by rw [e]; abel
      rw [this]
      exact Submodule.sub_mem _ (Submodule.smul_of_tower_mem _ _ hy) (hlatR hb))
    rw [e, ha0, zero_add]; exact hb

end PositivityTheory.Xgf
end
