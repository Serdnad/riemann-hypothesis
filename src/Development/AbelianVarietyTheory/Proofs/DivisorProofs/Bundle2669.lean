module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle666
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2593
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle134
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle164
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle111
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CompHS GlobalTheory.FlagMod GlobalTheory.Reg GlobalTheory.ShFam
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.FlagHodge

attribute [local instance] Over.cartesianMonoidalCategory

theorem ev_cocycle {Z : Scheme.{0}} {L : LB Z} (hL : L.IsLB) {S : Type} [CommRing S] (z : Sp S ⟶ Z) (i j k : L.ι)
    (hij : ⊤ ≤ z ⁻¹ᵁ (L.U i ⊓ L.U j)) (hjk : ⊤ ≤ z ⁻¹ᵁ (L.U j ⊓ L.U k)) (hik : ⊤ ≤ z ⁻¹ᵁ (L.U i ⊓ L.U k)) :
    ev z _ hij (L.g i j).val * ev z _ hjk (L.g j k).val = ev z _ hik (L.g i k).val := by
  have h3 : ⊤ ≤ z ⁻¹ᵁ (L.U i ⊓ L.U j ⊓ L.U k) := le_preimage_inf hij (le_preimage_mono inf_le_right hjk)
  have e := congrArg (fun u => ev z _ h3 u.val) (hL.cocycle i j k)
  exact (congrArg₂ (· * ·) (ev_res z _ h3 hij _).symm (ev_res z _ h3 hjk _).symm).trans
    ((map_mul (ev z _ h3) _ _).symm.trans (e.trans (ev_res z _ h3 hik _)))

theorem lbIso_of_coboundary {Z : Scheme.{0}} {J : Type} {U : J → Z.Opens} {g g' : ∀ i j, Γ(Z, U i ⊓ U j)ˣ}
    (hA : (⟨J, U, g⟩ : LB Z).IsLB) (d : ∀ k, Γ(Z, U k)ˣ)
    (h : ∀ k k', (g' k k').val * resG Z inf_le_right (d k').val = (g k k').val * resG Z inf_le_left (d k).val) :
    LBIso (⟨J, U, g⟩ : LB Z) ⟨J, U, g'⟩ := by
  refine ⟨⟨fun p => g p.1 p.2 * res inf_le_left (d p.1)⟩, fun p q => ?_⟩
  refine Eq.trans ?_ (mul_right_comm _ _ _)
  refine eq_mul_inv_of_mul_eq (Units.ext (ext_ev fun S _ z hz => ?_))
  have hp := le_preimage_mono inf_le_left hz
  have hq := le_preimage_mono inf_le_right hz
  have hp1 : ⊤ ≤ z ⁻¹ᵁ U p.1 := le_preimage_mono inf_le_left hp
  have hq1 : ⊤ ≤ z ⁻¹ᵁ U q.1 := le_preimage_mono inf_le_left hq
  have hp2 : ⊤ ≤ z ⁻¹ᵁ U p.2 := le_preimage_mono inf_le_right hp
  have hq2 : ⊤ ≤ z ⁻¹ᵁ U q.2 := le_preimage_mono inf_le_right hq
  have c₁ := ev_cocycle hA z p.1 p.2 q.2 hp (le_preimage_inf hp2 hq2) (le_preimage_inf hp1 hq2)
  have c₂ := ev_cocycle hA z p.1 q.1 q.2 (le_preimage_inf hp1 hq1) hq (le_preimage_inf hp1 hq2)
  have c₃ := congrArg (ev z _ (le_preimage_inf hp1 hq1)) (h p.1 q.1)
  rw [map_mul, map_mul, ev_res z _ _ hq1, ev_res z _ _ hp1] at c₃
  refine (map_mul (ev z _ hz) _ _).trans (Eq.trans ?_ (map_mul (ev z _ hz) _ _).symm)
  refine (congrArg₂ (· * ·) ((ev_res z _ hz hp _).trans ((map_mul (ev z _ hp) _ _).trans
    (congrArg (_ * ·) (ev_res z _ hp hp1 _)))) (ev_res z _ hz (le_preimage_inf hp2 hq2) _)).trans (Eq.trans ?_
    (congrArg₂ (· * ·) (ev_res z _ hz (le_preimage_inf hp1 hq1) _) ((ev_res z _ hz hq _).trans
      ((map_mul (ev z _ hq) _ _).trans (congrArg (_ * ·) (ev_res z _ hq hq1 _))))).symm)
  have alg : ∀ a b e m n u v w : S, a * b = e → m * n = e → w * v = m * u → a * u * b = w * (n * v) :=
    fun a b e m n u v w h₁ h₂ h₃ => by linear_combination u * (h₁ - h₂) - n * h₃
  exact alg _ _ _ _ _ _ _ _ c₁ c₂ c₃

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y)

theorem exists_eigFrame {W : X.YY.Opens} (hW : IsAffineOpen W) {S : Type} [CommRing S] (z : Sp S ⟶ X.YY)
    (hzW : ⊤ ≤ z ⁻¹ᵁ W) : ∃ φ : c.F →+* S, ∀ (k : X.F.J) (_ : W ≤ X.F.U k) (hz : ⊤ ≤ z ⁻¹ᵁ X.F.U k),
      ∃ f : EigFrame Y φ (z ≫ X.π), ∀ τ, f.vec τ = X.F.vecAt k z hz rfl τ := by
  obtain ⟨ψ, rfl⟩ : ∃ ψ : Γ(X.YY, W) →+* S, spMap ψ ≫ tau hW = z := ⟨_, spMap_ev z hW hzW⟩
  haveI := X.proper
  haveI := GlobalTheory.ThetaDescent.isProper_of_isProjOver Y.proj
  haveI : IsLocallyNoetherian X.YY := LocallyOfFiniteType.isLocallyNoetherian (X.π ≫ Y.s)
  obtain ⟨φ, hφ⟩ : ∃ φ : c.F →+* Γ(X.YY, W), spMap φ = tau hW ≫ X.π ≫ Y.s :=
    ⟨(Spec.preimage (tau hW ≫ X.π ≫ Y.s)).hom, Spec.map_preimage _⟩
  refine ⟨ψ.comp φ, fun k hk hz => ?_⟩
  obtain ⟨K, _, ρ, hρ, hK⟩ := affineOpen_injects_to_dense X.YY (flagOpen X) (dense_flagOpen X) W hW
  letI : Algebra c.F K := (ρ.comp φ).toAlgebra
  have h₀ : ⊤ ≤ tau hW ⁻¹ᵁ X.F.U k := tau_le hW hk
  have hz' : ⊤ ≤ (spMap ρ ≫ tau hW) ⁻¹ᵁ X.F.U k := le_preimage_comp _ h₀
  have hr : Set.range ((spMap ρ ≫ tau hW) ≫ X.π) ⊆ Set.range Y.j := by
    rintro _ ⟨s, rfl⟩
    exact hK (Set.mem_univ s)
  let yK := IsOpenImmersion.lift Y.j ((spMap ρ ≫ tau hW) ≫ X.π) hr
  have hyK : yK ≫ Y.j = (spMap ρ ≫ tau hW) ≫ X.π := IsOpenImmersion.lift_fac _ _ _
  have hjs : Y.j ≫ Y.s = pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) := by
    have h1 : spMap (RingHom.id c.F) = 𝟙 _ := by
      unfold spMap; rw [CommRingCat.ofHom_id, Spec.map_id]
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over, h1, Category.comp_id]
  have hy : yK ≫ pullback.snd _ _ = spMap (algebraMap c.F K) := by
    rw [← hjs, ← Category.assoc, hyK]
    have h2 : spMap ρ ≫ spMap φ = spMap (algebraMap c.F K) := by
      unfold spMap; rw [← Spec.map_comp]; rfl
    rw [← h2, hφ]
    simp only [Category.assoc]
  have key : ∀ (x'' : Sp K ⟶ Y.X) (hx : (spMap ρ ≫ tau hW) ≫ X.π = x''),
      (∀ σ, initSpan K (X.F.vecAt k _ hz' hx σ) (Dw.mult σ) = eigLie c x'' σ) →
      ∀ σ, initSpan K (X.F.vecAt k _ hz' rfl σ) (Dw.mult σ) = eigLie c ((spMap ρ ≫ tau hW) ≫ X.π) σ := by
    rintro x'' rfl h
    exact h
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.ChartEigFrame.exists_eigFrame_of_top ρ hρ φ rfl (tau hW) k h₀ hz'
    (key _ hyK.symm fun σ => X.top K yK hy _ hyK.symm k hz' σ)
  obtain ⟨f, hf⟩ := f₀.exists_isMap ψ rfl (Category.assoc _ _ _)
  refine ⟨f, fun τ => funext fun i => tan_ext_left ?_⟩
  rw [← X.F.tanPull_vecAt k ψ (tau hW) h₀ hz rfl rfl (Category.assoc _ _ _).symm τ i, tanPull_left, ← hf₀, ← hf]
  simp only [EigFrame.vec, GlobalTheory.LieMet.left_tanOf]

def allDet (k : X.F.J) : Γ(X.YY, X.F.U k) :=
  rdet (Matrix.of fun (j : Fin (X.F.M k).n) (a : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ)))) =>
    X.F.u k ((Fintype.equivFin _).symm a).1 j ((Fintype.equivFin _).symm a).2)

theorem ev_allDet (k : X.F.J) {S : Type} [CommRing S] {z : Sp S ⟶ X.YY} (hz : ⊤ ≤ z ⁻¹ᵁ X.F.U k) {φ : c.F →+* S}
    {f : EigFrame Y φ (z ≫ X.π)} (hf : ∀ τ, f.vec τ = X.F.vecAt k z hz rfl τ) :
    ev z _ hz (allDet X k) = frameDet (X.F.M k).toMChart (X.F.inM hz rfl) f := by
  rw [allDet, map_rdet, frameDet]
  congr 1
  ext j a
  simp [Module.Basis.toMatrix_apply, eigBasisFin, eigBasis_apply, hf, Frames.vecAt, Frames.uAt, vec,
    Finsupp.single_apply]

theorem isUnit_allDet (k : X.F.J) : IsUnit (allDet X k) := by
  refine X.YY.toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx => ?_
  obtain ⟨W, hW, hxW, hle⟩ := exists_isAffineOpen_mem_and_subset (X := X.YY) (U := X.F.U k) (x := x) hx
  obtain ⟨φ, hφ⟩ := exists_eigFrame X hW (tau hW) (tau_le hW le_rfl)
  obtain ⟨f, hf⟩ := hφ k hle (tau_le hW hle)
  have hu := isUnit_frameDet (X.F.M k).toMChart (X.F.inM (tau_le hW hle) rfl) f
  rw [← ev_allDet X k _ hf, ev_tau hW hle] at hu
  have := hu.map (X.YY.presheaf.germ W x hxW).hom
  rwa [show (X.YY.presheaf.germ W x hxW).hom (resG X.YY hle (allDet X k)) = _ from
    X.YY.presheaf.germ_res_apply (homOfLE hle) x hxW _] at this

theorem lbIso_detOm_Llam : LBIso X.detOm (X.Llam (mu0 Dw)) := by
  classical
  rw [FlagCover.Llam, unitaryWeightExponentVector_signatureWeightMuZero]
  refine lbIso_of_coboundary X.F.isLB_detOm (fun k => (isUnit_allDet X k).unit) fun k k' =>
    ext_ev_loc fun x hx => ?_
  obtain ⟨W, hW, hxW, hle⟩ := exists_isAffineOpen_mem_and_subset (X := X.YY) (U := X.F.U k ⊓ X.F.U k') (x := x) hx
  refine ⟨W, hxW, fun S _ z hh hzW => ?_⟩
  have hz := le_preimage_mono inf_le_left hh
  have hz' := le_preimage_mono inf_le_right hh
  have hM := le_preimage_inf (X.F.inM hz rfl) (X.F.inM hz' rfl)
  obtain ⟨φ, hφ⟩ := exists_eigFrame X hW z hzW
  obtain ⟨f, hf⟩ := hφ k (fun _ h => (hle h).1) hz
  obtain ⟨f', hf'⟩ := hφ k' (fun _ h => (hle h).2) hz'
  have hco : ∀ τ, f.co f' τ = (X.F.B k k' τ).map (ev z _ hh) := fun τ => by
    ext a i
    have e := f.vec_eq f' τ i
    rw [hf', X.F.vecAt_eq_sum k k' z hz hz' hh rfl τ i, ← hf] at e
    exact ((Fintype.linearIndependent_iffₛ.1 (f.linearIndependent_vec τ)) _ _ e a).symm
  have e₁ := (ev_detChg_mul_frameDet (X.F.M k).toMChart (X.F.M k').toMChart (X.F.inM hz rfl) (X.F.inM hz' rfl) hM
    f').trans (frameDet_change _ _ f f')
  have e₂ : ∏ τ, (f.co f' τ).det = (∏ p : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), X.F.TAt k k' z hh (some p)).val := by
    rw [Units.coe_prod, Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [hco, Matrix.det_of_upperTriangular (X.F.B_map_tri k k' τ _)]
    rfl
  have e₃ := X.F.ev_LL_g (fun ix => ix.elim 0 fun _ => 1) k k' z hh
  rw [Fintype.prod_option] at e₃
  simp only [Option.elim, neg_zero, zpow_zero, one_mul, zpow_neg, zpow_one, Finset.prod_inv_distrib] at e₃
  let a : Sˣ := Units.map (ev (z ≫ X.π) _ hM).toMonoidHom (detChg (X.F.M k).toMChart (X.F.M k').toMChart)
  have e₄ : ev z _ hh (X.F.detOm.g k k').val = (a⁻¹).val :=
    (ev_unit_inv z hh _).trans (congrArg (fun u : Sˣ => (u⁻¹).val) (Units.ext (ev_appLE z X.π _ hh hM _)))
  rw [← ev_allDet X k hz hf, ← ev_allDet X k' hz' hf', e₂] at e₁
  rw [map_mul, map_mul, ev_res z _ hh hz, ev_res z _ hh hz']
  refine (congrArg (· * _) e₃).trans (Eq.trans ?_ (congrArg (· * _) e₄).symm)
  rw [_root_.one_mul, Units.inv_mul_eq_iff_eq_mul, mul_left_comm, Units.eq_inv_mul_iff_mul_eq, _root_.mul_comm (Units.val _) (ev z _ hz _)]
  exact e₁

end GlobalTheory.FlagHodge
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

noncomputable section

namespace GlobalTheory.LevelDescent

open GlobalTheory.SiegelPull GlobalTheory.CharZeroPts

theorem exists_geomPt_specializes (R : Type) [CommRing R] (R₁ : Subring R) (p : Sp R₁) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (z : Sp K ⟶ Sp R), ∀ u, (z ≫ spMap R₁.subtype) u ⤳ p := by
  haveI := p.isPrime
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R₁)) (J := p.asIdeal) bot_le
  obtain ⟨P, hP, hPq⟩ :=
    Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective (f := R₁.subtype) Subtype.val_injective q hq
  obtain ⟨K, _, _, t, ht⟩ := GlobalTheory.SiegelTypings.exists_geomPt (S := Sp R) ⟨P, hP⟩
  refine ⟨K, inferInstance, inferInstance, t, fun u => ?_⟩
  have e : t u = ⟨P, hP⟩ := by
    obtain ⟨v, hv⟩ := ht
    rw [Subsingleton.elim u v, hv]
  rw [Scheme.Hom.comp_apply, e]
  refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
  show P.comap R₁.subtype ≤ p.asIdeal
  rw [hPq]
  exact hqp

section Labels

variable {h M : ℕ}

def toStd : (Fin (h + h) → ZMod M) →+ IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit.Std h M where
  toFun c := (fun i => c (Fin.castAdd h i), fun i => c (Fin.natAdd h i))
  map_zero' := rfl
  map_add' _ _ := rfl

theorem toStd_append (a : IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit.Std h M) : toStd (Fin.append a.1 a.2) = a :=
  Prod.ext (funext fun i => Fin.append_left a.1 a.2 i) (funext fun i => Fin.append_right a.1 a.2 i)

theorem append_toStd (c : Fin (h + h) → ZMod M) : Fin.append (toStd c).1 (toStd c).2 = c :=
  Fin.append_castAdd_natAdd

theorem toStd_injective : Function.Injective (toStd (h := h) (M := M)) := fun c c' e => by
  rw [← append_toStd c, ← append_toStd c', e]

theorem sum_val_smul [NeZero M] (c : Fin (h + h) → ZMod M) :
    ∑ i, (c i).val • toStd (Pi.single i (1 : ZMod M)) = toStd c := by

  simp_rw [← map_nsmul, ← map_sum]
  congr 1
  conv_rhs => rw [← Finset.univ_sum_single c]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Pi.single_smul, nsmul_eq_mul, _root_.mul_one, ZMod.natCast_zmod_val]

end Labels

section Sections

variable {S : Scheme.{0}} {h M : ℕ} {A : Over S} [GrpObj A] {lv : IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit.Std h M → (𝟙_ (Over S) ⟶ A)}

theorem lv_zero (add : ∀ a b, lv (a + b) = lv a * lv b) : lv 0 = 1 := by
  have e := add 0 0
  rw [add_zero] at e
  exact left_eq_mul.1 e

theorem lv_nsmul (add : ∀ a b, lv (a + b) = lv a * lv b) (n : ℕ) (a) : lv (n • a) = lv a ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, lv_zero add]
  | succ n ih => rw [succ_nsmul, add, ih, pow_succ]

theorem lv_pow (add : ∀ a b, lv (a + b) = lv a * lv b) (a) : lv a ^ M = 1 := by
  rw [← lv_nsmul add, show M • a = 0 by ext i <;> simp, lv_zero add]

theorem linComb_lv (add : ∀ a b, lv (a + b) = lv a * lv b) {T : Over S} (g : T ⟶ 𝟙_ (Over S)) :
    ∀ {r : ℕ} (v : Fin r → IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit.Std h M) (n : Fin r → ℕ),
      Out.linComb (fun i => g ≫ lv (v i)) n = g ≫ lv (∑ i, n i • v i) := by
  intro r
  induction r with
  | zero =>
    intro v n
    simp [Out.linComb, lv_zero add]
  | succ r ih =>
    intro v n
    have e := ih (fun i => v i.succ) (fun i => n i.succ)
    simp only [Out.linComb] at e ⊢
    rw [List.ofFn_succ, List.prod_cons, e, Fin.sum_univ_succ, add, MonObj.comp_mul, lv_nsmul add,
      MonObj.comp_pow]

end Sections

end GlobalTheory.LevelDescent

namespace GlobalTheory.LevelDescent

open GlobalTheory.SiegelPull GlobalTheory.CharZeroPts

section Cond

variable {S : Scheme.{0}} {h M : ℕ} {A : Over S} [GrpObj A] {lv : IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit.Std h M → (𝟙_ (Over S) ⟶ A)}

theorem cond_iff [NeZero M] (add : ∀ a b, lv (a + b) = lv a * lv b) {k : Type} [Field k] (x : Sp k ⟶ S) :
    ((Function.Injective fun a => toUnit (Over.mk x) ≫ lv a) ∧
      ∀ g : Over.mk x ⟶ A, g ^ M = 1 ↔ ∃ a, toUnit (Over.mk x) ≫ lv a = g) ↔
    ∀ y : Over.mk x ⟶ A, y ^ M = 1 → ∃! c : Fin (h + h) → ZMod M,
      Out.linComb (fun i => toB x ≫ lv (toStd (Pi.single i 1))) (fun i => (c i).val) = y := by
  have E : ∀ c : Fin (h + h) → ZMod M,
      Out.linComb (fun i => toB x ≫ lv (toStd (Pi.single i 1))) (fun i => (c i).val) =
        toUnit (Over.mk x) ≫ lv (toStd c) := fun c =>
    (linComb_lv add (toB x) _ _).trans (by rw [sum_val_smul]; rfl)
  have tors : ∀ a, (toUnit (Over.mk x) ≫ lv a) ^ M = 1 := fun a => by
    rw [← MonObj.comp_pow, lv_pow add, MonObj.comp_one]
  constructor
  · rintro ⟨inj, sp⟩ y hy
    obtain ⟨a, rfl⟩ := (sp y).1 hy
    refine ⟨Fin.append a.1 a.2, by beta_reduce; rw [E, toStd_append], fun c hc => toStd_injective ?_⟩
    rw [toStd_append]
    exact inj ((E c).symm.trans hc)
  · intro H
    refine ⟨fun a b e => ?_, fun g => ⟨fun hg => ?_, ?_⟩⟩
    · obtain ⟨c, -, hc⟩ := H _ (tors a)
      have ea := hc (Fin.append a.1 a.2) (by beta_reduce; rw [E, toStd_append])
      have eb := hc (Fin.append b.1 b.2) (by beta_reduce; rw [E, toStd_append]; exact e.symm)
      rw [← toStd_append a, ← toStd_append b, ea, eb]
    · obtain ⟨c, hc, -⟩ := H g hg
      exact ⟨toStd c, (E c).symm.trans hc⟩
    · rintro ⟨a, rfl⟩
      exact tors a

end Cond

section Transfer

variable {h M : ℕ} {S S₁ : Scheme.{0}} {A : Over S} [GrpObj A] {A₁ : Over S₁} [GrpObj A₁] {f : S ⟶ S₁}
  {φ : A.left ⟶ A₁.left} {lv : IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit.Std h M → (𝟙_ (Over S) ⟶ A)}
  {lv₁ : IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit.Std h M → (𝟙_ (Over S₁) ⟶ A₁)}

theorem push_lv (hp : IsGrpPullback A A₁ f φ) (hl : ∀ a, (lv a).left ≫ φ = f ≫ (lv₁ a).left) (T : Over S) (a) :
    pushHom hp T (toUnit T ≫ lv a) = toUnit (Over.mk (T.hom ≫ f)) ≫ lv₁ a := by
  apply Over.OverMorphism.ext
  show ((toUnit T).left ≫ (lv a).left) ≫ φ = (toUnit (Over.mk (T.hom ≫ f))).left ≫ (lv₁ a).left
  rw [Category.assoc, hl, Over.toUnit_left, Over.toUnit_left, ← Category.assoc]
  rfl

theorem cond_push (hp : IsGrpPullback A A₁ f φ) (hl : ∀ a, (lv a).left ≫ φ = f ≫ (lv₁ a).left) {k : Type} [Field k]
    (x : Sp k ⟶ S)
    (H : (Function.Injective fun a => toUnit (Over.mk x) ≫ lv a) ∧
      ∀ g : Over.mk x ⟶ A, g ^ M = 1 ↔ ∃ a, toUnit (Over.mk x) ≫ lv a = g) :
    (Function.Injective fun a => toUnit (Over.mk (x ≫ f)) ≫ lv₁ a) ∧
      ∀ g : Over.mk (x ≫ f) ⟶ A₁, g ^ M = 1 ↔ ∃ a, toUnit (Over.mk (x ≫ f)) ≫ lv₁ a = g := by
  have P := push_lv hp hl (Over.mk x)
  have inj := push_injective hp (Over.mk x)
  refine ⟨fun a b e => H.1 (inj ?_), fun g => ?_⟩
  · rw [P, P]
    exact e
  · obtain ⟨g', rfl⟩ := push_surjective hp (Over.mk x) g
    rw [← map_pow, ← map_one (pushHom hp (Over.mk x)), inj.eq_iff, H.2 g']
    refine exists_congr fun a => ?_
    rw [← inj.eq_iff, P]
    rfl

end Transfer

end GlobalTheory.LevelDescent

namespace GlobalTheory.LevelDescent

open GlobalTheory.SiegelPull GlobalTheory.CharZeroPts

theorem isLevel_of_subring : ∀ (h M : ℕ) (R : Type) [CommRing R] (R₁ : Subring R) (A : Over (Sp R)) [GrpObj A] (A₁ : Over (Sp R₁)) [GrpObj A₁] (φ : A.left ⟶ A₁.left) (lv : Std h M → (𝟙_ (Over (Sp R)) ⟶ A)) (lv₁ : Std h M → (𝟙_ (Over (Sp R₁)) ⟶ A₁)), 0 < M → IsUnit (M : R₁) → IsAbelianScheme A₁ → IsGrpPullback A A₁ (spMap R₁.subtype) φ → (∀ a, (lv a).left ≫ φ = spMap R₁.subtype ≫ (lv₁ a).left) → (∀ a b, lv₁ (a + b) = lv₁ a * lv₁ b) → IsLevel A lv → IsLevel A₁ lv₁ := by
  intro h M R _ R₁ A _ A₁ _ φ lv lv₁ hM hu hA hp hl hadd hlev
  haveI : NeZero M := ⟨hM.ne'⟩
  have hu' : IsUnit ((M : ℕ) : Γ(Sp R₁, ⊤)) := by
    simpa using hu.map (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom
  refine ⟨hadd, fun k _ _ x => (cond_iff hadd x).2 fun y hy => ?_⟩
  refine torsion_basis_of_generization A₁ M (h + h) (fun i => lv₁ (toStd (Pi.single i 1))) hA hM hu'
    (fun i => lv_pow hadd _) (fun p => ?_) k x y hy
  obtain ⟨K, _, _, z, hz⟩ := exists_geomPt_specializes R R₁ p
  exact ⟨K, inferInstance, inferInstance, z ≫ spMap R₁.subtype, hz,
    (cond_iff hadd _).1 (cond_push hp hl z (hlev.2 K z))⟩

end GlobalTheory.LevelDescent
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.UnitLocus

theorem mem_basicOpen_iff {X : Scheme.{0}} {k : Type} [Field k] (g : Sp k ⟶ X) (s : Γ(X, ⊤)) :
    g (default : PrimeSpectrum k) ∈ X.basicOpen s ↔ IsUnit (g.appTop.hom s) := by
  have p : g ⁻¹ᵁ X.basicOpen s = (Sp k).basicOpen (g.appTop.hom s) := Scheme.preimage_basicOpen g s
  constructor
  · intro H
    refine RingedSpace.isUnit_of_isUnit_germ (Sp k).toRingedSpace ⊤ _ fun y hy => ?_
    have : y ∈ (Sp k).basicOpen (g.appTop.hom s) := by
      rw [← p]
      have e : y = (default : PrimeSpectrum k) := Subsingleton.elim (α := PrimeSpectrum k) _ _
      rw [e]
      exact H
    exact ((Sp k).mem_basicOpen _ y hy).1 this
  · intro H
    have : (default : PrimeSpectrum k) ∈ g ⁻¹ᵁ X.basicOpen s := by
      rw [p, Scheme.basicOpen_of_isUnit _ H]; trivial
    exact this

theorem exists_geometricPoint {X : Scheme.{0}} (x : X) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (g : Sp k ⟶ X), g (default : PrimeSpectrum k) = x := by
  refine ⟨AlgebraicClosure (X.residueField x), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) (AlgebraicClosure (X.residueField x)))) ≫
      X.fromSpecResidueField x, ?_⟩
  exact Scheme.fromSpecResidueField_apply x _

theorem avg_cases {R : Type} [CommRing R] [IsDomain R] {n : ℕ} {m w : R} (hm : m * n = 1) (hw : w ^ n = 1) :
    (w = 1 → m * ∑ i ∈ Finset.range n, w ^ i = 1) ∧ (w ≠ 1 → m * ∑ i ∈ Finset.range n, w ^ i = 0) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa [h] using hm
  · have h₀ : (∑ i ∈ Finset.range n, w ^ i) * (w - 1) = 0 := by rw [geom_sum_mul, hw, sub_self]
    rw [(mul_eq_zero.1 h₀).resolve_right (sub_ne_zero.2 h), mul_zero]

end GlobalTheory.UnitLocus

namespace GlobalTheory


open UnitLocus in
theorem loc_units_eq :
    ∀ (X : Scheme.{0}) (N : ℕ) (c₀ u : Γ(X, ⊤)ˣ), IsUnit (N : Γ(X, ⊤)) → c₀ ^ N = 1 → (∀ (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ X), Units.map g.appTop.hom.toMonoidHom u ^ N = 1) → GlobalTheory.HkClopen.Loc (S := X) (fun (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ X) => Units.map g.appTop.hom.toMonoidHom c₀ = Units.map g.appTop.hom.toMonoidHom u) := by
  intro X N c₀ u hN hc hu
  obtain ⟨m, hm⟩ := hN.exists_left_inv
  let w : Γ(X, ⊤) := (c₀ * u⁻¹).val
  let e : Γ(X, ⊤) := m * ∑ i ∈ Finset.range N, w ^ i
  have key : ∀ (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ X),
      (g (default : PrimeSpectrum k) ∈ X.basicOpen e ↔
        Units.map g.appTop.hom.toMonoidHom c₀ = Units.map g.appTop.hom.toMonoidHom u) ∧
      (g (default : PrimeSpectrum k) ∈ X.basicOpen (1 - e) ↔
        ¬ Units.map g.appTop.hom.toMonoidHom c₀ = Units.map g.appTop.hom.toMonoidHom u) := by
    intro k _ _ g
    have : IsDomain Γ(Sp k, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isDomain k
    have hval : g.appTop.hom w =
        (Units.map g.appTop.hom.toMonoidHom c₀ * (Units.map g.appTop.hom.toMonoidHom u)⁻¹).val := by
      rw [← map_inv, ← map_mul]; rfl
    have h1 : Units.map g.appTop.hom.toMonoidHom c₀ = Units.map g.appTop.hom.toMonoidHom u ↔
        g.appTop.hom w = 1 := by
      rw [hval, Units.val_eq_one, mul_inv_eq_one]
    have hw : g.appTop.hom w ^ N = 1 := by
      rw [hval, ← Units.val_pow_eq_pow_val, mul_pow, inv_pow, hu, ← map_pow, hc, map_one, inv_one,
        _root_.mul_one, Units.val_one]
    have hm' : g.appTop.hom m * N = 1 := by
      have := congrArg g.appTop.hom hm
      rwa [map_mul, map_natCast, map_one] at this
    have he : g.appTop.hom e = g.appTop.hom m * ∑ i ∈ Finset.range N, g.appTop.hom w ^ i := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [e, map_mul, map_sum, map_pow]
    obtain ⟨a, b⟩ := avg_cases hm' hw
    rw [mem_basicOpen_iff, mem_basicOpen_iff, h1, map_sub, map_one, he]
    by_cases h : g.appTop.hom w = 1
    · rw [a h]; simp [h]
    · rw [b h]; simp [h]
  refine ⟨X.basicOpen e, ⟨?_, (X.basicOpen e).isOpen⟩, fun k _ _ g => (key k g).1⟩
  have : (X.basicOpen e : Set X) = (X.basicOpen (1 - e) : Set X)ᶜ := by
    ext x
    obtain ⟨k, _, _, g, rfl⟩ := exists_geometricPoint x
    exact (key k g).1.trans (not_not.symm.trans (not_congr (key k g).2.symm))
  rw [this]
  exact (X.basicOpen (1 - e)).isOpen.isClosed_compl

end GlobalTheory
end
