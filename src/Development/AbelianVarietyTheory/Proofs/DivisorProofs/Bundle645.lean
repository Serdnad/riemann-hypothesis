module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle018
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyRestrictBasisExtendedBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle292
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle452
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCocycleCoboundaryCommaLocalBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle155
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle157
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle290
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle601
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle591
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle500
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle595
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle602
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle590
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle598
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle599
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle503
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle606
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle622
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open GlobalTheory.TanPtMod

namespace GlobalTheory.UPel.HT.ES.WTors

theorem killedBy_iff_map {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) (w : Ideal (𝓞 D.F)) {T : Over S} (x : T ⟶ o.A) :
    GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (w.map (algebraMap (𝓞 D.F) D.O)) x ↔ KilledBy o w x := by
  constructor
  · intro h a ha
    exact h _ (Ideal.mem_map_of_mem _ ha)
  · intro h a ha
    simp only [GlobalTheory.IwLevel.htAct_act]
    refine Submodule.span_induction (p := fun y _ => x ≫ o.act.act y = 1) ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨c, hc, rfl⟩
      exact h c hc
    · have h0 : o.act.act 0 = 1 := by
        have := o.act.add 0 0
        rw [add_zero] at this
        exact mul_left_cancel (this.symm.trans (_root_.mul_one _).symm)
      rw [h0, comp_one]
    · intro y z _ _ hy hz
      rw [o.act.add, comp_mul, hy, hz, _root_.mul_one]
    · intro c y _ hy
      haveI := o.act.hom c
      rw [smul_eq_mul, o.act.mul, ← Category.assoc, hy, one_comp]

end GlobalTheory.UPel.HT.ES.WTors
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs.BasisO

theorem restrict_bijective_one : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (C' : Type)
    [Category.{0} C'] [Quiver.IsThin C'] (G : C' ⥤ AffOp X),
    (∀ (x : X) (U : X.Opens), x ∈ U → ∃ t : C', x ∈ (G.obj t).unop.1 ∧ (G.obj t).unop.1 ≤ U) →
    (∀ (t₁ t₂ : C') (x : X) (U : X.Opens), x ∈ U → x ∈ (G.obj t₁).unop.1 → x ∈ (G.obj t₂).unop.1 →
      ∃ t₃ : C', Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ (G.obj t₃).unop.1 ∧ (G.obj t₃).unop.1 ≤ U) →
    Function.Bijective (CoefMap.restrict (OAff s) G).pull1 := by
  intro R _ X s C' _ _ G h1 h2
  have H := hasLoc_OAff s
  have hcov := BasisExt.hcov_of_basis s G h1
  have hdir := BasisExt.hdir_of_basis s G h2
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s) G H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s) G H hcov hdir
  have hv := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (OAff s) G H hcov hdir
  exact ⟨_root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ hs hg,
    _root_.GlobalTheory.CatCoh.pull1_restrict_surjective_of_comma _ _ hs hg hv⟩

end GlobalTheory.Obs.BasisO
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.levelwiseEquivalence_isEquivalence : GlobalTheory.EtC.A3 := by
  first | (exact @GlobalTheory.EtC.levelwise_eqv) | (exact GlobalTheory.EtC.levelwise_eqv) | (intros; apply GlobalTheory.EtC.levelwise_eqv  <;> assumption)
end

section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

theorem _root_.GlobalTheory.T.degZeroCocycle_exists_coboundary_of_rich_based : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → K.Based → ∀ (h : C1 K.Oc), (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 → h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) → ∃ G : C0 K.Oc, ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → h T T' φ = G T' - φ.φ (G T) := by
  first | exact @GlobalTheory.AnPer.Charts.DegZero.exists_gauge | exact GlobalTheory.AnPer.Charts.DegZero.exists_gauge | (intros; apply GlobalTheory.AnPer.Charts.DegZero.exists_gauge <;> assumption)
end

section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

theorem _root_.GlobalTheory.T.invariant_cochainOne_const_on_degree : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → ∀ (h : C1 K.Oc) (l : Λ), (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = l → ψ.deg = 0 → h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ)) → (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = l → h T T'' (φ ≫ ψ) = h T' T'' ψ) → ∃ p : Hol F.V, ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = l → h T T' φ = algebraMap (Hol F.V) T'.C p := by
  first | exact @GlobalTheory.AnPer.Charts.invCochain_const | exact GlobalTheory.AnPer.Charts.invCochain_const | (intros; apply GlobalTheory.AnPer.Charts.invCochain_const <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
open scoped nonZeroDivisors

namespace GlobalTheory.CMVal.IdeleIdeal

variable {E : Type} [Field E] [NumberField E]

def ordAt (y : (Af E)ˣ) (w : HeightOneSpectrum (𝓞 E)) : ℕ := (-WithZero.log (Valued.v ((y : Af E) w))).toNat

def idealOf (y : (Af E)ˣ) : Ideal (𝓞 E) := ∏ᶠ w : HeightOneSpectrum (𝓞 E), w.asIdeal ^ ordAt y w

theorem ordAt_eventually (y : (Af E)ˣ) : ∀ᶠ w in Filter.cofinite, ordAt y w = 0 := by
  filter_upwards [(FiniteAdeleRing.isUnit_iff.1 y.isUnit).2] with w hw
  simp [ordAt, hw]

theorem finite_pow (y : (Af E)ˣ) :
    (Function.mulSupport fun w : HeightOneSpectrum (𝓞 E) => w.asIdeal ^ ordAt y w).Finite := by
  have := ordAt_eventually y
  rw [Filter.eventually_cofinite] at this
  refine this.subset fun v hv h1 => hv ?_
  simp [h1]

theorem ordAt_cast {y : (Af E)ˣ} {w : HeightOneSpectrum (𝓞 E)} (h : Valued.v ((y : Af E) w) ≤ 1) :
    (ordAt y w : ℤ) = -WithZero.log (Valued.v ((y : Af E) w)) := by
  have h0 := IdeleModule.coord_ne y w
  have : WithZero.log (Valued.v ((y : Af E) w)) ≤ 0 := by
    rw [← WithZero.exp_le_exp, WithZero.exp_log h0, WithZero.exp_zero]; exact h
  unfold ordAt
  omega

theorem modF_eq {y : (Af E)ˣ} (h : ∀ w, Valued.v ((y : Af E) w) ≤ 1) :
    modF y = ((Ideal.absNorm (idealOf y) : ℕ) : ℝ)⁻¹ := by
  unfold idealOf modF
  rw [map_finprod Ideal.absNorm (finite_pow y)]
  have hf : (Function.mulSupport fun w : HeightOneSpectrum (𝓞 E) => Ideal.absNorm (w.asIdeal ^ ordAt y w)).Finite :=
    (finite_pow y).subset fun w hw h1 => hw (by simp only [h1, map_one])
  have := map_finprod (Nat.castRingHom ℝ) hf
  simp only [eq_natCast] at this
  rw [this, ← finprod_inv_distrib]
  refine finprod_congr fun w => ?_
  rw [map_pow, Nat.cast_pow, ← zpow_natCast, ordAt_cast (h w), zpow_neg, inv_inv]

theorem count_idealOf (y : (Af E)ˣ) (w : HeightOneSpectrum (𝓞 E)) :
    FractionalIdeal.count E w (idealOf y : FractionalIdeal (𝓞 E)⁰ E) = ordAt y w := by
  have h1 : (idealOf y : FractionalIdeal (𝓞 E)⁰ E) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 E), (v.asIdeal : FractionalIdeal (𝓞 E)⁰ E) ^ (ordAt y v : ℤ) := by
    have := map_finprod (FractionalIdeal.coeIdealHom (𝓞 E)⁰ E) (finite_pow y)
    simp only [map_pow, FractionalIdeal.coeIdealHom_apply] at this
    simp only [zpow_natCast]
    exact this
  rw [h1, FractionalIdeal.count_finprod]
  filter_upwards [ordAt_eventually y] with v hv
  simp [hv]

theorem val_eq_of_idealOf_eq {y y' : (Af E)ˣ} (h : ∀ w, Valued.v ((y : Af E) w) ≤ 1)
    (h' : ∀ w, Valued.v ((y' : Af E) w) ≤ 1) (e : idealOf y = idealOf y') (w : HeightOneSpectrum (𝓞 E)) :
    Valued.v ((y : Af E) w) = Valued.v ((y' : Af E) w) := by
  have h1 := count_idealOf y w
  rw [e, count_idealOf, ordAt_cast (h w), ordAt_cast (h' w), neg_inj] at h1
  rw [← WithZero.exp_log (IdeleModule.coord_ne y w), ← h1, WithZero.exp_log (IdeleModule.coord_ne y' w)]

end GlobalTheory.CMVal.IdeleIdeal


open GlobalTheory.CMVal.IdeleIdeal in
theorem GlobalTheory.CMVal.exists_idele_section_of_ideal : ∀ (E : Type) [Field E] [NumberField E] , ∃ g : Ideal (𝓞 E) → (Af E)ˣ, ∀ y : (Af E)ˣ, (∀ w, Valued.v ((y : Af E) w) ≤ 1) → ∃ J : Ideal (𝓞 E), modF y = ((Ideal.absNorm J : ℕ) : ℝ)⁻¹ ∧ ∀ w, Valued.v ((((g J)⁻¹ * y : (Af E)ˣ) : Af E) w) = 1 := by
  intro E _ _
  classical
  refine ⟨fun J => if h : ∃ y : (Af E)ˣ, (∀ w, Valued.v ((y : Af E) w) ≤ 1) ∧ idealOf y = J then h.choose else 1,
    fun y hy => ⟨idealOf y, modF_eq hy, fun w => ?_⟩⟩
  have h : ∃ y' : (Af E)ˣ, (∀ w, Valued.v ((y' : Af E) w) ≤ 1) ∧ idealOf y' = idealOf y := ⟨y, hy, rfl⟩
  simp only [dif_pos h]
  rw [Units.val_mul, mul_coord, inv_coord, map_mul, map_inv₀,
    val_eq_of_idealOf_eq h.choose_spec.1 hy h.choose_spec.2 w, inv_mul_cancel₀ (IdeleModule.coord_ne y w)]
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WinLift

theorem eigen_eq_of_frame_eq : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ x y : Ainf p O, WittVector.frobenius x = WittVector.frobenius (xi ε) * x → WittVector.frobenius y = WittVector.frobenius (xi ε) * y → F.a x = F.a y → x = y := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F x y hx hy hxy
  have hsub : WittVector.frobenius (x - y) = WittVector.frobenius (xi ε) * (x - y) := by
    rw [map_sub, hx, hy, mul_sub]
  obtain ⟨c, hc, -⟩ := GlobalTheory.PDivLat.existsUnique_padic_of_eigen p C v O hv ε hε (x - y) hsub
  have h0 : F.a (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  rw [← hc, map_mul, ← F.p_τ] at h0
  have h1 : F.τ * F.a (ofPadic p O c) = 0 := by
    apply tf F
    rw [← h0]; ring
  have h2 : Sandwich.mu ε ∣ ofPadic p O c := (F.τ_mul _).1 h1
  have h3 : WittVector.fontaineTheta O p (ofPadic p O c) = 0 := by
    obtain ⟨w, hw⟩ := h2
    rw [hw, map_mul, theta_mu hv hε, zero_mul]
  have hc0 : c = 0 := by
    by_contra hne
    have hs := PadicInt.unitCoeff_spec hne
    rw [hs, map_mul, map_pow, map_natCast, map_mul, map_pow, map_natCast] at h3
    have hp : (p : O) ≠ 0 := by
      intro h
      have := congrArg (algebraMap O C) h
      rw [map_natCast, map_zero] at this
      exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) this
    have hu : IsUnit (WittVector.fontaineTheta O p (ofPadic p O (PadicInt.unitCoeff hne : ℤ_[p]))) :=
      ((PadicInt.unitCoeff hne).isUnit.map (ofPadic p O)).map _
    rcases mul_eq_zero.1 h3 with h | h
    · exact hu.ne_zero h
    · exact hp (pow_eq_zero_iff'.1 h).1
  rw [← sub_eq_zero, ← hc, hc0, map_zero, zero_mul]

end GlobalTheory.WinLift
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.hasPeriod_reduce_along_theta_to_integers : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ Θ : F.Q →+* E, (∀ b, Θ (algebraMap F.B F.Q b) = algebraMap O E (F.θ b)) → ∀ (f : MvPowerSeries (Fin d) F.Q) (t : G.Tate) (y : F.B), QL μ' ⊤ f → c.HasPeriod F.θ t f y → c.HasPeriod (RingHom.id O) t (map Θ f) (F.θ y) := by
  first | exact @GlobalTheory.QLog.hasPeriod_reduce | exact GlobalTheory.QLog.hasPeriod_reduce | (intros; apply GlobalTheory.QLog.hasPeriod_reduce <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.WTop

theorem mulVec_add_mul {R ι : Type} [CommRing R] [Fintype ι] (N : Matrix ι ι R) (a b : ι → R) (s : R) (i : ι) :
    N.mulVec (fun j => a j + s * b j) i = N.mulVec a i + s * N.mulVec b i := by
  simp only [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring



theorem main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (ι : Type) [Fintype ι] (N : Matrix ι ι (Ainf p O)) (v0 : ι → Ainf p O), IsNil (WittVector.fontaineTheta O p) WittVector.frobenius N → (∀ i, WittVector.frobenius (xi ε) * Sandwich.mu ε ∣ N.mulVec (fun j => WittVector.frobenius (v0 j)) i - WittVector.frobenius (xi ε) * v0 i) → ∃ w : ι → Ainf p O, (∀ i, Sandwich.mu ε ∣ w i - v0 i) ∧ ∀ i, WittVector.frobenius (xi ε) * w i = N.mulVec (fun j => WittVector.frobenius (w j)) i := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε ι _ N v0 hN h
  choose c hc using h
  obtain ⟨z, hz⟩ := (GlobalTheory.T.ainf_frobenius_semilinear_equation_existsUnique p C v O hv ε hε ι N hN).1 c
  refine ⟨fun i => v0 i + Sandwich.mu ε * z i, fun i => ⟨z i, by ring⟩, fun i => ?_⟩
  have hw : (fun j => WittVector.frobenius (v0 j + Sandwich.mu ε * z j)) =
      fun j => WittVector.frobenius (v0 j) +
        (WittVector.frobenius (xi ε) * Sandwich.mu ε) * WittVector.frobenius (z j) := by
    funext j
    rw [map_add (f := _), map_mul, GlobalTheory.WinLift.frob_mu]
  rw [hw, mulVec_add_mul]
  linear_combination (-1 : Ainf p O) * hc i + WittVector.frobenius (xi ε) * Sandwich.mu ε * hz i

end GlobalTheory.WTop
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.formalChart_hasPeriod_linear_integral : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (f g : MvPowerSeries (Fin d) F.Q) (t : G.Tate) (y y' b : F.B), c.HasPeriod F.θ t f y → c.HasPeriod F.θ t g y' → c.HasPeriod F.θ t (f + algebraMap F.B F.Q b • g) (y + b * y') ∧ (∀ s : MvPowerSeries (Fin d) F.B, constantCoeff s = 0 → c.HasPeriod F.θ t (map (algebraMap F.B F.Q) s) 0) := by
  first | exact @GlobalTheory.QLog.hasPeriod_linear | exact GlobalTheory.QLog.hasPeriod_linear | (intros; apply GlobalTheory.QLog.hasPeriod_linear <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLogPeriod

theorem theta_eval_char : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] (ε : PreTilt O p) (hε : IsPrimitiveSystem ε) (F : BFrame ε) (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (χ : G.dual.Tate) (g : MvPowerSeries (Fin d) F.B), (∀ n, c.ev n (map F.θ g) = charElem χ n) → ∀ (t : G.Tate) (n : ℕ) (z : Fin d → F.B), (∀ i, F.θ (z i) = t.pt n (c.x n i)) → (∀ i, ∃ N : ℕ, (p : F.B) ∣ z i ^ N) → ∀ E : MvPowerSeries (Fin d) F.B →ₐ[F.B] F.B, IsEval p z E → F.θ (E g) = zeta ε n ^ GlobalTheory.PDiv.digit n (epsPairing hε G t χ) := by
  intro p _ O _ _ _ _ ε hε F G d c χ g hg t n z hz hnil E hE
  haveI := F.frame.complete
  let Ev : MvPowerSeries (Fin d) O →ₐ[O] O := (t.pt n).comp (c.ev n)
  have hEv : IsEval p (fun i => F.θ (z i)) Ev := by
    refine ⟨fun i => ?_, fun m => ?_⟩
    · change t.pt n (c.ev n (X i)) = F.θ (z i)
      rw [(c.isEval n).1 i, hz]
    · obtain ⟨N, hN⟩ := (c.isEval n).2 m
      refine ⟨N, fun g hg => ?_⟩
      obtain ⟨w, hw⟩ := hN g hg
      refine ⟨t.pt n w, ?_⟩
      change t.pt n (c.ev n g) = _
      rw [hw, map_mul, map_pow, map_natCast]
  have h1 : F.θ (E g) = Ev (map F.θ g) :=
    ((GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural p F.B F.B (Fin d) z hnil).2 E hE).2.2 O O F.θ F.θ Ev (fun _ => rfl) hEv g
  have h2 : Ev (map F.θ g) = t.pt n (charElem χ n) := by
    change t.pt n (c.ev n (map F.θ g)) = _
    rw [hg n]
  rw [h1, h2, ← GlobalTheory.PDivGroup.muRoot_pairing, ← GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.epsPairing_smul hε,
    GlobalTheory.PDivGroup.muRoot_smul]
  unfold epsTate
  rw [GlobalTheory.PDivGroup.muRoot_muTate]

end GlobalTheory.QLogPeriod
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.ev_res_counit_compat : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ n, (∀ f, G.res n (c.ev (n + 1) f) = c.ev n f ∧ Coalgebra.counit (R := O) (c.ev n f) = constantCoeff f) ∧ ∀ s, Algebra.TensorProduct.lift (Bialgebra.counitAlgHom O (G.A n)) (Bialgebra.counitAlgHom O (G.A n)) (fun _ _ => Commute.all _ _) (c.ev₂ n s) = constantCoeff s := by
  first | exact @GlobalTheory.QLog.Chart.ev_res_counit | exact GlobalTheory.QLog.Chart.ev_res_counit | (intros; apply GlobalTheory.QLog.Chart.ev_res_counit <;> assumption)
end
