module

import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.VanishingIdealConePrimeHomogeneous
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle439
public import Development.AbelianVarietyTheory.Counterexamples.AbelianLawCounterexamples.WeilIsUniqueOfLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle520
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle393
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle250
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle755
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle051
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechFirstCohomologyDimensionBoundCocycles
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.SemidirectProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle754
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
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle002
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Jacobson.Ring
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003

@[expose] public section

section

open TensorProduct

noncomputable section
namespace GlobalTheory.CxPointsSep

theorem eq_zero_of_forall_algHom {k A : Type} [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]
    [IsReduced A] [Algebra.FiniteType k A] (a : A) (h : ∀ e : A →ₐ[k] k, e a = 0) : a = 0 := by
  apply (config := { allowSynthFailures := true }) GlobalTheory.ZH.ConePrime.eq_zero_of_forall_algHom <;> assumption

theorem isReduced_complex_tensor (D : Type) [CommRing D] [IsDomain D] [Algebra ℚ D]
    [Algebra.FiniteType ℚ D] : IsReduced (ℂ ⊗[ℚ] D) := by
  set K := FractionRing D
  have : Algebra.EssFiniteType ℚ K := inferInstanceAs (Algebra.EssFiniteType ℚ (Localization _))
  have h1 : IsReduced (K ⊗[ℚ] ℂ) := ReciprocityTheory.AnForm.R.BaseChangeC.isReduced_tensor_of_essFiniteType K ℂ
  have h2 : IsReduced (ℂ ⊗[ℚ] K) :=
    isReduced_of_injective (Algebra.TensorProduct.comm ℚ ℂ K).toRingEquiv.toRingHom
      (Algebra.TensorProduct.comm ℚ ℂ K).injective
  have hinj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id ℚ ℂ)
      (IsScalarTower.toAlgHom ℚ D K)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective _ _)
  exact isReduced_of_injective (Algebra.TensorProduct.map (AlgHom.id ℚ ℂ)
      (IsScalarTower.toAlgHom ℚ D K)).toRingHom hinj

theorem exists_det_ne_zero (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Algebra.FiniteType ℤ B]
    (r : ℕ) (f : Fin r → B) (hf : LinearIndependent ℤ f) :
    ∃ x : Fin r → (B →+* ℂ), (Matrix.of fun i j => x i (f j)).det ≠ 0 := by
  classical
  let K := FractionRing B
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra ℤ B).FG)
  let D : Subalgebra ℚ K := Algebra.adjoin ℚ ((algebraMap B K) '' (s : Set B))
  have hmem : ∀ b : B, algebraMap B K b ∈ D := by
    intro b
    have hb : b ∈ Algebra.adjoin ℤ (s : Set B) := by rw [hs]; trivial
    induction hb using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
    | algebraMap n => rw [eq_intCast, map_intCast]; exact intCast_mem D n
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  haveI : Algebra.FiniteType ℚ D := by
    rw [← Subalgebra.fg_iff_finiteType]
    have := Subalgebra.fg_adjoin_finset (R := ℚ) (s.image (algebraMap B K))
    simpa [D] using this
  let g : B →+* D := (algebraMap B K).codRestrict D hmem
  have hg : Function.Injective g := fun a b h =>
    IsFractionRing.injective B K (congrArg Subtype.val h)
  have hD : LinearIndependent ℚ (fun j => g (f j)) := by
    rw [← LinearIndependent.iff_fractionRing ℤ ℚ]
    exact hf.map' g.toAddMonoidHom.toIntLinearMap (LinearMap.ker_eq_bot.mpr hg)
  have hT : LinearIndependent ℂ (fun j => (1 : ℂ) ⊗ₜ[ℚ] g (f j)) :=
    Module.Flat.linearIndependent_one_tmul hD
  haveI : IsReduced (ℂ ⊗[ℚ] D) := isReduced_complex_tensor D
  let pt : ((ℂ ⊗[ℚ] D) →ₐ[ℂ] ℂ) → (B →+* ℂ) := fun φ =>
    (φ.toRingHom.comp (Algebra.TensorProduct.includeRight (R := ℚ) (A := ℂ) (B := D)).toRingHom).comp g
  let S : Set (Fin r → ℂ) := Set.range fun x : B →+* ℂ => fun j => x (f j)
  have hspan : Submodule.span ℂ S = ⊤ := by
    by_contra hne
    obtain ⟨ℓ, hℓ, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    let c : Fin r → ℂ := fun i => ℓ (fun j => if i = j then 1 else 0)
    have hℓv : ∀ v, ℓ v = ∑ i, v i * c i := fun v => by
      rw [LinearMap.pi_apply_eq_sum_univ ℓ v]; rfl
    have hu : ∑ i, c i • ((1 : ℂ) ⊗ₜ[ℚ] g (f i)) = 0 := by
      apply eq_zero_of_forall_algHom (k := ℂ)
      intro φ
      have h0 : ℓ (fun j => pt φ (f j)) = 0 := hle (Submodule.subset_span ⟨pt φ, rfl⟩)
      rw [hℓv] at h0

      rw [map_sum, ← h0]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
      rfl
    have hc : c = 0 := funext fun i => Fintype.linearIndependent_iff.mp hT c hu i
    apply hℓ
    refine LinearMap.ext fun v => ?_
    rw [hℓv, hc]
    simp
  obtain ⟨b, hbS, hbspan, hli⟩ := exists_linearIndependent ℂ S
  have hb_top : ⊤ ≤ Submodule.span ℂ (Set.range ((↑) : b → Fin r → ℂ)) := by
    rw [Subtype.range_coe, hbspan, hspan]
  let bb := Module.Basis.mk hli hb_top
  let e : b ≃ Fin r := bb.indexEquiv (Pi.basisFun ℂ (Fin r))
  have hx : ∀ i : Fin r, ∃ x : B →+* ℂ, (fun j => x (f j)) = ((e.symm i : b) : Fin r → ℂ) :=
    fun i => hbS (e.symm i).2
  choose x hx using hx
  refine ⟨x, ?_⟩
  have hrows : LinearIndependent ℂ (fun i => (Matrix.of fun i j => x i (f j)) i) := by
    have : (fun i => (Matrix.of fun i j => x i (f j)) i) = (fun v : b => (v : Fin r → ℂ)) ∘ e.symm := by
      funext i; exact hx i
    rw [this]; exact hli.comp _ e.symm.injective
  exact ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hrows)).ne_zero

end GlobalTheory.CxPointsSep
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FullLevel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem weilIs_unitOn_unique {S : Scheme.{0}} (G : Over S) [GrpObj G] {L : LB G.left} (hL : L.IsLB)
    {k : Type} [Field k] (x : Sp k ⟶ S) (n : ℤ) (g g' : Over.mk x ⟶ G) (c c' : kˣ)
    (h : Out.WeilIs G L n g g' (unitOn c)) (h' : Out.WeilIs G L n g g' (unitOn c')) : c = c' := by
  apply (config := { allowSynthFailures := true }) GlobalTheory.weilIs_unique_fieldPoint <;> assumption

theorem exists_unique_fullLevel {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B}
    {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S)
    (β : B →+* k) (hx : x ≫ s = spMap β) (z : kˣ) (hz : IsPrimitiveRoot z l.M')
    (hzA : (z : k) ^ (l.M' / l.A) = β b.ζ) :
    ∃! ev : D.La → (Over.mk x ⟶ o.t.G),
      IsSympLevel D (fun a g => g ≫ o.t.act.act a)
          (fun n g g' c => Out.WeilIs o.t.G o.t.PP.L n g g' (unitOn c)) l.M' z ev ∧
        Induces l (fun a => toUnit _ ≫ o.etaA a) (fun a => toUnit _ ≫ o.eta a) ev := by
  obtain ⟨-, I, hIA, hetaA, heta⟩ := o.geom k x β hx
  have hzA' : z ^ (l.M' / l.A) = I.ζ l.A := Units.ext (by rw [Units.val_pow_eq_pow_val, hzA, hIA])
  obtain ⟨ev, hev, hA, hM⟩ := GlobalTheory.T.exists_fullSymplecticLevelStructure_of_tateIso l I hz hzA'
  have hi : Induces l (fun a => toUnit _ ≫ o.etaA a) (fun a => toUnit _ ≫ o.eta a) ev :=
    ⟨fun a => (hA a).trans (hetaA a).symm, fun a ha => (hM a ha).trans (heta a ha).symm⟩
  refine ⟨ev, ⟨hev, hi⟩, ?_⟩
  rintro ev' ⟨h1, h2⟩
  have := GlobalTheory.T.isFullSymplecticLevelStructure_unique_of_levels l (fun g g' c c' => weilIs_unitOn_unique o.t.G o.t.PP.isLB x _ g g' c c') hz
    hev hi h1 h2
  exact this.symm

end GlobalTheory.FullLevel
end
end

section

set_option autoImplicit false
noncomputable section
open Polynomial WittVector GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta

namespace GlobalTheory.BRing

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem frob_congr (x : Ainf p O) : ∃ z, frobenius x = x ^ p + (p : Ainf p O) * z := by
  have h : frobenius x - x ^ p ∈ Ideal.span {(p : Ainf p O)} := by
    rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, map_pow,
      WittVector.constantCoeff_apply, WittVector.constantCoeff_apply, coeff_frobenius_charP, sub_self]
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp h
  exact ⟨y, by linear_combination -hy⟩

theorem frob_teich (r : PreTilt O p) :
    frobenius (teichmuller p r : Ainf p O) = teichmuller p (r ^ p) := by
  rw [frobenius_eq_map_frobenius, map_teichmuller, frobenius_def]

theorem frob_nu (ε : PreTilt O p) : frobenius (nu ε) = mu ε := by
  rw [nu, mu, map_sub, map_one, frob_teich, root, frobeniusEquiv_symm_pow_p]

theorem frob_mu (ε : PreTilt O p) : frobenius (mu ε) = mu ε * frobenius (xi ε) := by
  rw [show frobenius (mu ε) = frobenius (xi ε * nu ε) by rw [xi_mul_nu], map_mul, frob_nu,
    mul_comm]

theorem frob_xi (ε : PreTilt O p) : ∃ d, frobenius (xi ε) = p + mu ε * d := by
  have h : frobenius (xi ε) = ∑ i ∈ Finset.range p, (teichmuller p ε : Ainf p O) ^ i := by

    rw [xi, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_pow, frob_teich, root, frobeniusEquiv_symm_pow_p]
  have hd : ∀ i : ℕ, mu ε ∣ (teichmuller p ε : Ainf p O) ^ i - 1 := fun i => by
    rw [mu]; simpa using sub_dvd_pow_sub_pow (teichmuller p ε : Ainf p O) 1 i
  choose d hd using hd
  refine ⟨∑ i ∈ Finset.range p, d i, ?_⟩
  rw [h, Finset.mul_sum, ← Finset.sum_congr rfl fun i _ => hd i]
  simp [Finset.sum_sub_distrib]

theorem theta_mu {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) :
    fontaineTheta O p (mu ε) = 0 := by
  rw [mu, map_sub, fontaineTheta_teichmuller, map_one, sub_eq_zero]
  exact hε.zeta_zero

variable (ε : PreTilt O p)

def rel : Ideal (Ainf p O)[X] := Ideal.span {C (p : Ainf p O) * X - C (mu ε), X ^ 2}

abbrev BR : Type := (Ainf p O)[X] ⧸ rel ε

def a : Ainf p O →+* BR ε := (Ideal.Quotient.mk (rel ε)).comp C

def τ : BR ε := Ideal.Quotient.mk (rel ε) X

theorem p_τ : (p : BR ε) * τ ε = a ε (mu ε) := by
  rw [τ, a, RingHom.comp_apply, ← map_natCast (Ideal.Quotient.mk (rel ε)), ← map_mul,
    ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, ← map_natCast C]
  exact Ideal.subset_span (Set.mem_insert _ _)

theorem τ_sq : τ ε * τ ε = 0 := by
  rw [τ, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, ← sq]
  exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)

theorem a_natCast (n : ℕ) : a ε n = n := map_natCast _ n

def θ {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) : BR ε →+* O :=
  Ideal.Quotient.lift (rel ε) (eval₂RingHom (fontaineTheta O p) 0) (fun f hf => by
    have h : rel ε ≤ RingHom.ker (eval₂RingHom (fontaineTheta O p) 0) := by
      refine Ideal.span_le.2 ?_
      rintro g (rfl | rfl) <;> simp [theta_mu hε]
    exact (RingHom.mem_ker).1 (h hf))

theorem θ_a {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) (x : Ainf p O) :
    θ hε (a ε x) = fontaineTheta O p x := by
  rw [θ, a, RingHom.comp_apply, Ideal.Quotient.lift_mk]; simp

theorem θ_τ {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) : θ hε (τ ε) = 0 := by
  rw [θ, τ, Ideal.Quotient.lift_mk]; simp

def σ : BR ε →+* BR ε :=
  Ideal.Quotient.lift (rel ε) (eval₂RingHom ((a ε).comp frobenius) (τ ε * a ε (frobenius (xi ε))))
    (fun f hf => by
      have h : rel ε ≤ RingHom.ker (eval₂RingHom ((a ε).comp frobenius)
          (τ ε * a ε (frobenius (xi ε)))) := by
        refine Ideal.span_le.2 ?_
        rintro g (rfl | rfl)
        · simp only [SetLike.mem_coe, RingHom.mem_ker, coe_eval₂RingHom, eval₂_sub, eval₂_mul,
            eval₂_C, eval₂_X, eval₂_natCast, RingHom.comp_apply, map_natCast]
          rw [frob_mu, map_mul, ← p_τ]; ring
        · simp only [SetLike.mem_coe, RingHom.mem_ker, coe_eval₂RingHom, eval₂_X_pow]
          rw [mul_pow, sq (τ ε), τ_sq, zero_mul]
      exact (RingHom.mem_ker).1 (h hf))

theorem σ_a (x : Ainf p O) : σ ε (a ε x) = a ε (frobenius x) := by
  simp [σ, a, Ideal.Quotient.lift_mk]

theorem σ_τ : σ ε (τ ε) = τ ε * a ε (frobenius (xi ε)) := by
  simp [σ, τ, Ideal.Quotient.lift_mk]

abbrev BQ : Type := Localization.Away (p : BR ε)

def s : BQ ε →+* BQ ε :=
  IsLocalization.map (M := Submonoid.powers (p : BR ε)) (T := Submonoid.powers (p : BR ε))
    (BQ ε) (σ ε) (by
      rintro _ ⟨n, rfl⟩
      exact ⟨n, by rw [map_pow, map_natCast]⟩)

theorem s_alg (b : BR ε) : s ε (algebraMap (BR ε) (BQ ε) b) = algebraMap (BR ε) (BQ ε) (σ ε b) :=
  IsLocalization.map_eq _ _

theorem gen (b : BR ε) : ∃ x y, b = a ε x + τ ε * a ε y := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
  refine ⟨f.coeff 0, f.divX.coeff 0, ?_⟩
  have h1 := divX_mul_X_add f
  have h2 := divX_mul_X_add f.divX
  have hX : Ideal.Quotient.mk (rel ε) (X ^ 2) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  conv_lhs => rw [← h1, ← h2]
  simp only [map_add (f := _), map_mul, a, τ, RingHom.comp_apply]
  have : Ideal.Quotient.mk (rel ε) f.divX.divX * Ideal.Quotient.mk (rel ε) X *
      Ideal.Quotient.mk (rel ε) X = 0 := by
    rw [mul_assoc, ← map_mul, ← sq, hX, mul_zero]
  linear_combination this

section Faithful

variable {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} [Algebra O C]
  {ε : PreTilt O p}

theorem prim (hε : IsPrimitiveSystem ε) : IsPrimitiveRoot (root ε).untilt p := by
  simpa [zeta] using hε 1

theorem eps_ne (hv : v.Integers O) (hε : IsPrimitiveSystem ε) : ε - 1 ≠ 0 := by
  rw [← GlobalTheory.MuDivides.constantCoeff_mu, WittVector.constantCoeff_apply]
  exact (GlobalTheory.DetInv.mu_coeff_zero_ne_zero p C v O hv ε (prim hε)).1

theorem mu_ne (hv : v.Integers O) (hε : IsPrimitiveSystem ε) : mu ε ≠ 0 :=
  (GlobalTheory.DetInv.mu_coeff_zero_ne_zero p C v O hv ε (prim hε)).2.1

theorem mu_dvd (hv : v.Integers O) (hε : IsPrimitiveSystem ε) (w : Ainf p O)
    (h : mu ε ∣ (p : Ainf p O) * w) : mu ε ∣ w :=
  GlobalTheory.MuDivides.dvd_of_dvd_p_mul hv ε (eps_ne hv hε) w h

theorem mu_sq_dvd (hv : v.Integers O) (hε : IsPrimitiveSystem ε) (w : Ainf p O)
    (h : mu ε ^ 2 ∣ (p : Ainf p O) * w) : mu ε ^ 2 ∣ w := by
  haveI := GlobalTheory.AinfXi.isDomain_ainf (p := p) hv
  obtain ⟨w', rfl⟩ := mu_dvd hv hε w (dvd_trans (dvd_pow_self _ two_ne_zero) h)
  rw [sq, mul_left_comm] at h
  rw [sq]
  exact mul_dvd_mul_left _ (mu_dvd hv hε w' ((mul_dvd_mul_iff_left (mu_ne hv hε)).1 h))

theorem dvd_of_eq_zero (x y : Ainf p O) (h : a ε x + τ ε * a ε y = 0) :
    mu ε ^ 2 ∣ (p : Ainf p O) * x + mu ε * y := by
  have hm : C x + C y * X ∈ rel ε := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← h, map_add (f := _), map_mul, mul_comm]; rfl
  obtain ⟨h1, h2, he⟩ := Ideal.mem_span_pair.1 hm
  have he' : C x + C y * X = h1 * C (p : Ainf p O) * X - h1 * C (mu ε) + h2 * X ^ 2 := by
    rw [← he]; ring
  have e0 := congrArg (fun f => _root_.AddMonoidAlgebra.coeff (M := ℕ) f 0) he'
  have e1 := congrArg (fun f => _root_.AddMonoidAlgebra.coeff (M := ℕ) f 1) he'
  simp only [coeff_add, coeff_sub, coeff_C_zero, coeff_mul_X_zero, coeff_mul_C,
    coeff_mul_X_pow', coeff_C_succ] at e0 e1
  rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_mul_X, coeff_mul_X, coeff_mul_C, coeff_C_zero] at e1
  simp only [coeff_C_succ, zero_add, Nat.one_lt_ofNat, if_neg (by norm_num : ¬ (2 ≤ 1)),
    if_neg (by norm_num : ¬ (2 ≤ 0)), add_zero, zero_sub] at e0 e1
  refine ⟨-(h1.coeff 1), ?_⟩
  rw [e0, e1]; ring

theorem eq_zero_of_dvd (hv : v.Integers O) (hε : IsPrimitiveSystem ε) (x y : Ainf p O)
    (h : mu ε ^ 2 ∣ (p : Ainf p O) * x + mu ε * y) : a ε x + τ ε * a ε y = 0 := by
  haveI := GlobalTheory.AinfXi.isDomain_ainf (p := p) hv
  obtain ⟨z, hz⟩ := h
  obtain ⟨x', rfl⟩ := mu_dvd hv hε x ⟨-y + mu ε * z, by linear_combination hz⟩
  have hy : y = mu ε * z - p * x' := by
    have : mu ε * (y - (mu ε * z - p * x')) = 0 := by linear_combination hz
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (mu_ne hv hε))
  subst hy
  have h1 := p_τ ε
  have h2 := τ_sq ε
  simp only [map_mul, map_sub, map_natCast]
  rw [← h1]
  linear_combination (↑p * a ε z) * h2

theorem torsion_free (hv : v.Integers O) (hε : IsPrimitiveSystem ε) (b : BR ε)
    (h : (p : BR ε) * b = 0) : b = 0 := by
  obtain ⟨x, y, rfl⟩ := gen ε b
  refine eq_zero_of_dvd hv hε x y (mu_sq_dvd hv hε _ ?_)
  have := dvd_of_eq_zero (ε := ε) (p * x) (p * y) (by
    rw [map_mul, map_mul, a_natCast]; linear_combination h)
  rw [show (p : Ainf p O) * (p * x + mu ε * y) = p * (p * x) + mu ε * (p * y) by ring]
  exact this

end Faithful

end GlobalTheory.BRing
end
end

section

open NumberField MeasureTheory

theorem _root_.GlobalTheory.T.archFactor_mul_pSeries_eq_integral_alt : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ), (∃ i, n i ≠ 0) → ∀ (F : NumberField.RingOfIntegers K → ℂ) (C : ℝ), (∀ α, ‖F α‖ ≤ C) → (∀ (u : (NumberField.RingOfIntegers K)ˣ) (α : NumberField.RingOfIntegers K), F ((u : NumberField.RingOfIntegers K) * α) * GlobalTheory.HeckeStrip.wt φ n (((u : NumberField.RingOfIntegers K) * α : NumberField.RingOfIntegers K) : K) = F α * GlobalTheory.HeckeStrip.wt φ n (α : K)) → ∀ p : (I → ℝ) → ℝ, Measurable p → (∀ y, 0 ≤ p y) → (∀ y, HasSum (fun u : (NumberField.RingOfIntegers K)ˣ => p (y + GlobalTheory.HeckeTheta.ulog φ u)) 1) → ∀ s : ℂ, 1 < s.re → GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor n s * GlobalTheory.HeckeStrip.pSeries F φ n s = 2 ^ Fintype.card I * ∫ y, (p y : ℂ) * GlobalTheory.HeckeTheta.theta (fun α : NumberField.RingOfIntegers K => GlobalTheory.HeckeTheta.emb φ (α : K)) F n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.HeckeMellin.archFactor_mul_pSeries_eq_integral | exact GlobalTheory.HeckeMellin.archFactor_mul_pSeries_eq_integral | (intros; apply GlobalTheory.HeckeMellin.archFactor_mul_pSeries_eq_integral <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

theorem _root_.GlobalTheory.T.cech_first_cohomology_dimension_bound_cocycles : ∀ (K : Type) [Field K] (Y : Scheme.{0}) (s : Y ⟶ Sp K) (g : ℕ) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens), Module.Finite K ((GlobalTheory.AbLaw.cechLB s (LB.triv Y) D).homology 1) → Module.finrank K ((GlobalTheory.AbLaw.cechLB s (LB.triv Y) D).homology 1) ≤ g → ∀ (e : Fin (g + 1) → ∀ i i' : κ, Γ(Y, D i ⊓ D i')), (∀ b i i' i'', resG Y (inf_le_left : D i ⊓ D i' ⊓ D i'' ≤ D i ⊓ D i') (e b i i') + resG Y (le_inf (inf_le_left.trans inf_le_right) inf_le_right : D i ⊓ D i' ⊓ D i'' ≤ D i' ⊓ D i'') (e b i' i'') = resG Y (le_inf (inf_le_left.trans inf_le_left) inf_le_right : D i ⊓ D i' ⊓ D i'' ≤ D i ⊓ D i'') (e b i i'')) → ∃ c : Fin (g + 1) → K, c ≠ 0 ∧ ∃ h : ∀ i, Γ(Y, D i), ∀ i i', ∑ b, (s.appLE ⊤ (D i ⊓ D i') le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (c b)) * e b i i' = resG Y inf_le_left (h i) - resG Y inf_le_right (h i') := by
  first | exact @GlobalTheory.OrdCechDep.exists_comb_coboundary | exact GlobalTheory.OrdCechDep.exists_comb_coboundary | (intros; apply GlobalTheory.OrdCechDep.exists_comb_coboundary <;> assumption)
end

section

open NumberField

namespace GlobalTheory.CuspRep

theorem Zalg_acts_by_scalar : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (c : (E →+* ℂ) → ℂ → ℂ) (z : Module.End ℂ (GlobalTheory.CuspRep.Sm E a)), z ∈ GlobalTheory.CuspRep.Zalg E a →
    ∃ s : ℂ, ∀ φ : GlobalTheory.CuspRep.Sm E a, (∀ τ u, GlobalTheory.CuspRep.cap τ u φ = c τ u • φ) → z φ = s • φ := by
  intro E _ _ _ a c z hz
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨τ, u, rfl⟩ := hx
    exact ⟨c τ u, fun φ hφ => hφ τ u⟩
  | algebraMap r => exact ⟨r, fun φ _ => by simp [Algebra.algebraMap_eq_smul_one]⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    exact ⟨s + t, fun φ hφ => by rw [LinearMap.add_apply, hs φ hφ, ht φ hφ, add_smul]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    exact ⟨s * t, fun φ hφ => by rw [Module.End.mul_apply, ht φ hφ, map_smul, hs φ hφ, smul_smul, mul_comm]⟩

end GlobalTheory.CuspRep
end

section

open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.CuspRep.UnipInv

theorem Eop_unip_left :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (f : Sm E a),
      (∀ (x : BlockIx a r → Ad E) (g : GA E a), f.1 (unip x * g) = f.1 g) →
      ∀ (τ : E →+* ℂ) (i j : Fin a) (x : BlockIx a r → Ad E) (g : GA E a),
        (Eop τ i j f).1 (unip x * g) = (Eop τ i j f).1 g := by
  intro E _ _ _ a r f hf τ i j x g
  have hc : chart f.1 (unip x * g) = chart f.1 g := by
    funext y
    unfold chart
    split_ifs
    · rw [mul_assoc, hf]
    · rfl
  have hD : ∀ X, lieD X f.1 (unip x * g) = lieD X f.1 g := fun X => by
    simp only [lieD, hc]
  simp only [Eop, LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul, Submodule.coe_sub,
    Pi.smul_apply, Pi.sub_apply, lieS_apply, lie_apply, hD]

end GlobalTheory.CuspRep.UnipInv
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.semidirect_coset_pairing_eq_zero_or_twist : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ χ χ' : G ⋊[φ] Γ → ℂ, IsIrrChar ℂ ℂ χ → IsIrrChar ℂ ℂ χ' → ∑ᶠ g, χ (inl g * inr s) * star (χ' (inl g * inr s)) = 0 ∨ ∃ η : G ⋊[φ] Γ →* ℂˣ, (∀ g, η (inl g) = 1) ∧ ∀ x, χ x = χ' x * (η x : ℂ) := by
  first | (exact @GlobalTheory.Shin.coset_pair_eq_zero_or_twist) | (exact GlobalTheory.Shin.coset_pair_eq_zero_or_twist) | (intros; apply GlobalTheory.Shin.coset_pair_eq_zero_or_twist <;> assumption)
end
