module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.OverOf4
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle064
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.DirichletGroupPowers.Bundle001
import GroundTheory.GlobalFields.CyclotomicCharacters.Character
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.GoodOf4
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.Bundle001
public import GroundTheory.GlobalFields.ExistenceTheorem.ExistsIsAbelianGaloisRangeIdeleClassNormEqOfFini
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open UpperTheory.V.Ws

namespace UpperTheory.V.Cu.RankFourTwistExistence

section SlopeTestRemainingChoices

variable {Γ O : Type} [Group Γ] [TopologicalSpace Γ] [CommRing O] {I : Ideal O} {γ δ : Γ →* Oˣ}

theorem ac_mul (h : AdicCont I fun g => (γ g : O)) (h' : AdicCont I fun g => (δ g : O)) :
    AdicCont I fun g => ((γ * δ) g : O) := fun N => by
  simp only [MonoidHom.mul_apply, Units.val_mul, map_mul]
  exact (h N).mul (h' N)

theorem ac_zpow (h : AdicCont I fun g => (γ g : O)) (n : ℤ) : AdicCont I fun g => ((γ ^ n) g : O) := fun N => by
  have h1 : IsLocallyConstant fun g => Units.map (Ideal.Quotient.mk (I ^ N)).toMonoidHom (γ g) :=
    IsLocallyConstant.desc _ Units.val (h N) Units.val_injective
  have h2 := h1.comp fun u => ((u ^ n : (O ⧸ I ^ N)ˣ) : O ⧸ I ^ N)
  refine (congrArg IsLocallyConstant (funext fun g => ?_)).mp h2
  simp only [Function.comp_apply, MonoidHom.zpow_apply]
  rw [← map_zpow]
  rfl

theorem ac_ker [IsTopologicalGroup Γ] (h : IsOpen (γ.ker : Set Γ)) : AdicCont I fun g => (γ g : O) := fun N => by
  rw [IsLocallyConstant.iff_exists_open]
  refine fun x => ⟨(fun y => x⁻¹ * y) ⁻¹' γ.ker, h.preimage (continuous_const_mul _), by simp, fun y hy => ?_⟩
  have h1 : γ (x⁻¹ * y) = 1 := hy
  beta_reduce
  rw [← mul_inv_cancel_left x y, map_mul γ, h1, mul_one]

end SlopeTestRemainingChoices

noncomputable def rd {l : ℕ} [Fact l.Prime] (c : Coef l) : c.Oˣ →* (ResidueField c.O)ˣ :=
  Units.map (residue c.O).toMonoidHom

theorem eq_of_rd {l : ℕ} [Fact l.Prime] {c : Coef l} {x y : c.Oˣ} {m : ℕ} (hm : l.Coprime m) (hx : x ^ m = 1)
    (hy : y ^ m = 1) (h : rd c x = rd c y) : x = y :=
  (congrFacts (AlgebraicClosure ℚ) l c).2.2.2.1 x y m ((Nat.Prime.coprime_iff_not_dvd Fact.out).1 hm) hx hy
    (Ideal.Quotient.eq.1 (congrArg Units.val h))

theorem grpF {M : Type} [CommGroup M] (η ω ξ ψ : M) (e k : ℤ) :
    (η ^ (e + 2 - k)) ^ 2 * ((η ^ 2 * ω) ^ (k - 1) * (ξ * ψ)) =
      η ^ 2 * ω * ω⁻¹ * ξ * ((η ^ 2 * ω) ^ e * ψ) * (ω ^ (k - 1) * (ω ^ e)⁻¹) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_pow, ofMul_zpow, ofMul_inv]
  module

theorem grpT {M : Type} [CommGroup M] (η ω ξ ψ : M) (e k : ℤ) :
    (ω ^ e * ψ * η ^ (e + 2 - k)) ^ 2 * ((η ^ 2 * ω) ^ (k - 1) * (ξ * ψ⁻¹)) =
      η ^ 2 * ω * ω⁻¹ * ξ * ((η ^ 2 * ω) ^ e * ψ) * (ω ^ (k - 1) * (ω ^ e)⁻¹) * (ω ^ e) ^ 2 := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_pow, ofMul_zpow, ofMul_inv]
  module

theorem cancel3 {M : Type} [CommGroup M] {a b d p : M} (h : a * b = d ^ 2 * p) (hb : b = d) : a = d * p := by
  subst hb
  apply mul_right_cancel (b := b)
  rw [h, sq, mul_right_comm]

end UpperTheory.V.Cu.RankFourTwistExistence

open UpperTheory.V.Cu.RankFourTwistExistence in
theorem UpperTheory.V.Cu.twEx4 : UpperTheory.V.Cu.TwEx4 := by
  intro Ω _ _ _ l hl c D T h3 k hk1 hk
  have h : D.Good := h3.1
  obtain ⟨-, he2, -, ⟨mψ, -, hmψ, hψ⟩, -⟩ := UpperTheory.V.Ws.large₂.host3 D h3
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hcont, -, homo, -⟩ := UpperTheory.V.GradeZeroInterpolatingElement.facts D h
  obtain ⟨mξ, hmξ, hξ⟩ := h.xi_ord
  have hl1 : l.Coprime (l - 1) := (Nat.coprime_self_sub_right hl.out.one_le).2 (Nat.coprime_one_right l)
  set ε := chiO ℚ Ω l c.O with hε
  set μ : G ℚ Ω →* c.Oˣ := D.al * D.ξ ^ (-1 : ℤ) with hμ
  set P : G ℚ Ω →* c.Oˣ := D.om ^ (D.e : ℤ) * D.ψ with hP
  have al_eq : ∀ g, D.al g = ε g * (D.om g)⁻¹ * D.ξ g := fun _ => rfl
  have mu_eq : ∀ g, μ g = ε g * (D.om g)⁻¹ := fun g => by
    rw [hμ, MonoidHom.mul_apply, MonoidHom.zpow_apply, al_eq, zpow_neg_one, mul_inv_cancel_right]
  have charpoly_eq_of_isIso : ∀ g, P g = D.om g ^ D.e * D.ψ g := fun g => by
    rw [hP, MonoidHom.mul_apply, MonoidHom.zpow_apply, zpow_natCast]
  have P_eqz : ∀ g, P g = D.om g ^ (D.e : ℤ) * D.ψ g := fun g => by
    rw [hP, MonoidHom.mul_apply, MonoidHom.zpow_apply]
  have Psi_z : ∀ g, D.Psi g = ε g ^ (D.e : ℤ) * D.ψ g := fun _ => rfl
  have Psi_eq : ∀ g, D.Psi g = μ g ^ D.e * P g := fun g => by
    have : D.Psi g = ε g ^ D.e * D.ψ g := by rw [← zpow_natCast]; rfl
    rw [this, mu_eq, charpoly_eq_of_isIso, mul_pow, inv_pow, mul_assoc, inv_mul_cancel_left]
  have al_eq' : ∀ g, D.al g = μ g * D.ξ g := fun g => by rw [al_eq, mu_eq]
  have th_eq : ∀ g, D.th g = D.al g * D.Psi g := fun _ => rfl
  have rmu : ∀ g, rd c (μ g) = 1 := fun g => by
    have : rd c (D.om g) = rd c (ε g) := Units.ext (h.om_bar g)
    rw [mu_eq, map_mul, map_inv, this, mul_inv_cancel]
  have ral : ∀ g, rd c (D.al g) = rd c (D.ξ g) := fun g => by rw [al_eq', map_mul, rmu, one_mul]
  have rPsi : ∀ g, rd c (D.Psi g) = rd c (P g) := fun g => by rw [Psi_eq, map_mul, map_pow, rmu, one_pow, one_mul]
  have omp : ∀ g, D.om g ^ (l - 1) = 1 := fun g => DFunLike.congr_fun h.om_pow g
  have hM : l.Coprime ((l - 1) * mψ * mξ) := (hl1.mul_right hmψ).mul_right hmξ
  have PM : ∀ g, P g ^ ((l - 1) * mψ * mξ) = 1 := fun g => by
    have h1 : D.ψ g ^ mψ = 1 := DFunLike.congr_fun hψ g
    rw [charpoly_eq_of_isIso, mul_pow, ← pow_mul, mul_comm D.e, mul_assoc, mul_assoc, pow_mul, omp, one_pow, one_mul, mul_assoc, mul_left_comm,
      pow_mul, h1, one_pow]
  have xM : ∀ g, D.ξ g ^ ((l - 1) * mψ * mξ) = 1 := fun g => by
    have h1 : D.ξ g ^ mξ = 1 := DFunLike.congr_fun hξ g
    rw [mul_comm, pow_mul, h1, one_pow]
  have h2 : IsUnit (2 : c.O) := by
    have : IsUnit ((2 : ℕ) : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
      exact (Nat.coprime_primes hl.out Nat.prime_two).2 h.l_odd
    simpa [map_ofNat] using this.map (algebraMap ℤ_[l] c.O)
  obtain ⟨η, η2, ηr, ηc, η1⟩ := UpperTheory.exists_square_root_character c.O h2 (G ℚ Ω) μ (fun g => congrArg Units.val (rmu g))
    (ac_mul (hcont 2) (ac_zpow (ac_ker h.xi_open) _))
  have rη : ∀ g, rd c (η g) = 1 := fun g => Units.ext (ηr g)
  have eps_eq : ∀ g, ε g = η g ^ 2 * D.om g := fun g => by rw [η2, mu_eq, inv_mul_cancel_right]
  have epz : ∀ g, ε g ^ (k - 1) = ε g ^ ((k : ℤ) - 1) := fun g => by
    rw [← zpow_natCast, Nat.cast_sub hk1, Nat.cast_one]
  have hkz : ((k : ℤ) - 1) = ((k - 1 : ℕ) : ℤ) := by omega
  have omz : ∀ g, D.om g ^ ((k : ℤ) - 1) = D.om g ^ (D.e : ℤ) := fun g => by
    rw [hkz, zpow_natCast, zpow_natCast]
    exact pow_eq_pow_iff_modEq.2 (hk.of_dvd (orderOf_dvd_of_pow_eq_one (omp g)))
  have om2 : ∀ g, (D.om g ^ (D.e : ℤ)) ^ 2 = 1 := fun g => by
    obtain ⟨n, hn⟩ := he2
    rw [zpow_natCast, ← pow_mul, mul_comm, hn, pow_mul, omp, one_pow]
  set j : ℤ := (D.e : ℤ) + 2 - k with hj
  have hc03 : ∀ g, chi D T.pr 0 g * chi D T.pr 3 g = D.th g := fun g => by
    cases T.pr
    · change D.th g * 1 = D.th g
      rw [mul_one]
    · rfl
  obtain ⟨t, tc, tmul, tred, t1⟩ : ∃ t : G ℚ Ω →* c.Oˣ, AdicCont (maximalIdeal c.O) (fun g => (t g : c.O)) ∧
      (∀ g, (t g * η g ^ j) ^ 2 * UpperTheory.V.Cu.Phi D T.pr k g = D.th g) ∧
      (∀ g, rd c (chi D T.pr 3 g) = rd c (t g)) ∧ ∀ g, P g = 1 → t g = 1 := by
    cases hpr : T.pr
    · refine ⟨1, ac_ker (by rw [MonoidHom.ker_one]; exact isOpen_univ), fun g => ?_, fun g => ?_, fun _ _ => rfl⟩
      · change (1 * η g ^ j) ^ 2 * (ε g ^ (k - 1) * (D.ξ g * D.ψ g)) = ε g * (D.om g)⁻¹ * D.ξ g * (ε g ^ (D.e : ℤ) * D.ψ g)
        rw [one_mul, epz, eps_eq, hj, grpF, omz, mul_inv_cancel, mul_one]
      · rfl
    · refine ⟨P, ac_mul (ac_zpow (ac_ker homo) _) (ac_ker h.psi_open), fun g => ?_, fun g => rPsi g, fun _ h => h⟩
      · change (P g * η g ^ j) ^ 2 * (ε g ^ (k - 1) * (D.ξ g * (D.ψ g)⁻¹)) =
          ε g * (D.om g)⁻¹ * D.ξ g * (ε g ^ (D.e : ℤ) * D.ψ g)
        rw [P_eqz, epz, eps_eq, hj, grpT, omz, mul_inv_cancel, mul_one, om2, mul_one]
  have δ_eq : ∀ g, (t * η ^ j) g = t g * η g ^ j := fun _ => rfl
  have rδ : ∀ g, rd c ((t * η ^ j) g) = rd c (t g) := fun g => by rw [δ_eq, map_mul, map_zpow, rη, one_zpow, mul_one]
  refine ⟨t * η ^ j, ⟨ac_mul tc (ac_zpow ηc j), fun g => ?_, fun g => ?_, fun g => ?_, fun g hg hr => ?_,
    D.om.ker ⊓ D.ψ.ker, j, homo.inter h.psi_open, fun g hg => ?_⟩⟩
  · rw [δ_eq]
    exact tmul g
  · have e0 : chi D T.pr 0 g * chi D T.pr 3 g = (t * η ^ j) g ^ 2 * UpperTheory.V.Cu.Phi D T.pr k g := (hc03 g).trans (tmul g).symm
    have e1 := congrArg (rd c) e0
    rw [map_mul, map_mul, map_pow] at e1
    exact congrArg Units.val (cancel3 e1 ((tred g).trans (rδ g).symm))
  · exact congrArg Units.val ((tred g).trans (rδ g).symm)
  · have hr' : ∀ i, rd c (D.ps i g) = 1 := fun i => Units.ext (by
      have := congrFun (congrFun hr i) i
      change residue c.O (D.ps i g : c.O) = 1
      simpa [Raw.rbar, Raw.r0, diagRep] using this)
    have e1 : ε g = 1 := by rw [hε, chiO, MonoidHom.comp_apply, hg, map_one]
    have o1 : D.om g = 1 := eq_of_rd hl1 (omp g) (one_pow _) (e1 ▸ Units.ext (h.om_bar g))
    have p1 : P g = 1 := eq_of_rd hM (PM g) (one_pow _) (by rw [← rPsi, map_one]; exact hr' 1)
    have x1 : D.ξ g = 1 := eq_of_rd hM (xM g) (one_pow _) (by rw [← ral, map_one]; exact hr' 2)
    have s1 : D.ψ g = 1 := by rw [charpoly_eq_of_isIso, o1, one_pow, one_mul] at p1; exact p1
    refine ⟨?_, ?_⟩
    · rw [δ_eq, t1 g p1, η1 g (by rw [mu_eq, e1, o1, inv_one, mul_one]), one_zpow, mul_one]
    · cases T.pr
      · change D.ξ g * D.ψ g = 1
        rw [x1, s1, mul_one]
      · change D.ξ g * (D.ψ g)⁻¹ = 1
        rw [x1, s1, inv_one, mul_one]
  · have o1 : D.om g = 1 := hg.1
    have o2 : D.ψ g = 1 := hg.2
    rw [← hε, δ_eq, t1 g (by rw [charpoly_eq_of_isIso, o1, o2, one_pow, mul_one]), one_mul, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, η2, mu_eq, o1, inv_one, mul_one]
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3 UpperTheory.V.Cu

namespace UpperTheory.V.Cu.AutomorphyOfRankFourLift

theorem irr_cover {H H' K : Type} [Group H] [Group H'] [Field K] {n : Type} [Fintype n] [DecidableEq n]
    (r : H →* Matrix n n K) (r' : H' →* Matrix n n K) (h : ∀ x, ∃ y, ∃ u : K, r x = u • r' y) (hr : Irr r) :
    Irr r' := by
  unfold Irr at hr ⊢
  rw [eq_top_iff, ← hr, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, u, e⟩ := h x
  rw [SetLike.mem_coe, e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem q_apply (d : Dat Ω l) (T : Tower d.D) (g : G T.F Ω) :
    ((d.Q T).map (algebraMap d.c₁.O (PadicAlgCl l))).r g =
      ((toB d.δ (resQ T.F g) : (Qbar l)ˣ) : Qbar l) •
        mapRep (algebraMap d.c₁.O (PadicAlgCl l)) (rep4 1 d.ρ₁ d.τ) (resQ T.F g) := by
  ext i j
  simp only [PD.map_r, Matrix.map_apply, Dat.Q, MonoidHom.comp_apply, mapRep_apply, Matrix.smul_apply, smul_eq_mul,
    rep4, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.one_apply, Units.val_one, one_smul, map_mul]
  rfl

end UpperTheory.V.Cu.AutomorphyOfRankFourLift

open UpperTheory.V.Cu.AutomorphyOfRankFourLift in
theorem UpperTheory.V.Cu.autOf4_of (hne : AlNe) : AutOf4 := by
  intro Ω _ _ _ l _ d T hT hok hirr
  have h1 : Irr ((mapRep (algebraMap d.c₁.O (PadicAlgCl l)) (rep4 1 d.ρ₁ d.τ)).comp (resQ T.L)) := by
    refine irr_cover _ _ (fun x => ?_) hirr
    have hfix : ∀ z ∈ T.L, (x : G T.F Ω) z = z := by
      intro z hz
      have hz' : z ∈ T.F ⊔ T.K := T.hL ▸ hz
      have hle : T.F ⊔ T.K ≤ IntermediateField.fixedField (Subgroup.zpowers (resQ T.F x)) := by
        rw [sup_le_iff, IntermediateField.le_iff_le, IntermediateField.le_iff_le, Subgroup.zpowers_le,
          Subgroup.zpowers_le]
        refine ⟨?_, x.2.1⟩
        rw [IntermediateField.mem_fixingSubgroup_iff]
        exact fun y hy => x.1.commutes ⟨y, hy⟩
      exact (IntermediateField.mem_fixedField_iff _ _).1 (hle hz') _ (Subgroup.mem_zpowers _)
    let y : G T.L Ω := { (x : G T.F Ω).toRingEquiv with commutes' := fun z => hfix z.1 z.2 }
    refine ⟨y, ((toB d.δ (resQ T.F x) : (Qbar l)ˣ) : Qbar l), ?_⟩
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, q_apply,
      show resQ T.L y = resQ T.F (x : G T.F Ω) from AlgEquiv.ext fun _ => rfl]
    rfl
  have hL : IsIrr ((tenB d.ρ₁ d.τ).comp (resQ T.L)) := by
    have := ((irrIff (Qbar l)).1 _).1 h1
    convert this using 1
    ext g : 2
    rfl
  have hkL : ¬ d.K' ≤ T.L := fun hle => by
    obtain ⟨g, hg, hn⟩ := hne Ω l d T hT hok
    refine hn (IntermediateField.fixingSubgroup_le hle ?_)
    rw [T.hL, IntermediateField.fixingSubgroup_sup]
    exact ⟨(IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => g.commutes ⟨y, hy⟩, hg.1⟩
  haveI : Algebra.IsQuadraticExtension ℚ T.K := { finrank_eq_two' := T.degK }
  have hK : IsAbelianGalois ℚ T.K := IsAbelianGalois.of_isCyclic ℚ T.K
  have hLa : IsAbelianGalois ℚ T.L := by
    have h := @GroundTheory.Global.isAbelianGalois_sup ℚ Ω _ _ _ _ T.F T.K
      T.nF.to_finiteDimensional T.nK.to_finiteDimensional T.abF hK
    rw [← T.hL] at h
    exact h
  obtain ⟨π, hreg, hatt⟩ := d.aut T.L hLa hkL
    (goodOf4 Ω l d.c d.D d.T₀ T d.ctx.1 hT d.K' d.quad.splS d.quad.off d.w d.θ d.wp d.wsp d.wunr d.k _ d.ρ d.c₁ d.h d.ρ₁ d.x d.mod) hL
  refine ⟨π, hreg, ?_⟩
  have key : Af.tw (((d.Q T).map (algebraMap d.c₁.O (PadicAlgCl l))).r.comp (resLe T.F_le)).toHomUnits
      ((toB d.δ).comp (resQ T.L))⁻¹ = (tenB d.ρ₁ d.τ).comp (resQ T.L) := by
    ext g : 2
    rw [tw_val]
    change _ • ((d.Q T).map (algebraMap d.c₁.O (PadicAlgCl l))).r (resLe T.F_le g) = _
    rw [q_apply, smul_smul]
    simp only [MonoidHom.inv_apply, MonoidHom.comp_apply]
    rw [show resQ T.F (resLe T.F_le g) = resQ T.L g from AlgEquiv.ext fun _ => rfl, Units.inv_mul, one_smul]
    rfl
  rw [key]
  exact hatt
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open scoped Matrix

namespace UpperTheory.V.Cu.RankFourHodgeWeights

section Alg

variable {R : Type} [CommRing R]

theorem flg_eq (x σ : R) : flg x σ = !![1, 0, 0, 0; σ, 1, 0, 0; -(x * σ), -x, 1, 0; x, 0, -σ, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [flg, tn, nA, low, Matrix.mul_apply, Fin.sum_univ_succ]

theorem adj_flg (x σ : R) : adj (flg x σ) = !![1, 0, 0, 0; -σ, 1, 0, 0; 0, x, 1, 0; -x, x * σ, σ, 1] := by
  rw [flg_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev]

theorem diag (c x σ y : R) (g t : M2 R)
    (h1 : g 0 0 + g 0 1 * x = y) (h2 : g 1 1 - x * g 0 1 = 1)
    (ht1 : t 1 1 = t 0 0) (ht2 : t 1 0 = t 0 1) (i : Fin 4) :
    (adj (flg x σ) * (c • tn g t) * flg x σ) i i =
      c * ![y * (t 0 0 + t 0 1 * σ), y * (t 0 0 - t 0 1 * σ), t 0 0 + t 0 1 * σ, t 0 0 - t 0 1 * σ] i := by
  rw [adj_flg, flg_eq]
  fin_cases i
  · simp [tn, Matrix.mul_apply, Fin.sum_univ_succ, ht1, ht2]
    linear_combination (c * (t 0 0 + t 0 1 * σ)) * h1
  · simp [tn, Matrix.mul_apply, Fin.sum_univ_succ, ht1, ht2]
    linear_combination (c * (t 0 0 - t 0 1 * σ)) * h1
  · simp [tn, Matrix.mul_apply, Fin.sum_univ_succ, ht1, ht2]
    linear_combination (c * (t 0 0 + t 0 1 * σ)) * h2
  · simp [tn, Matrix.mul_apply, Fin.sum_univ_succ, ht1, ht2]
    linear_combination (c * (t 0 0 - t 0 1 * σ)) * h2

theorem hyperbolicOrthogonal_entry_sq_sub_sq_eq_one (t : M2 R) (h : tᵀ * !![1, 0; 0, -1] * t = !![1, 0; 0, -1]) (ht2 : t 1 0 = t 0 1) :
    t 0 0 * t 0 0 - t 0 1 * t 0 1 = 1 := by
  have := congrFun (congrFun h 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_succ] at this
  rw [ht2] at this
  linear_combination this

theorem fin_cg {α : Type} [CommGroup α] (E D : α) (j : ℤ) (n m : ℕ) (hD : D ^ 2 = E ^ j) (i : Fin 4) :
    (D * ![E ^ n * E ^ m, E ^ n * (E ^ m)⁻¹, E ^ m, (E ^ m)⁻¹] i) ^ 2 =
      E ^ (j + 2 * ![(n : ℤ) + m, (n : ℤ) - m, (m : ℤ), -(m : ℤ)] i) := by
  rw [mul_pow, hD, zpow_add]
  congr 1
  fin_cases i <;> simp <;> group

end Alg

private theorem psi_map {ι Γ R R' : Type} [Group Γ] [CommRing R] [CommRing R'] (P : PD ι Γ R) (f : R →+* R') (v : ι) (i : Fin 4) (s : Γ) :
    (P.map f).ψ v i s = f (P.ψ v i s) := by
  have a : adj ((P.n v).map f) = (adj (P.n v)).map f := by
    ext i j
    simp [adj_apply]
  have b : (P.map f).r s = (P.r s).map f := rfl
  have c : (P.map f).n v = (P.n v).map f := rfl
  rw [PD.ψ, b, c, a, ← Matrix.map_mul, ← Matrix.map_mul]
  rfl

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]

private theorem cont_emb (E : Type) [Field E] [NumberField E] [Algebra E Ω] : Continuous (galEmb ℚ E Ω) := by
  haveI : FaithfulSMul E Ω := (faithfulSMul_iff_algebraMap_injective E Ω).2 (algebraMap E Ω).injective
  haveI : Module.IsTorsionFree E Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure E Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) E⟩
  exact (galEmbTop ℚ E Ω).1.continuous

private theorem cont_res (F : IntermediateField ℚ Ω) [NumberField F] : Continuous (resQ F) := cont_emb F

private theorem toB_chi (c : Coef l) (g : G ℚ Ω) : toB (chiO ℚ Ω l c.O) g = cycBar ℚ Ω l g := by
  ext
  rfl

theorem psi_eq (d : Dat Ω l) (T : Tower d.D) (v : T.ι) (s : G T.F Ω) (hs : resQ T.F s ∈ Ine (F := ℚ) (T.pl v)) (i : Fin 4) :
    (d.Q T).ψ v i s = ((toC d.h d.δ (resQ T.F s) * ![chiO ℚ Ω l d.c₁.O (resQ T.F s) ^ (d.k - 1) * chiO ℚ Ω l d.c₁.O (resQ T.F s) ^ d.m,
      chiO ℚ Ω l d.c₁.O (resQ T.F s) ^ (d.k - 1) * (chiO ℚ Ω l d.c₁.O (resQ T.F s) ^ d.m)⁻¹,
      chiO ℚ Ω l d.c₁.O (resQ T.F s) ^ d.m, (chiO ℚ Ω l d.c₁.O (resQ T.F s) ^ d.m)⁻¹] i : d.c₁.Oˣ) : d.c₁.O) := by
  have hA := T.ovl v
  have hD := Ine_le_Dec _ hs
  have hK := d.quad.split _ hA hD
  obtain ⟨h1, h2⟩ := d.mod.ine _ hA _ hs
  obtain ⟨ht1, ht2⟩ := d.tau.on _ hK
  have hp := d.tau.ine _ hA _ hs
  have hσ : d.s (T.pl v) * d.s (T.pl v) = 1 := by
    rcases d.tau.sgn (T.pl v) with h | h <;> rw [h] <;> ring
  have hf : d.τ (resQ T.F s) 0 0 * d.τ (resQ T.F s) 0 0 - d.τ (resQ T.F s) 0 1 * d.τ (resQ T.F s) 0 1 = 1 :=
    hyperbolicOrthogonal_entry_sq_sub_sq_eq_one _ (d.tau.form (resQ T.F s)) ht2
  have hm : d.τ (resQ T.F s) 0 0 - d.τ (resQ T.F s) 0 1 * d.s (T.pl v) =
      (((chiO ℚ Ω l d.c₁.O (resQ T.F s) ^ d.m)⁻¹ : d.c₁.Oˣ) : d.c₁.O) := by
    refine Units.eq_inv_of_mul_eq_one_right ?_
    rw [← hp]
    linear_combination hf - d.τ (resQ T.F s) 0 1 * d.τ (resQ T.F s) 0 1 * hσ
  have e : (d.Q T).ψ v i s = (adj (flg (d.x (T.pl v)) (d.s (T.pl v))) *
      (((toC d.h d.δ (resQ T.F s) : d.c₁.Oˣ) : d.c₁.O) • tn (d.ρ₁ (resQ T.F s)) (d.τ (resQ T.F s))) *
      flg (d.x (T.pl v)) (d.s (T.pl v))) i i := rfl
  rw [e, diag _ _ _ _ _ _ h1 h2 ht1 ht2 i, hp, hm, Units.val_mul]
  congr 1
  fin_cases i <;> simp [Units.val_mul]

end UpperTheory.V.Cu.RankFourHodgeWeights

open UpperTheory.V.Cu

theorem UpperTheory.V.Cu.wtsOf4 : WtsOf4 := by
  intro Ω _ _ _ l _ d T U j hU hj
  refine ⟨U.comap (resQ T.F), hU.preimage (RankFourHodgeWeights.cont_res T.F), fun v i s hs => ?_⟩
  have hI : resQ T.F s ∈ Ine (F := ℚ) (T.pl v) := ⟨hs.2.1, hs.2.2⟩
  have e3 : toB d.δ (resQ T.F s) ^ 2 = cycBar T.F Ω l s ^ j := by
    have := congrArg (Units.map (algebraMap d.c.O (PadicAlgCl l)).toMonoidHom) (hj _ hs.1)
    rw [map_pow, map_zpow] at this
    exact this.trans (congrArg (· ^ j) (RankFourHodgeWeights.toB_chi d.c (resQ T.F s)))
  have hk : (d.k : ℤ) - 1 = ((d.k - 1 : ℕ) : ℤ) := by
    have := d.big
    omega
  dsimp only
  rw [RankFourHodgeWeights.psi_map, RankFourHodgeWeights.psi_eq d T v s hI i, hk]
  have key := RankFourHodgeWeights.fin_cg (cycBar T.F Ω l s) (toB d.δ (resQ T.F s)) j (d.k - 1) d.m e3 i
  have hδ : (Units.map (algebraMap d.c₁.O (PadicAlgCl l)).toMonoidHom) (toC d.h d.δ (resQ T.F s)) = toB d.δ (resQ T.F s) :=
    Units.ext rfl
  have hE : (Units.map (algebraMap d.c₁.O (PadicAlgCl l)).toMonoidHom) (chiO ℚ Ω l d.c₁.O (resQ T.F s)) = cycBar T.F Ω l s :=
    Units.ext rfl
  have hU : (Units.map (algebraMap d.c₁.O (PadicAlgCl l)).toMonoidHom)
      (toC d.h d.δ (resQ T.F s) * ![chiO ℚ Ω l d.c₁.O (resQ T.F s) ^ (d.k - 1) * chiO ℚ Ω l d.c₁.O (resQ T.F s) ^ d.m,
        chiO ℚ Ω l d.c₁.O (resQ T.F s) ^ (d.k - 1) * (chiO ℚ Ω l d.c₁.O (resQ T.F s) ^ d.m)⁻¹,
        chiO ℚ Ω l d.c₁.O (resQ T.F s) ^ d.m, (chiO ℚ Ω l d.c₁.O (resQ T.F s) ^ d.m)⁻¹] i) =
      toB d.δ (resQ T.F s) * ![cycBar T.F Ω l s ^ (d.k - 1) * cycBar T.F Ω l s ^ d.m,
        cycBar T.F Ω l s ^ (d.k - 1) * (cycBar T.F Ω l s ^ d.m)⁻¹, cycBar T.F Ω l s ^ d.m, (cycBar T.F Ω l s ^ d.m)⁻¹] i := by
    rw [← hδ, ← hE]
    fin_cases i <;> simp [map_mul, map_pow, map_inv]
  rw [← key, ← hU, Units.val_pow_eq_pow_val, Units.coe_map]
  rfl
end
end
