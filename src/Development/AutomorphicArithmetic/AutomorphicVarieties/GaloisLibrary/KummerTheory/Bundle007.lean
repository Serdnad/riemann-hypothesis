module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle003
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle006
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle002
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.FinrankAdjoinRootsEqRootDeg
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.GalOpen
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle002
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem totient_le_finrank_mul_natDegree_minpoly (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [CharZero Ω] (ζ : Ω) (N : ℕ) (hζ : IsPrimitiveRoot ζ N) (hN : 0 < N) : N.totient ≤ Module.finrank ℚ F * (minpoly F ζ).natDegree := by
  have hint : IsIntegral F ζ := (hζ.isIntegral hN).tower_top
  haveI : FiniteDimensional F (IntermediateField.adjoin F ({ζ} : Set Ω)) := IntermediateField.adjoin.finiteDimensional hint
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin F ({ζ} : Set Ω)) := Module.Finite.trans F (IntermediateField.adjoin F ({ζ} : Set Ω))
  rw [← IntermediateField.adjoin.finrank hint, Module.finrank_mul_finrank ℚ F (IntermediateField.adjoin F ({ζ} : Set Ω))]
  have h1 : minpoly ℚ ζ = minpoly ℚ ((⟨ζ, IntermediateField.mem_adjoin_simple_self F ζ⟩ : IntermediateField.adjoin F ({ζ} : Set Ω))) :=
    minpoly.algebraMap_eq (A := ℚ) (algebraMap (IntermediateField.adjoin F ({ζ} : Set Ω)) Ω).injective ⟨ζ, IntermediateField.mem_adjoin_simple_self F ζ⟩
  calc N.totient = (minpoly ℚ ζ).natDegree := by
        rw [← Polynomial.cyclotomic_eq_minpoly_rat hζ hN, Polynomial.natDegree_cyclotomic]
    _ = (minpoly ℚ ((⟨ζ, IntermediateField.mem_adjoin_simple_self F ζ⟩ : IntermediateField.adjoin F ({ζ} : Set Ω)))).natDegree := by rw [h1]
    _ ≤ _ := minpoly.natDegree_le _

private theorem natDegree_minpoly_le_of_cycZ_pow_eq_one (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [CharZero Ω] (l : ℕ) [Fact l.Prime] (k : ℕ) (hk : 0 < k) (h : ∀ g : G F Ω, cycZ F Ω l g ^ k = 1) (n : ℕ) (ζ : Ω) (hζ : IsPrimitiveRoot ζ (l ^ n)) : (minpoly F ζ).natDegree ≤ k := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : Normal F Ω := IsAlgClosure.normal F Ω
  haveI : NeZero (l : Ω) := ⟨by exact_mod_cast (Fact.out : l.Prime).ne_zero⟩
  have hint : IsIntegral F ζ := (hζ.isIntegral (pow_pos (Fact.out : l.Prime).pos n)).tower_top
  have hsep : ((minpoly F ζ).map (algebraMap F Ω)).Separable :=
    (minpoly.irreducible hint).separable.map
  have hne : (minpoly F ζ).map (algebraMap F Ω) ≠ 0 :=
    Polynomial.map_ne_zero (minpoly.ne_zero hint)
  let S : Finset ℤ_[l] := (Polynomial.nthRoots k (1 : ℤ_[l])).toFinset
  let T : Finset Ω := S.image (fun x => ζ ^ (PadicInt.toZModPow n x).val)
  have hsub : ((minpoly F ζ).map (algebraMap F Ω)).roots.toFinset ⊆ T := by
    intro y hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hne] at hy
    have hy' : Polynomial.aeval y (minpoly F ζ) = 0 := by
      rw [← Polynomial.eval_map_algebraMap]
      exact hy
    have hmy : minpoly F ζ = minpoly F y :=
      minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hy' (minpoly.monic hint)
    obtain ⟨g, rfl⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := F) (E := Ω)).mp hmy.symm
    rw [Finset.mem_image]
    refine ⟨(cycZ F Ω l g : ℤ_[l]), ?_, ?_⟩
    · rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hk, ← Units.val_pow_eq_pow_val, h g, Units.val_one]
    · exact (cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (G F Ω) Ω g) ζ hζ.pow_eq_one).symm
  calc (minpoly F ζ).natDegree = ((minpoly F ζ).map (algebraMap F Ω)).natDegree :=
        (Polynomial.natDegree_map _).symm
    _ = Multiset.card ((minpoly F ζ).map (algebraMap F Ω)).roots :=
        IsAlgClosed.card_roots_eq_natDegree.symm
    _ = ((minpoly F ζ).map (algebraMap F Ω)).roots.toFinset.card :=
        (Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep)).symm
    _ ≤ T.card := Finset.card_le_card hsub
    _ ≤ S.card := Finset.card_image_le
    _ ≤ Multiset.card (Polynomial.nthRoots k (1 : ℤ_[l])) := Multiset.toFinset_card_le _
    _ ≤ k := Polynomial.card_nthRoots k 1

theorem UpperTheory.V.Kum.resInfInj :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (e : ℤ), e ≠ 0 → Procyc F Ω l → Function.Injective (resInf D e) := by
  intro F Ω _ _ _ _ _ l _ D e he hP
  have hcomp : ∀ h : G F Ω, D.chi (QuotientGroup.mk h) = cycZ F Ω l h := by
    intro h
    rw [← D.hchi]
    rfl
  have hchi : Continuous D.chi := by
    apply (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
    have h := continuous_cycZ F Ω l
    convert h using 1
    funext h
    exact hcomp h
  have hINF : ∃ g : G F Ω, cycZ F Ω l g ^ e ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
    have hk : 0 < e.natAbs := Int.natAbs_pos.mpr he
    have hall : ∀ g : G F Ω, cycZ F Ω l g ^ e.natAbs = 1 := by
      intro g
      have h0 := hcon g
      rcases Int.natAbs_eq e with h' | h'
      · rw [h', zpow_natCast] at h0
        exact h0
      · rw [h', zpow_neg, inv_eq_one, zpow_natCast] at h0
        exact h0
    haveI : NeZero (l : Ω) := ⟨by exact_mod_cast (Fact.out : l.Prime).ne_zero⟩
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ (e.natAbs * Module.finrank ℚ F + 1))
    have hlb := totient_le_finrank_mul_natDegree_minpoly F Ω ζ _ hζ (pow_pos (Fact.out : l.Prime).pos _)
    have hub := natDegree_minpoly_le_of_cycZ_pow_eq_one F Ω l e.natAbs hk hall _ ζ hζ
    have htot : e.natAbs * Module.finrank ℚ F + 1 ≤ (l ^ (e.natAbs * Module.finrank ℚ F + 1)).totient := by
      rw [Nat.totient_prime_pow_succ (Fact.out : l.Prime)]
      have h1 : e.natAbs * Module.finrank ℚ F < l ^ (e.natAbs * Module.finrank ℚ F) :=
        Nat.lt_pow_self (Fact.out : l.Prime).one_lt
      have h2 : 1 ≤ l - 1 := by
        have := (Fact.out : l.Prime).two_le
        omega
      calc e.natAbs * Module.finrank ℚ F + 1 ≤ l ^ (e.natAbs * Module.finrank ℚ F) := h1
        _ = l ^ (e.natAbs * Module.finrank ℚ F) * 1 := (mul_one _).symm
        _ ≤ _ := Nat.mul_le_mul_left _ h2
    have h3 : Module.finrank ℚ F * (minpoly F ζ).natDegree ≤ Module.finrank ℚ F * e.natAbs :=
      Nat.mul_le_mul_left _ hub
    rw [mul_comm (Module.finrank ℚ F) e.natAbs] at h3
    omega
  have hDIV : ∀ a : ℤ_[l], a ≠ 0 → Function.Surjective (fun m : QZ l => a • m) := by
    intro a ha m
    obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) m
    have ha' : algebraMap ℤ_[l] ℚ_[l] a ≠ 0 := by
      intro h0
      apply ha
      exact (FaithfulSMul.algebraMap_injective ℤ_[l] ℚ_[l]) (by rw [h0, map_zero])
    refine ⟨Submodule.Quotient.mk ((algebraMap ℤ_[l] ℚ_[l] a)⁻¹ * q), ?_⟩
    show a • (Submodule.Quotient.mk _ : ℚ_[l] ⧸ ZlSub l) = _
    rw [← Submodule.Quotient.mk_smul, ← algebraMap_smul ℚ_[l] a, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ ha', one_mul]
  rw [← LinearMap.ker_eq_bot]
  unfold resInf resTriv
  apply Submodule.ker_liftQ_eq_bot
  intro z hz
  rw [LinearMap.mem_ker] at hz
  have hclosed : IsClosed ((D.chi.range : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) := by
    rw [MonoidHom.coe_range]
    exact (isCompact_range hchi).isClosed
  have hcond : l ≠ 2 ∨ D.chi.range ≤ KStar.TotallyRealRoots.princ l 2 := by
    rcases hP with h | h
    · exact Or.inl h
    · right
      rintro _ ⟨g, rfl⟩
      obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
      rw [KStar.TotallyRealRoots.princ, MonoidHom.mem_ker, hcomp]
      exact h g'
  obtain ⟨u, huV, hu⟩ := existsGen l D.chi.range hclosed hcond
  obtain ⟨γ, rfl⟩ := huV
  have hcont : ReciprocityTheory.Gal.ContAction (qzTw D e) := by
    apply contScal
    exact Units.continuous_val.comp (hchi.zpow (-e))
  have hne : (((D.chi γ) ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) - 1 ≠ 0 := by
    intro h0
    have h1 : D.chi γ ^ (-e) = 1 := Units.ext (sub_eq_zero.mp h0)
    have h2 : D.chi γ ^ e = 1 := by
      rw [zpow_neg, inv_eq_one] at h1
      exact h1
    obtain ⟨g, hg⟩ := hINF
    apply hg
    have hmem : D.chi (QuotientGroup.mk g) ∈ (Subgroup.zpowers (D.chi γ)).topologicalClosure :=
      hu ⟨_, rfl⟩
    rw [← hcomp]
    have hsub : ((Subgroup.zpowers (D.chi γ)).topologicalClosure : Set ℤ_[l]ˣ) ⊆ {x | x ^ e = 1} := by
      rw [Subgroup.topologicalClosure_coe]
      apply closure_minimal
      · rintro _ ⟨k, rfl⟩
        show ((D.chi γ) ^ k) ^ e = 1
        rw [← zpow_mul, mul_comm, zpow_mul, h2, one_zpow]
      · exact isClosed_eq (continuous_zpow e) continuous_const
    exact hsub hmem
  apply cobOfGen l _ D.chi ℤ_[l] (QZ l) (qzTw D e) γ hchi hcont
  · intro g hg m
    simp [qzTw, scalRep, hg]
  · intro g
    exact hu ⟨g, rfl⟩
  · intro m
    obtain ⟨m', hm'⟩ := hDIV _ hne m
    refine ⟨m', ?_⟩
    simp only [qzTw, scalRep] at hm' ⊢
    rw [← hm', sub_smul, one_smul]
    rfl
  · exact z.2
  · intro g hg
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective g
    have hh : h ∈ Uinf F Ω l := by
      rw [Uinf, cycU, Subgroup.mem_inf, MonoidHom.mem_ker, ← hcomp]
      exact ⟨trivial, hg⟩
    have := congrFun hz ⟨h, hh⟩
    exact this
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.xdualBase :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (E : Type) [Field E] [NumberField E] [Algebra F E] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω] (N : ℕ) (U : Subgroup (G F Ω)) (R M : Type) [CommRing R] [AddCommGroup M] [Module R M], U ≤ galOf F E Ω →
    (∃ ε : (U → M) ≃ₗ[R] (U.comap (galEmb F E Ω) → M), (∀ φ u, ε φ u = φ ⟨galEmb F E Ω u.1, u.2⟩) ∧ (XDual N U R M).map ε.toLinearMap = XDual N (U.comap (galEmb F E Ω)) R M ∧
      ∀ (σ : Ω ≃+* Ω) (T : M →ₗ[R] M), (conjCond U σ T).map ε.toLinearMap = conjCond (U.comap (galEmb F E Ω)) σ T) ∧
    ∀ (l : ℕ) [Fact l.Prime], (cycU l (galOf F E Ω)).comap (galEmb F E Ω) = Uinf E Ω l ∧ ∀ n, (levU l (galOf F E Ω) n).comap (galEmb F E Ω) = Un E Ω l n := by
  intro F Ω _ _ _ _ _ E _ _ _ _ _ _ N U R M _ _ _ hU
  obtain ⟨hD, hI, hc, -⟩ := toGalDict F Ω E U hU
  obtain ⟨hE, -, -⟩ := galEmbTop F E Ω
  let e : U.comap (galEmb F E Ω) ≃ U :=
    { toFun := fun u => ⟨galEmb F E Ω u.1, u.2⟩
      invFun := fun u => ⟨toGal E hU u, u.2⟩
      left_inv := fun u => rfl
      right_inv := fun u => rfl }
  have hec : Continuous e := (hE.continuous.comp continuous_subtype_val).subtype_mk _
  have hes : Continuous e.symm := hc.subtype_mk _
  have hm : ∀ a b, e (a * b) = e a * e b := fun a b => rfl
  have hms : ∀ a b, e.symm (a * b) = e.symm a * e.symm b := fun a b => rfl
  refine ⟨⟨LinearEquiv.funCongrLeft R M e, fun φ u => rfl, ?_, fun σ T => ?_⟩, fun l _ => ?_⟩
  · ext ψ
    constructor
    · rintro ⟨φ, ⟨h1, h2, h3, h4⟩, rfl⟩
      exact ⟨h1.comp_continuous hec, fun a b => h2 (e a) (e b), fun A u hu => h3 A (e u) ((hI A (e u)).1 hu),
        fun A hA u hu => h4 A hA (e u) ((hD A (e u)).1 hu)⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨ψ ∘ e.symm, ⟨h1.comp_continuous hes, fun a b => h2 (e.symm a) (e.symm b),
        fun A u hu => h3 A (e.symm u) ((hI A u).2 hu), fun A hA u hu => h4 A hA (e.symm u) ((hD A u).2 hu)⟩, rfl⟩
  · ext ψ
    constructor
    · rintro ⟨φ, h, rfl⟩
      exact fun u u' huu => h (e u) (e u') huu
    · intro h
      exact ⟨ψ ∘ e.symm, fun u u' huu => h (e.symm u) (e.symm u') huu, rfl⟩
  · have hz : ∀ g, cycZ F Ω l (galEmb F E Ω g) = cycZ E Ω l g := fun g => rfl
    refine ⟨?_, fun n => ?_⟩
    · ext g
      exact ⟨fun h => ⟨trivial, (hz g).symm.trans h.2⟩, fun h => ⟨galEmb_mem F E Ω g, (hz g).trans h.2⟩⟩
    · ext g
      exact ⟨fun h => ⟨trivial, h.2⟩, fun h => ⟨galEmb_mem F E Ω g, h.2⟩⟩
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base

namespace UpperTheory.V.Kum

section Lim

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
  {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

omit [IsAlgClosure F Ω] in
theorem levU_anti (U : Subgroup (G F Ω)) {m n : ℕ} (h : m ≤ n) : levU l U n ≤ levU l U m := by
  intro g hg
  simp only [levU, Subgroup.mem_inf, Subgroup.mem_comap, KStar.TotallyRealRoots.mem_princ] at hg ⊢
  exact ⟨hg.1, (pow_dvd_pow _ h).trans hg.2⟩


theorem galOf_Fn (n : ℕ) : galOf F (Fn F Ω l n) Ω = Un F Ω l n := by
  have := (fnCyc F Ω l n).1
  rw [galOfCyc F Ω l n F (Fn F Ω l n), galOf_self]


private theorem princ_smul_eq_self_of_pow_smul_eq_zero {k : ℕ} {x : QZ l} (hx : l ^ k • x = 0) {w : ℤ_[l]ˣ}
    (hw : w ∈ KStar.TotallyRealRoots.princ l k) : (w : ℤ_[l]) • x = x := by
  rw [KStar.TotallyRealRoots.mem_princ] at hw
  obtain ⟨c, hc⟩ := hw
  have h1 : ((w : ℤ_[l]) - 1) • x = 0 := by
    rw [hc, mul_comm ((l : ℤ_[l]) ^ k) c, mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, hx, smul_zero]
  rw [sub_smul, one_smul, sub_eq_zero] at h1
  exact h1

theorem locConst_qzG (e : ℤ) (m : QZ l) : IsLocallyConstant fun g => qzG F Ω l e g m := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g0
  obtain ⟨k, hk⟩ := (qzBasic l).2.1 m
  have hc : Continuous fun g => cycZ F Ω l g * (cycZ F Ω l g0)⁻¹ :=
    (continuous_cycZ F Ω l).mul continuous_const
  have hmem : ∀ᶠ g in nhds g0, cycZ F Ω l g * (cycZ F Ω l g0)⁻¹ ∈ KStar.TotallyRealRoots.princ l k := by
    apply hc.continuousAt.preimage_mem_nhds
    apply (KStar.TotallyRealRoots.isOpen_princ k).mem_nhds
    simp only [mul_inv_cancel]
    exact (KStar.TotallyRealRoots.princ l k).one_mem
  filter_upwards [hmem] with g hg
  show ((cycZ F Ω l g ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • m = ((cycZ F Ω l g0 ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • m
  have hw : (cycZ F Ω l g * (cycZ F Ω l g0)⁻¹) ^ (-e) ∈ KStar.TotallyRealRoots.princ l k := zpow_mem hg _
  have hx : l ^ k • (((cycZ F Ω l g0 ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • m) = 0 := by
    rw [smul_comm, hk, smul_zero]
  have key : cycZ F Ω l g ^ (-e) =
      (cycZ F Ω l g * (cycZ F Ω l g0)⁻¹) ^ (-e) * cycZ F Ω l g0 ^ (-e) := by
    rw [← mul_zpow, inv_mul_cancel_right]
  rw [key, Units.val_mul, mul_smul, princ_smul_eq_self_of_pow_smul_eq_zero hx hw]

variable [IsCMField F]

end Lim

end UpperTheory.V.Kum

end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem ext_of_prod {Γ R M : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    [T2Space Γ] [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    (ρ : Representation R Γ M) (C U : Subgroup Γ) [hN : U.Normal] (hC : IsClosed (C : Set Γ))
    (hU : IsClosed (U : Set Γ)) (hCU : ∀ g : Γ, ∃ p : C × U, p.1.1 * p.2.1 = g) (φ : U → M) (hρ : ContAction ρ)
    (htr : ∀ u ∈ U, ∀ m, ρ u m = m) (hφ : Continuous φ) (hadd : ∀ a b, φ (a * b) = φ a + φ b)
    (heq : ∀ (g : Γ) (u u' : U), u'.1 * g = g * u.1 → φ u' = ρ g (φ u)) (hv : ∀ x : U, x.1 ∈ C → φ x = 0) :
    ∃ z ∈ Z1 ρ, ∀ u : U, z u.1 = φ u := by
  classical
  obtain ⟨f, hf⟩ : ∃ f : C × U → Γ, ∀ p, f p = p.1.1 * p.2.1 := ⟨_, fun _ => rfl⟩
  have hwd : ∀ p q : C × U, f p = f q → ρ p.1.1 (φ p.2) = ρ q.1.1 (φ q.2) := by
    rintro ⟨⟨c, hc⟩, ⟨u, hu⟩⟩ ⟨⟨c', hc'⟩, ⟨u', hu'⟩⟩ h
    rw [hf, hf] at h
    change c * u = c' * u' at h
    change ρ c (φ ⟨u, hu⟩) = ρ c' (φ ⟨u', hu'⟩)
    have hw1 : c'⁻¹ * c = u' * u⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
    have hwC : c'⁻¹ * c ∈ C := C.mul_mem (C.inv_mem hc') hc
    have hwU : c'⁻¹ * c ∈ U := hw1 ▸ U.mul_mem hu' (U.inv_mem hu)
    have hφw : φ ⟨_, hwU⟩ = 0 := hv _ hwC
    have hu'eq : (⟨u', hu'⟩ : U) = ⟨_, hwU⟩ * ⟨u, hu⟩ := by
      ext
      simp [hw1]
    have h2 : φ ⟨u', hu'⟩ = φ ⟨u, hu⟩ := by rw [hu'eq, hadd, hφw, zero_add]
    rw [h2, show ρ c = ρ c' * ρ (c'⁻¹ * c) by rw [← map_mul, mul_inv_cancel_left],
      Module.End.mul_apply, htr _ hwU]
  choose s hs using hCU
  obtain ⟨z, hz⟩ : ∃ z : Γ → M, ∀ g, z g = ρ (s g).1.1 (φ (s g).2) := ⟨_, fun _ => rfl⟩
  have hzf : ∀ p : C × U, z (f p) = ρ p.1.1 (φ p.2) := by
    intro p
    rw [hz]
    exact hwd _ _ (by rw [hf, hs])
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hC.isCompact
  haveI : CompactSpace U := isCompact_iff_compactSpace.mp hU.isCompact
  have hfc : Continuous f := by
    have : f = fun p : C × U => p.1.1 * p.2.1 := funext hf
    rw [this]
    exact (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  have hfs : Function.Surjective f := fun g => ⟨s g, by rw [hf, hs]⟩
  have hq : Topology.IsQuotientMap f := hfc.isClosedMap.isQuotientMap hfc hfs
  have hzc : Continuous z := by
    rw [hq.continuous_iff]
    have : z ∘ f = fun p : C × U => ρ p.1.1 (φ p.2) := funext hzf
    rw [this]
    exact hρ.comp ((continuous_subtype_val.comp continuous_fst).prodMk (hφ.comp continuous_snd))
  have hzU : ∀ u : U, z u.1 = φ u := by
    intro u
    have h1 := hzf (⟨1, C.one_mem⟩, u)
    rw [hf] at h1
    simpa using h1
  have hcoc : ∀ g h : Γ, z (g * h) = z g + ρ g (z h) := by
    intro g h
    obtain ⟨⟨⟨c, hc⟩, ⟨u, hu⟩⟩, rfl⟩ := hfs g
    obtain ⟨⟨⟨d, hd⟩, ⟨v, hv'⟩⟩, rfl⟩ := hfs h
    have hu0 : d⁻¹ * u * d ∈ U := by simpa using hN.conj_mem u hu d⁻¹
    have hprod : f (⟨c, hc⟩, ⟨u, hu⟩) * f (⟨d, hd⟩, ⟨v, hv'⟩)
        = f (⟨c * d, C.mul_mem hc hd⟩, ⟨d⁻¹ * u * d, hu0⟩ * ⟨v, hv'⟩) := by
      simp only [hf, Subgroup.coe_mul]
      group
    rw [hprod, hzf, hzf, hzf, hf]
    change ρ (c * d) (φ (⟨d⁻¹ * u * d, hu0⟩ * ⟨v, hv'⟩)) = ρ c (φ ⟨u, hu⟩) + ρ (c * u) (ρ d (φ ⟨v, hv'⟩))
    have hconj : φ ⟨u, hu⟩ = ρ d (φ ⟨d⁻¹ * u * d, hu0⟩) :=
      heq d ⟨d⁻¹ * u * d, hu0⟩ ⟨u, hu⟩ (by show u * d = d * (d⁻¹ * u * d); group)
    rw [hadd, map_add (f := _), hconj]
    simp only [map_mul, Module.End.mul_apply]
    rw [htr u hu]
  exact ⟨z, ⟨hzc, hcoc⟩, hzU⟩

theorem UpperTheory.V.Kum.extCocycle :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R (G F Ω) M) (φ : Uinf F Ω l → M), Procyc F Ω l → ContAction ρ → (∀ u ∈ Uinf F Ω l, ∀ m, ρ u m = m) → (∀ m : M, ∃ k : ℕ, l ^ k • m = 0) →
    IsLocallyConstant φ → (∀ a b, φ (a * b) = φ a + φ b) → (∀ g : G F Ω, φ ∈ conjCond (Uinf F Ω l) g.toRingEquiv (ρ g)) → ∃ z ∈ Z1 ρ, ∀ u : Uinf F Ω l, z u.1 = φ u := by
  intro F Ω _ _ _ _ _ l _ R M _ _ _ _ _ ρ φ hP hρ htr htors hloc hadd hconj
  classical
  have hVc : IsClosed ((cycZ F Ω l).range : Set ℤ_[l]ˣ) := by
    rw [MonoidHom.coe_range]
    exact (isCompact_range (continuous_cycZ F Ω l)).isClosed
  have hcond : l ≠ 2 ∨ (cycZ F Ω l).range ≤ KStar.TotallyRealRoots.princ l 2 := by
    rcases hP with h | h
    · exact Or.inl h
    · right
      rintro _ ⟨g, rfl⟩
      exact MonoidHom.mem_ker.mpr (h g)
  obtain ⟨γ0, hγ0, hgen⟩ := existsGen l _ hVc hcond
  obtain ⟨γ, rfl⟩ := hγ0
  have hnf : ¬ IsOfFinOrder (cycZ F Ω l γ) := by
    intro hfin
    obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
    have hS : ∀ u ∈ (cycZ F Ω l).range, u ^ n = 1 := by
      intro u hu
      have hsub : closure ((Subgroup.zpowers (cycZ F Ω l γ) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ)
          ⊆ {x | x ^ n = 1} := by
        apply closure_minimal
        · intro x hx
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
          show ((cycZ F Ω l γ) ^ k) ^ n = 1
          rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hpow, one_zpow]
        · exact isClosed_eq (continuous_pow n) continuous_const
      have h1 := hgen hu
      rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe] at h1
      exact hsub h1
    have htop : KStar.TotallyRealRoots.nu l (KStar.TotallyRealRoots.galImage l F) n = ⊤ := by
      rw [ENat.eq_top_iff_forall_ge]
      intro k
      rw [KStar.TotallyRealRoots.le_nu_iff_pow_mem_princ]
      intro u hu
      rw [KStar.TotallyRealRoots.mem_galImage_iff_of_equiv (RingEquiv.refl F) Ω] at hu
      obtain ⟨g, rfl⟩ := hu
      have h2 := hS (cyclotomicCharacter Ω l g.toRingEquiv) (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
      rw [h2]
      exact Subgroup.one_mem _
    exact KStar.TotallyRealRoots.nu_ne_top KStar.TotallyRealRoots.isOpen_galImage hn.ne' htop
  haveI hN : (Uinf F Ω l).Normal := by
    show (⊤ ⊓ (cycZ F Ω l).ker).Normal
    infer_instance
  have hUc : IsClosed ((Uinf F Ω l : Subgroup (G F Ω)) : Set (G F Ω)) := by
    show IsClosed ((⊤ ⊓ (cycZ F Ω l).ker : Subgroup (G F Ω)) : Set (G F Ω))
    rw [Subgroup.coe_inf, Subgroup.coe_top, Set.univ_inter, MonoidHom.coe_ker]
    exact isClosed_singleton.preimage (continuous_cycZ F Ω l)
  have hCc := Subgroup.isClosed_topologicalClosure (Subgroup.zpowers γ)
  have hmemU : ∀ x : G F Ω, cycZ F Ω l x = 1 → x ∈ Uinf F Ω l := by
    intro x hx
    show x ∈ (⊤ ⊓ (cycZ F Ω l).ker : Subgroup (G F Ω))
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_top x, MonoidHom.mem_ker.mpr hx⟩
  have hCU : ∀ g : G F Ω, ∃ p : (Subgroup.zpowers γ).topologicalClosure × Uinf F Ω l,
      p.1.1 * p.2.1 = g := by
    intro g
    have himg : closure ((Subgroup.zpowers (cycZ F Ω l γ) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ)
        ⊆ (cycZ F Ω l) '' ((Subgroup.zpowers γ).topologicalClosure : Set (G F Ω)) := by
      apply closure_minimal
      · intro x hx
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        exact ⟨γ ^ k, Subgroup.le_topologicalClosure _ (Subgroup.zpow_mem_zpowers γ k), map_zpow _ _ _⟩
      · exact (hCc.isCompact.image (continuous_cycZ F Ω l)).isClosed
    have hg := hgen (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
    rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe] at hg
    obtain ⟨c, hc, hcg⟩ := himg hg
    refine ⟨(⟨c, hc⟩, ⟨c⁻¹ * g, hmemU _ ?_⟩), mul_inv_cancel_left c g⟩
    rw [map_mul, map_inv, hcg, inv_mul_cancel]
  have heq : ∀ (g : G F Ω) (u u' : Uinf F Ω l), u'.1 * g = g * u.1 → φ u' = ρ g (φ u) := by
    intro g u u' h
    apply hconj g u u'
    intro x
    have h3 := congrArg (fun e : G F Ω => e x) h
    simpa [AlgEquiv.mul_apply] using h3
  have hv : ∀ x : Uinf F Ω l, x.1 ∈ (Subgroup.zpowers γ).topologicalClosure → φ x = 0 :=
    fun x hx => vanishCyc F Ω l M φ γ hloc hadd htors hnf x hx
  exact ext_of_prod ρ _ _ hCc hUc hCU φ hρ htr hloc.continuous hadd heq hv
end
