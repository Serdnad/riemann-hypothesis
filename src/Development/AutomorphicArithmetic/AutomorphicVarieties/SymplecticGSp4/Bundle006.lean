module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle182
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle006
import Development.AutomorphicArithmetic.AutomorphicVarieties.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
public import Aesop.BuiltinRules
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
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem re_two {Γ M : Type} [Group Γ] [Monoid M] (a b : Γ →* M) :
    ∃ g, (∃ x, a x ≠ 1) → (∃ y, b y ≠ 1) → a g ≠ 1 ∧ b g ≠ 1 := by
  by_cases h : (∃ x, a x ≠ 1) ∧ ∃ y, b y ≠ 1
  · obtain ⟨⟨x, hx⟩, y, hy⟩ := h
    by_cases h1 : b x = 1
    · by_cases h2 : a y = 1
      · exact ⟨x * y, fun _ _ => ⟨by rwa [map_mul, h2, mul_one], by rwa [map_mul, h1, one_mul]⟩⟩
      · exact ⟨y, fun _ _ => ⟨h2, hy⟩⟩
    · exact ⟨x, fun _ _ => ⟨hx, h1⟩⟩
  · exact ⟨1, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩

private theorem re_unit (l : ℕ) [hl : Fact l.Prime] : ∃ u : ℤ_[l]ˣ, ¬ IsOfFinOrder u := by
  have hu : IsUnit ((l + 1 : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    simp
  refine ⟨hu.unit, fun h => ?_⟩
  obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have h1 : ((l + 1 : ℕ) : ℤ_[l]) ^ n = 1 := by
    have := congrArg Units.val e
    rwa [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one] at this
  have h2 : (l + 1) ^ n = 1 := by exact_mod_cast h1
  have h3 := hl.out.pos
  rw [pow_eq_one_iff_left hn.ne'] at h2
  omega

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

private theorem re_cc : ∃ σ : G ℚ Ω, IsCC σ := by
  obtain ⟨σ, h⟩ := exists_isConjOm (E := ℚ) (Ω := Ω)
  refine ⟨AlgEquiv.ofRingEquiv (f := σ) fun x => by rw [eq_ratCast (algebraMap ℚ Ω), map_ratCast], ?_⟩
  exact h

private theorem re_mul {A : ValuationSubring Ω} {q : ℕ} {t g : G ℚ Ω} (ht : t ∈ Ine (F := ℚ) A)
    (hg : IsFrob (F := ℚ) A q g) : IsFrob (F := ℚ) A q (t * g) := by
  refine ⟨mul_mem ht.1 hg.1, fun x hx => ?_⟩
  have hy : A.valuation (g x) ≤ 1 :=
    (A.valuation_le_one_iff _).2 ((apply_mem_iff_of_mem_Dec hg.1 x).2 ((A.valuation_le_one_iff _).1 hx))
  have h3 := Valuation.map_add_lt A.valuation (ht.2 _ hy) (hg.2 x hx)
  rw [sub_add_sub_cancel] at h3
  exact h3

private theorem re_frob (l : ℕ) [hl : Fact l.Prime] (v : ℕ) :
    ∃ (A : ValuationSubring Ω) (σ : G ℚ Ω), v.Prime → A.valuation (v : Ω) < 1 ∧ IsFrob (F := ℚ) A v σ ∧
      (v = l → cycZ ℚ Ω l σ = 1) := by
  by_cases hv : v.Prime
  · obtain ⟨A, hA⟩ := (ML.placeBasic Ω).1 v hv
    obtain ⟨g, hg⟩ := (ML.placeBasic Ω).2.1 A v hv hA
    by_cases e : v = l
    · subst e
      obtain ⟨t, ht, e⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω v A hA (cycZ ℚ Ω v g)⁻¹
      exact ⟨A, t * g, fun _ => ⟨hA, re_mul ht hg, fun _ => by rw [map_mul, e, inv_mul_cancel]⟩⟩
    · exact ⟨A, g, fun _ => ⟨hA, hg, fun h => absurd h e⟩⟩
  · exact ⟨⊤, 1, fun h => absurd h hv⟩

end

theorem UpperTheory.V.GradeZeroInterpolatingElement.rawEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}, l ≠ 2 → ∀ (S : Finset ℕ) (e : ℕ) (ψ ξ : G ℚ Ω →* c.Oˣ), IsOpen (ψ.ker : Set (G ℚ Ω)) → ∃ D : Raw Ω c, D.S = S ∧ D.e = e ∧ D.ψ = ψ ∧ D.ξ = ξ ∧ (∀ p : ℕ, p.Prime → (D.pl p).valuation (p : Ω) < 1) ∧ IsCC D.cc ∧ D.om ^ (l - 1) = 1 ∧ (∀ g, Raw.bar D.om g = Raw.bar (chiO ℚ Ω l c.O) g) ∧ (∀ v : ℕ, v.Prime → IsFrob (D.pl v) v (D.sg v)) ∧ cycZ ℚ Ω l (D.sg l) = 1 ∧ Filter.Tendsto (fun n : ℕ => D.sg l ^ l ^ n.factorial) Filter.atTop (nhds D.ph) ∧ ((∃ g, Raw.bar D.al g ≠ 1) → (∃ g, Raw.bar D.Psi g ≠ 1) → Raw.bar D.al D.g0 ≠ 1 ∧ Raw.bar D.Psi D.g0 ≠ 1) ∧ (D.s0 : G ℚ Ω) ∈ D.Ip l ⊓ D.ψ.ker ⊓ D.om.ker ∧ ¬ IsOfFinOrder (cycZ ℚ Ω l D.s0) := by
  intro Ω _ _ _ l hl c _ S e ψ ξ hψ
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hl2 : 2 ≤ l := hl.out.two_le
  obtain ⟨om, hom, -⟩ := (omT Ω l c).1
  obtain ⟨cc, hcc⟩ := re_cc (Ω := Ω)
  choose pl sg h using re_frob (Ω := Ω) l
  obtain ⟨ph, hph⟩ := (primeTo l (G ℚ Ω) (sg l)).1
  let red : c.Oˣ →* ResidueField c.O := (residue c.O).toMonoidHom.comp (Units.coeHom c.O)
  obtain ⟨g0, hg0⟩ := re_two (red.comp (chiO ℚ Ω l c.O * om⁻¹ * ξ)) (red.comp (Chr.Psi l e ψ))
  obtain ⟨u, hu⟩ := re_unit l
  obtain ⟨s, hs, hsu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l (pl l) (h l hl.out).1 u
  have : Finite (G ℚ Ω ⧸ ψ.ker) := Subgroup.quotient_finite_of_isOpen _ hψ
  have hi : ψ.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hI : s ^ (ψ.ker.index * (l - 1)) ∈ Ine (F := ℚ) (pl l) := pow_mem hs _
  refine ⟨⟨S, e, ψ, ξ, om, cc, pl, sg, ph, g0, ⟨_, hI.1⟩⟩, rfl, rfl, rfl, rfl, fun p hp => (h p hp).1, hcc, hom.1,
    fun g => Ideal.Quotient.eq.2 (hom.2 g), fun v hv => (h v hv).2.1, (h l hl.out).2.2 rfl, hph, hg0, ⟨⟨hI, ?_⟩, ?_⟩, ?_⟩
  · show s ^ (ψ.ker.index * (l - 1)) ∈ ψ.ker
    rw [pow_mul]
    exact pow_mem (Subgroup.pow_index_mem _ s) _
  · show om (s ^ (ψ.ker.index * (l - 1))) = 1
    rw [pow_mul, map_pow]
    exact DFunLike.congr_fun hom.1 _
  · show ¬ IsOfFinOrder (cycZ ℚ Ω l (s ^ (ψ.ker.index * (l - 1))))
    rw [map_pow, hsu]
    exact fun h => hu (h.of_pow (mul_ne_zero hi (by omega)))
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV

namespace UpperTheory.V.GradeZeroInterpolatingElement

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}

def w4 (i : Fin 4) : ℤ × ℤ := (lamW i, muW i)

theorem w4_sub_w4_eq_wt (i j : Fin 4) : w4 i - w4 j = wt i j := rfl

def J4 (R : Type) [CommRing R] : M4 R := !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]

def form (O : Type) [CommRing O] : FormData O w4 where
  J := J4 O
  unit := IsUnit.of_mul_eq_one (-J4 O) (by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [J4, Matrix.mul_apply, Fin.sum_univ_four])
  sym := Or.inr (by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [J4])
  κ := Unit
  blk _ := ()
  σ := id
  invol _ := rfl
  hblk _ _ _ := rfl
  c := (1, 1)
  hw a b h := by
    fin_cases a <;> fin_cases b <;> simp [J4] at h <;> decide

namespace Raw

variable (D : Raw Ω c)

theorem residueChar_mem_levelPrimes : l ∈ D.T := Finset.mem_insert_self _ _

theorem mem_T {p : ℕ} (hp : p ∈ D.Sb) : p ∈ D.T := Finset.mem_insert_of_mem hp

def LocEqs {R : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R] (ρ : ∀ v : D.T, Lift c.O (D.rbarAt v) R) : Prop :=
  D.eqL (ρ ⟨l, D.residueChar_mem_levelPrimes⟩).hom ∧ ∀ p (hp : p ∈ D.Sb), D.eqP p (ρ ⟨p, D.mem_T hp⟩).hom

def SP : Set (HeightOneSpectrum (𝓞 ℚ)) := {v | ∃ p ∈ D.S, ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal}

abbrev Gam : Type := GS Ω D.SP

def frame : Frame D.Gam where
  T := D.T
  v0 := ⟨l, D.residueChar_mem_levelPrimes⟩
  Gv v := D.Gp v
  φ v := locHom D.SP (D.pl v)
  hφ v := continuous_locHom D.SP (D.pl v)
  Q := (D.S \ D.T : Finset ℕ)
  Gq q := D.Gp q
  ψ q := locHom D.SP (D.pl q)
  hψ q := continuous_locHom D.SP (D.pl q)
  N q := (D.Ip q ⊓ D.rbar.ker).subgroupOf (D.Gp q)

def Nums : Prop :=
  ∀ (rb : D.Gam →* M4 (ResidueField c.O)), rb.comp (toGS Ω D.SP) = D.rbar → ∀ (h : (form c.O).Normalises rb) (j : ℤ × ℤ),
    Module.Finite (ResidueField c.O) (D.frame.Ob (FormData.adRep h j)) ∧
    Module.finrank (ResidueField c.O) (D.frame.Ob (FormData.adRep h j)) =
      Module.finrank (ResidueField c.O) (D.frame.H1c (FormData.adRep h j)) +
        (if j = 0 then 2 else if j = wPs ∨ j = -wPs then 1 else 0) ∧
    (j ≠ 0 → j ≠ wPs → j ≠ -wPs → Module.finrank (ResidueField c.O) (D.frame.H1c (FormData.adRep h j)) = 0)

end Raw

structure LocBase (D : Raw Ω c) where
  B : Type
  [cB : CommRing B]
  [aB : Algebra c.O B]
  [coB : IsCO c.O B]
  W : WPres c.O (ℤ × ℤ) B
  wt_mem : ∀ i, W.wt i ∈ wts
  org : W.HasOrigin
  ρ : ∀ v : D.T, Lift c.O (D.rbarAt v) B
  eqs : D.LocEqs ρ
  univ : ∀ (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (ρ' : ∀ v : D.T, Lift c.O (D.rbarAt v) R), D.LocEqs ρ' →
    ∃! f : B →ₐ[c.O] R, ∀ v, (ρ v).map f = ρ' v
  hom : ∀ (v : D.T) g i j, (ρ v).hom g i j ∈ W.part (wt i j)
  at0 : ∀ (v : D.T) (g : D.Gp v) i j, W.origin org ((ρ v).hom g i j) = D.r0 g i j
  smooth : SmoothPt W.gr ((W.origin org).comp W.A.val) fun j => dimL j + D.Sb.card * dimP j

attribute [instance] LocBase.cB LocBase.aB LocBase.coB

end UpperTheory.V.GradeZeroInterpolatingElement

end
end
